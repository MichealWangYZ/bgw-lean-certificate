#!/usr/bin/env python3
"""Generate docs/review/index.html: an interactive guide for a HUMAN reviewer of
the BerkeleyGW endpoint proof chain.

    python3 bgw/endpoint/make_review.py [--bgw-tree DIR] [--out docs/review/index.html]

The page is for reading the ~2k lines that must be read (definitions and
headline statements next to the BerkeleyGW source they transcribe), not the
~90k lines the Lean kernel checks. Every excerpt is extracted from the files
at generation time -- Lean declarations by name, Fortran by cited line range,
Python by function name, axioms from artifacts/axioms.log -- and the script
FAILS if any reference is missing, so the page cannot silently drift from the
repository. Self-contained: no network, no external assets.
"""
import argparse
import datetime
import html
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
DEFAULT_TREE = pathlib.Path(os.environ.get("BGW_TREE", pathlib.Path.home() / "bgw-src/pristine/BerkeleyGW-4.0"))

# ----------------------------------------------------------------------------- extraction

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                  r"(def|theorem|lemma|structure|abbrev|instance)\s+(\S+)")
TOP = re.compile(r"^(?:/--|/-!|@\[|(?:private |protected )?(?:noncomputable )?"
                 r"(?:def|theorem|lemma|structure|abbrev|instance|class|inductive)\b|end\b|"
                 r"section\b|namespace\b|variable\b|open\b|#)")


class Missing(Exception):
    pass


def lean_decl(rel, name, statement_only=None):
    """(first line number, text) of declaration `name` in file `rel`, with its
    docstring. Theorems are cut at the proof (the kernel checks it)."""
    path = ROOT / rel
    lines = path.read_text().splitlines()
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m and m.group(2).split(".")[-1] == name.split(".")[-1] and (
                "." not in name or m.group(2) == name or m.group(2).endswith(name)):
            kind = m.group(1)
            start = i
            if i > 0 and lines[i - 1].rstrip().endswith("-/"):
                j = i - 1
                while j >= 0 and not lines[j].lstrip().startswith("/--"):
                    j -= 1
                start = j if j >= 0 else i
            end = i + 1
            while end < len(lines) and not TOP.match(lines[end]):
                end += 1
            body = lines[start:end]
            cut = statement_only if statement_only is not None else kind in ("theorem", "lemma")
            if cut:
                out = []
                for l2 in lines[start:end]:
                    if ":= by" in l2 or re.search(r":=\s*$", l2):
                        out.append(l2.split(":=")[0].rstrip() + " := ⋯  -- proof checked by the Lean kernel")
                        break
                    out.append(l2)
                    if re.search(r":=\s*\S", l2) and l2 is not lines[start]:
                        break
                body = out
            while body and not body[-1].strip():
                body.pop()
            return start + 1, "\n".join(body)
    raise Missing(f"Lean declaration {name} not found in {rel}")


def fortran(tree, rel, a, b):
    p = tree / rel
    if not p.is_file():
        raise Missing(f"BerkeleyGW source {rel} not found under {tree}")
    lines = p.read_text(errors="replace").splitlines()
    if b > len(lines):
        raise Missing(f"{rel}:{a}-{b} beyond end of file ({len(lines)} lines)")
    return "\n".join(f"{n:5d}  {lines[n - 1]}" for n in range(a, b + 1))


def python_def(rel, name, max_lines=70):
    lines = (ROOT / rel).read_text().splitlines()
    pat = re.compile(r"^(\s*)(?:def|class)\s+" + re.escape(name) + r"\b")
    for i, l in enumerate(lines):
        m = pat.match(l)
        if m:
            ind = len(m.group(1))
            end = i + 1
            while end < len(lines) and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip()) > ind):
                end += 1
            body = lines[i:min(end, i + max_lines)]
            if end > i + max_lines:
                body.append(f"    # ... ({end - i - max_lines} more lines in {rel})")
            return i + 1, "\n".join(body)
    raise Missing(f"Python {name} not found in {rel}")


def audited_axioms():
    log = ROOT / "artifacts/axioms.log"
    out = {}
    if log.is_file():
        for l in log.read_text().splitlines():
            m = re.search(r"AUDITED (\S+): \[(.*)\]", l)
            if m:
                out[m.group(1)] = m.group(2)
    return out


def audit_passed_count():
    """N from the "AXIOM AUDIT PASSED: N theorems" line of artifacts/axioms.log (the count
    README and STATE quote), or None when the log or the line is missing. It can exceed
    len(audited_axioms()): a few AUDITED entries wrap their axiom list onto a second line,
    and the single-line pattern there does not match them."""
    log = ROOT / "artifacts/axioms.log"
    if not log.is_file():
        return None
    hits = re.findall(r"AXIOM AUDIT PASSED: (\d+) theorems", log.read_text())
    return int(hits[-1]) if hits else None


def git(*a):
    try:
        return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return "?"


# ----------------------------------------------------------------------------- content

STATUS = {
    "lean": ("Kernel-checked in Lean", "#1b7f3b"),
    "python": ("Certified in Python interval arithmetic (not Lean)", "#b7791f"),
    "trusted": ("Trusted: not proved", "#b83232"),
    "estimate": ("Estimate / measurement (no bound)", "#5a6472"),
}

# Each node: the claim a reviewer must accept, where it lives, and what to check.
NODES = [
    dict(id="inputs", title="0 · Input files", status="trusted",
         claim="The numbers in BerkeleyGW's binary files WFN, WFNq, WFN_inner and RHO are read by "
               "<code>bgwio.py</code> and written into Lean as exact dyadic rationals (every float64 is a "
               "dyadic, and the exporter asserts the conversion is exact). Lean does not parse the files.",
         why="If the reader mis-parses a record, every theorem downstream is about the wrong numbers.",
         python=[("bgw/endpoint/bgwio.py", "read_wfn"), ("bgw/endpoint/bgwio.py", "read_rho")],
         checks=["read_wfn follows BerkeleyGW 4.0's wfn record layout (Common/wfn_rho_vxc_io_inc.f90)",
                 "the pinned files are the ones produced by run_production.py (its output digests are written "
                 "to run.json in the run directory and are not committed; no committed digest links the Lean "
                 "literals to the run files)",
                 "kernel_export.py asserts exact float→dyadic conversion for every exported literal"]),
    dict(id="unfold", title="1 · Symmetry unfolding", status="lean",
         claim="From the irreducible k-points and the crystal's 48 operations (integer matrices, fractional "
               "translations t = t2/2), Lean rebuilds every wavefunction on the full grids, the G-spheres, "
               "BerkeleyGW's sphere order and the ε index map, and checks them equal to what the later "
               "stages consume. It also checks the 32-point k-set is the group closure and the weights.",
         why="Unfolding (rotations, the non-symmorphic phase of diamond, the last-match op choice) was the "
             "largest piece of trusted Python before; a sign error here changes χ and Σ.",
         lean=[("GW/Endpoint/Kernel/Unfold.lean", "flipG"), ("GW/Endpoint/Kernel/Unfold.lean", "rot"),
               ("GW/Endpoint/Kernel/Unfold.lean", "find"), ("GW/Endpoint/Kernel/Unfold.lean", "kfull"),
               ("GW/Endpoint/Kernel/Unfold.lean", "lastMatch"), ("GW/Endpoint/Kernel/Unfold.lean", "bgwSphere"),
               ("GW/Endpoint/Kernel/UnfoldPhase.lean", "flipG_phase")],
         fortran=[("Common/irrbz.f90", 150, 170)],
         python=[("bgw/endpoint/spec.py", "rotate")],
         checks=["flipG's sign (−1)^((MG)·t2) is exp(−2πi (MG)·t) (proved: flipG_phase) and that is "
                 "BerkeleyGW's rotation convention for a state at Mk",
                 "dropping the global phase e^{2πi(Mk)·t} is legitimate: every use is M(G)·M(G')* or |M|², "
                 "where a per-state phase cancels",
                 "irrbz takes the LAST matching (q, op) pair (lastMatch), not the first",
                 "bgwSphere's 1e-12 tie grouping and GK tie-break reproduce sortrx"]),
    dict(id="eps", title="2 · Dielectric matrix ε", status="lean",
         claim="ε_GG'(q) = δ_GG' − v(q+G)·χ(G,G'), with χ = 4/(N_k Ω) Σ_{k,v,c} M_vc(G) M_vc(G')/(E_v(k+q) − E_c(k)) "
               "and v = 8π/|q+G|² (real π). The kernel proves the TRUE ε, computed from the unfolded "
               "coefficients, lies in the interval box the inverse step uses, at all 3 q-points.",
         why="This is the RPA screening every later number depends on.",
         lean=[("GW/Endpoint/Kernel/EpsSpec.lean", "M"), ("GW/Endpoint/Kernel/EpsSpec.lean", "chi"),
               ("GW/Endpoint/Kernel/EpsSpec.lean", "vC"), ("GW/Endpoint/Kernel/EpsSpec.lean", "epsR")],
         theorems=[("GW/Endpoint/Kernel/Data/E1Check.lean", "epsinv_true_q1")],
         fortran=[("Epsilon/mtxel.f90", 8, 20), ("Epsilon/mtxelmultiply.f90", 58, 100),
                  ("Epsilon/epsinv.f90", 226, 253)],
         python=[("bgw/endpoint/cert.py", "epsinv_iv")],
         checks=["the factor 4/(N_k Ω): 2 for spin × 2 from the ±ω terms at ω = 0, N_k = 32",
                 "the energy denominator E_v − E_c (negative), with valence at k+q from WFNq when q = q0",
                 "row scaling v(q+G_i)·χ (unsymmetrised), as epsinv.f90 does",
                 "the 8π/|q+G|² uses BerkeleyGW's metric bdot (Rydberg units)"]),
    dict(id="epsinv", title="3 · Inverse ε⁻¹", status="lean",
         claim="Every real matrix inside the ε box is invertible and its inverse lies entrywise in the "
               "claimed enclosure (componentwise Neumann bound with exact power-of-two balancing, "
               "re-checked by the kernel in exact integers).",
         why="Spec A uses the exact inverse; production's LAPACK inverse differs by rounding, which is "
             "part of the production-vs-spec comparison (node 9), not of this theorem.",
         lean=[("GW/Endpoint/CertInverse.lean", "inverse_cw_sound")],
         theorems=[("GW/Endpoint/Kernel/Data/Q1Check.lean", "epsinv_enclosure_q1")],
         checks=["the theorem's hypothesis is exactly node 2's conclusion (composed in epsinv_true_q1)"]),
    dict(id="coul", title="4 · Coulomb averages", status="lean",
         claim="v̄(Q) = (8π/|P|) ∫_P |Q+u|⁻² du over the mini-BZ cell P, and the analogous |Q+u|⁻¹ "
               "average for the q→0 wings. Proved in Lean for all 1363 + 7 entries (cone decomposition, "
               "kernel-checked cubature with proved remainders). P is the 26-half-space cell; it equals the "
               "Wigner–Seitz cell a.e. since it contains it and |P| = 1/8 (proved).",
         why="Spec A uses the exact averages; production estimates them by Monte Carlo. That difference "
             "is almost all of the 5.21 µeV production-vs-spec gap.",
         lean=[("GW/Endpoint/Coulomb/Geometry.lean", "cellP"), ("GW/Endpoint/Coulomb/Average.lean", "cavg"),
               ("GW/Endpoint/Coulomb/Average.lean", "vbTrue"), ("GW/Endpoint/Coulomb/Average.lean", "oqTrue"),
               ("GW/Endpoint/Coulomb/Geometry.lean", "volume_cell")],
         theorems=[("GW/Endpoint/Kernel/Data/CoulTab.lean", "vb_hyp")],
         fortran=[("Common/minibzaverage.f90", 47, 85)],
         python=[("bgw/endpoint/coulomb.py", "production")],
         checks=["keyQ: the table key is 2(q+G) in crystal coordinates, and Q = key/2",
                 "the quantity BerkeleyGW's Monte Carlo estimates is this average (spec A vs production)"]),
    dict(id="gpp", title="5 · Plasmon-pole modes", status="lean",
         claim="From ε⁻¹ and the charge density: I = δ − ε⁻¹ (with BerkeleyGW's q→0 wing rule), "
               "Ω²_GG' from RHO (wpeff, including the q = 0, G = 0 row), w̃² = Ω²/I, the drop thresholds "
               "(TOL_SMALL) and the invalid-mode convention w̃ = 1e12.",
         why="These are the branch-sensitive quantities; a threshold or wing mistake changes Σ.",
         lean=[("GW/Endpoint/Kernel/SigmaSpec.lean", "epsS"), ("GW/Endpoint/Kernel/SigmaSpec.lean", "IeS"),
               ("GW/Endpoint/Kernel/SigmaSpec.lean", "Om2S"), ("GW/Endpoint/Kernel/SigmaSpec.lean", "wt2"),
               ("GW/Endpoint/Kernel/SigmaSpec.lean", "wtM"), ("GW/Endpoint/Kernel/SigmaSpec.lean", "keepM")],
         fortran=[("Sigma/mtxel_cor.f90", 690, 797), ("Common/fixwings.f90", 61, 110),
                  ("Common/read_rho_vxc.f90", 185, 196)],
         python=[("bgw/endpoint/cert.py", "modes")],
         checks=["wings applied in the irreducible frame at the sortrx-first G = 0 element",
                 "TS = TOL_SMALL, TZ = TOL_Zero, WINV = 1e12 are BerkeleyGW's constants (binary64 values)",
                 "wpsq = RYD²·16π·n_elec/Ω as in read_rho_vxc.f90"]),
    dict(id="sigma", title="6 · Self-energy Σ", status="lean",
         claim="Bare exchange X, the GPP kernels (generic / near-pole / zero branch, sexcut clamp) summed "
               "over q, bands and (G, G'), the exact static COHSEX remainder, with 1/(N_q Ω). The "
               "division-free branch tests are proved equivalent to the source's wherever the source's formula is "
               "defined, x ≠ ±w̃ (certSsx_eq_srcSsx).",
         why="The formula whose output production prints.",
         lean=[("GW/Endpoint/Kernel/SigmaSpec.lean", "schM"), ("GW/Endpoint/Kernel/SigmaSpec.lean", "ssxM"),
               ("GW/Endpoint/CertSexcut.lean", "srcSsx"), ("GW/Endpoint/CertSexcut.lean", "certSsx"),
               ("GW/Endpoint/CertSexcut.lean", "certSsx_eq_srcSsx"),
               ("GW/Endpoint/Kernel/SigmaSpec.lean", "Xq"), ("GW/Endpoint/Kernel/SigmaSpec.lean", "CSq"),
               ("GW/Endpoint/Kernel/SigmaSpec.lean", "SigA")],
         fortran=[("Sigma/mtxel_cor.f90", 1766, 1850), ("Sigma/mtxel_cor.f90", 600, 649),
                  ("Sigma/mtxel_cor.f90", 3924, 3965)],
         python=[("bgw/endpoint/cert.py", "kernel")],
         checks=["the three branches and their thresholds match mtxel_cor.f90:1817-1843 line by line",
                 "sexcut clamp: ssx = 0 iff |ssx| > sexcut·|I| and wx < 0 (applied after the branch)",
                 "at wx = w̃ (source 0/0) the certificates hold for both IEEE and continuous conventions",
                 "static remainder = ½(exact static CH − Σ partial static CH): exact static CH at "
                 "mtxel_cor.f90:600-649, the per-band partial static CH accumulated by acc_static_ch "
                 "(3924-3965, called at 1703)"]),
    dict(id="o1", title="7 · Eqp1 and O1 (linearised)", status="lean",
         claim="Eqp1 = Eqp0 + dΣ/(1 − dΣ)·(Eqp0 − Eo), Eqp0 = Eo + Σ(Eo) (Vxc = 0), forward difference "
               "with dE = 1 eV; O1 = Eqp1(X, bands 5–6 average) − Eqp1(L, band 5). "
               "<b>Theorem: O1 ∈ [15.4057523, 15.4057537] meV, hence O1 &gt; 0</b>, from the irreducible "
               "WFN data, the exact mini-BZ Coulomb averages and the true ε⁻¹, with no hypothesis left "
               "(Headline.o1_enclosure_irr_unconditional). O1 &gt; 0 compares X and L only; that the "
               "minimum over ALL sampled k-points (Γ included) is at L is Python (cert_o1.json). "
               "This is a statement about the specified 18-band calculation (a code claim), not the "
               "physical band ordering: with all bands of the finite basis the linearised O1 is ≈ −3.8 meV "
               "(Python interval diagnostic, docs/BRIDGE.md BRIDGE-COR).",
         why="The headline claim for spec A.",
         lean=[("GW/Endpoint/Kernel/SigmaSpec.lean", "avg"), ("GW/Endpoint/Kernel/SigmaSpec.lean", "eqp1"),
               ("GW/Endpoint/Kernel/SigmaSpec.lean", "O1")],
         theorems=[("GW/Endpoint/Kernel/Headline.lean", "o1_enclosure_irr_unconditional"),
                   ("GW/Endpoint/Kernel/Headline.lean", "o1_pos_irr_unconditional"),
                   ("GW/Endpoint/Kernel/Data/CoulTab.lean", "o1_enclosure_unconditional"),
                   ("GW/Endpoint/Kernel/Data/US.lean", "o1_enclosure_irr")],
         fortran=[("Sigma/shiftenergy.f90", 176, 196)],
         python=[("bgw/endpoint/cert.py", "eqp1")],
         checks=["the printed unprimed Eqp1 = enew + achcor·zrenorm (sigma_main.f90:2132, "
                 "write_result_hp.f90:66; enew/zrenorm from shiftenergy.f90 WITHOUT achcor) equals the Lean "
                 "eqp1, which puts the E-independent static remainder inside Σ: Eo + (Σ0 + C)/(1 − d), "
                 "with iwlda0 = Eo, iwlda2 = Eo + dE",
                 "RYD = 13.60569253 (nrtype.f90:155)",
                 "the multiplet average and which bands/k-points define O1 (sigma.inp)"]),
    dict(id="roots", title="8 · Full quasiparticle equation", status="lean",
         claim="f(E) = Emf + Σ(E) − E. Kernel-checked: exactly one zero in each of two brackets "
               "(X ≈ 4.1944 eV, Z ≈ 0.858; L ≈ 4.1254 eV, Z ≈ 0.855) and O1_fullQP ∈ [68.9856742, "
               "68.9856744] meV &gt; 0 for those zeros. <b>Only in Python</b>: that these are the PRINCIPAL "
               "(largest-Z) roots, and that they are the only two zeros in "
               "[−10⁴, 10⁴] eV besides a low-weight pair near 30 eV (qp_unique.py; ~3000 CPU-h in the kernel).",
         why="BerkeleyGW's printed Eqp1 is one Newton step; the full equation moves O1 by +54 meV, and "
             "picking the satellite solutions instead would flip its sign (−537 meV).",
         lean=[("GW/Endpoint/Kernel/RootSpec.lean", "fQP"), ("GW/Endpoint/Kernel/RootSpec.lean", "SrcDefOn"),
               ("GW/Endpoint/QPUnique.lean", "IsolatingBracket"),
               ("GW/Endpoint/QPUnique.lean", "qp_roots_enumerated")],
         theorems=[("GW/Endpoint/Kernel/Headline.lean", "o1_fullQP_irr_unconditional"),
                   ("GW/Endpoint/Kernel/Headline.lean", "roots_exist_irr_unconditional")],
         python=[("bgw/endpoint/qp_unique.py", "cover"), ("bgw/endpoint/qp_unique.py", "isolate_root")],
         checks=["the principal (largest-Z) root is the physically intended solution",
                 "the enumeration window [−10⁴, 10⁴] eV is a stated hypothesis (artificial structure near 1e12 eV)"]),
    dict(id="prod", title="9 · Production vs spec A", status="python",
         claim="BerkeleyGW prints O1 = +15.400547 meV; spec A's O1 lies within 5.21 µeV of it. The gap is "
               "the Monte Carlo Coulomb averaging (seed 5000) that spec A replaces by the exact integral. "
               "Individual energies differ more (Eqp1 by ≈ 0.14–0.18 meV, CH by ≈ 0.14–0.30 meV) and "
               "largely cancel in O1; with production's own Monte Carlo averages the reproducer encloses "
               "the printed Eqp1 of the four O1/O2 states and O1 (test_production_conventions_enclose_production).",
         why="This is the link between the theorems (about spec A) and the program's actual output.",
         python=[("bgw/endpoint/observable.py", "observables")],
         checks=["the production value parsed from sigma_hp.log is the right table entry",
                 "the Python reproducer with production's Monte Carlo values reproduces production (E1 tests)"]),
    dict(id="mb", title="10 · GW vs exact (finite models)", status="lean",
         claim="For any finite fermion system H0 + λV with real two-body integrals, H0 diagonal in the reference "
               "orbitals and a strict Slater-determinant ground state: the true "
               "Σ(ω; λ) = λ·HF + λ²(direct + SOX + relax) + O(λ³) (|remainder| ≤ K|λ|³ for some K and small |λ|, "
               "ω off the unperturbed excitations), while at ω also off the GW poles (GWOffPoles) G0W0 gives "
               "λ·HF + λ²·direct; elsewhere sigmaGW2 is a totalized polynomial. So GW misses SOX and relax at "
               "second order (relax = 0 under the Brillouin "
               "condition). Hubbard dimer: Σ_exact = U/2 + direct + SOX exactly, for every U.",
         why="The model layer: what GW leaves out, as theorems rather than estimates. It does not bound GW "
             "for real silicon.",
         lean=[("GW/Endpoint/ManyBody/Decomp.lean", "sig1"), ("GW/Endpoint/ManyBody/DirectSOX.lean", "dir2"),
               ("GW/Endpoint/ManyBody/DirectSOX.lean", "sox2"), ("GW/Endpoint/ManyBody/Static.lean", "relax"),
               ("GW/Endpoint/ManyBody/GroundState.lean", "IsGround"),
               ("GW/Endpoint/ManyBody/Analytic.lean", "sigmaR"), ("GW/Endpoint/ManyBody/Analytic.lean", "sigmaGW2")],
         theorems=[("GW/Endpoint/ManyBody/Analytic.lean", "sigma_exact_expansion"),
                   ("GW/Endpoint/ManyBody/GWError.lean", "gw_error_second_order"),
                   ("GW/Endpoint/HubbardDimerExactSigma.lean", "sigEx_B"),
                   ("GW/Endpoint/HubbardDimerSecondOrder.lean", "gw_error_is_minus_sox")],
         checks=["IsGround (strict ground state of H0 in its sector) is the intended physical hypothesis",
                 "the GW side beyond second order is a truncated polynomial (sigmaGW2), not the full G0W0 function",
                 "the index convention v_pqrs = v_qpsr = v_rspq matches the physics being claimed"]),
    dict(id="si", title="11 · GW approximation for Si (estimates)", status="estimate",
         claim="Measured, not bounded: the plasmon-pole error −31.6 meV at E = Eo; O1 across the GW hierarchy "
               "15 → 69 → 58–67 → 134–138 meV; second-order exchange ≈ +2 meV (relax not estimated).",
         why="No theorem bounds GW for a real solid; these numbers show the spread across GW variants; no physical conclusion is claimed.",
         checks=["C1 (O1 > 0) holds for every 18-band GW variant in the table below; it is NOT robust to "
                 "the band count (all 168 computed bands of the finite basis: ≈ −3.8 meV, Python diagnostic)"]),
]

FINDINGS = [
    ("The production number is not physically meaningful at this setup",
     "With Vxc = 0 (EPM) the QP energies sit ~7 eV from Emf. Linearisation moves O1 by −54 meV; the "
     "plasmon-pole error on Σ_c(X) − Σ_c(L) at E = Eo is −32 meV; O1 spans 15–138 meV across the "
     "well-defined GW variants at 18 bands (~+154 with sexcut off, not unique). With all 168 computed bands "
     "of the finite basis the linearised O1 is ≈ −3.8 meV (Python interval diagnostic, BerkeleyGW "
     "cross-checked; docs/BRIDGE.md BRIDGE-COR), so C1 (O1 > 0) is a property of the specified 18-band "
     "calculation, not the physical band ordering."),
    ("The QP equation has two solutions per state",
     "Principal roots (Z ≈ 0.86) and low-weight roots near 30 eV (Z ≈ 0.04). C1 depends on choosing the "
     "principal one; the other pairing gives −537 meV."),
    ("Production agrees with the transcribed specification on this run",
     "Production O1 matches spec A to 5.21 µeV, and no discrepancy between production and spec A was found. "
     "That spec A is BerkeleyGW's formula is the transcription trust item (source reading plus this "
     "agreement on one run); it is not a proof that BerkeleyGW is correct."),
    ("Bugs found were in the certifier, and fixed",
     "Near-pole sexcut threshold off by 2; value at wx = w̃ disagreeing with the Fortran; rescaling not "
     "rounded outward for subnormals; an earlier ‘unique root’ that was a window artefact."),
    ("The planned second-order theorem was false",
     "GW misses SOX and a relaxation term unless the start is self-consistent HF (confirmed by exact "
     "diagonalisation, check_sigma2.py --n 4 with its defaults: max mismatch ≈ 13.5 without relax, "
     "≤ 6e-7 with it)."),
]

TABLE = [("G0W0-GPP, linearised (spec A; production prints 15.400547 meV, measured)", "+15.4", "Lean (spec A)"),
         ("G0W0-GPP, linearised, all 168 computed bands of the finite basis", "≈ −3.8 ([−5.25, −4.71] without the static residual)",
          "Python intervals (BRIDGE-COR, R28-F3/F4)"),
         ("G0W0-GPP, full QP equation, principal roots", "+69.0", "Lean (roots in brackets); principal-root selection Python"),
         ("G0W0-GPP, full QP, sexcut off", "~+154, not unique", "float"),
         ("G0W0 full-frequency RPA (contour deformation)", "+58 to +67", "production runs"),
         ("evGW0-GPP", "+137.9", "production runs"),
         ("evGW-GPP", "+134.2 ± 0.03", "production runs")]

TRUSTED = [
    ("Binary file reader", "bgwio.py and the exporter's float→dyadic transcription (node 0)."),
    ("Transcription", "that the Lean definitions are BerkeleyGW's formulas: they mirror the Python reproducer, "
                      "which with production's Monte Carlo averages encloses the printed Eqp1 of the four "
                      "O1/O2 states and O1; "
                      "no proof can remove this — it is what this page is for."),
    ("Production vs spec A", "the 5.21 µeV link (node 9): exact rational arithmetic on the kernel-checked "
                             "endpoints and the printed production value (1 neV print slack), in a Python test."),
    ("Root cover", "“exactly two roots” in the window and the principal-root selection (node 8) are Python."),
    ("CBM over all k-points", "that the conduction minimum over ALL sampled k-points (Γ included) is at L "
                              "(node 7) is a Python interval result; the Lean theorem compares X and L."),
    ("Constants", "RYD = 13.60569253 and BerkeleyGW's thresholds as their binary64 values."),
    ("Physical symmetry", "that the 48 operations map the crystal onto itself is taken from the file header."),
    ("Rounding hypothesis", "the Python interval code assumes IEEE round-to-nearest (only for the parts still in Python)."),
]

# ----------------------------------------------------------------------------- rendering

CSS = """
:root{--bg:#fbfbfa;--fg:#1d2330;--mute:#5a6472;--card:#fff;--line:#e3e5e8;--code:#f4f5f7}
*{box-sizing:border-box}body{margin:0;font:15px/1.55 -apple-system,Segoe UI,Helvetica,Arial,sans-serif;color:var(--fg);background:var(--bg)}
header{padding:22px 32px;border-bottom:1px solid var(--line);background:#fff}
h1{font-size:22px;margin:0 0 6px}h2{font-size:18px;margin:28px 0 10px}h3{font-size:15px;margin:18px 0 6px}
.sub{color:var(--mute);font-size:13px}
.wrap{display:flex;min-height:calc(100vh - 90px)}
nav{width:290px;flex:none;border-right:1px solid var(--line);background:#fff;padding:14px;position:sticky;top:0;height:100vh;overflow:auto}
main{flex:1;padding:18px 32px 80px;max-width:1150px}
nav a{display:flex;align-items:center;gap:8px;padding:6px 8px;border-radius:6px;color:var(--fg);text-decoration:none;font-size:14px}
nav a:hover,nav a.on{background:#eef1f5}
.dot{width:10px;height:10px;border-radius:50%;flex:none}
.pill{display:inline-block;padding:1px 9px;border-radius:10px;color:#fff;font-size:12px;font-weight:600}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:16px 20px;margin:14px 0}
.flow{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:10px 0}
.flow .n{border:2px solid;border-radius:8px;padding:6px 10px;font-size:13px;cursor:pointer;background:#fff}
.flow .arr{color:var(--mute)}
pre{background:var(--code);border:1px solid var(--line);border-radius:6px;padding:10px 12px;overflow:auto;font:12.5px/1.45 ui-monospace,SFMono-Regular,Menlo,monospace;margin:6px 0}
.loc{font:12px ui-monospace,monospace;color:var(--mute)}
.tabs{display:flex;gap:4px;border-bottom:1px solid var(--line);margin-top:10px}
.tabs button{border:0;background:none;padding:6px 12px;cursor:pointer;font-size:13px;border-bottom:2px solid transparent;color:var(--mute)}
.tabs button.on{border-color:#2b5cab;color:var(--fg);font-weight:600}
.pane{display:none}.pane.on{display:block}
.chk label{display:block;padding:3px 0;font-size:14px}
.kw{color:#7a3e9d;font-weight:600}.cm{color:#6a737d}.th{color:#1b5e20}
table{border-collapse:collapse;width:100%;font-size:14px}td,th{border-bottom:1px solid var(--line);padding:6px 8px;text-align:left}
#bar{height:8px;background:#e7e9ec;border-radius:4px;overflow:hidden;margin:6px 0}#bar i{display:block;height:100%;background:#1b7f3b;width:0}
input#q{width:100%;padding:6px 8px;border:1px solid var(--line);border-radius:6px;margin:4px 0 10px}
.ax{font:12px ui-monospace,monospace;color:#1b5e20}
.small{font-size:13px;color:var(--mute)}
"""

JS = r"""
const KEY='bgw-review-v1';
const st=JSON.parse(localStorage.getItem(KEY)||'{}');
function save(){localStorage.setItem(KEY,JSON.stringify(st));prog();}
function prog(){const b=[...document.querySelectorAll('.chk input')];const d=b.filter(x=>x.checked).length;
 document.querySelector('#bar i').style.width=(100*d/Math.max(1,b.length))+'%';
 document.getElementById('pc').textContent=d+' / '+b.length+' review items checked';
 document.querySelectorAll('nav a[data-node]').forEach(a=>{const n=a.dataset.node;const bs=[...document.querySelectorAll('#'+n+' .chk input')];
   const ok=bs.length&&bs.every(x=>x.checked);a.querySelector('.done').textContent=ok?'✓':'';});}
document.querySelectorAll('.chk input').forEach(c=>{c.checked=!!st[c.id];c.onchange=()=>{st[c.id]=c.checked;save();};});
document.querySelectorAll('.tabs').forEach(t=>{t.querySelectorAll('button').forEach(b=>b.onclick=()=>{
  t.querySelectorAll('button').forEach(x=>x.classList.remove('on'));b.classList.add('on');
  const card=t.parentElement;card.querySelectorAll('.pane').forEach(p=>p.classList.toggle('on',p.dataset.p===b.dataset.p));});});
function go(id){const e=document.getElementById(id);if(e){e.scrollIntoView({behavior:'smooth',block:'start'});
  document.querySelectorAll('nav a').forEach(a=>a.classList.toggle('on',a.getAttribute('href')==='#'+id));}}
document.querySelectorAll('[data-go]').forEach(e=>e.onclick=()=>go(e.dataset.go));
document.getElementById('q').oninput=e=>{const q=e.target.value.toLowerCase();
  document.querySelectorAll('section.node').forEach(s=>{s.style.display=!q||s.textContent.toLowerCase().includes(q)?'':'none';});};
document.getElementById('reset').onclick=()=>{if(confirm('Clear all review checks in this browser?')){for(const k in st)delete st[k];document.querySelectorAll('.chk input').forEach(c=>c.checked=false);save();}};
prog();
"""

KW = r"\b(noncomputable|def|theorem|lemma|structure|abbrev|where|let|if|then|else|fun|∀|∃|Prop|ℝ|ℕ|ℤ)\b"


def hl_lean(s):
    s = html.escape(s)
    s = re.sub(r"(--[^\n]*)", r'<span class="cm">\1</span>', s)
    s = re.sub(r"(/--.*?-/)", r'<span class="cm">\1</span>', s, flags=re.S)
    s = re.sub(KW, r'<span class="kw">\1</span>', s)
    return s


def code_block(loc, text, lean=False):
    body = hl_lean(text) if lean else html.escape(text)
    return f'<div class="loc">{html.escape(loc)}</div><pre>{body}</pre>'


def render(tree):
    ax = audited_axioms()
    commit = git("rev-parse", "--short", "HEAD")
    branch = git("rev-parse", "--abbrev-ref", "HEAD")
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    n_pass = audit_passed_count()
    n_ax = n_pass if n_pass is not None else len(ax)

    def axioms_for(name):
        hits = [v for k, v in ax.items() if k.endswith("." + name) or k == name]
        return hits[0] if len(hits) == 1 else (hits[0] if hits else None)

    out = []
    out.append("<!doctype html><html lang='en'><head><meta charset='utf-8'>"
               "<meta name='viewport' content='width=device-width,initial-scale=1'>"
               f"<title>BerkeleyGW endpoint — reviewer's guide</title><style>{CSS}</style></head><body>")
    out.append(f"<header><h1>BerkeleyGW endpoint: a reviewer's guide to the proof chain</h1>"
               f"<div class='sub'>Si-EPM, BerkeleyGW 4.0 GPP self-energy · branch <code>{branch}</code> @ "
               f"<code>{commit}</code> · generated {now} by <code>bgw/endpoint/make_review.py</code> · "
               f"{n_ax} audited theorems in artifacts/axioms.log</div></header>")
    out.append("<div class='wrap'><nav><input id='q' placeholder='Filter nodes…'>"
               "<div id='bar'><i></i></div><div class='small' id='pc'></div>"
               "<a href='#start'>How to read this</a>")
    for n in NODES:
        c = STATUS[n["status"]][1]
        out.append(f"<a href='#{n['id']}' data-node='{n['id']}'><span class='dot' style='background:{c}'></span>"
                   f"<span style='flex:1'>{html.escape(n['title'])}</span><span class='done th'></span></a>")
    out.append("<a href='#findings'>Findings</a><a href='#table'>O1 across treatments</a>"
               "<a href='#trusted'>What is still trusted</a>"
               "<p class='small'><button id='reset'>reset checklist</button></p></nav><main>")

    out.append("<section id='start'><h2>How to read this</h2><div class='card'>")
    out.append("<p><b>The claim.</b> For the Si-EPM test case, the observable O1 = Eqp1(X) − Eqp1(L) of the "
               "Lean specification of BerkeleyGW's equations (<i>spec A</i>), evaluated on the run's exported "
               "data, lies in [15.4057523, 15.4057537] meV (so Eqp1(X) &gt; Eqp1(L)); with the full QP "
               "equation, O1 ∈ [68.9856742, 68.9856744] meV for the unique roots in two certified brackets "
               "(that these are the principal roots is Python). Both are Lean theorems checked by the kernel "
               "from the irreducible wavefunctions, with no Coulomb-box hypothesis left. They are statements "
               "about the "
               "specified 18-band calculation, not the physical band ordering: with all bands of the finite "
               "basis the linearised O1 is ≈ −3.8 meV (Python). Trusted, not proved: the decoding of the run "
               "files, that spec A transcribes BerkeleyGW's Fortran (what this page is for), and the "
               "production run.</p>")
    out.append("<p><b>What you need to read.</b> Not the proofs — the kernel checks those, and the axiom "
               "audit confirms nothing was assumed. You need to read the <i>definitions</i> and the "
               "<i>statements</i>: if a definition says the wrong thing, the theorem proves the wrong thing. "
               "Each node below puts the Lean definition next to the BerkeleyGW source it claims to "
               "transcribe, with a checklist. Your progress is saved in this browser.</p>")
    out.append("<p>" + " ".join(f"<span class='pill' style='background:{c}'>{html.escape(t)}</span>"
                                for t, c in STATUS.values()) + "</p>")
    groups = [("Implementation layer — spec A, from the files to O1", ["inputs", "unfold", "eps", "epsinv", "coul",
                                                                    "gpp", "sigma", "o1", "roots"]),
              ("Link to the program's printed output", ["prod"]),
              ("Physics layer — GW versus the exact many-body answer", ["mb", "si"])]
    byid = {n["id"]: n for n in NODES}
    for gtitle, ids in groups:
        out.append(f"<h3>{html.escape(gtitle)}</h3><div class='flow'>")
        for i, nid in enumerate(ids):
            n = byid[nid]
            c = STATUS[n["status"]][1]
            if i:
                out.append("<span class='arr'>→</span>" if gtitle.startswith("Impl") else "<span class='arr'>·</span>")
            out.append(f"<span class='n' style='border-color:{c}' data-go='{n['id']}'>{html.escape(n['title'])}</span>")
        out.append("</div>")
    assert sorted(i for _, ids in groups for i in ids) == sorted(byid)
    out.append("</div></section>")

    for n in NODES:
        label, c = STATUS[n["status"]]
        out.append(f"<section class='node' id='{n['id']}'><div class='card'>"
                   f"<h2 style='margin-top:0'>{html.escape(n['title'])} "
                   f"<span class='pill' style='background:{c}'>{label}</span></h2>")
        out.append(f"<p>{n['claim']}</p><p class='small'><b>Why it matters.</b> {html.escape(n['why'])}</p>")
        tabs = [("chk", "Checklist")]
        if n.get("lean"):
            tabs.append(("lean", "Lean definitions"))
        if n.get("theorems"):
            tabs.append(("thm", "Theorems"))
        if n.get("fortran"):
            tabs.append(("f90", "BerkeleyGW source"))
        if n.get("python"):
            tabs.append(("py", "Python reproducer"))
        out.append("<div class='tabs'>" + "".join(
            f"<button data-p='{k}' class='{'on' if i == 0 else ''}'>{t}</button>" for i, (k, t) in enumerate(tabs)) + "</div>")
        out.append("<div class='pane chk on' data-p='chk'>")
        for j, item in enumerate(n.get("checks", [])):
            out.append(f"<label><input type='checkbox' id='{n['id']}-{j}'> {html.escape(item)}</label>")
        out.append("</div>")
        if n.get("lean"):
            out.append("<div class='pane' data-p='lean'>")
            for rel, name in n["lean"]:
                ln, text = lean_decl(rel, name, statement_only=None)
                out.append(code_block(f"{rel}:{ln}  ({name})", text, lean=True))
            out.append("</div>")
        if n.get("theorems"):
            out.append("<div class='pane' data-p='thm'>")
            for rel, name in n["theorems"]:
                ln, text = lean_decl(rel, name, statement_only=True)
                a = axioms_for(name)
                axs = f"<div class='ax'>axioms: [{html.escape(a)}]</div>" if a is not None else \
                      "<div class='ax' style='color:#b83232'>not found in artifacts/axioms.log — run verify.sh</div>"
                out.append(code_block(f"{rel}:{ln}", text, lean=True) + axs)
            out.append("</div>")
        if n.get("fortran"):
            out.append("<div class='pane' data-p='f90'>")
            for rel, a, b in n["fortran"]:
                out.append(code_block(f"BerkeleyGW-4.0/{rel}:{a}-{b}", fortran(tree, rel, a, b)))
            out.append("</div>")
        if n.get("python"):
            out.append("<div class='pane' data-p='py'>")
            for rel, name in n["python"]:
                ln, text = python_def(rel, name)
                out.append(code_block(f"{rel}:{ln}", text))
            out.append("</div>")
        out.append("</div></section>")

    out.append("<section id='findings'><h2>Findings (checkable without Lean)</h2>")
    for t, d in FINDINGS:
        out.append(f"<div class='card'><b>{html.escape(t)}.</b> {html.escape(d)}</div>")
    out.append("</section><section id='table'><h2>O1 across treatments (meV)</h2><div class='card'><table>"
               "<tr><th>treatment</th><th>O1</th><th>evidence</th></tr>")
    for a, b, c in TABLE:
        out.append(f"<tr><td>{html.escape(a)}</td><td>{html.escape(b)}</td><td>{html.escape(c)}</td></tr>")
    out.append("</table></div></section><section id='trusted'><h2>What is still trusted</h2><div class='card'><table>")
    for a, b in TRUSTED:
        out.append(f"<tr><td><b>{html.escape(a)}</b></td><td>{html.escape(b)}</td></tr>")
    out.append("</table></div><p class='small'>Everything else on the chain is checked by the Lean kernel; "
               "only propext, Classical.choice and Quot.sound are permitted as axioms, and the exhaustive audit "
               "enforces it. Details: docs/ENDPOINT.md, docs/CODEMAP.md (canonical and archived modules) "
               "and .agent/handoffs/. Scope: README.md and docs/reviews/README.md (REVIEW-28). The "
               "theory-to-specification bridge (conditional identities) is in docs/BRIDGE.md; this project "
               "does not claim to have formally verified the core physics of BerkeleyGW.</p>"
               "<p class='small'>The BerkeleyGW source excerpts on this page are copyright The Regents of the "
               "University of California, through Lawrence Berkeley National Laboratory, and are reproduced "
               "under BerkeleyGW's licence; see THIRD_PARTY_NOTICES.md.</p></section>")
    out.append(f"</main></div><script>{JS}</script></body></html>")
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bgw-tree", default=str(DEFAULT_TREE))
    ap.add_argument("--out", default=str(ROOT / "docs/review/index.html"))
    a = ap.parse_args(argv)
    try:
        page = render(pathlib.Path(a.bgw_tree))
    except Missing as e:
        print(f"make_review: {e}", file=sys.stderr)
        return 1
    out = pathlib.Path(a.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(page)
    print(f"wrote {out} ({len(page) // 1024} KB)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
