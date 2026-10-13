#!/usr/bin/env python3
"""Generate the figures of docs/talk and README from committed data.

    python3 docs/figures/make_figures.py

Every plotted number is read from a committed file, except the full-frequency O1 values,
which exist only in docs/ENDPOINT.md (A2, measured) and are written here with that source.
Outputs PDF (slides) and PNG (README, notes) next to this script.
"""
import json
import pathlib
import re
from fractions import Fraction

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import FancyArrowPatch, Rectangle  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = pathlib.Path(__file__).resolve().parent
DATA = ROOT / "bgw/endpoint/data"

plt.rcParams.update({
    "font.family": "serif", "mathtext.fontset": "stix", "font.serif": ["STIXGeneral", "DejaVu Serif"],
    "font.size": 10, "axes.titlesize": 10.5, "axes.labelsize": 10, "legend.fontsize": 8.5,
    "xtick.labelsize": 8.5, "ytick.labelsize": 8.5, "axes.spines.top": False,
    "axes.spines.right": False, "savefig.bbox": "tight", "savefig.pad_inches": 0.04,
})

# evidence classes, colour-blind-safe (Okabe-Ito)
KERNEL, PYIV, MEASURED, TRUSTED = "#0072B2", "#009E73", "#E69F00", "#999999"
EVIDENCE = {KERNEL: "kernel-checked (Lean)", PYIV: "outward interval (Python)",
            MEASURED: "measured (production run)"}


def save(fig, name):
    for ext in ("pdf", "png"):
        fig.savefig(OUT / f"{name}.{ext}", dpi=220)
    plt.close(fig)
    print("wrote", name)


def production_o1_meV():
    head = (DATA / "mutations_e1.log").read_text()
    return float(re.search(r"production O1 = ([0-9.]+) meV", head).group(1))


# ---------------------------------------------------------------- figure 1: three scales
def fig_scales():
    cert = json.loads((DATA / "cert_o1.json").read_text())
    lo, hi = Fraction(cert["O1_lo"]), Fraction(cert["O1_hi"])          # eV, binary64 endpoints
    prod = Fraction(str(production_o1_meV())) / 1000                       # eV, printed value
    qp = json.loads((DATA / "qp_cert.json").read_text())["O1_full_QP"]
    evgw0 = json.loads((DATA / "evgw0.json").read_text())[-1]["O1"]
    evgw = json.loads((DATA / "evgw.json").read_text())[-1]["O1"]
    f3 = json.loads((ROOT / "bgw/r28_f3/data/f3.json").read_text())
    allband = f3["all_bands_nb_168"]["O1_meV"]   # Python interval (R28-F3)

    fig, ax = plt.subplots(1, 3, figsize=(9.4, 3.0), gridspec_kw={"width_ratios": [1.45, 1, 1]})

    # (a) meV: what O1 is under different treatments
    rows = [
        ("G$_0$W$_0$-GPP, linearised\n(the certified quantity)", float(lo) * 1e3, float(hi) * 1e3, KERNEL),
        ("G$_0$W$_0$-GPP, full QP eq.", qp[0] * 1e3, qp[1] * 1e3, KERNEL),
        ("G$_0$W$_0$ full-frequency (CD)", 58.1, 67.2, MEASURED),   # docs/ENDPOINT.md A2
        ("evGW$_0$-GPP", evgw0 * 1e3, evgw0 * 1e3, MEASURED),
        ("evGW-GPP", evgw * 1e3, evgw * 1e3, MEASURED),
        ("linearised, all 168 bands\nof the EPM basis", allband[0], allband[1], PYIV),
    ]
    a = ax[0]
    for i, (lab, x0, x1, c) in enumerate(rows):
        y = len(rows) - 1 - i
        if x1 - x0 > 0.3:
            a.plot([x0, x1], [y, y], color=c, lw=5, solid_capstyle="butt")
        else:
            a.plot([(x0 + x1) / 2], [y], "o", color=c, ms=6)
        a.text(-0.02, y, lab, ha="right", va="center", fontsize=8.3, transform=a.get_yaxis_transform())
    a.axvline(0, color="k", lw=0.6)
    a.text(allband[1] + 3, 0, f"[{allband[0]:.2f}, {allband[1]:.2f}]", va="center", fontsize=7.5, color=PYIV)
    a.set_xlim(-25, 160)
    a.set_yticks([])
    a.spines["left"].set_visible(False)
    a.set_xlabel(r"$O_1 = E^{\rm QP}_X - E^{\rm QP}_L$  (meV)")
    a.set_title("(a) meV: the physics is not settled", loc="left")
    a.text(2, -0.95, r"$O_1>0$: $L$ below $X$", fontsize=7.5, color="0.35")
    for c, lab in EVIDENCE.items():
        a.plot([], [], "s", color=c, label=lab)
    a.legend(loc="lower right", frameon=False, fontsize=7.2, handletextpad=0.2, borderaxespad=0)
    a.set_ylim(-1.3, len(rows) - 0.4)

    # (b) micro-eV: production vs the specification
    b = ax[1]
    to_ueV = lambda v: float((v - prod) * 10**6)
    b.axvline(0, color=MEASURED, lw=2.2)
    b.add_patch(Rectangle((to_ueV(lo), 0.3), max(to_ueV(hi) - to_ueV(lo), 0.06), 0.25, color=KERNEL))
    gap = to_ueV(lo)
    b.add_artist(FancyArrowPatch((0, 0.2), (gap, 0.2), arrowstyle="<->", mutation_scale=9, lw=0.9))
    b.text(gap / 2, 0.08, f"{gap:.2f} µeV", ha="center", fontsize=9)
    b.text(0.2, 0.97, "production (BerkeleyGW 4.0,\nMonte Carlo Coulomb averages)", color="#8a5d00", fontsize=7.8, va="top")
    b.text(gap - 0.2, 0.68, "specification,\nexact averages", color=KERNEL, fontsize=7.8, va="center", ha="right")
    b.set_xlim(-1, gap + 1)
    b.set_ylim(0, 1)
    b.set_yticks([])
    b.spines["left"].set_visible(False)
    b.set_xlabel(r"$O_1 - O_1^{\rm prod}$  (µeV)")
    b.set_title("(b) µeV: code vs. specification", loc="left")

    # (c) nano-eV: the enclosure itself
    c = ax[2]
    w = float((hi - lo) * 10**9)
    c.add_patch(Rectangle((0, 0.35), w, 0.3, color=KERNEL, alpha=0.9))
    c.add_artist(FancyArrowPatch((0, 0.2), (w, 0.2), arrowstyle="<->", mutation_scale=9, lw=0.9))
    c.text(w / 2, 0.08, f"{w:.2f} neV", ha="center", fontsize=9)
    c.text(w / 2, 0.86, "every real value of the\nspecified calculation", ha="center", va="top",
           fontsize=8, color=KERNEL)
    c.set_xlim(-0.4, w + 0.4)
    c.set_ylim(0, 1)
    c.set_yticks([])
    c.spines["left"].set_visible(False)
    c.set_xlabel(r"$O_1 - $ lower endpoint  (neV)")
    c.set_title("(c) neV: the theorem", loc="left")
    fig.subplots_adjust(wspace=0.14)
    save(fig, "fig1_three_scales")


# ---------------------------------------------------------------- figure 2: conventions
NAMES = {
    "op_first_match": "q→0: first matching symmetry op\n(BerkeleyGW uses the last)",
    "wing_at_target_G0": "wing fix at target G=0 (not irreducible)",
    "wing_v0_is_G0": "wing scale: v(G=0) instead of sortrx-first",
    "no_wing_fix_q_nonzero": "no wing rescaling at q≠0",
    "static_remainder_factor_1": "static remainder factor 1 (not ½)",
    "no_static_remainder": "no static remainder",
    "unocc_nearpole_ch_kept": "keep CH of unoccupied near-pole modes",
    "invalid_modes_skipped": "skip invalid modes (ω̃² < 0)",
    "gamma_0.25": "near-pole width γ = 0.25 eV (not 0.5)",
    "sexcut_disabled": "sexcut clamp disabled",
    "dw_0.5": "finite difference dE = 0.5 eV (not 1)",
    "q_weight_off_by_one": "q weights off by one",
    "ryd_codata2018": "Ry from CODATA 2018",
    "tol_small_1e-4": "mode drop threshold 1e-4 (not 1e-6)",
    "no_fractional_translations": "no fractional translations",
}


def fig_conventions():
    rows = []
    for line in (DATA / "mutations_e1.log").read_text().splitlines():
        m = re.match(r"(\S+)\s+max table dev ([0-9.e+-]+) eV.*O1 ([+-][0-9.]+) meV.*\s(DETECTED|control-agrees)$", line)
        if m and m.group(4) == "DETECTED":
            rows.append((m.group(1), float(m.group(2)), float(m.group(3))))
    prod = production_o1_meV()
    rows.sort(key=lambda r: r[2])
    fig, ax = plt.subplots(figsize=(5.9, 4.4))
    for i, (k, dev, o1) in enumerate(rows):
        col = "#D55E00" if o1 < 0 else "#56B4E9"
        ax.barh(i, o1 - prod, left=prod, color=col, height=0.62)
        ax.text(1.0, i, f"Σ-table dev. {dev:.0e} eV", transform=ax.get_yaxis_transform(),
                fontsize=6.6, va="center", ha="left", color="0.4")
    ax.set_yticks(range(len(rows)), [NAMES.get(r[0], r[0]) for r in rows], fontsize=7.6)
    ax.axvline(prod, color="k", lw=1)
    ax.axvline(0, color="0.6", lw=0.6, ls=":")
    ax.set_xscale("symlog", linthresh=20)
    ax.set_xlim(-800, 250)
    ax.set_xlabel(r"$O_1$ under the counterfactual convention (meV; production: "
                  f"{prod:.1f} meV)")
    flips = sum(1 for r in rows if r[2] < 0)
    ax.set_title(f"All {len(rows)} counterfactual conventions are detected in the Σ table "
                 f"(threshold $10^{{-8}}$ eV);\n{flips} of them flip the sign of $O_1$", loc="left")
    save(fig, "fig2_conventions")


# ---------------------------------------------------------------- figure 3: convergence
def fig_convergence():
    rows = [json.loads(l) for l in (DATA / "e2_results.jsonl").read_text().splitlines() if l.strip()]
    sel = [r for r in rows if r["N"] == 2 and r["ecutwfc"] == 11.0]
    fig, axs = plt.subplots(1, 2, figsize=(8.0, 3.2), sharey=True)
    cmap = plt.get_cmap("viridis")
    cuts = sorted({r["ecuts"] for r in sel})
    for j, (key, title) in enumerate([("O1", "(a) with BerkeleyGW's static remainder"),
                                      ("O1_noremainder", "(b) without the static remainder")]):
        ax = axs[j]
        for i, ec in enumerate(cuts):
            pts = sorted({(r["nb_used"], r[key] * 1e3) for r in sel if r["ecuts"] == ec})
            ax.plot([p[0] for p in pts], [p[1] for p in pts], "-o", ms=3, lw=1.2,
                    color=cmap(i / max(1, len(cuts) - 1)), label=f"{ec:g} Ry")
        prod = [r for r in sel if r["ecuts"] == 7.0 and r["nb_used"] == 18][0]
        ax.plot([18], [prod[key] * 1e3], marker="*", ms=13, color="#D55E00", zorder=5)
        ax.axhline(0, color="k", lw=0.6)
        ax.set_xscale("log")
        ax.set_xlabel("bands in Σ and ε")
        ax.set_xticks([18, 40, 60, 100, 150], ["18", "40", "60", "100", "150"])
        ax.minorticks_off()
        ax.set_title(title, loc="left")
    axs[0].set_ylabel(r"$O_1$ (meV)")
    axs[0].annotate("production\n(18 bands, 7 Ry)", xy=(18, 15.4), xytext=(30, -50), fontsize=8,
                    arrowprops=dict(arrowstyle="->", lw=0.7))
    axs[1].legend(title="screened cutoff", ncol=2, frameon=False, loc="upper left", fontsize=7.5,
                  title_fontsize=7.5)
    fig.suptitle("Measured with the production binaries (2×2×2 grid, 11 Ry wavefunction cutoff): "
                 "the sign of $O_1$ at the production point comes from cancelling truncations",
                 fontsize=9, x=0.02, ha="left", y=1.07)
    save(fig, "fig3_convergence")


# ---------------------------------------------------------------- figure 0: the levels
def production_levels():
    """{k-label: [(n, Emf, Eqp1)]} from bgw/export/sigma_hp.log (eV)."""
    lab = {(0.0, 0.0, 0.0): "Γ", (0.0, 0.0, 0.5): "L", (0.0, 0.5, 0.5): "X"}
    out, cur = {}, None
    for line in (ROOT / "bgw/export/sigma_hp.log").read_text().splitlines():
        m = re.match(r"\s+k =\s+(\S+)\s+(\S+)\s+(\S+)\s+ik", line)
        if m:
            cur = lab.get(tuple(float(t) for t in m.groups()))
            if cur in out:
                cur = None          # only the first (diagonal) table of each k
            elif cur:
                out[cur] = []
            continue
        f = line.split()
        if cur and len(f) == 15 and f[0].isdigit():
            out[cur].append((int(f[0]), float(f[1]), float(f[9])))
        elif cur and out[cur] and not line.strip():
            cur = None
    return out


def fig_levels():
    lv = production_levels()
    order = ["L", "Γ", "X"]
    fig, axs = plt.subplots(1, 2, figsize=(7.4, 3.5), sharey=True)
    for ax, idx, title in [(axs[0], 1, "mean field (EPM)"), (axs[1], 2, "G$_0$W$_0$-GPP (production)")]:
        vbm = max(r[idx] for r in lv["Γ"] if r[0] <= 4)
        for i, k in enumerate(order):
            for n, *e in lv[k]:
                y = e[idx - 1] - vbm
                col = "0.25" if n <= 4 else ("#0072B2" if (k, n) in {("X", 5), ("L", 5)} else "0.6")
                ax.plot([i - 0.32, i + 0.32], [y, y], color=col, lw=2.2 if col != "0.6" else 1.4)
        xc = lv["X"][4][idx] - vbm
        lc = lv["L"][4][idx] - vbm
        ax.annotate("", xy=(2.45, xc), xytext=(2.45, lc) if abs(xc - lc) > 0.05 else (2.45, xc),
                    arrowprops=dict(arrowstyle="-", lw=0))
        ax.set_xticks(range(3), order)
        ax.set_xlim(-0.6, 2.9)
        ax.axhline(0, color="0.8", lw=0.6, ls=":")
        ax.set_title(title, loc="left")
        d = (xc - lc) * 1000
        txt = (f"$X$ below $L$ by {-d / 1000:.3f} eV" if d < 0 else f"$L$ below $X$ by {d:.1f} meV")
        ax.text(0.5, 0.97, txt, transform=ax.transAxes, ha="center", va="top", fontsize=9.5, color="#0072B2",
                bbox=dict(fc="white", ec="#0072B2", lw=0.6, boxstyle="round,pad=0.25"))
    axs[0].set_ylabel("energy relative to the valence top at Γ (eV)")
    axs[0].set_ylim(-14, 8.5)
    fig.subplots_adjust(wspace=0.08)
    save(fig, "fig0_levels")


# ---------------------------------------------------------------- slide versions (larger type)
def fig_conventions_slide():
    rows = []
    for line in (DATA / "mutations_e1.log").read_text().splitlines():
        m = re.match(r"(\S+)\s+max table dev ([0-9.e+-]+) eV.*O1 ([+-][0-9.]+) meV.*\s(DETECTED|control-agrees)$", line)
        if m and m.group(4) == "DETECTED":
            rows.append((m.group(1), float(m.group(3))))
    prod = production_o1_meV()
    rows = sorted([r for r in rows if abs(r[1] - prod) > 0.5], key=lambda r: r[1])
    with plt.rc_context({"font.size": 12, "ytick.labelsize": 11, "xtick.labelsize": 11}):
        fig, ax = plt.subplots(figsize=(7.2, 4.0))
        for i, (k, o1) in enumerate(rows):
            ax.barh(i, o1 - prod, left=prod, color="#D55E00" if o1 < 0 else "#56B4E9", height=0.64)
            ax.annotate(f"{o1:+.1f}", xy=(o1, i), xytext=(5 if o1 > prod else -5, 0),
                        textcoords="offset points", va="center",
                        ha="left" if o1 > prod else "right", fontsize=10)
        ax.set_yticks(range(len(rows)), [NAMES[r[0]].replace("\n", " ") for r in rows])
        ax.axvline(prod, color="k", lw=1.2)
        ax.text(prod, len(rows) - 0.3, f"  production {prod:.1f}", fontsize=10)
        ax.set_xlim(-3000, 400)
        ax.set_xscale("symlog", linthresh=20)
        ax.set_xlabel("$O_1$ with one convention changed (meV)")
        save(fig, "fig2_conventions_slide")


def fig_convergence_slide():
    rows = [json.loads(l) for l in (DATA / "e2_results.jsonl").read_text().splitlines() if l.strip()]
    sel = [r for r in rows if r["N"] == 2 and r["ecutwfc"] == 11.0]
    cuts = [3.0, 5.0, 7.0, 11.0, 25.0]
    cmap = plt.get_cmap("viridis")
    with plt.rc_context({"font.size": 12, "xtick.labelsize": 11, "ytick.labelsize": 11}):
        fig, ax = plt.subplots(figsize=(6.4, 4.0))
        for i, ec in enumerate(cuts):
            pts = sorted({(r["nb_used"], r["O1"] * 1e3) for r in sel if r["ecuts"] == ec})
            ax.plot([p[0] for p in pts], [p[1] for p in pts], "-o", ms=4, lw=1.8,
                    color=cmap(i / (len(cuts) - 1)), label=f"{ec:g} Ry")
        ax.plot([18], [15.4], marker="*", ms=17, color="#D55E00", zorder=5)
        ax.annotate("production", xy=(18, 15.4), xytext=(26, 33), fontsize=11,
                    arrowprops=dict(arrowstyle="->", lw=0.8))
        ax.axhline(0, color="k", lw=0.7)
        ax.set_xscale("log")
        ax.set_xticks([18, 40, 60, 100, 150], ["18", "40", "60", "100", "150"])
        ax.minorticks_off()
        ax.set_ylim(-95, 45)
        ax.set_xlabel("bands in Σ and ε")
        ax.set_ylabel("$O_1$ (meV)")
        ax.legend(title="screened\ncutoff", frameon=False, ncol=1, loc="center left",
                  bbox_to_anchor=(1.01, 0.5), fontsize=10,
                  title_fontsize=10)
        save(fig, "fig3_convergence_slide")


if __name__ == "__main__":
    fig_levels()
    fig_conventions_slide()
    fig_convergence_slide()
    fig_scales()
    fig_conventions()
    fig_convergence()
