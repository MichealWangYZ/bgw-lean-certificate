#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Can the exported T-004 dataset test the band-index symmetry of Sigma?

## The question

`Sigma/mtxel_cor.f90` computes, per its own header comment (:14-24),

    < psi_n(k) | Sigma_cor(E) | psi_m(k) >

with `n = sig%diag(in)` and `m = sig%diag(im)`. The natural symmetry claim is
`Sigma_nm = MYCONJG(Sigma_mn)`. This project builds the **real** flavor
(`flavor_real.mk`), where `MYCONJG` is the identity, so the relation to test
would be plain symmetry, `Sigma_nm = Sigma_mn`, not conjugate symmetry. That
reading is not assumed: it follows from the accumulated form quoted at
`Sigma/mtxel_cor.f90:1710-1717`,

    SX(E) = M(n,G) * conj(M(m,G')) * Omega^2(G,G') / (...) * Vcoul(G')

under which

    Sigma_nm - Sigma_mn = sum_{G,G'} M_n(G) M_m(G') [ T(G,G') - T(G',G) ]
    with T(G,G') = Vcoul(G') * ( -occ*ssx(G,G') + sch(G,G')/2 )

in real flavor, after relabelling `G <-> G'` in the second term.

## The finding this module reports

**The relation cannot be tested on the exported dataset**, and the obstruction
is not a missing export field. It is the run configuration. See
`testability()` for the machine-checked version and section "verdict" of the
emitted JSON.

The ket band `m` is indeed not passed into `mtxel_cor`: `Sigma/sigma_main.f90`
:1825-1830 passes `sig%offmap(...,1)` as `in` and `sig%offmap(...,3)` as `il`,
while `m = sig%offmap(...,2)` enters only as the array argument
`aqsaug(:,:,sig%offmap(...,2),ispin)` bound to `aqsmtemp`. So `m` is absent
from the exported integer fields. But `m` is nevertheless **recoverable** from
the export, by fingerprinting the exported `aqsm` values against the `aqsn`
values of the diagonal calls in the same call block, which this module does and
which succeeds unambiguously. The band index is therefore not the blocker.

The blocker is that the probe run's `sigma.inp` requests only three offdiagonal
elements -- `(1,1,1)`, `(1,8,1)`, `(2,1,2)` in `(off1, off2, off3)` form -- so
the computed `(n,m)` pairs are `(1,1)`, `(1,8)` and `(2,1)`. The transposes
`(8,1)` and `(1,2)` were never computed by BerkeleyGW and are not in the
dataset under any reading of it. `(1,1)` is its own transpose, so it carries no
information about the relation. Obtaining the missing side requires a different
BerkeleyGW run, not a different export format.

## What BerkeleyGW itself does about this

Relevant because it bears on whether the relation is expected to hold exactly:

* `Sigma/inread.f90:621-651`: under the `sigma_matrix loff toff` keyword,
  `toff = -1` computes the lower triangle only, `toff = +1` the upper triangle
  only, and `toff = 0` computes **both** triangles.
* `Sigma/offdiag.f90:204-222`: the post-processing utility *imposes*
  Hermiticity when `toff = +-1`, by copying `MYCONJG` of one triangle into the
  other. With `toff = 0` it diagonalises the matrix as computed, using the
  general non-symmetric solver `dgeev`/`zgeev`.
* `Sigma/offdiag.f90:78`: an explicit warning that "Sigma is not Hermitian
  unless all matrix elements are evaluated at the same energy" (`loff < 0`).
* `Sigma/sigma_main.f90:1716-1733`: `sig%offdiagsym` zeroes elements between
  bands whose degenerate-subspace sizes differ, described in the source comment
  as something that "helps enforce symmetry".

Read together, upstream treats exact band-index symmetry of the *computed*
matrix as something to be imposed or aided rather than something guaranteed by
the kernel. This module makes no claim about whether it does or does not hold;
it reports that this dataset cannot decide it.

## A separate, clearly different measurement

`gg_transpose_report()` measures the `(G, G')` antisymmetry of the recorded
near-pole kernel `T` defined above. This is **not** the band-index test and
must never be quoted as one. It is at most a *necessary condition*: exact
term-by-term symmetry of `T` would force `Sigma_nm = Sigma_mn` for every band
pair, while asymmetry of `T` does not by itself imply `Sigma_nm != Sigma_mn`,
because the difference is `T`'s antisymmetric part contracted with
`M_n(G) M_m(G')`, which can be small or zero for particular `n, m`. It is also
measured on the near-pole `occ != 1` subset only -- the generic-branch terms of
the same sums were never exported -- so it is not even a complete measurement
of `T`'s antisymmetry.
"""

from fractions import Fraction as F
import argparse
import collections
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import weighted_mismatch as wm  # noqa: E402  (imported unmodified, never edited)

#: Source facts this module depends on, each with the line it was read at, so a
#: reviewer can check the reading rather than the conclusion. "read" means a
#: human read Fortran; nothing here is measured.
SOURCE_READING = {
    "flavor": (
        "real flavor (flavor_real.mk), so MYCONJG is the identity and the "
        "relation to test is Sigma_nm = Sigma_mn, not conjugate symmetry"),
    "Sigma/mtxel_cor.f90:14-24": (
        "mtxel_cor computes <psi_n|Sigma_cor(E)|psi_m> with n = sig%diag(in), "
        "m = sig%diag(im); only `in` and `il` are dummy arguments"),
    "Sigma/mtxel_cor.f90:1710-1717": (
        "SX(E) = M(n,G)*conj(M(m,G'))*Omega^2(G,G')/(...)*Vcoul(G'); the "
        "Vcoul factor carries G', not G"),
    "Sigma/sigma_main.f90:1825-1830": (
        "mtxel_cor is called with sig%offmap(ioff,1) as `in` and "
        "sig%offmap(ioff,3) as `il`; the ket band sig%offmap(ioff,2) enters "
        "only through the aqsmtemp array argument, so it is never an integer "
        "argument and cannot be exported by instrumenting the argument list"),
    "Sigma/inread.f90:621-651": (
        "sigma_matrix loff toff: toff=-1 lower triangle only, toff=+1 upper "
        "triangle only, toff=0 BOTH triangles. An explicit `offdiag` block "
        "computes exactly the listed pairs and no others"),
    "Sigma/offdiag.f90:204-222": (
        "the post-processing utility imposes Hermiticity by copying one "
        "triangle when toff=+-1; with toff=0 it diagonalises the computed "
        "matrix with the general non-symmetric solver dgeev/zgeev"),
    "Sigma/offdiag.f90:78": (
        "explicit warning: Sigma is not Hermitian unless all matrix elements "
        "are evaluated at the same energy"),
    "Sigma/sigma_main.f90:1716-1733": (
        "sig%offdiagsym zeroes elements between bands with different "
        "degenerate-subspace sizes; the source comment says this 'helps "
        "enforce symmetry'"),
}

#: `icalc` as emitted by the instrumentation: 1 for the diagonal call site,
#: 2 for the offdiagonal one (Sigma/sigma_main.f90, the trailing `1`/`2`
#: argument of the two mtxel_cor calls).
ICALC_DIAGONAL = 1
ICALC_OFFDIAGONAL = 2


class SymmetryError(ValueError):
    """The dataset does not support the inventory this module builds."""


def parse_offdiag_block(text):
    """The `(off1, off2, off3)` triples of a sigma.inp `offdiag` block.

    Returned in file order. `off1` is the bra band `n`, `off2` the ket band
    `m`, `off3` the band `l` whose energy sets the evaluation frequency
    (Sigma/inread.f90:249, :716-718).
    """
    rows, inside = [], False
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if re.fullmatch(r"begin\s+offdiag", line):
            inside = True
            continue
        if inside and re.fullmatch(r"end", line):
            inside = False
            continue
        if inside:
            parts = line.split()
            if len(parts) != 3:
                raise SymmetryError(
                    f"offdiag block line {line!r} does not have 3 fields")
            rows.append(tuple(int(p) for p in parts))
    if inside:
        raise SymmetryError("offdiag block was never closed by `end`")
    return rows


def call_blocks(accumulators):
    """Maximal runs of consecutive `call_id` sharing one q-point.

    The wavefunction matrix elements `aqsn`/`aqsm` are only comparable within
    one such run, because they belong to one `(k, q)` pass of sigma_main. The
    blocking is derived from the accumulator rows' own `qk`, not assumed.
    """
    qk = {}
    for (call_id, _iw), v in accumulators.items():
        q = v["ident"][4:]
        seen = qk.setdefault(call_id, q)
        if seen != q:
            raise SymmetryError(
                f"call {call_id} carries two different q-points {seen} and {q}")
    blocks, cur = [], []
    for call_id in sorted(qk):
        if cur and qk[call_id] == qk[cur[-1]] and call_id == cur[-1] + 1:
            cur.append(call_id)
        else:
            if cur:
                blocks.append(cur)
            cur = [call_id]
    if cur:
        blocks.append(cur)
    return {c: i for i, b in enumerate(blocks) for c in b}, blocks


def fingerprint_bands(rows, block_of):
    """Recover each call's bra band `n` and ket band `m` from the export.

    For a diagonal call, `aqsntemp` and `aqsmtemp` are the same array, so every
    diagonal record supplies two known samples of band `band_in`'s matrix
    elements: `(n1true, ig) -> aqsn` and `(n1true, igp) -> aqsm`. Those build a
    per-block table. An offdiagonal record's `aqsm` is then matched against it
    by exact binary64 equality.

    Exact equality is the right test here and not a floating-point sin: both
    numbers are the same stored `aqsaug` element written twice by the same
    program, so a match is bit-identical or it is a coincidence. Coincidences
    are guarded against by requiring that every matched record in a call agree
    on one band and that no second band ever match.

    Two tables are built on purpose.

    * `tab_diag` uses diagonal records only. The exported `band_in` is matched
      against it, which is a genuine cross-check: nothing in the construction
      of `tab_diag` used the offdiagonal calls' own `band_in`.
    * `tab_all` additionally records that, in *every* call, `aqsn` is the
      matrix element of the exported band `band_in` at index `ig`. That is
      true by the instrumentation's own write statement, and it widens
      coverage: a band whose near-pole events are absent from the diagonal
      calls of a block can still be sampled from an offdiagonal call's `aqsn`.
      `tab_all` is used for the ket band `m` only, where it is not circular.
    """
    tab_diag, tab_all = {}, {}

    def put(table, key, val, what):
        prev = table.setdefault(key, val)
        if prev != val:
            raise SymmetryError(
                f"{what} gives two values for key {key}: {prev} and {val}; "
                f"the fingerprint table is not well defined")

    for r in rows:
        blk = block_of[r["call_id"]]
        b = r["band_in"]
        put(tab_all, (blk, b, r["n1true"], r["ig"]), r["aqsn"],
            f"band {b} block {blk} aqsn")
        if r["icalc"] == ICALC_DIAGONAL:
            for idx, val in ((r["ig"], r["aqsn"]), (r["igp"], r["aqsm"])):
                put(tab_diag, (blk, b, r["n1true"], idx), val,
                    f"diagonal band {b} block {blk}")
                put(tab_all, (blk, b, r["n1true"], idx), val,
                    f"band {b} block {blk}")
    bands = sorted({r["band_in"] for r in rows})

    hits = collections.defaultdict(collections.Counter)
    covered = collections.Counter()
    for r in rows:
        blk = block_of[r["call_id"]]
        for role, table, idx, val in (("n", tab_diag, r["ig"], r["aqsn"]),
                                      ("m", tab_all, r["igp"], r["aqsm"])):
            any_known = False
            for b in bands:
                key = (blk, b, r["n1true"], idx)
                if key in table:
                    any_known = True
                    if table[key] == val:
                        hits[(r["call_id"], role)][b] += 1
            if any_known:
                covered[(r["call_id"], role)] += 1

    out = {}
    for call_id in sorted({r["call_id"] for r in rows}):
        entry = {}
        for role in ("n", "m"):
            c = hits[(call_id, role)]
            if len(c) == 1 and covered[(call_id, role)] > 0:
                (band, n_match), = c.items()
                entry[role] = band
                entry[role + "_matches"] = n_match
                entry[role + "_records_with_a_comparable_sample"] = \
                    covered[(call_id, role)]
                entry[role + "_ambiguous"] = False
            else:
                entry[role] = None
                entry[role + "_matches"] = dict(c)
                entry[role + "_records_with_a_comparable_sample"] = \
                    covered[(call_id, role)]
                entry[role + "_ambiguous"] = len(c) > 1
        out[call_id] = entry
    return out


def pair_inventory(rows, fingerprints):
    """The `(n, m)` band pairs the dataset actually contains, per icalc."""
    inv = collections.defaultdict(lambda: dict(calls=set(), records=0))
    unresolved = []
    for r in rows:
        fp = fingerprints[r["call_id"]]
        if fp["n"] is None or fp["m"] is None:
            unresolved.append(r["call_id"])
            continue
        key = (r["icalc"], fp["n"], fp["m"])
        inv[key]["calls"].add(r["call_id"])
        inv[key]["records"] += 1
    return ({k: dict(calls=sorted(v["calls"]), records=v["records"])
             for k, v in inv.items()},
            sorted(set(unresolved)))


def testability(inventory):
    """Is the band-index symmetry relation testable on this dataset?

    Testable means: some computed pair `(n, m)` with `n != m` has its transpose
    `(m, n)` also computed, so two independently accumulated quantities exist
    to compare. `n == m` pairs are excluded because `Sigma_nn = Sigma_nn`
    holds by construction and constrains nothing.
    """
    pairs = {(n, m) for (_icalc, n, m) in inventory}
    offdiag_pairs = sorted(p for p in pairs if p[0] != p[1])
    testable = sorted(p for p in offdiag_pairs if (p[1], p[0]) in pairs)
    return dict(
        band_pairs_present=sorted(pairs),
        distinct_band_pairs_present=offdiag_pairs,
        self_transpose_pairs_present=sorted(p for p in pairs if p[0] == p[1]),
        transposed_partners_missing=sorted(
            (p[1], p[0]) for p in offdiag_pairs if (p[1], p[0]) not in pairs),
        testable_pairs=testable,
        testable=bool(testable),
        verdict=(
            "TESTABLE" if testable else
            "NOT TESTABLE on this dataset: no band pair (n, m) with n != m has "
            "its transpose (m, n) also computed, so there is no second "
            "quantity to compare against. Pairs with n == m are excluded "
            "because Sigma_nn = Sigma_nn constrains nothing."),
        what_would_be_required=(
            "NOT an additional export field. The ket band m is already "
            "recoverable from the export by fingerprinting aqsm against the "
            "diagonal calls' aqs values, which this module does successfully. "
            "What is missing is the transposed matrix elements themselves: "
            "BerkeleyGW only computes the (off1, off2) pairs listed in "
            "sigma.inp. A run with `sigma_matrix <loff> 0`, or an explicit "
            "offdiag block containing both (n, m, l) and (m, n, l), would "
            "compute both sides. That is a different BerkeleyGW run, which is "
            "outside the scope of a fixture-only analysis. Exporting "
            "sig%offmap(ioff,2) would still be worth doing -- it would make m "
            "explicit instead of inferred -- but on its own it would not make "
            "the relation testable."),
        also_required_even_then=(
            "Even with both triangles present, the comparison would have to "
            "use the exported per-call accumulators asxtemp+achtemp, not the "
            "3702 near-pole records: the records are a branch-selected subset "
            "of each call's (n1, ig, igp) sum, and Sigma_nm is the whole sum. "
            "Additionally, Sigma/offdiag.f90:78 warns that Sigma is not "
            "Hermitian unless all elements are evaluated at the same energy, "
            "so off3 (the `l` band) would have to match between the two sides."),
    )


def gg_transpose_report(rows):
    """Antisymmetry of the recorded near-pole kernel `T` under `G <-> G'`.

    THIS IS NOT THE BAND-INDEX SYMMETRY TEST AND MUST NOT BE QUOTED AS ONE.
    See the module docstring. `T(G,G') = Vcoul(G') * (-occ*ssx + sch/2)` is the
    per-(ig, igp, n1, iw) factor that multiplies `M_n(G) M_m(G')`. Exact
    term-by-term symmetry of `T` would be sufficient for `Sigma_nm = Sigma_mn`;
    its absence is not sufficient for the negation, because the antisymmetric
    part is contracted with `M_n(G) M_m(G')` and can cancel.

    Measured only on record pairs where both `(ig, igp)` and `(igp, ig)` were
    exported. Terms whose transpose took the generic branch were never
    exported, so this is a subset of a subset and cannot be aggregated into a
    statement about the full sums.
    """
    index = {}
    for r in rows:
        index[(r["call_id"], r["iw"], r["n1true"], r["ig"], r["igp"])] = r
    present = absent = diagonal_g = 0
    rels = []
    for key, r in index.items():
        call_id, iw, n1true, ig, igp = key
        if ig == igp:
            diagonal_g += 1
            continue
        t = index.get((call_id, iw, n1true, igp, ig))
        if t is None:
            absent += 1
            continue
        present += 1
        t1 = F(r["vcoul"]) * (-F(r["occ"]) * F(r["ssx_post"]) + F(r["sch"]) / 2)
        t2 = F(t["vcoul"]) * (-F(t["occ"]) * F(t["ssx_post"]) + F(t["sch"]) / 2)
        scale = (abs(t1) + abs(t2)) / 2
        if scale == 0:
            continue
        rels.append((abs(t1 - t2) / scale, key))
    rels.sort(key=lambda x: -x[0])
    n = len(rels)
    return dict(
        THIS_IS_NOT_THE_BAND_INDEX_TEST=(
            "antisymmetry of the recorded near-pole kernel T under G <-> G'. "
            "Sufficient-condition diagnostic only: exact symmetry of T would "
            "force Sigma_nm = Sigma_mn for every band pair, but asymmetry of T "
            "does NOT establish Sigma_nm != Sigma_mn, because the "
            "antisymmetric part is contracted with M_n(G) M_m(G') and can "
            "cancel. Measured on the near-pole occ != 1 subset only; the "
            "generic-branch terms of the same sums were never exported, so "
            "this cannot be aggregated into a statement about Sigma."),
        ordered_pairs_with_both_orderings_exported=present,
        ordered_pairs_whose_transpose_was_not_exported=absent,
        records_with_ig_equal_igp=diagonal_g,
        pairs_compared=n,
        max_relative_antisymmetry=float(rels[0][0]) if n else None,
        max_at=list(rels[0][1]) if n else None,
        median_relative_antisymmetry=float(rels[n // 2][0]) if n else None,
        min_relative_antisymmetry=float(rels[-1][0]) if n else None,
        exactly_symmetric_pairs=sum(1 for rel, _ in rels if rel == 0),
    )


def run(records_path, accumulators_path, sigma_inp_path):
    rows = wm.parse(pathlib.Path(records_path).read_text())
    accumulators = wm.parse_accumulators(
        pathlib.Path(accumulators_path).read_text())
    block_of, blocks = call_blocks(accumulators)
    missing = sorted({r["call_id"] for r in rows} - set(block_of))
    if missing:
        raise SymmetryError(
            f"records reference calls with no accumulator row: {missing[:5]}")
    offdiag_requested = parse_offdiag_block(
        pathlib.Path(sigma_inp_path).read_text())
    fingerprints = fingerprint_bands(rows, block_of)
    inventory, unresolved = pair_inventory(rows, fingerprints)
    verdict = testability(inventory)
    requested_pairs = sorted({(a, b) for a, b, _l in offdiag_requested})
    return dict(
        what=("whether the exported T-004 dataset can test the band-index "
              "symmetry of Sigma. Real flavor: MYCONJG is the identity, so "
              "the relation is Sigma_nm = Sigma_mn, not conjugate symmetry."),
        source_reading=SOURCE_READING,
        records=len(rows),
        accumulator_rows=len(accumulators),
        call_blocks=len(blocks),
        calls_per_block=sorted({len(b) for b in blocks}),
        sigma_inp_offdiag_block=[list(t) for t in offdiag_requested],
        sigma_inp_requested_band_pairs=[list(p) for p in requested_pairs],
        band_pair_inventory=[
            dict(icalc=icalc, n=n, m=m, calls=v["calls"], records=v["records"])
            for (icalc, n, m), v in sorted(inventory.items())],
        calls_with_unresolved_bands=unresolved,
        unresolved_note=(
            "A call is unresolved when no band's exported samples cover the "
            "record indices needed to fingerprint it. This happens where a "
            "band contributed no near-pole occ != 1 events in that call "
            "block, so the export simply contains no comparable sample. Such "
            "calls are reported and excluded from the inventory rather than "
            "guessed. They do not affect the verdict, which depends on which "
            "(n, m) pairs exist at all, and the resolved inventory already "
            "reproduces every pair the sigma.inp offdiag block requests."),
        fingerprint_method=(
            "the ket band m is not a dummy argument of mtxel_cor and is not an "
            "exported field. It is recovered by exact binary64 matching of the "
            "exported aqsm against the diagonal calls' aqs values in the same "
            "call block, requiring a unique band to match across every "
            "comparable record of a call."),
        fingerprint_detail={str(k): v for k, v in sorted(fingerprints.items())
                            if any(r["call_id"] == k and
                                   r["icalc"] == ICALC_OFFDIAGONAL
                                   for r in rows)},
        inventory_agrees_with_sigma_inp=(
            sorted({(n, m) for (_i, n, m) in inventory
                    if _i == ICALC_OFFDIAGONAL}) == requested_pairs),
        hermiticity_testability=verdict,
        gg_transpose_diagnostic=gg_transpose_report(rows),
    )


def format_report(result):
    v = result["hermiticity_testability"]
    lines = ["# Band-index symmetry: testability on the exported dataset", ""]
    lines.append(f"verdict: {v['verdict']}")
    lines.append("")
    lines.append("sigma.inp offdiag block (off1=n, off2=m, off3=l): "
                 + ", ".join(str(tuple(t))
                             for t in result["sigma_inp_offdiag_block"]))
    lines.append("")
    lines.append("| icalc | n (exported band_in) | m (fingerprinted) | calls | "
                 "records | transpose (m,n) present? |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    present = {(e["n"], e["m"]) for e in result["band_pair_inventory"]}
    for e in result["band_pair_inventory"]:
        tr = "n/a (n == m)" if e["n"] == e["m"] else (
            "yes" if (e["m"], e["n"]) in present else "NO")
        lines.append(f"| {e['icalc']} | {e['n']} | {e['m']} | "
                     f"{len(e['calls'])} | {e['records']} | {tr} |")
    lines.append("")
    lines.append("transposed partners missing: "
                 + (", ".join(str(tuple(p))
                              for p in v["transposed_partners_missing"])
                    or "none"))
    lines.append("")
    lines.append("what would be required: " + v["what_would_be_required"])
    lines.append("")
    lines.append("and even then: " + v["also_required_even_then"])
    g = result["gg_transpose_diagnostic"]
    lines += ["", "## Separate diagnostic, NOT the band-index test", "",
              g["THIS_IS_NOT_THE_BAND_INDEX_TEST"], "",
              "| quantity | value |", "| --- | --- |"]
    for k in ("ordered_pairs_with_both_orderings_exported",
              "ordered_pairs_whose_transpose_was_not_exported",
              "records_with_ig_equal_igp", "pairs_compared",
              "exactly_symmetric_pairs", "max_relative_antisymmetry",
              "median_relative_antisymmetry", "min_relative_antisymmetry"):
        val = g[k]
        lines.append(f"| {k} | "
                     f"{val if not isinstance(val, float) else f'{val:.6e}'} |")
    return "\n".join(lines)


def main(argv=None):
    here = pathlib.Path(__file__).parent
    ap = argparse.ArgumentParser()
    ap.add_argument("records", nargs="?",
                    default=here / "fixtures" / "t004_nearpole_weighted.dat")
    ap.add_argument("--accumulators",
                    default=here / "fixtures" / "t004_accumulators.dat")
    ap.add_argument("--sigma-inp",
                    default=here / "fixtures" / "fermi_sigma.inp")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    result = run(args.records, args.accumulators, args.sigma_inp)
    if args.json:
        json.dump(result, sys.stdout, indent=2)
        print()
    else:
        print(format_report(result))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (SymmetryError, wm.WeightedError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
