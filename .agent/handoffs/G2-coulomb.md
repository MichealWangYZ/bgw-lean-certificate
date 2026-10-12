# G2-coulomb handoff: the mini-BZ Coulomb averages kernel-checked (`VbHyp` discharged)

Status: ready for review. This is **not accepted**. Branch `lean/g2-coulomb`, forked from
`bgw-e/endpoint` (6a609a2). Nothing is merged.

**Outcome (a): all entries, composed theorem.**

    GW.Endpoint.Kernel.Coul.vb_hyp : VbHyp S3.vbT S3.eg.SV vbTrue          (all 1363 vbar boxes)
    GW.Endpoint.Kernel.Coul.oq_hyp : VbHyp S3.oqT S3.eg.SV oqTrue          (all 7 oneoverq boxes)
    GW.Endpoint.Kernel.Coul.o1_enclosure_unconditional :
      O1 S3.gl S3.stX S3.stL S3.Etrue vbTrue oqTrue ∈ [8880811588953599/2^59, 8880812351936001/2^59]
    GW.Endpoint.Kernel.Coul.o1_pos_unconditional : 0 < O1 … vbTrue oqTrue          (C1, spec A)

The boxes are exactly those of `coulomb_cert.json` / stage 3 (no widening), so stage 3 is
**not** re-run: `o1_enclosure_unconditional` is literally `S3.o1_enclosure vbTrue oqTrue vb_hyp
oq_hyp`.

## What is proved (plain mathematics)

Definitions (`GW/Endpoint/Coulomb/Geometry.lean`, `Average.lean`), crystal coordinates
`u ∈ ℝ³`, metric `B = Bint/2^54` (the exact dyadic `bdot` of the file; `Bint` = the integers of
stage 3's `gl.B`):

* `cellP = {u | 2⟨u, n/2⟩_B ≤ |n/2|²_B for the 26 n ∈ {-1,0,1}³∖0}` — the Wigner–Seitz cell of
  the q-lattice `(ℤ/2)³` exactly as `certcoulomb.ws_cell` builds it (26 half-spaces);
* `cavg k Q = 8π / |P| · ∫_P |Q+u|_B^{-k} du` (Lebesgue measure, `|P|` its volume, proved `= 1/8`),
  `vbTrue key = cavg 2 (key/2)`, `oqTrue key = cavg 1 (key/2)`; `key = 2(q+G)` as in stage 3.

The average is invariant under linear changes of variables, so this is the same number as the
Cartesian mini-BZ average `(1/V) ∫ 8π/|q+G+p|² d³p` (certcoulomb's `sqrt(det B)` cancellation);
Lean states it in crystal coordinates only.

Theorems (default target `GW`, all generic, then instantiated by kernel-checked data):

1. **Taylor remainders** (`Series.lean`): with `z = 1+α+β`, `α² ≤ 4β ≤ 4t²`, `t < 1`,
   `|1/z − Σ_{n≤N} W_n| ≤ φ_N(t)` and `|z^{-1/2} − Σ_{n≤N} V_n| ≤ φ_N(t)`,
   `φ_N(t) = ((N+2)t^{N+1} + (N+1)t^{N+2})/(1−t)²`, where `W_n`, `V_n` are the
   Chebyshev-/Legendre-type graded pieces. Both via quadratic invariants
   (`W_{n+1}²+αW_{n+1}W_n+βW_n² = β^{n+1}`, the Legendre analogue is nonincreasing), which give
   `|W_n|, |V_n| ≤ (n+1)tⁿ`; the `z^{-1/2}` remainder by the FTC along `λ ↦ (λα, λ²β)`.
2. **Triangle integration** (`Simplex.lean`): Dirichlet moments `∫_{T2} s₁^a s₂^b = a!b!/(a+b+2)!`,
   the exact 4-way midpoint split, and `rule_exact`: a rule passing the integer check `ruleOK`
   (exactness on every monomial of degree ≤ d) integrates every polynomial of degree ≤ d exactly.
3. **Leaf bound** (`Leaf.lean`): for a triangle leaf with centre `c` and `|v−c| ≤ t|c|` at the
   vertices, `|∫ f − Σ w_i f(x_i)| ≤ (1/2 + Σ|w_i|) φ_d(t) |c|^{-k}` (`f = |x|_B^{-k}`).
4. **Checker soundness** (`CheckDefs.lean` core Lean, `CheckSound.lean`): `treeChk` (quadtree of
   leaves; Grundmann–Möller rules of degree 3…23 computed in Lean; exact integers, floor/ceil,
   verified integer square roots for `k = 1`) returns `[lo, hi]` with
   `lo ≤ 2^K WCc sD^{-k} ∫_{T2} |y(s)|^{-k} ≤ hi` (`treeChk_sound`).
5. **Cone formula** (`Cone.lean`): `∫_{conv(0,a,b,c)} g = |det(a,b,c)|/(3−k) ∫_{T2} g(a+s₁(b−a)+s₂(c−a))`
   for measurable `g ≥ 0` homogeneous of degree `−k` (linear change of variables, radial map
   `(r,s) ↦ r(1−s₁−s₂, s₁, s₂)` with Jacobian `r²`, Fubini).
6. **Signed cones** (`Signed.lean`, `Assemble.lean`): for any tetrahedron `T` and the cones from
   the origin over its faces, `Σ_{c_j>0} ∫_{cone j} g = ∫_T g + Σ_{c_j<0} ∫_{cone j} g`
   (`c_j` = barycentric coordinates of the origin), proved pointwise off finitely many affine
   hyperplanes (the feasible-parameter interval argument) — no Stokes theorem.
7. **The cell** (`GeomDefs.lean` checks, `Geometry.lean`): `P = ⋃ T_i` over the 72 face-centre
   fan tetrahedra `conv(0, c_F, V_j, V_{j+1})`, pairwise a.e.-disjoint, `T_i ⊆ P`, `|P| = 1/8`,
   from integer certificates (`geom_ok`, kernel 19 s): adjugates, single-term Farkas certificates
   of a lifted piecewise-linear convex function `φ_i` (max-trick covering), separation by
   `φ_i − φ_j`, vertex containment.
8. **Exact reduction** (`Cell.lean`, `Average.lean`): `cavg k Q = 64π Σ_i sg(c₀ⁱ(Q)) Cc_i(Q)`
   over the 72 outer faces of `P+Q` (inner cones cancel by an involution on the shared faces;
   signs from the certificates), `Cc_i = |det|/(3−k) J_i`, `J_i` a triangle integral.
9. **Symmetry** (`Symm.lean`): `cavg k (gQ) = cavg k Q` for the 12 signed coordinate
   permutations of the exact metric (they preserve `B`, permute the 26 normals, `|det| = 1`).
10. **Tables** (`Table.lean`): `rep_of_faces` (72 face checks ⇒ `64π[SL, SH]/N` encloses
    `cavg` of an orbit representative), `tab_sound` (each table entry `= g · rep`, `boxOK` places
    `64π[SL,SH]/N` inside `[lo,hi]/2^SV` with `π ∈ (3.14159265358979323846, …847)` from Mathlib).

Kernel data (`GW/Endpoint/Kernel/Data/Coul*.lean`, target `GWKernelData`, root `CoulTab`):
`CoulRules` (154 row checks: GM degrees 3…23 exact on all monomials), `CoulV0…CoulV149` (150
vbar orbit representatives), `CoulO0…O2` (3 oneoverq representatives), each 72 face theorems
`faceChkC … = true` + the two sums, all `decide +kernel`; `CoulTab` (rule certificate, 153
`RepOK`s, hints and `tabChk` over stage 3's own `vbT`/`oqT`, the composed theorems).

## What remains trusted / not claimed

* The definition of the physical quantity: that BerkeleyGW's `vbar`/`oneoverq` (Monte Carlo) are
  estimates of this exact average (coulomb.py/E1 evidence, not Lean). Lean proves the exact
  average lies in the boxes; it says nothing about the production Monte Carlo values.
* The cell is the 26-half-space cell (as certcoulomb.py); that the remaining lattice vectors
  are redundant (true WS cell) is not proved in Lean.
* Everything upstream of `VbHyp` in stage 3 (symmetry unfolding, capture) is unchanged.

## Numbers

* 150 + 3 orbit representatives (12-element group), 2,668,863 cubature nodes, 12k leaves;
  planner budget `0.85 × min(margin to box)`; smallest relative box margin ≈ 6.4e-17.
* Kernel throughput ≈ 0.65 ms per node; modules chunked to ≤ 110k nodes (peak RSS ≈ 2.7 GB; an
  unchunked 319k-node module peaked at 6.6 GB).

## Checks

* `lake build GW`: PASS (the 17 `GW/Endpoint/Coulomb/*` modules are imported by `GW.lean`;
  `geom_ok` is a 19 s `decide +kernel`).
* `lake build GW.Endpoint.Kernel.Data.CoulAudit` (the 157-module serial Coul* chain + `CoulTab`,
  `CoulTamper`): PASS, **1 h 06 min wall, peak RSS 7.2 GB** (max over the chain's processes; the
  heaviest single rep module peaked at 2.7 GB in isolation — the 7.2 GB is most likely `CoulTab`,
  which imports S3Check; a heavy unrelated job ran concurrently).
* `#print axioms` (`CoulAudit.lean`): `o1_enclosure_unconditional`, `o1_pos_unconditional`,
  `vb_hyp`, `oq_hyp`, `deg_ok`, `repV0`, `repO0` → `[propext, Classical.choice, Quot.sound]`;
  the tamper theorems use at most `propext`. `lake env lean GW/Audit.lean`: the 19 new Coulomb
  lines only list allowed axioms. No `sorry`/`admit`/`native_decide`/axioms in the new files.
* Full `lake env lean scripts/CheckAxioms.lean` (imports CoulTab, CoulTamper): **AXIOM AUDIT PASSED: 31390 theorems**, 159 Coul* modules covered (28 min, 5.8 GB).
* Negative controls (`CoulTamper.lean`): a certified face with `lo+1` → `faceChkC … = false`
  (the unmodified record → `true`); a GM weight changed by one → `ruleRow … = false`; a stage-3
  box collapsed to its lower end → `boxOK … = false`; a cell vertex moved by one unit →
  `invOK … = false`.
* `metric_same` (CoulTab): stage 3's `gl.B`, `gl.SB = 54` are the integers of the metric used
  here.
* `verify.sh` was not run end to end (time).

## Commands

```
cd .claude/worktrees/lean-coul && source scripts/env.sh
~/bgw-src/pyenv-e1/bin/python bgw/endpoint/coulomb_export.py --geom          # GeomData.lean
~/bgw-src/pyenv-e1/bin/python bgw/endpoint/coulomb_export.py --lean --cache PLANS.pkl
    # plans every representative (≈ 15 min), mirrors the Lean checker exactly and asserts every
    # box before writing Coul*.lean
nice lake build GW
nice lake build GW.Endpoint.Kernel.Data.CoulAudit      # the Coul* chain (serial) + CoulTab
lake env lean GW/Endpoint/Kernel/Data/CoulAudit.lean
lake env lean GW/Audit.lean
```

## Failed attempts / design notes

* 3D cubature on subdivided tetrahedra: ≈ 28 M nodes even with symmetry — infeasible at the
  kernel's ~0.5 ms/node; the cone formula reduces everything to 2D triangle integrals (2.7 M).
* A single-module `ruleOK` for degree 23: 47 s, 10.9 GB → split into per-row theorems.
* Kernel loops: the equation compiler's structural recursion and lazy accumulators hit
  `maxRecDepth`; strict `bif` accumulators and core-Lean data modules (no Mathlib import:
  0.5 GB baseline instead of 4.8 GB).
* A 319k-node module peaked at 6.6 GB (kernel memory grows within a module) → chunks.

## Next action

Review the definitions (`cellP`, `cavg`, `keyQ`) against certcoulomb.py / BerkeleyGW, the
statement of `o1_enclosure_unconditional`, and rerun the checks.
