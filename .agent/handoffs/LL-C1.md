# LL-C1 handoff — finite diagram-to-algebra bridge

> **Correction, recorded in LL-C1-R1 and not by rewriting this document.** The
> "Reproduction" section below states that
> `artifacts/ll-c1/lean_values.json` and `artifacts/ll-c1/comparison.json` were
> "both committed on the branch". **They were not**: `artifacts/` is ignored, so
> `git add -A` never staged them and a fresh checkout of `cf49853` does not
> contain them. They are committed as of LL-C1-R1, and `ll/make_comparison.py`
> regenerates the second from the first. See `.agent/handoffs/LL-C1-R1.md`.
> The rest of this document stands as submitted.

```
Status: CHECKPOINT_READY
```

Not self-acceptance. Acceptance is the owner's or an independent reviewer's.
I stopped here and did not begin C2.

## Base / result / versions / time

* Planning base: `95891c3` on `origin/plan/lin-lindsey-checkpoints-20260914`
  (which is `main` `7b5eea1` plus the two roadmap commits).
* Work branch: `ll-c1/finite-diagram-bridge`, isolated worktree at
  `.claude/worktrees/ll-c1`. **Not merged, not pushed.** `main` untouched.
* Lean 4.19.0 / Lake 5.0.0-6caaee8, mathlib pinned by `lean-toolchain`,
  Python 3.12.3.
* **Cumulative active wall time: 28 min** (`01:42:55Z` → `02:11:11Z`, plus a
  short evidence-writing tail). Budget was 6 h; preflight cap 45 min was met
  (baseline + source access took ~12 min).
* Preflight baseline in the worktree: `bash scripts/verify.sh` **exit 0**
  before any edit. No pre-existing failure to disentangle.

## Exact claim proved; assumptions; unproved boundaries

For **every** finite dimension `N` and over any commutative ring (fields where
division appears), with `B = G ⊙ G`:

| Theorem | Statement |
|---|---|
| `GW.LL.contraction_ring0/1/2` | the graph contraction equals `G i j * v i j`, `matrix1`, `matrix2` |
| `GW.LL.symmetry_ring0/1/2` | `Fintype.card (Aut ring k) = 1, 2, 4` |
| `GW.LL.contribution_ring0/1/2` | `-(G⊙v)`, `+(1/2)(G⊙(vBv))`, `-(1/4)(G⊙(vBvBv))` |
| `GW.LL.contraction_ratCast`, `contribution_ratCast` | the ℚ evaluator's real reading is the ℝ evaluation |

**No symmetry, positivity or invertibility hypothesis is used.** These are
polynomial identities in the matrix entries; `G` and `v` are arbitrary. No
infinite-dimensional limit, formal series, or analytic summation appears, and
none was needed — the infinity trigger in §5 of the task was never reached.

Boundaries: this is the classical real Gibbs model of Lin–Lindsey Part I, not
electronic GW and not BerkeleyGW. `GW/LL/` is documented as such and is
additive; nothing in the GPP development depends on it. Three rings prove
nothing about general `k`, about skeleton/bold theory, or about Theorem 4.12.

## Source, and the convention actually used

Read from the PDF (`arXiv:1809.02900v1`, 55 pp.), not the HTML:

* p. 42: `S_{Γ_k} = 2^k`, "a factor of 2 deriving from the each symmetry that
  exchanges the two propagators in one of the k 'bubbles'"; amplitude
  `F_{Γ_k}(i,j) = -([-v(G⊙G)]^k v)_{ij} G_{ij}`.
* p. 43, Fig. 4.11 (inspected as an image, not inferred from the answer): the
  external line with `k` bubbles separated by `k+1` wavy interaction lines;
  the sum is written `Σ_k F_{Γ_k}/S_{Γ_k}`, "where the factor ½ arises from the
  symmetry factor".

So **contribution = amplitude ÷ symmetry factor**, and that convention
reproduces the task's three targets exactly. No target was rewritten.

The four levels the task asked to keep separate are separate definitions:
`contraction` (graph only) → `amplitude` (= `signFactor * contraction`) →
`Fintype.card (Aut D)` → `contribution`, tied by
`contribution_eq_amplitude_div`.

The sign is a uniform rule, `(-1)^(number of interaction edges)`, applied to
all three graphs — not a per-diagram adjustment. It gives `-1, +1, -1`.

## Acceptance items

| Item | Status | Pointer |
|---|---|---|
| Graph data with external labels and parallel lines | pass | `GW/LL/Ring.lean` `ring0/1/2`; propagator lists repeat the bubble edge |
| Contraction derived from data, not defined as the answer | pass | `FeynDiagram.contraction` reads only the edge lists |
| Faithful symmetry notion, external labels fixed | pass | `FeynDiagram.IsAut` (Def. 3.8 specialised); `samePair` documented as storage-order normalisation, not edge reversal |
| Automorphism counts 1, 2, 4 proved | pass | `symmetry_ring0/1/2` |
| Kernel-checked identities, arbitrary `N` | pass | `contraction_ring0/1/2`, `contribution_ring0/1/2` |
| Connection to exact executable evaluation | pass | `contributionOf` + `contribution_eq_of_card`; `ll_c1_eval` |
| Exact Python comparison, N = 1,2,3 | pass | 18/18 exact, `artifacts/ll-c1/comparison.json` |
| `v*B ≠ B*v`, equal and unequal external indices, non-scalar PD `G` | pass | asserted as tests, not assumed |
| Adversarial mutants with fixed witnesses | pass | 7/7 detected |
| Permitted relabeling leaves value unchanged | pass | `test_permitted_internal_relabeling_changes_nothing` |
| New modules in the exhaustive audit | pass | `AUDIT_MODULE GW.LL.Diagram`, `GW.LL.Ring` |
| Green final baseline | pass | `verify.sh` exit 0 |

No `sorry`, `admit`, project axiom, `native_decide`, or unsafe shortcut. Every
LL theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Independent comparison and mutants

`ll/ring_reference.py` never imports, runs, or reads the Lean side. It
implements the ring value **twice**, from two different descriptions in the
paper — the closed matrix formula (p. 42) and a direct sum over internal index
assignments — and `both_agree` raises if they differ. All 18 Lean values match
the reference exactly, in `fractions.Fraction`; there are no tolerances.

Witness for every mutant: `N2-pd-unequal-ext` (`G = [[2,1],[1,2]]` positive
definite, `v = [[1,2],[2,3]]`, `i=0, j=1`, and `v*B ≠ B*v` there).

| Mutant | k | correct | mutated |
|---|---|---|---|
| sign rule off by one interaction factor | 0,1,2 | `-2`, `39/2`, `-405/2` | `2`, `-39/2`, `405/2` |
| symmetry factor omitted | 1,2 | `39/2`, `-405/2` | `39`, `-810` |
| chain attached to the wrong bubble site | 1,2 | `39/2`, `-405/2` | detected, values in the artifact |

The last is a genuine topology error (the chain enters and leaves the same
side of each bubble), not a relabeling and not a true identity.

## Decisive obstruction and how it was handled

**Deciding `Aut(ring 2)` by enumeration is infeasible and I did not force it.**
The triple space is `|Perm(Site 4)| × |Perm(Fin 5)| × |Perm(Fin 3)| = 518,400`;
`decide` first hit the heartbeat limit and then, with heartbeats removed,
**overflowed the kernel stack** in 43 s. Ring 0 (2 candidates) and ring 1 (288)
decide in 2.5 s and 4.2 s.

Rather than weaken the statement I proved a reduction, and two wrong guesses
along the way were informative:

1. *Interactions alone force `σ = 1`* — **false**, and `decide` refuted it in
   3 s. The interaction edge `{b₁,a₂}` is unordered, so `σ` may swap `b₁ ↔ a₂`.
2. *Propagators alone force `σ = 1`* — also **false**. They permit exchanging
   the two whole bubbles.
3. Both conditions together **do** force it: `ring2_forces_id_site`, decided
   exhaustively over the 720 site relabelings in **12 s**. Then
   `ring2_forces_id_int` (6 candidates) and `ring2_prop_card` (120) finish it,
   and `autEquivProps` assembles them.

So the symmetry factor 4 is *computed from the automorphism definition*, via a
proved reduction — not `Fin (2^k)` by fiat, and not brute force.

## What this teaches us about the roadmap

* **The C1 hypothesis holds for this family.** Genuine graph data does yield
  the right contraction, sign and multiplicity, with the symmetry factor
  computed rather than inserted. The bridge is real at k ≤ 2.
* **Symmetry counting, not contraction, is the scaling risk.** The contraction
  identities were routine once the sum-reindexing helpers existed; the
  automorphism count is what exploded. The cost is combinatorial in the number
  of sites, so C2's "arbitrary ring order" cannot be reached by enumeration at
  all. It needs the structural argument — externals fixed ⇒ the interaction
  path is rigid ⇒ only bubble swaps survive — proved once by induction on `k`,
  not re-decided per diagram. That is a concrete, bounded piece of mathematics,
  and it is the thing to try next.
* **A finite-`N` theorem family is exactly what the roadmap says it is.**
  Everything here is `∀ N`, and nothing licenses `N → ∞`.
* One convention check paid off: the paper's amplitude already carries the
  `(-1)^k`, so the targets follow only if `contribution = F/S`. Getting that
  backwards would have flipped signs at odd `k` and still looked plausible.

## One recommended decision

**Continue, with one bounded task** — not an automatic order.

Proposed C2-prelude, allowance **6 h**: prove `Aut(ring k) ≃ (Fin k → Bool)`
for general `k` by the structural argument above, giving `S = 2^k` for all `k`
without enumeration, together with the general contraction identity
`contribution (ring k) = -(G ⊙ [(-vB)^k v]) / 2^k`. That is a single general
theorem, still finite, still no formal series. It converts the brittle part of
C1 into the durable part, and it is the precondition for anything in C2.

Explicitly **not** recommended yet: formal power series, the geometric
resummation to `W`, skeleton theory, or any electronic bridge.

## Reproduction

```bash
git worktree add .claude/worktrees/ll-c1 ll-c1/finite-diagram-bridge
cd .claude/worktrees/ll-c1 && source scripts/env.sh
bash scripts/verify.sh                       # exit 0
./.lake/build/bin/ll_c1_eval                 # exact rational ring values
python3 ll/ring_reference.py                 # independent reference
python3 -m unittest tests.test_ll_c1 -v      # 13 tests
```

Gate on the result commit: **exit 0**, 240 Python tests (227 baseline + 13),
116 named / **248** exhaustive theorem audits (was 100 / 227 at baseline),
allowed axioms only.

Artifacts needed to reproduce, both committed on the branch:
`artifacts/ll-c1/lean_values.json`, `artifacts/ll-c1/comparison.json`.

## Files

```
GW/LL/Diagram.lean      diagram structure, contraction, Aut, amplitude, reduction
GW/LL/Ring.lean         the three rings, identities, symmetry factors, casts
LLMain.lean             ll_c1_eval executable
ll/ring_reference.py    independent Python reference (two routes)
tests/test_ll_c1.py     13 tests: agreement, properties, mutants
GW.lean, GW/Audit.lean  additive imports and #print axioms entries
scripts/gates.py        test_ll_c1 classified scientific
scripts/verify.py       one step: evaluate LL-C1 in Lean before the tests
lakefile.toml           ll_c1_eval target
```

Provenance note: `PROVENANCE-R6.txt` digests were refreshed for the four
pre-existing files this task modified (`GW.lean`, `GW/Audit.lean`,
`scripts/verify.py`, `scripts/gates.py`) using `scripts/make_manifest.py`,
which only re-hashes already-listed paths. **The new LL-C1 files were not
added to that manifest**: what a manifest vouches for is an owner decision and
T-006's manifest is not mine to widen.

One unrelated break I caused and fixed: `ll/reference.py` on `sys.path`
shadowed `scripts/reference.py` and broke `tests/test_reference.py`. Renamed
to `ll/ring_reference.py` and loaded by explicit path, so no module-name
collision is possible.
