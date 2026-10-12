# LL-C2A handoff — arbitrary finite ring structure

```
Status: CHECKPOINT_READY
```

Not self-acceptance. I stopped here: **C2B was not started**, nothing was
pushed, `main` was not merged, no dependency or toolchain changed, and no
upstream community was contacted.

## Base, result, versions, elapsed

* Task base: PR #4 result `111e97c`. Branch base:
  `plan/ll-c2a-structural-rings-20260915` at `ca6fe1a`.
* Work branch `ll-c2a/structural-rings`, isolated worktree.
* Lean 4.19.0 / Lake 5.0.0-6caaee8, mathlib `c44e0c8`, Python 3.12.3.
* **Cumulative active wall time: ~50 min** (`05:51:38Z` → `06:41Z`) against a
  6-hour allowance. Preflight ~3 min (cap 30); opening cleanup ~5 min (cap 45).
  The 90-minute no-new-evidence rule was never approached.

## Opening cleanup (§2)

### 2.1 One validator — pass

Reproduced all four of the review's probes against the old generator first;
all four exited 0. Root cause: `ll/make_comparison.py` built `{name: row}`
directly and copied the candidate's own `symmetry_factors` into a field it
named `*_from_paper`.

* `ll/evidence.py` is now the single validator. Both `tests/test_ll_c1.py` and
  `ll/make_comparison.py` call it; the test module is not imported into the
  generator.
* `EXPECTED_SYMMETRY_FACTORS = {ring0:1, ring1:2, ring2:4}` is an independent
  constant checked against the artifact. The emitted field is renamed
  `symmetry_factors_checked_against_paper`; nothing launders candidate data as
  the paper's, and a test asserts the old field name is gone.
* Six CLI regressions in `ReportGeneratorRejectsBadEvidence`: unmodified table
  succeeds; duplicate row, invalid `N/i/j`, forged symmetry metadata and an
  ordinary wrong value all exit non-zero.
* `scripts/verify.py` now runs the generator after the Lean evaluator, so the
  checked report cannot lag the checked values.

No schema framework, provenance system or report hierarchy was added.

### 2.2 Precise witness and docstrings — pass

* `loopExample` replaced by the review's witness `selfLoopWitness`: sites
  `I,J,a,b`; interactions `(I,J)`, `(a,b)`; propagators `(I,a)`, `(a,J)`,
  `(b,b)`. `selfLoopWitness_compressed_card` proves the compressed count is 1.
  The half-edge count of 2 is labelled **external reasoning, not
  kernel-checked**, because this repository formalises no half-edge model for
  self-loops — `RingHalfEdge` is deliberately ring-only.
* The `Aut` docstring no longer identifies the compressed cardinality with
  Definition 3.8 for arbitrary `FeynDiagram`; it says so only where the
  correspondence is proved.
* `example : True := trivial` removed.

## The structural family (§3)

`GW/LL/StructuralRing.lean`. Internal sites are interleaved, `a_m = 2m`,
`b_m = 2m+1`, which is what makes the induction work: peeling two indices off
an assignment leaves exactly an assignment for `ring k`.

**Specialisation is definitional, not numerical:**
`ring_zero/one/two : ring 0 = ring0`, `ring 1 = ring1`, `ring 2 = ring2`, each
by `rfl`. That is agreement as graph data, which is stronger than the task
required.

### 3.1 General contraction — pass

```
contraction_ring (k) (G v) (i j) :
  contraction (ring k) G v i j = G i j * (v * (bubble G * v) ^ k) i j
```

For every `k` and every finite `N`, over any `CommRing`. **No positivity,
invertibility, symmetry or convergence hypothesis** — it is a polynomial
identity in the matrix entries. Route: closed forms for both edge products
(`edgeProd_ringProps`, `edgeProd_ringInts_succ`), the chain peel
(`edgeProd_ringInts_peel`), an explicit peeling equivalence (`peelEquiv`,
`sum_peel`), then induction via `ringPart_succ` and `ringPart_eq_chain`.

```
contribution_ring (k) : contribution (ring k) G v i j
  = (-1)^(k+1) * (G i j * (v * (bubble G * v)^k) i j) / 2^k
```

### 3.2 Structural automorphism classification — pass, no per-`k` enumeration

**Chain rigidity.** `extI` lies on exactly one interaction edge, so that edge
is fixed (`sigma_fixes_aS_zero`); the only propagators at `a_m` are that
bubble's two copies, so `b_m` is fixed once `a_m` is (`sigma_fixes_bS`); `b_m`
lies on exactly one interaction edge, whose other end is `a_{m+1}`
(`sigma_fixes_aS_succ`). Alternating these pins every internal site
(`sigma_fixes_all`), giving `sigma_eq_one` for every `k`.

**`rho_eq_one`.** With `σ = 1`, no stored interaction pair is the reverse of
another — left ends are `extI` or some `b`, right ends are some `a` or `extJ`,
and those sets are disjoint — so the unordered condition collapses to equality
of stored pairs, and `ringInts_nodup` forces the identity.

**`π`.** `props_pair_eq`, `pi_fixes_external`, `pi_bubble_mem` and
`pi_pIdx2_of_pIdx1` show the external index is fixed and each bubble's two
copies map onto themselves. `autEquivBits : Aut (ring k) ≃ (Fin k → Bool)` is
built from an explicit involution (`flipIdx`), not a product of swaps, so its
action on each index is computable and no disjointness argument is needed.

```
card_aut_ring (k) : Fintype.card (Aut (ring k)) = 2 ^ k
```

`2^k` is **never an input**: the `Aut` Fintype comes from the decidable
predicate, and the evaluator's use of the literal divisor is certified by
`contribution_ring_eq_contributionOf`.

Purported extra automorphisms are refuted **at theorem level for every `k`**,
not by `decide` at one order: `aut_no_bubble_exchange`,
`aut_no_intra_bubble_exchange`, `aut_fixes_extI/extJ`.

### 3.3 Ring-only half-edge fidelity — pass

`GW/LL/RingHalfEdge.lean`. `RingFlag k` has one inhabitant per half-edge:
`extProp s`, `bub m c s` (bubble `m`, copy `c`, side `s`), `int e s`. Each edge
carries two flags as separate inhabitants, and `mate` is a fixed-point-free
involution, so **exchanging the two flags of a single edge is expressible**.
It is excluded by the site-map condition plus the fact that a ring propagator
joins two distinct sites (`ring_no_self_loop`) — not by the encoding. That is
what stops this from restating the compressed model.

Rigidity is reproved independently in this model (`flagAut_chain`,
`flagAut_sites`, `flagAut_sigma_eq_one`, `flagAut_fixes_int`,
`flagAut_fixes_extProp`, `flagAut_bub`), giving

```
ringHalfEdgeEquivBits (k) : RingHalfEdgeAut k ≃ (Fin k → Bool)
ringHalfEdgeEquivAut  (k) : RingHalfEdgeAut k ≃ Aut (ring k)
ringHalfEdgeEquivAut_bits : autBits (ringHalfEdgeEquivAut k a) = flagBits a.2
card_ringHalfEdgeAut (k) : Fintype.card (RingHalfEdgeAut k) = 2 ^ k
```

The last line is an independent count: `RingHalfEdgeAut` has its own
decidable-predicate Fintype (`instDecIsFlagAut`), deliberately **not** derived
from the equivalence, so the card is not a restatement of it. The
`_bits` theorem is the required commuting interpretation: the bit read off a
half-edge automorphism is the bit read off its compressed image.

**Claim boundary.** This is asserted for the ring family only. No half-edge
model is defined outside the rings, no general faithfulness is claimed, no
tadpoles, Wick contractions or skeleton decomposition are supported, and
`FeynDiagram` still does not enforce quartic well-formedness.

## Executable evidence (§4)

`ll_c2a_eval` (new, separate from `ll_c1_eval` so the C1 artifact and its
contracts are untouched) emits exact rationals for **k = 0..4** on three
fixtures, including a nonscalar `N=2` positive-definite `G` with
`v*B ≠ B*v`, one with non-integer rationals, and one `N=3`.

All **15** Lean values match the independent Python reference exactly, and the
reference's two internal routes (matrix formula, direct contraction) agree.
`tests/test_ll_c2a.py`, 13 tests, mutants at `k = 3, 4`:

| Mutant | Detected |
|---|---|
| missing bubble factor of two | yes |
| wrong interaction-chain attachment (enter/leave the same side) | yes |
| duplicated bubble | yes |
| dropped bubble | yes |
| order shift (`ring k` vs `ring (k-1)`) | yes |
| permitted internal relabeling | unchanged, as required |

The extra-automorphism class is covered by the theorems in §3.2 rather than a
finite check. All C1 fixtures and repaired evidence checks are preserved.

## Verification

| Command | Exit | Result |
|---|---|---|
| `bash scripts/verify.sh` | **0** | PASS (all) |
| `./.lake/build/bin/ll_c2a_eval` | 0 | k = 0..4, three fixtures |
| `python3 ll/make_comparison.py` | 0 | 18/18 exact, 7/7 mutants |
| `python3 -m unittest tests.test_ll_c2a` | 0 | 13 tests |

**267 tests** (253 scientific, 14 workflow); **167 named / 505 exhaustive**
theorem dependency audits; `AUDIT_MODULE` present for `GW.LL.Diagram`,
`GW.LL.Ring`, `GW.LL.StructuralRing`, `GW.LL.RingHalfEdge`; only `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, `admit`, custom axiom,
`native_decide` or unsafe shortcut. `PROVENANCE-R6.txt` digests refreshed for
covered files with the existing `scripts/make_manifest.py`; claim scope not
enlarged.

## Failed attempts and things that went wrong

1. **Corrupted `GW/Audit.lean` with a prefix-substring replace.** Replacing
   `#print axioms GW.LL.contraction_ring` also matched `contraction_ring0/1/2`,
   inserting the block four times and renaming three entries to nonexistent
   constants. The gate caught it (`unknown constant
   'GW.LL.ring_no_self_loop0'`). Reverted and appended instead, then
   deduplicated. Anchoring a replace on a name that is a prefix of other names
   is the error.
2. **Two dead ends on the `Aut` reduction, both refuted in seconds.** I first
   tried to force `σ = 1` from the interaction condition alone — `decide`
   refuted it, because the interaction edge `{b₁,a₂}` is unordered so `σ` may
   swap `b₁ ↔ a₂`. Then from the propagator condition alone — also refuted,
   because propagators alone permit exchanging two whole bubbles. Only both
   together force it. Those refutations shaped the final proof.
3. **`rw` could not unify `Fin (2*(k+1))` with `Fin (?n+1)`**, since the
   literal `2` is not a successor numeral, so `sum_over_pi_succ` would not fire.
   Solved with the explicit `peelEquiv`/`sum_peel` rather than by fighting the
   unifier.
4. **Several `rw`s failed on "motive is not type correct"** where the goal's
   term depended on `(ringProps k).length`. Fixed by giving `omega` the length
   as a hypothesis instead of rewriting it.
5. **`interval_cases` was not imported**; restated the doubled-list lemma with
   a ℕ index, which also removed all `Fin` transport from that induction.

## What this teaches us about C2B and general theory

* **The representation scales.** C1's three examples were not a lucky family:
  the same encoding supports a single structural definition with a general
  contraction identity and a general symmetry factor. The C1 → C2A step needed
  no semantic change to the diagram model.
* **Rigidity, not counting, is the reusable idea.** At ring 2 the compressed
  automorphism group could only be obtained by a proved reduction because
  enumeration overflowed the kernel. The general proof never counts: it walks
  the interaction chain. Any future family with a rigid external attachment
  should admit the same argument; a family without one will not.
* **The half-edge gap is now precisely located.** Fidelity holds on rings for
  one reason only — no propagator joins a site to itself. That is a checkable
  side condition, so a future general result should be stated as "faithful on
  loopless diagrams" rather than attempted unconditionally.
* **For C2B**, what is now available is exactly a coefficient family: for each
  `k`, a proved closed form and a proved weight. Assembling those as a formal
  power series is a statement about sequences of coefficients and needs no new
  diagram theory — but it does need the formal-series API, and it must not be
  conflated with convergence. Nothing in C2A licenses an analytic claim; the
  infinity trigger was never reached because every statement is finite in both
  `N` and `k`.

## One recommended next decision

**C2B**, as its own explicitly scoped task with its own allowance — a
recommendation, not an order, and not self-acceptance.

Concretely I would propose: define the ring generating function as a formal
power series in one variable whose degree-`k` coefficient is
`contribution (ring k)`, and prove the screening identity coefficientwise
against `v * (1 + (1/2)(G ⊙ G) v)⁻¹`-style data, with the inverse handled as a
formal-series inverse and **no** convergence or analytic claim. Local
finiteness and the combinatorics are the content; `Mathlib.RingTheory.PowerSeries`
should be checked against the pinned version before committing to an API.

Not recommended yet: skeleton/bold theory, an electronic bridge, or any
general diagram library.
