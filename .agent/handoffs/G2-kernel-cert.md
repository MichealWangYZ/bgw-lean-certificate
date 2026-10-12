# G2 stage 1 handoff: kernel-checked eps⁻¹ certificate

Status: ready for review. This is **not accepted**. Branch
`lean/g2-kernel-cert`, forked from `bgw-e/endpoint` (c1a834f). Nothing is merged.

**Outcome (a).** For all three q-points, the Lean kernel checked the eps⁻¹
enclosure that `cert.py` claims. All arithmetic was redone by kernel
reduction in exact integers. The theorems are:

| theorem | q | n | build (wall = CPU) | peak RSS |
| --- | --- | --- | --- | --- |
| `GW.Endpoint.Kernel.Q0.epsinv_enclosure_q0` | (0,0,0.001) (q0, head ~3e7 before balancing) | 65 | 146 s | 2.9 GB |
| `GW.Endpoint.Kernel.Q1.epsinv_enclosure_q1` | (0,0,0.5) | 76 | 221 s | 3.1 GB |
| `GW.Endpoint.Kernel.Q2.epsinv_enclosure_q2` | (0,0.5,0.5) | 92 | 397 s | 3.6 GB |

Each build time includes elaborating that q-point's data module: 22 / 30 / 45 s.
The three builds ran one after another. The total is about 13 CPU-minutes.
`#print axioms` for each theorem gives `[propext, Classical.choice, Quot.sound]`.
A per-row kernel theorem such as `Q1.e_0` depends on no axioms.
`native_decide`, `ofReduceBool` and `sorry` do not occur anywhere.

## What is proved

`Cert.sound` in `GW/Endpoint/Kernel/Sound.lean`, restated in the generated
`epsinv_enclosure_q{i}`:

> If `c.Valid` holds, take any real `A0 : Matrix (Fin n) (Fin n) ℝ` with
> `epsLo i j / 2^SE ≤ A0 i j ≤ epsHi i j / 2^SE` for all `i, j`. Then `A0` is
> invertible, and `outLo i j / 2^SO ≤ A0⁻¹ i j ≤ outHi i j / 2^SO` for all `i, j`.

How the data files relate to cert.py:

- `epsLo`, `epsHi` are cert.py's `eps.lo`, `eps.hi`. This is the unbalanced
  interval matrix built in `epsinv_iv`.
- `outLo`, `outHi` are the enclosure `inv` that `epsinv_iv` returns.
- Every float is written exactly, as an integer over one power of two per matrix.
- `f` holds the balancing exponents: cert.py's `s_i` equals `2^(f_i)` times one
  common factor, which cancels.

The proof reuses these theorems from `GW/Endpoint/CertInverse.lean`:
`inverse_cw_sound` (with m = 2, cert.py's `terms`), `det_balance` and
`inv_mem_of_balanced`.

- **The balancing is now exact in Lean.** `A' = balance s A0` never passes
  through a float. That removes the subnormal caveat on
  `eps * scale` / `invb * back`, which CertInverse lists as a named gap.
- **Nothing from iv.py is trusted.** The checker recomputes every sum exactly.
  The Python-computed quantities are only hints that the checker compares against.

## Trust boundary (what is still not proved)

1. **The eps interval itself is still Python's.** chi, v(q+G), the WFN
   arithmetic and `mtxel_iv` all remain in iv.py. Stage 1 removes trust only
   from `inverse_cw` and the balancing.
2. **Exporter correspondence.** `kernel_export.py` captures `eps`, `s`, `R` and
   `inv` from the live cert.py run:
   - it wraps `iv.inverse_cw` and reads the `epsinv_iv` frame locals;
   - it wraps `np.linalg.inv` to record the R that was actually used;
   - it converts floats to integers with `float.as_integer_ratio`, and asserts
     the conversion is exact.

   The claim "these Lean literals are cert.py's floats" is therefore a
   Python-side claim. It is checked by those assertions, not by Lean. R is
   only a certificate, so a wrong R could make the check fail but never make a
   false statement pass.
3. **The Sigma side does not use these theorems yet.** `SigmaIV` still consumes
   the Python interval `inv`. The Lean statement is about the same numbers,
   but there is no Lean link.

## Design (measured choices)

- **Checker** (`GW/Endpoint/Kernel/Check.lean`): the functions are
  `List.rec`-based (`axpy`, `zipW`, `comb`, `all2`, `sumL`) and marked
  `noncomputable`, because the code generator rejects `List.rec`. The kernel
  reduces them about 1.7x faster than equation-compiled recursion (synthetic
  32³ Nat matmul: 2.3 s vs 3.9 s).
- **Row checks** of the certificate:
  - `chkE`: `F ≥ |1 - R A'|` in mid-radius form,
    `2^K (|δ - X 2^f_j| + Y 2^f_j) ≤ F 2^S1`.
  - `chkMul`: `F·|R| ≤ T0 2^SR` and `F·T_k ≤ T_(k+1) 2^K`.
  - `chkRow`: the ℕ encodings, `|R|`, the row sums (≤ β, ρ), and the output
    enclosure against `[R-B, R+B]·s_i/s_j`.
- **Global check** `chkGlobal`: shapes, `colM`, `β < 1`, and the tail
  `β³ρ ≤ tail (2^K-β) 2^(2K)`.
- **All O(n³) work is ℕ multiply-adds.** The signed product `R·mid(A)` is
  formed as `(R + MR)·(mid + M)` in ℕ, with O(n) corrections. The reason is
  that Int arithmetic has no kernel GMP acceleration: the same synthetic
  matmul took 9.9 s in Int vs 3.9 s in Nat, and a first Int version of `chkE`
  was about 3.5x slower per multiply-add.
- **Hints** are at scale 2^-128. `kernel_export.py` computes them with exact
  Python integers, rounding up. The measured β values are 4.8e-12 (q0),
  8.9e-13 (q1) and 7.3e-13 (q2); cert.py reports 4.77e-12, 9.02e-13 and 7.45e-13.
- **One theorem per row and per check**, generated as `Data/Q{i}R{k}.lean`
  with 6 rows per module. The modules are chained by imports, so lake builds
  them one at a time. `Data/Q{i}Check.lean` collects them with
  `forall_lt_succ_of` and states the theorem.

## Measurements

- **Kernel speed.** End to end, about 1.1e4 ℕ multiply-adds per second on
  100–400-bit integers. For q2 that is 5n³ = 3.9M multiply-adds in about
  350 CPU-s, excluding data elaboration. Single checks at n = 92:
  - `chkE` row (2n² = 17k multiply-adds plus O(n)): about 2–3 s;
  - `chkMul` row (8.5k): about 0.3–0.5 s;
  - `chkRow`: about 0.2 s;
  - `chkGlobal`: about 7 s.
- **Memory.** Memory retained per declaration grows in one process, at about
  10 KB per multiply-add. Repeating an identical theorem 4 times grew it just
  as much, so this is not caching. One module holds at most about 300k
  multiply-adds at 3–4 GB. That is the reason for 6-row modules.
- **Data elaboration.** About 2.3k integer literals per second. For
  comparison, a single 76×76 list literal takes 27 s to parse, against 3 s when
  written one row per definition.

## Failed attempts / pitfalls (recorded for the next stage)

- **All rows in one declaration.** `rowsOK p 0 16`, or a 16-way `&&`, is
  superlinear in the kernel: 23–27 s for 16 rows, against 3.3 s as 16 separate
  theorems. One whole q in one file (all rows) took 216 s and **15.6 GB**.
- **`[a, b, …]` list literals.** They elaborate into nested `let`s, which the
  kernel re-instantiates every time the definition unfolds; row `i` got slower
  as `i` grew. The generator now writes `a :: b :: … :: []`, one definition
  per row.
- **Plain `-123` Int literals** parse about 4x slower than `(.negSucc 122)`.
- **Signed (Int) `comb` for E.** About 3.5x slower; replaced by the ℕ offset form.
- **`omega` inside the E proof.** With the big `all2` hypothesis in context it
  hit whnf timeouts. Explicit length rewrites are used instead.
- **Lean 4.19 `decide +kernel` runs on the elaboration thread.** There was no
  parallelism inside a file: user time ≈ wall time.

## Negative controls

`GW/Endpoint/Kernel/Tamper.lean` is part of the `GWKernelData` target and
built in 12 s. On a tampered q1 certificate the kernel proves each of these
checks evaluates to `false`:

- claimed lower end replaced by the upper end → `chkRow` false;
- `F := T2` (far too small) → `chkE` false;
- `F·T0 ≤ T2` → `chkMul` false;
- `tail := 0` → `chkGlobal` false;
- `epsLo := epsHi` with stale encodings → `chkRow` false.

## Commands

```
cd ../lean-g2 && source scripts/env.sh
# capture (runs cert.epsinv_iv on the 3 q-points, ~9 s) and generate the Lean data + proof modules
python3 bgw/endpoint/kernel_export.py RUNDIR --npz CAP.npz --lean
#   (RUNDIR used: <scratch>/fix/run)
nice lake build GW                   # default target incl. Check.lean + Sound.lean: PASS (227 s from a cold worktree, 6.7 GB peak)
lake env lean GW/Audit.lean          # new Kernel section: all [propext, Classical.choice, Quot.sound]
nice lake build GWKernelData         # slow: ~13 CPU-min, ≤3.6 GB per process, three chains
lake env lean GW/Endpoint/Kernel/AuditData.lean   # axioms of the three theorems
```

`--block N` in the exporter writes the leading N×N sub-block, with its own
inverse_cw enclosure, for scaling runs. No scaling runs were needed, because
the full matrices checked.

## Files

- New: `GW/Endpoint/Kernel/{Check,Sound,Tamper,AuditData}.lean`,
  `GW/Endpoint/Kernel/Data/Q{0,1,2}.lean` (data, 6.4 MB total),
  `Q{i}R{k}.lean` (row theorems) and `Q{i}Check.lean` (all generated),
  `bgw/endpoint/kernel_export.py`.
- Edited:
  - `GW.lean`: two import lines, for Check and Sound;
  - `GW/Audit.lean`: a new section at the end;
  - `lakefile.toml`: a new `GWKernelData` lean_lib. Existing targets are unchanged.

## Estimate: the full chain in the kernel

The chain is WFN coefficients → mtxel → chi → eps → eps⁻¹ → Sigma → O1. The
estimate assumes about 1.1e4 multiply-adds per second end to end and about
10 KB retained per multiply-add, so modules of ≤ 3e5 multiply-adds.

| stage | multiply-adds | interval factor | CPU time |
| --- | --- | --- | --- |
| mtxel convolutions | 3e7 | ×2 (mid-rad, or ×1 on exact point data) | 45–90 CPU-min, ~100–200 modules |
| chi outer products | 1.5e7 | ×2 | 25–45 CPU-min |
| eps⁻¹ (done) | — | — | 13 CPU-min |
| Sigma | ~1e6 per energy; ~10 energies over bands, k-points and the forward difference | — | ~15–30 CPU-min |

- **Data.** WFN coefficients as literals, at about 2.3k literals per second.
  1e5–1e6 coefficients would take 1–8 min.
- **Total.** About 2–3 CPU-hours. That is about 1 hour of wall time with 3–4
  parallel chains, which is what the 23 GB shared machine allows. This looks
  **feasible**. The limit is memory, not time.

Extra proof work beyond arithmetic volume:

- outward-rounded dyadic division and sqrt lemmas for:
  - `1/(Ev-Ec)`;
  - `8π/|q+G|²` (a π enclosure);
  - the GPP `sqrt` and poles;
- the `sexcut` and branch rules (CertSexcut already covers the logic);
- the mini-BZ Coulomb integrals (certcoulomb.py: Monte-Carlo-free enclosures
  would have to be redone in Lean);
- a Lean *definition* of chi/eps/Sigma matching BerkeleyGW's formulas. This is
  a modeling claim, separate from the arithmetic.

**Best design for scaling.** Keep this hint-and-check pattern with exact ℕ
fixed point. Put one row, or one (band, k) block, per theorem. Chain modules
by import to bound memory, and build independent chains in parallel. Hints do
not reduce the O(work) of products. They only remove division and rounding
from the kernel.

## Next action

- Review the soundness statement and the exporter capture method.
- If accepted, stage 2 would be:
  - make SigmaIV's input the Lean-checked `inv`, with a Lean statement
    connecting it;
  - move chi/eps (mtxel + chi) into the same checker, which needs exporting
    the WFN coefficients.
