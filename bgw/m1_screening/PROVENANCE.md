# BGW-M1 — provenance of the matched-input screening comparison — ARCHIVED (2026-10-01): BGW-M1/M2 lineage, superseded by the kernel-checked eps^-1 certificates (GW.Endpoint.Kernel, Data.Q*Check/E*Check); kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Supports `GW/BGW/M1Screening.lean` and `tests/test_bgw_m1.py`. Nothing here is a
proof; the kernel-checked claim is the Lean module. Revised in BGW-M1-R1 after
the BGW-M1 review found this packet incomplete and its patch command broken.

## The production event, identified unambiguously

| Item | Value |
| --- | --- |
| Code | BerkeleyGW 4.0, `Epsilon/epsinv.f90`, static (`pol%freq_dep == 0`), serial, real flavor |
| Pristine `epsinv.f90` SHA-256 | `cb7c9fb326df1b437c0a043305789e60f793148233ed516420669d8e946998e1` |
| Instrumentation patch SHA-256 | `046456cc941bc3bcbc00f5dd2304aaa2d26aa8c1a7a41fe439a862d2314cd77d` |
| `arch.mk` SHA-256 | `3d096ebde2b50b3dced767cc4ac605ac9ca410e1e4bbc0766551fca768327411` |
| Compiler | `/tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-gfortran`, `-O2`, OpenBLAS 0.3.34 |
| Built executable SHA-256 | `de13f3045c3426035c97c79720939ecdc892a76159be51d74df990c71d640a96` |
| Flavor selection | `cp flavor_real.mk flavor.mk` (`TYPEFLAG` empty), then `make clean` |
| `WFN` SHA-256 | `f85a1534fe70a5a1b966fdbc1c6f0fc1d8acab2f08215b39ef0f04ff9bfce37d` |
| `WFNq` SHA-256 | `1138228a81c562bbfd88693072446443a259f4676f095d9afe15bb86f3e6c8ca` |
| `epsilon.inp` SHA-256 | `e7f5b9ae68996a6fdf5c63e85c27a2eebb8194c8670c3ff268c47388583d51ee` |
| Selected q | index **2**, `q = (0.000000, 0.000000, 0.500000)`, regular non-zero |
| Retained basis | complete, `nmtx = 8` |
| Run log SHA-256 | `f6ed5c8a61a08f4b4b58373af1c838c991e3a724a22d72ac7f31b6e3088c8d23` |

The exact `epsilon.inp` used (the archived `bgw/export/epsilon.inp`, SHA-256
`b5b1a11a…`, with **only** `epsilon_cutoff` changed):

```
epsilon_cutoff 1.5

number_bands 18

begin qpoints
  0.000000000  0.000000000  0.001000000   1.0 1
  0.000000000  0.000000000  0.500000000   1.0 0
  0.000000000  0.500000000  0.500000000   1.0 0
end
```

**`epsilon_cutoff 1.5` Ry is deliberately small so that one complete retained
basis is certifiable. The run is unconverged for material properties.**

### Locations of the large inputs

Not committed, and a location is not permission to redistribute:

* BerkeleyGW 4.0 pristine tree: `/tmp/bgw/BerkeleyGW-4.0` (159 MB)
* instrumented tree: `/tmp/bgw/m1-eps-instr` (regenerable; see below)
* `WFN`/`WFNq`: `artifacts/t002-codex-final/pristine/` in this repository's
  working tree (`artifacts/` is gitignored), hashes above
* fresh reproduction run: `/tmp/bgw/m1run-1.5-repro`

These `/tmp` paths are **not durable provenance**. What is durable is the hash
set above plus the committed slices; anything else must be rebuilt from the
recorded commands. Retention beyond this session was not checked and is not
claimed.

## Committed evidence

| File | SHA-256 |
| --- | --- |
| `data/m1_eps_dump_q2.txt` | `047557fe024854e137c7ec86b046726d11c1d56b8749e1d263f73108dbb6e393` |
| `data/m1_gvec_q2.txt` | `5060298f692adea87acba7f846a64695c322377b1079cfb858cc82a6dac3a320` |
| `data/epsilon_out_excerpt.txt` | `ab5f973ca51bd6575f99e43a9530311dd659e227965deb881bd3fbb243699881` |

`tests/test_bgw_m1.py::SnapshotIsPinned` pins the first two to these constants,
so a replaced snapshot fails instead of redefining what is correct.

## Ordered retained basis

From `data/m1_gvec_q2.txt`. `pol%isrtx` holds the sort indices for
`|q0 + gvec%components|^2` (source comment near line 142), so row `i` of `E`
corresponds to `gvec%components(:, pol%isrtx(i))`. Components are integer
reciprocal-lattice coordinates; the last column is `ekin = |q0+G|^2` in Ry.

| row | G (crystal) | `ekin` (Ry) |
| --- | --- | --- |
| 1 | `( 0,  0, -1)` | `0.281206072713701` |
| 2 | `( 0,  0,  0)` | `0.281206072713701` |
| 3 | `(-1, -1, -1)` | `1.031088933283572` |
| 4 | `(-1,  0, -1)` | `1.031088933283572` |
| 5 | `( 0, -1, -1)` | `1.031088933283572` |
| 6 | `( 0,  1,  0)` | `1.031088933283572` |
| 7 | `( 1,  0,  0)` | `1.031088933283572` |
| 8 | `( 1,  1,  0)` | `1.031088933283572` |

Two distinct `|q0+G|^2` shells, which is exactly why `vcoul` takes two distinct
values and therefore why **`E` is not symmetric**. A transpose or one-sided
permutation mistake is a genuine error on this input.

## Convention, read from the pinned source

`Epsilon/epsinv.f90`, static branch:

```fortran
eps(irowm,icolm) = ZERO
if (i.eq.j) eps(irowm,icolm) = ONE
chitmp = pol%chi(irowm,icolm,1)
eps(irowm,icolm) = eps(irowm,icolm) - vc*chitmp      ! vc = vcoul(i)
```

**`E = I - V*chi`**, `V` diagonal on the **row** index, unsymmetrized. The file
header says "2. Inverts epsilon. 3. Writes the result", and inversion is in
place, so **`epsmat` stores the inverse**. Read from source, not inferred from a
filename. `We are using no truncation` was active, so there is no
Coulomb-truncation convention to reconcile.

## Input boundary

The **permitted narrower boundary**: the actual **pre-inversion `E`** and the
Coulomb diagonal `V` exported from the run, plus the run's post-inversion
result. Formation of `E` from `chi` is an **input** and is NOT verified. `E` is
dumped from the live `eps` array immediately before `X(invert_serial)`; it was
**not** obtained by inverting the output under test.

## Reproduction

```bash
# 1. instrument a pristine copy (validated against the hash above)
cp -a /tmp/bgw/BerkeleyGW-4.0 /tmp/bgw/m1-eps-instr
PATCH=$PWD/bgw/m1_screening/epsinv_dump.patch          # absolute: we cd below
cd /tmp/bgw/m1-eps-instr && patch -p1 < "$PATCH"

# 2. build the REAL flavor from clean (stale .mod files from a complex build
#    otherwise fail with "Type mismatch ... REAL(8) to COMPLEX(8)")
cp flavor_real.mk flavor.mk && make clean && make -j8 epsilon

# 3. run in a FRESH directory -- the dump is opened in append mode, so reusing
#    a directory accumulates blocks from several runs
mkdir -p /tmp/bgw/m1run-1.5-repro && cd /tmp/bgw/m1run-1.5-repro
ln -s <archived>/WFN WFN; ln -s <archived>/WFNq WFNq
cp <epsilon.inp above> epsilon.inp
/tmp/bgw/m1-eps-instr/Epsilon/epsilon.real.x > epsilon.out

# 4. check the regenerated certificate against the committed snapshot
python3 bgw/m1_screening/regenerate_certificate.py --check
```

The patch now carries relative `a/`/`b/` headers and applies with `-p1` from a
copied source root; this was validated by applying it to a hash-checked pristine
copy and comparing the result byte-for-byte with the instrumented tree. The
previous version had absolute headers and did **not** work with the documented
command.

**Verified determinism:** step 3 in a fresh directory reproduced
`data/m1_eps_dump_q2.txt` **byte-identically** (same SHA-256). The `GVEC` records
are written to a separate file precisely so this snapshot stays unchanged.

## Independent validation of the export

The run's log prints, from code paths this patch does not touch:

```
 q-pt      2: Head of Epsilon         =    3.104320810754696E+000
 q-pt      2: Head of Epsilon Inverse =    3.448293583556872E-001
 q-pt      2: Epsilon Inverse(2,2)    =    3.448293583556872E-001
```

Dumped `EPSINV(1,1)`/`EPSINV(2,2)` equal the printed inverse values exactly.
Dumped `EPSPRE(1,1) = 3.1043208107546962` agrees with the printed epsilon to the
16 significant digits that format carries — the log is the correctly rounded
form of the dumped double, which is print precision, not a discrepancy.

**This is a print statement inside the instrumented run, not a separate
uninstrumented execution.** It shows the dump agrees with what the surrounding
un-patched code reports; it does not by itself establish that the instrumented
and pristine executables agree. No separate pristine run at this cutoff was
performed.

`extract.py` re-checks the decimal/bits round trip for every entry and rejects a
broken round trip, an in-block duplicate, a missing or out-of-range label, a
repeated q, a nested or unterminated block, a mismatched block end, and data
outside a block.

## Interpretation

The rationals are the exact values **of the stored doubles**. Not the unrounded
physical dielectric matrix; forming `E` exactly from rounded `chi` and `vcoul`
would give a different matrix `E*`, and this milestone certifies the inverse of
the stored `E`, not of `E*`.

## Numerical criteria

Input-dependent **engineering** rules, fixed from export precision, dimension and
measured input conditioning. Neither is a universal proved LAPACK forward-error
bound; the proved statements here are the Lean theorems.

* `forward_rel_inf <= 100 * n * kappa_inf(E) * 2^-53`
* `normalized_residual <= 100 * n * 2^-53`

Measured `kappa_inf(E) = 3.8461483735980266`, so the limits are `3.416065984394502e-13`
and `8.881784197001252e-14`.

**Predeclaration caveat.** These rules were written before the comparison was run
in this session, but version history alone cannot establish that ordering to a
third party, and no contemporaneous external record exists. The rules are
unchanged by BGW-M1-R1 and were frozen before the reproduction above.

## Result

| Metric | Measured | Limit | |
| --- | --- | --- | --- |
| relative forward error, inf-norm | `1.7112154669742808e-16` | `3.416065984394502e-13` | pass |
| normalized residual (max-entry) | `8.757690843317078e-17` | `8.881784197001252e-14` | pass |
| entrywise max abs difference | `9.627035010723234e-17` | reported | |
| normalized residual (inf-norm) | `7.008168410280357e-17` | reported | |

The max-entry residual is the original criterion and is retained unchanged. The
inf-norm residual `||EX-I||_inf / (||E||_inf ||X||_inf)` is reported alongside;
the review computed `5.5620368e-17` for an inf-norm variant, which differs from
this value by normalization choice, not by conclusion.

Convention mutations, each injected into the checked path with the reference
recomputed for the mutated input, each rejected by the same criterion the
unmodified control passes:

| Mutation | relative forward error |
| --- | --- |
| Coulomb prefactor doubled | `3.156e-01` |
| one side transposed | `1.923e-01` |
| one-sided row permutation | `7.153e-01` |
| sign of `V*chi` flipped | `9.471e-01` |

## What is NOT established

The IO parser, the floating-point implementation, agreement between the
instrumented and pristine executables, the origin of `chi`, the formation of
`E`, physical or convergence accuracy, the frequency convolution, and
self-consistency. One screening/inversion stage, for one represented input.
