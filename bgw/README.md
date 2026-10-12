# `bgw/` --- BerkeleyGW 4.0 correspondence evidence — ARCHIVED (2026-10-01): for the T-001..T-005 files it describes; T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Everything here supports `docs/BERKELEYGW_4.0_GPP.md`, which is the document to
read first. Nothing here is a proof; the kernel-checked claims live in
`GW/GPP/BerkeleyGWMap.lean`.

| Path | What it is |
| --- | --- |
| `kernel_transcript.f90` | restricted standalone transcription for positive real modes. **Not BerkeleyGW or a compiler proof.** |
| `oracle.py` | exact-rational check of `kernel_transcript` output against the S1 closed forms |
| `verify_export.py` | exact-rational check of records exported from a real BerkeleyGW run |
| `reproduce.py` | fresh EPM/epsilon/sigma runs using two already-built trees and 24 upstream assertions each |
| `export/` | the exported records, the instrumentation patch, build and input provenance, and `SHA256SUMS` |

## Reproducing the transcript check

Needs only a Fortran compiler and Python 3.

```bash
gfortran -O2 -o /tmp/kt bgw/kernel_transcript.f90
/tmp/kt > /tmp/kt.out
python3 bgw/oracle.py /tmp/kt.out
```

## Reproducing the export check

Needs nothing but Python 3; the records are included in the workspace.

```bash
python3 bgw/verify_export.py bgw/export/gpp_kernel_dump.dat
python3 bgw/verify_export.py bgw/export/gpp_nearpole_dump.dat
python3 bgw/verify_export.py --all
```

## Reproducing the run

Needs two already-built BerkeleyGW 4.0 trees (pristine and instrumented) and a
fresh output directory:

```bash
python3 bgw/reproduce.py --pristine /path/to/pristine-tree \
  --instrumented /path/to/instrumented-tree --output /path/to/new-run
```

Do not pin BLAS threads for a comparison against the saved evidence. With
`--blas-threads 1` the EPM diagonalization picks a different eigenvector basis
inside the degenerate subspaces; the 24 upstream assertions and the diagonal
quasiparticle table still hold, but the symmetrized off-diagonal block of
`sigma_hp.log` and the exported kernel inputs (at `<= 2.5e-12` relative) no
longer match byte-for-byte. `report.json` is written in both cases and records
the differing lines and per-column deviations. See
`docs/BERKELEYGW_4.0_GPP.md` section 7.8.

## Regenerating the export itself

This needs a BerkeleyGW 4.0 source tree and a Fortran toolchain, and is
described in `docs/BERKELEYGW_4.0_GPP.md` section 7.7. Historical absolute paths
in `export/arch.mk` must be adapted in new trees; compiler packages are not
locked. The tarball
is identified by SHA-256
`1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49`; do not
substitute a different revision without updating that document.

## Integrity

`export/SHA256SUMS` covers every other file in `export/`. Check with:

```bash
cd bgw/export && sha256sum -c SHA256SUMS
```
