# BGW-E2 handoff — convergence structure of O1 (in progress)

Written 2026-09-23 for a session change. Ready for continuation; nothing
accepted. Read first: `docs/ENDPOINT.md` (sections 1-3, "E1 result",
"E2 interim result"), `.agent/handoffs/BGW-E1.md`.

## Where things are

- Branch `bgw-e/endpoint`, worktree
  `<repo>/.claude/worktrees/bgw-e` (stacked on
  `bgw-m4/gpp-preflight`). E0 and E1 done (E1 exit SUCCESS, independently
  reviewed); E2 interim results committed; E3 not started.
- Data: `bgw/endpoint/data/e2_results.jsonl` (125 points; `host` =
  <node> for the remote ones). Failed points (multiplet-safe band window
  not found, etc.) in `e2_results.errors.jsonl` locally and on <node>.

## Still running at handoff (<node>, node-local, nice 10)

| run | started | expected |
| --- | --- | --- |
| `N8_nb150_ec25_ew11_eb25` | ~00:40 | 1-2 h more |
| `N6_nb300_ec25_ew20_eb25` (converged corner) | ~01:00 | 2-4 h more |

To collect when they finish (both append to jsonl files on <node>):

```
ssh <login> 'ssh <node> "cat /scratch/<user>/e2_callisto.jsonl /scratch/<user>/e2_callisto_corner.jsonl"' > /tmp/c.jsonl
python3 - <<'PY'
import json, pathlib
p = pathlib.Path("bgw/endpoint/data/e2_results.jsonl")
have = {json.loads(l)["id"] for l in p.read_text().splitlines() if l.strip()}
with p.open("a") as fh:
    for l in open("/tmp/c.jsonl"):
        if l.strip() and (r := json.loads(l))["id"] not in have:
            r["host"] = "<node>"; fh.write(json.dumps(r) + "\n")
PY
ssh <login> 'ssh <node> "pgrep -fa sigma.real.x"'   # empty = done
```

## Cluster facts (do not relearn the hard way)

- `hpcload` (on the login host) lists nodes and load. Local known_hosts lacks the
  other nodes: always hop via the login host (`ssh <login> 'ssh <node> ...'`).
- **Home quota is 10 GB soft / 12 GB hard and ~7.6 GB is used.** Put
  toolchains and runs on node-local `/scratch/<user>` (<node>: 1.7 TB).
  Home holds only the code copy `~/physics-lean-e2` (rsync from the worktree,
  excluding .lake/.tools/.git/artifacts).
- <node> has the pinned BerkeleyGW built by `bgw/toolchain/setup.sh
  /scratch/<user>/bgw-src` (sha256 of the archive and mtxel_cor.f90 match);
  use `BGW_TREE=/scratch/<user>/bgw-src/pristine/BerkeleyGW-4.0`. A pinned
  production run there reproduces the archived diagonal table byte-for-byte.
- Owner allowed 32 cores at nice 10 on shared nodes; <node> was idle.
- Local: `~/bgw-src` (pristine tree, micromamba env, python-flint venv
  `~/bgw-src/pyenv-e1`), runs in `~/bgw-e-runs/e2`.

## Commands

```
python3 bgw/endpoint/sweep.py OUTROOT --grid N.. --nb .. --ecuts .. [--ecutwfc ..] [--ecutb ..] --jobs J [--results F]
python3 bgw/endpoint/e2_analyze.py --N 2 --ecutwfc 11 --field O1 O1_noremainder dXL.CH
python3 bgw/endpoint/e2_layer1.py RUNDIR          # E1 reproducer vs production at a sweep point
BGW_TOOLCHAIN=$HOME/bgw-src/mm/envs/bgw bash scripts/verify.sh
```

Band counts are raised automatically to the first multiplet-safe window
(`nb_used`); EPM basis caps nb at ~0.97*162*(ecutwfc/11)^1.5.

## Remaining work, in order

1. Collect the two runs above; add them to the jsonl.
2. E2 gate item 5: one more layer-1 check at an N>2 point, e.g.
   `python3 bgw/endpoint/e2_layer1.py ~/bgw-e-runs/e2/N4_nb18_ec7_ew11_eb11`
   (N=4 has 64 q: expect ~10-20 min).
3. Write the E2 result (replace "E2 interim result" in docs/ENDPOINT.md):
   the empirical convergence estimate for O1 with method and assumptions.
4. E3 (gates in docs/ENDPOINT.md). Most important open falsification test:
   **the GPP invalid-mode convention** (`invalid_gpp_mode 0` = skip) flipped
   the sign of O1 at production settings (-5.2 meV). Re-test it, and the
   other layer-3 conventions from `data/mutations_e1.log`, at converged
   settings (e.g. N=2, ecutwfc 25, ~450 bands, ecuts 25; and N=4/N=6).
   Note sweep.py passes only the defaults; add a `--sigma-extra KEY=VALUE`
   option rather than editing inputs by hand, and note that
   spec.Run.check_preconditions deliberately rejects non-default GPP keys
   (the E1 reproducer does not cover them).
5. Record in `.agent/STATE.md`, commit, push; open a PR for
   `bgw-e/endpoint` only if the owner wants one (merges need a decision).

## Preliminary reading (not a verdict)

C1 (O1 > 0) has held at every ecuts-converged point (min +7.8 meV) and is
certified at layer 1 (5 µeV). The production value +15.4 meV has the right
sign for partly wrong reasons (nb/ecuts error cancellation, and a static
remainder that is +117 meV of it). The converged magnitude is uncertain,
roughly 20-45 meV depending on k-grid and band extrapolation. Layer 3
(GPP conventions) is untested at converged settings and could still flip C1.
