# BGW-E0/E1 — pin the observable; certified layer-1 bound on it

Assigned 2026-09-22 by the owner in session (continuous run, E0/E1 first).
Plan, gates and exit conditions: `docs/ENDPOINT.md` section 3. That section is
the contract; this file only fixes scope.

Write scope: `bgw/endpoint/`, `tests/test_endpoint_*.py`, `GW/Endpoint/`
(Lean soundness of the enclosure arithmetic), `docs/ENDPOINT.md`,
`scripts/gates.py` (registration), `bgw/toolchain/setup.sh` (EPM build),
`.agent/handoffs/BGW-E1.md`, `.agent/STATE.md` (ledger line).

Not in scope: layer 2/3 claims; merges; upstream contact; per-record Lean
certificates of the M1–M5 kind.

Checkpoint = commit + push of `bgw-e/endpoint` at each E1.x gate. Completion
means ready for review, not accepted.
