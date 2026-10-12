# Wakeup and Resume Protocol

This file is readable by Claude and Codex. It does not schedule either agent.
The initial demo uses one foreground bounded Claude job followed by Codex review.

## Feature freeze (since 2026-10-01)

The owner froze the project on 2026-10-01: no new scientific work (no new physics
theorems, certificates, measurements or runs). Only documentation, tooling, gates,
registries and verified defect repairs that change no claim are allowed. Only the
owner can lift the freeze, by a recorded decision; see `.agent/STATE.md`. On restart,
do not dispatch scientific work, including the open decisions listed in STATE.md.
Scoped lift (owner, 2026-10-02): the REVIEW-28 corrections F1–F4 only
(`.agent/tasks/R28-*.md`); nothing else is unfrozen.

## Every Restart

1. Read `AGENTS.md`, `.agent/STATE.md`, `docs/CODEMAP.md`, `docs/ENDPOINT.md` /
   `docs/BRIDGE.md`, the active task, and its handoff (`Specification.md` is the
   archived demo contract). Inspect current files and recent verification artifacts.
2. Check `.agent/runs/worker.lock` with the dispatcher, which uses an OS lock.
   A lock file's existence alone does not mean a worker is running.
3. Do not start a second writer while the first holds the lock. If active,
   inspect progress without editing its files. Do not kill it for inactivity
   alone and do not redispatch a running job.
4. If a worker exited, inspect `result.json`, `stderr.log`, and `run.json` in its
   run directory. A zero exit or a worker claim is not acceptance.
5. Rerun the relevant checks and review the source, hypotheses, and trust
   boundaries. Record accepted work or a specific repair task in state/handoff.
6. On repeated identical blockers, stop automatic retries and record the exact
   missing input. Do not change physics assumptions to manufacture progress.

## Proposed Future Scheduler

Prefer one Codex supervisor wakeup every 30 minutes while an explicitly active
milestone exists. Claude runs only when dispatched for a bounded job. Both read
the same state; two independent writer schedules would create duplicate work.
This interval is a proposal, not an installed timer or a user-fixed requirement.

Use the host's supported automation management interface when available. Do not
write internal app databases, invent automation files, or install cron jobs as a
substitute. No such interface was exposed during initial setup.

Suggested saved prompt for a future supervisor automation:

```text
Work in <repo>. Read AGENTS.md and .agent/WAKEUP.md,
then .agent/STATE.md and the active task/handoff. Inspect current source and
worker status. Continue only the explicitly active, authorized milestone.
Never overlap writers, weaken the mathematical contract, or auto-expand scope.
Verify worker results before accepting them. Stay quiet when nothing changed
or no action is possible. Notify only on a meaningful milestone, completed
review, failure, or specific need for user input. Stop dispatching once the
active milestone is accepted or paused. A backlog item alone is not an active
assignment. Do not create a new recurring automation from this automation.
```

## Current Scheduling State

Not installed. A later owner must record the actual automation ID, host,
schedule, active/paused status, and a successful readback before changing this
statement. Reading this file is never evidence of future wakeups.
