#!/usr/bin/env python3
"""Run one bounded Claude job; repository files carry all durable context."""

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import uuid


ROOT = Path(__file__).resolve().parents[1]
RUNS = ROOT / ".agent" / "runs"


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, data):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def stop_group(process):
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task", nargs="?", default="T-001")
    parser.add_argument("--run", action="store_true", help="dispatch; otherwise print the command")
    parser.add_argument("--status", action="store_true", help="inspect the worker lock")
    parser.add_argument("--timeout", type=int, default=1800, help="job timeout in seconds")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    RUNS.mkdir(parents=True, exist_ok=True)
    with (RUNS / "worker.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("worker active; no duplicate dispatch")
            return 0 if args.status else 75
        if args.status:
            print("worker idle")
            return 0
        task = ROOT / ".agent" / "tasks" / f"{args.task}.md"
        if task.resolve().parent != (ROOT / ".agent" / "tasks").resolve() or not task.is_file():
            parser.error("task must name an existing file directly in .agent/tasks")
        claude = shutil.which("claude")
        if claude is None:
            parser.error("claude CLI is not installed")
        prompt = (
            f"Implement the bounded job in .agent/tasks/{args.task}.md. "
            "First read AGENTS.md, CLAUDE.md, Specification.md, .agent/STATE.md, "
            ".agent/WAKEUP.md, and the task and existing handoff. "
            "Respect the task's file ownership. The supervisor handles dependencies. "
            "Run Lean checks and write the required handoff before returning. "
            "No nested agents or schedulers."
        )
        command = [
            claude, "--safe-mode", "-p", prompt,
            "--output-format", "json", "--permission-mode", "acceptEdits",
            "--permission-prompts", "none", "--strict-mcp-config",
            "--mcp-config", '{"mcpServers":{}}',
            "--tools", "Read,Edit,Write,Glob,Grep,Bash",
            "--allowedTools", "Bash(lake *)", "Bash(python3 bgw/*)",
            "Bash(python3 -m unittest *)", "Bash(bash scripts/verify.sh)",
        ]
        if not args.run:
            print(shlex.join(command))
            return 0
        run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
        run_dir = RUNS / run_id
        run_dir.mkdir()
        metadata = {
            "task": args.task, "started_at": now(), "status": "running",
            "task_sha256": hashlib.sha256(task.read_bytes()).hexdigest(),
            "command": command, "timeout_seconds": args.timeout,
        }
        save(run_dir / "run.json", metadata)
        environment = os.environ.copy()
        environment["ELAN_HOME"] = str(ROOT / ".tools" / "elan")
        environment["PATH"] = environment["ELAN_HOME"] + "/bin:" + environment.get("PATH", "")
        print(f"Claude run: {run_dir}", flush=True)
        process = None
        try:
            with (run_dir / "result.json").open("w") as out, (run_dir / "stderr.log").open("w") as err:
                process = subprocess.Popen(
                    command, cwd=ROOT, env=environment, stdout=out, stderr=err,
                    start_new_session=True, pass_fds=(lock.fileno(),),
                )
                metadata["pid"] = process.pid
                save(run_dir / "run.json", metadata)
                try:
                    returncode = process.wait(timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    stop_group(process)
                    metadata["status"] = "timed_out"
                    returncode = 124
                except KeyboardInterrupt:
                    stop_group(process)
                    metadata["status"] = "interrupted"
                    returncode = 130
        except OSError as error:
            metadata.update(status="launch_failed", error=str(error))
            returncode = 1
        finally:
            if process is not None:
                stop_group(process)
        if metadata["status"] == "running":
            try:
                result = json.loads((run_dir / "result.json").read_text())
                metadata["session_id"] = result.get("session_id")
                failed = result.get("is_error", False) or bool(result.get("permission_denials"))
                metadata["status"] = "needs_review" if returncode == 0 and not failed else "failed"
                if failed and returncode == 0:
                    returncode = 1
            except (ValueError, OSError, AttributeError):
                metadata["status"] = "invalid_result"
                returncode = returncode or 1
        metadata.update(finished_at=now(), exit_code=returncode)
        save(run_dir / "run.json", metadata)
        print(f"Claude {metadata['status']}; exit={returncode}; logs={run_dir}")
        return returncode


if __name__ == "__main__":
    sys.exit(main())
