#!/usr/bin/env python3
"""Re-hash every path a provenance manifest already lists, in place.

WHY THIS EXISTS. The rule was "generate the manifest strictly last". That rule
failed seven times in this project, and the seventh time was exactly circular:
the edit that went stale was a handoff note *documenting* the staleness
problem. The rule cannot work, because rolling a manifest to a new revision is
itself an edit to files the manifest covers, and writing up the pass is an edit
to a file the manifest covers. There is no ordering that fixes that.

So manifest generation is no longer a one-shot act performed at the right
moment. It is an IDEMPOTENT step you re-run after any edit, as many times as
you like, until the tree stops changing:

    python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt

It only refreshes digests for paths the manifest ALREADY lists. It never adds
or removes an entry, so it cannot silently start vouching for something new --
deciding what a manifest covers stays a human act. A listed path that has
disappeared is reported and left untouched rather than dropped.
"""

import hashlib
import pathlib
import re
import sys

#: MULTILINE is load-bearing: without it `^`/`$` anchor to the whole
#: string, nothing matches, and this script reports success having
#: refreshed nothing -- a silent pass, which is the exact failure mode
#: it exists to prevent. The self-check below would catch a regression.
DIGEST = re.compile(r"^([0-9a-f]{64})  (.+)$", re.M)


def refresh(manifest_path):
    manifest = pathlib.Path(manifest_path)
    text = manifest.read_text()
    changed, missing = [], []

    def fix(match):
        old, rel = match.group(1), match.group(2)
        target = pathlib.Path(rel)
        if not target.exists():
            missing.append(rel)
            return match.group(0)
        new = hashlib.sha256(target.read_bytes()).hexdigest()
        if new != old:
            changed.append(rel)
        return f"{new}  {rel}"

    updated = DIGEST.sub(fix, text)
    if updated != text:
        manifest.write_text(updated)
    return changed, missing


def main(argv):
    if len(argv) != 2:
        print(__doc__)
        return 2
    entries = len(DIGEST.findall(pathlib.Path(argv[1]).read_text()))
    if not entries:
        print(f"FAIL: no digest lines matched in {argv[1]}; refusing to report "
              f"success having done nothing", file=sys.stderr)
        return 2
    changed, missing = refresh(argv[1])
    for rel in changed:
        print(f"refreshed  {rel}")
    for rel in missing:
        print(f"MISSING    {rel}", file=sys.stderr)
    print(f"{len(changed)} refreshed, {len(missing)} missing, "
          f"{entries} entries scanned")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
