#!/usr/bin/env python3
"""WORKFLOW GATE: every file a provenance manifest vouches for must be in the repository.

Review finding 6: four files listed in the two manifests were matched by
`.gitignore` and absent from the commits, so a fresh checkout received
16/18 and 23/25 of the vouched files. The normal gate did not notice, because
the manifests were only ever checked against the working tree.

Absolute paths (build trees under /tmp) are deliberately out of scope: they
document a disposable environment and are not expected in the repository.
"""

import pathlib
import re
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
#: Every manifest, historical and current. All of them must vouch only for
#: files that are actually in the repository.
MANIFESTS = [
    ROOT / "bgw" / "occupation_audit" / "PROVENANCE.txt",
    ROOT / "bgw" / "occupation_audit" / "PROVENANCE-R1.txt",
    ROOT / "bgw" / "occupation_audit" / "PROVENANCE-R2.txt",
    ROOT / "bgw" / "occupation_audit" / "PROVENANCE-R3.txt",
    ROOT / "bgw" / "occupation_audit" / "PROVENANCE-R4.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R1.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R2.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R3.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R4.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R5.txt",
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R6.txt",
]

#: Only the newest revision of each manifest is expected to match the files as
#: they stand now. The earlier ones are deliberately stale: T-003-R1 item 6
#: required recording repaired digests as a new revision rather than rewriting
#: history, so PROVENANCE.txt still carries the pre-repair digests of
#: check_occupation.py and REPORT.md, and that is correct.
#: Exactly ONE manifest is current, and it is a **cross-audit** manifest:
#: it vouches for every file changed in the latest pass, whichever audit the
#: file belongs to. `bgw/occupation_audit/PROVENANCE-R4.txt` is therefore the
#: prior *occupation* revision, not a current manifest, and is expected to be
#: stale, as are the superseded weighted `PROVENANCE-R3.txt` and
#: `PROVENANCE-R4.txt` and `PROVENANCE-R5.txt`.
CURRENT_MANIFESTS = [
    ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R6.txt",
]

#: Mutable owner-controlled files are deliberately NOT vouched for by the
#: current manifest: Codex edits and signs them after validation, which would
#: make any recorded digest stale by design. PROVENANCE-R2.txt hashed them once
#: and that stands as historical. Git still tracks both.
#: Files vouched for by a HISTORICAL manifest and deleted since, with the commit
#: that deleted them. Recorded so the test also passes in a checkout without the
#: development history (the public snapshot); where history is present,
#: `test_recorded_deletions_match_history` confirms each entry against it.
RECORDED_DELETIONS = {
    "tests/test_review_packet.py": "83700b5d5de70a34b30de3cd04b704b1e4103108",
}

OWNER_CONTROLLED = (
    ".agent/STATE.md",
    ".agent/handoffs/CODEX-T-003-T-004-ACCEPTANCE.md",
)
DIGEST = re.compile(r"^([0-9a-f]{64})  (.+)$")


def tracked_files():
    out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout
    return set(out.split("\0")) - {""}


class ProvenanceCommittedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            cls.tracked = tracked_files()
        except Exception as exc:            # not a git checkout
            raise unittest.SkipTest(f"git not available: {exc}")

    def test_manifests_exist(self):
        for m in MANIFESTS:
            self.assertTrue(m.exists(), m)

    def test_current_manifest_is_itself_listed(self):
        """Guard: a current manifest absent from MANIFESTS is never scanned."""
        for m in CURRENT_MANIFESTS:
            self.assertIn(m, MANIFESTS,
                          f"{m.name} is current but not in MANIFESTS, so its "
                          f"vouched files are never checked for tracking")

    def test_every_repo_relative_vouched_file_is_tracked(self):
        missing = []
        checked = 0
        for m in MANIFESTS:
            for line in m.read_text().splitlines():
                hit = DIGEST.match(line)
                if not hit:
                    continue
                path = hit.group(2)
                if path.startswith("/"):
                    continue            # disposable build tree, out of scope
                checked += 1
                if path in self.tracked:
                    continue
                # A HISTORICAL manifest may legitimately vouch for a file that
                # has since been deleted: it is recording what its own tree
                # looked like, which is the point of keeping it. The defect
                # this test exists to catch is different and narrower -- a file
                # vouched for but NEVER committed, so no reviewer can ever
                # obtain it. Git can tell the two apart.
                if path in RECORDED_DELETIONS or self._known_to_git_history(path):
                    continue
                missing.append(f"{path} (vouched by {m.name})")
        self.assertGreater(checked, 40, "manifests look empty")
        self.assertEqual(missing, [], f"vouched but untracked: {missing}")


    def test_recorded_deletions_match_history(self):
        """Each recorded deletion is a commit that deleted the path, which is absent now."""
        for path, sha in RECORDED_DELETIONS.items():
            self.assertNotIn(path, self.tracked, path)
            known = subprocess.run(["git", "cat-file", "-e", f"{sha}^{{commit}}"], cwd=ROOT,
                                   capture_output=True).returncode == 0
            if not known:
                continue    # no development history in this checkout (public snapshot)
            deleted = subprocess.run(
                ["git", "diff-tree", "--no-commit-id", "--name-only", "-r",
                 "--diff-filter=D", sha], cwd=ROOT, capture_output=True, text=True,
                check=True).stdout.split()
            self.assertIn(path, deleted, f"{sha} does not delete {path}")

    @staticmethod
    def _known_to_git_history(path):
        """True if this path exists in any commit, even if deleted since."""
        found = subprocess.run(
            ["git", "rev-list", "--all", "--max-count=1", "--", path],
            cwd=ROOT, capture_output=True, text=True)
        return bool(found.stdout.strip())

    def test_current_manifests_match_the_files_as_they_stand(self):
        """Only the newest revision of each manifest, by design.

        Historical manifests MUST disagree with the current files; that is what
        preserving the correction history means. Asserting currency on them
        would be wrong, not a stricter check.
        """
        import hashlib
        bad = []
        for m in CURRENT_MANIFESTS:
            for line in m.read_text().splitlines():
                hit = DIGEST.match(line)
                if not hit or hit.group(2).startswith("/"):
                    continue
                p = ROOT / hit.group(2)
                if not p.exists():
                    bad.append(f"{hit.group(2)}: absent")
                    continue
                got = hashlib.sha256(p.read_bytes()).hexdigest()
                if got != hit.group(1):
                    bad.append(f"{hit.group(2)}: {got[:12]} != {hit.group(1)[:12]}")
        self.assertEqual(bad, [], f"digest mismatches: {bad}")

    def test_current_manifest_excludes_owner_controlled_files(self):
        """Codex edits these after validation; vouching for them guarantees
        a stale digest. They stay tracked by git, just not hashed here."""
        for m in CURRENT_MANIFESTS:
            # Only the digest lines count as vouching. The manifest's prose
            # deliberately NAMES these files to explain why they are excluded.
            vouched = {hit.group(2) for hit in
                       (DIGEST.match(line) for line in m.read_text().splitlines())
                       if hit}
            for owned in OWNER_CONTROLLED:
                self.assertNotIn(owned, vouched,
                                 f"{m.name} vouches for owner-controlled {owned}")
        for owned in OWNER_CONTROLLED:
            self.assertIn(owned, self.tracked, f"{owned} is not tracked by git")

    def test_historical_manifests_are_not_required_to_be_current(self):
        """Guard the guard: at least one historical digest IS stale."""
        import hashlib
        stale = 0
        for m in MANIFESTS:
            if m in CURRENT_MANIFESTS:
                continue
            for line in m.read_text().splitlines():
                hit = DIGEST.match(line)
                if not hit or hit.group(2).startswith("/"):
                    continue
                p = ROOT / hit.group(2)
                if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest() != hit.group(1):
                    stale += 1
        self.assertGreater(stale, 0,
                           "no historical digest is stale; either history was "
                           "rewritten or CURRENT_MANIFESTS is wrong")


if __name__ == "__main__":
    unittest.main(verbosity=2)
