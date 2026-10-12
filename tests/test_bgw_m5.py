"""BGW-M5: one production GPP self-energy mode connected to the GPP core.

Committed data only: the checker accepts the real export and rejects targeted
corruptions; the Lean module is exactly what the data generates; the mutation
evidence is bound to the current certificate.
"""
import functools
import hashlib
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
M5 = ROOT / "bgw" / "m5_sigma"
sys.path.insert(0, str(M5))
import sigma_mode  # noqa: E402
import make_lean_m5  # noqa: E402

DUMP_SHA256 = "b9f8da77e1f82073defd2fdac8b291aa5a1e571be244411fceb89b384e3cb376"


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


@functools.lru_cache(maxsize=None)
def lines():
    return tuple(sigma_mode.read_lines())


@functools.lru_cache(maxsize=None)
def result():
    return sigma_mode.run(list(lines()))


def target_start():
    return next(i for i, l in enumerate(lines()) if l.startswith("GPP 1913 "))


def edit_first(prefix, k, fn, after=0):
    out, done = [], False
    for n, line in enumerate(lines()):
        if not done and n > after and line.startswith(prefix):
            t = line.split()
            t[k] = str(fn(int(t[k])))
            line, done = " ".join(t), True
        out.append(line)
    assert done, prefix
    return out


class Mode(unittest.TestCase):
    def test_dump_identity(self):
        self.assertEqual(sha256(sigma_mode.DUMP), DUMP_SHA256)

    def test_selection(self):
        r = result()
        self.assertEqual((r["records"], r["all_records"]), (8, 1824))
        self.assertEqual((r["sel"]["n1true"], r["sel"]["iw"]), (1, 2))

    def test_budget_model_fixed(self):
        self.assertEqual((sigma_mode.SQRT_SLACK, sigma_mode.N_LOC, sigma_mode.N_SCH_D,
                          sigma_mode.N_SSX_D), (2, 8, 2, 4))

    def test_ssx_reference_is_rational_occupied_sx(self):
        c = result()["cert"]
        self.assertEqual(c["ssx_star"], c["o_star"] / (c["x_star"] ** 2 - c["p_star"]))
        self.assertLess(abs(c["ssx_hat"] - c["ssx_star"]), 1e-12)


class Rejects(unittest.TestCase):
    def rejects(self, text, needle):
        with self.assertRaises((sigma_mode.M5Error, sigma_mode.bridge.BridgeError)) as cm:
            sigma_mode.run(text)
        self.assertIn(needle, str(cm.exception))

    def test_kernel_pole_not_setup_pole(self):
        self.rejects(edit_first("SGP ", 12, lambda b: b + 1, target_start()), "not the setup's pole")

    def test_other_call(self):
        self.rejects(edit_first("SGP ", 1, lambda v: v + 1, target_start()), "another call or mode")

    def test_local_arithmetic(self):
        # Any exported kernel record, not only the target call's.
        self.rejects(edit_first("SGQ ", 3, lambda b: b + 1), "sch is not its binary64")

    def test_clamped_selection_blocks(self):
        # Zero the post-clamp ssx of the selected record (n1=1, iw=2).
        out, done = [], False
        start = target_start()
        for n, line in enumerate(lines()):
            t = line.split()
            if not done and n > start and t[0] == "SGQ" and t[1] == "1" and t[2] == "2":
                t[5] = "0"
                line, done = " ".join(t), True
            out.append(line)
        self.assertTrue(done)
        self.rejects(out, "sexcut-clamped")

    def test_partial_occupation_blocks(self):
        # occ = 0.5 (Fermi level) on the selected record: the endpoint assumes occ = 1.
        import struct
        half = struct.unpack("<q", struct.pack("<d", 0.5))[0]
        out, done, start = [], False, target_start()
        for n, line in enumerate(lines()):
            t = line.split()
            if not done and n > start and t[0] == "SGQ" and t[1] == "1" and t[2] == "2":
                t[10] = str(half)
                line, done = " ".join(t), True
            out.append(line)
        self.assertTrue(done)
        self.rejects(out, "occ=0.5")

    def test_new_call_before_kernel_block(self):
        # A setup COL that restarts my_igp after the target means another call.
        start = target_start()
        out = list(lines())
        col = next(l for l in out[:start][::-1] if l.startswith("COL "))
        t = col.split()
        t[4] = "0"
        out.insert(start + 1, " ".join(t))
        # The M4-identity check would already refuse this dump; test the guard itself.
        with self.assertRaises(sigma_mode.M5Error) as cm:
            sigma_mode.kernel_records(out)
        self.assertIn("new Sigma call", str(cm.exception))

    def test_m4_records_must_match(self):
        self.rejects(edit_first("GPP 1913 ", 13, lambda b: b + 1),
                     "differ from the committed M4-R1 dump")


class Certificate(unittest.TestCase):
    def test_lean_module_generated(self):
        self.assertEqual(make_lean_m5.OUT.read_text(), make_lean_m5.render(result()))

    def test_mutation_evidence(self):
        text = (M5 / "evidence" / "mutations.log").read_text()
        self.assertIn(f"M5Sigma.lean sha256: {sha256(make_lean_m5.OUT)}", text)
        self.assertIn(f"mutate.py sha256: {sha256(M5 / 'mutate.py')}", text)
        self.assertIn(f"m5_dump.dat.gz sha256: {sha256(sigma_mode.DUMP)}", text)
        self.assertTrue(text.rstrip().endswith("ALL OK"))
        self.assertEqual(text.count("verdict                : OK"), 6)

    def test_instrumentation_adds_only(self):
        body = [l for l in (M5 / "m5_instrument.patch").read_text().splitlines()
                if l.startswith("-") and not l.startswith("---")]
        self.assertEqual(body, [])

    def test_ab_neutrality(self):
        text = (M5 / "evidence" / "ab-neutrality.log").read_text()
        for f in ("eqp0.dat", "eqp1.dat", "sigma_hp.log", "ch_converge.dat", "vxc.dat", "x.dat"):
            self.assertIn(f"IDENTICAL {f}", text)
        self.assertIn("M4-R1 RECORDS IDENTICAL", text)
        self.assertNotIn("DIFFER", text)


if __name__ == "__main__":
    unittest.main()
