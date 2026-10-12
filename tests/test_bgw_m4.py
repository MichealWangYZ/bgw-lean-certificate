"""BGW-M4-R1: the M2-to-Sigma input bridge and the frozen GPP target.

These tests run on committed data only. They check that the bridge checker
accepts the real export, rejects each targeted corruption of it, that the Lean
module is exactly what the data generates, and that the mutation evidence is
bound to the current certificate.
"""
import functools
import hashlib
import pathlib
import struct
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
M4 = ROOT / "bgw" / "m4_gpp"
sys.path.insert(0, str(M4))
import bridge  # noqa: E402
import make_lean  # noqa: E402

DUMP_SHA256 = "0910b6889637576200fdec4494d764d52ceec00f8896d023c9bafb38790c3e02"
PATCH = M4 / "m4r1_instrument.patch"
MUTLOG = M4 / "evidence" / "mutations.log"
ABLOG = M4 / "evidence" / "ab-neutrality.log"


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


@functools.lru_cache(maxsize=None)
def m2():
    return bridge.load_m2()


@functools.lru_cache(maxsize=None)
def lines():
    return tuple(bridge.read_lines())


@functools.lru_cache(maxsize=None)
def result():
    return bridge.run(list(lines()), m2())


def bits(x):
    return struct.unpack("<q", struct.pack("<d", x))[0]


def mutate(pred, edit, count=1):
    """Apply `edit` to the first `count` lines satisfying `pred`."""
    out, n = [], 0
    for line in lines():
        if n < count and pred(line):
            line, n = edit(line), n + 1
        out.append(line)
    assert n == count, "mutation site not found"
    return out


def field(line, k, value):
    t = line.split()
    t[k] = str(value)
    return " ".join(t)


class Bridge(unittest.TestCase):
    def test_committed_dump_identity(self):
        self.assertEqual(sha256(bridge.DUMP), DUMP_SHA256)

    def test_every_consumed_m2_operand_is_bound(self):
        r = result()
        self.assertEqual(r["visits"], [2, 3, 4, 5])
        self.assertEqual(r["checked"], 8448)

    def test_frozen_target(self):
        t, c = result()["target"], result()["cert"]
        self.assertEqual((t["occ"], t["rq"]["irq"], t["ig"], t["igp"]), (1913, 2, 2, 1))
        self.assertEqual(c["src"], (1, 2))
        self.assertEqual(c["kind"], "col-wing")
        self.assertEqual((t["rq"]["itran"], t["rq"]["kg"]), (38, (0, 0, 1)))

    def test_budget_model_is_fixed(self):
        self.assertEqual((bridge.N_OMEGA, bridge.N_MAP, bridge.N_FORMATION), (16, 4, 3))

    def test_target_within_budgets(self):
        c = result()["cert"]
        self.assertLessEqual(abs(c["o_hat"] - c["o_star"]), c["b_omega"])
        self.assertLessEqual(abs(c["i_hat"] - c["i_star"]), c["b_i"])
        self.assertLessEqual(abs(c["p_hat"] - c["p_star"]), c["b_p"])
        self.assertLessEqual(c["b_i"], abs(c["i_star"]) / 2)
        self.assertGreater(c["p_star"], 0)

    def test_budget_m2_is_lean_btotal(self):
        # M2's recorded replay value, to its printed precision.
        self.assertAlmostEqual(float(bridge.m2_btotal()), 2.578408e-13, delta=1e-19)


class BridgeRejects(unittest.TestCase):
    """Each targeted corruption of the real export must be refused."""

    def rejects(self, text, needle):
        with self.assertRaises(bridge.BridgeError) as cm:
            bridge.run(text, m2())
        self.assertIn(needle, str(cm.exception))

    def test_flipped_phase(self):
        is_map = lambda s: s.startswith("MAP 2 ") and s.split()[10] == str(bits(1.0))
        self.rejects(mutate(is_map, lambda s: field(s, 10, bits(-1.0))), "phase")

    def test_swapped_row_index(self):
        t = mutate(lambda s: s.startswith("MAP 2 1 "), lambda s: field(s, 3, 3 if s.split()[3] != "3" else 4))
        self.rejects(t, "irq 2 ig 1")

    def test_symmetry_matrix(self):
        def edit(s):
            t = s.split()
            t[2], t[6] = t[6], t[2]
            return " ".join(t)
        self.rejects(mutate(lambda s: s.startswith("SYM 2 "), edit), "S^-1")

    def test_wing_operand(self):
        def edit(s):
            t = s.split()
            t[12] = str(int(t[12]) + 1)
            return " ".join(t)
        self.rejects(mutate(lambda s: s.startswith("WING 2 "), edit), "wing image")

    def test_consumed_operand(self):
        def edit(s):
            t = s.split()
            t[10] = str(int(t[10]) + 1)
            return " ".join(t)
        self.rejects(mutate(lambda s: s.startswith("GPP 1913 "), edit), "consumed operand")

    def test_omega_not_wpeff_output(self):
        def edit(s):
            t = s.split()
            t[11] = str(int(t[11]) + 1)
            return " ".join(t)
        # The target's own wpeff record: the last WP line (igp=1, ig=2) before GPP 1913.
        target = next(i for i, l in enumerate(lines()) if l.startswith("GPP 1913 "))
        site = max(i for i, l in enumerate(lines()[:target]) if l.startswith("WP 1 2 "))
        text = list(lines())
        text[site] = edit(text[site])
        self.rejects(text, "Omega2 is not the wpeff output")

    def test_m2_anchor(self):
        bad = dict(m2())
        bad["xbits"] = dict(bad["xbits"])
        bad["xbits"][(1, 2)] += 1
        with self.assertRaises(bridge.BridgeError):
            bridge.run(list(lines()), bad)


class Certificate(unittest.TestCase):
    def test_lean_module_is_generated_from_data(self):
        self.assertEqual(make_lean.OUT.read_text(), make_lean.render(result()))

    def test_mutation_evidence_bound_to_current_files(self):
        text = MUTLOG.read_text()
        self.assertIn(f"M4GPP.lean sha256: {sha256(make_lean.OUT)}", text)
        self.assertIn(f"mutate.py sha256: {sha256(M4 / 'mutate.py')}", text)
        self.assertIn(f"m4r1_dump.dat.gz sha256: {sha256(bridge.DUMP)}", text)
        self.assertTrue(text.rstrip().endswith("ALL OK"))
        for tag in ("control", "wrong-source", "no-wing", "phase", "primitive", "division"):
            self.assertIn(f"--- {tag} ---", text)
        self.assertEqual(text.count("verdict                : OK"), 6)

    def test_instrumentation_adds_only(self):
        body = [l for l in PATCH.read_text().splitlines()
                if l.startswith("-") and not l.startswith("---")]
        self.assertEqual(body, [])

    def test_ab_neutrality_recorded(self):
        text = ABLOG.read_text()
        for f in ("eqp0.dat", "eqp1.dat", "sigma_hp.log", "ch_converge.dat", "vxc.dat", "x.dat"):
            self.assertIn(f"IDENTICAL {f}", text)
        self.assertNotIn("DIFFERS", text)


if __name__ == "__main__":
    unittest.main()
