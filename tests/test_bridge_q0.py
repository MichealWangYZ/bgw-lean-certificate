"""BRIDGE-Q0: the q -> 0 screening (GW/Bridge/EpsQ0.lean, EpsQ0Sigma.lean) and the
q0-direction spread of O1 (docs/BRIDGE.md, BRIDGE-Q0 section; bgw/bridge_q0/q0.py).

Three layers:

* an independent numpy oracle on a toy plane-wave crystal (own Hamiltonian, own
  diagonalisation, never reads Lean output or the project's BerkeleyGW code): the
  small-q structure of chi0 (head ~ q^2, wings ~ q, body O(1)) with the k.p/commutator
  coefficients, the scaled limits of eps^-1, the Schur forms, parity, the q0_error
  bound, the oddness of the GPP kernel and the head-average bound -- always run;
* checks of the committed measurement bgw/bridge_q0/data/q0.json against the E1
  certificate cert_o1.json and against the stated explanation of the spread -- always
  run;
* a fresh pinned production run: RHO is the UNSYMMETRIZED sum over the three IBZ
  k-points of WFN_co (independent re-implementation) -- needs the pristine BerkeleyGW
  tree, skipped otherwise.
"""
import json
import pathlib
import sys
import tempfile
import unittest

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import run_production as prod  # noqa: E402

DATA = json.loads((ROOT / "bgw/bridge_q0/data/q0.json").read_text())
CERT = json.loads((ROOT / "bgw/endpoint/data/cert_o1.json").read_text())
HAVE_TREE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES)


# ------------------------------------------------------------- toy crystal

class Toy:
    """Simple-cubic toy crystal, Ry units, reciprocal vectors = unit vectors: a FIXED
    plane-wave basis {-2..2}^3 (so H(k+q) = H(k) + 2 q.(k+G) + |q|^2 exactly), a real
    even local potential, nv occupied bands, a small k-grid."""

    def __init__(self, seed=3, nv=1):
        rng = np.random.default_rng(seed)
        r = range(-2, 3)
        self.G = np.array([(a, b, c) for a in r for b in r for c in r], float)
        self.idx = {tuple(g.astype(int)): i for i, g in enumerate(self.G)}
        V = {}
        for g in self.G:
            key = tuple(np.abs(g).astype(int))
            if key not in V:
                V[key] = rng.uniform(-0.6, 0.6) if any(key) else 0.0
        n = len(self.G)
        self.V = np.array([[V.get(tuple(np.abs(self.G[i] - self.G[j]).astype(int)), 0.0)
                            if np.abs(self.G[i] - self.G[j]).max() <= 2 else 0.0
                            for j in range(n)] for i in range(n)])
        self.nv = nv
        self.ks = [np.array(k) for k in [(0.13, 0.21, 0.07), (-0.19, 0.11, 0.23), (0.27, -0.09, -0.17)]]
        self.chan = [np.array(g, float) for g in [(0, 0, 0), (1, 0, 0), (-1, 0, 0), (0, 1, 0),
                                                  (0, -1, 0), (0, 0, 1), (0, 0, -1)]]
        self.C = 4.0 / (len(self.ks) * 1.0)

    def eig(self, k):
        H = np.diag(np.einsum("ij,ij->i", k + self.G, k + self.G)) + self.V
        e, c = np.linalg.eigh(H)
        return e, c.T                               # rows: bands

    def M(self, cv, cc, g):
        """M_vc(G) = sum_G2 c_v(G2 + G) c_c(G2) in the fixed basis."""
        out = 0.0
        for j, g2 in enumerate(self.G):
            p = self.idx.get(tuple((g2 + g).astype(int)))
            if p is not None:
                out += cv[p] * cc[j]
        return out

    def chi(self, q):
        n = len(self.chan)
        X = np.zeros((n, n))
        for k in self.ks:
            ec, cc = self.eig(k)
            ev, cv = self.eig(k + q)
            for v in range(self.nv):
                for c in range(self.nv, len(ec)):
                    m = np.array([self.M(cv[v], cc[c], g) for g in self.chan])
                    X += np.outer(m, m) / (ev[v] - ec[c])
        return self.C * X

    def kp(self, u):
        """head, wing vector, body from the k.p / commutator formula at q = 0."""
        n = len(self.chan)
        h, w, B = 0.0, np.zeros(n), np.zeros((n, n))
        for k in self.ks:
            e, c = self.eig(k)
            dH = 2.0 * (k + self.G) @ u
            for v in range(self.nv):
                for cb in range(self.nv, len(e)):
                    de = e[v] - e[cb]
                    p = np.sum(c[cb] * dH * c[v]) / de
                    m0 = np.array([self.M(c[v], c[cb], g) for g in self.chan])
                    h += p * p / de
                    w += p * m0 / de
                    B += np.outer(m0, m0) / de
        return self.C * h, self.C * w, self.C * B

    def vq(self, q):
        return np.array([8 * np.pi / np.dot(q + g, q + g) for g in self.chan])


def scaled_limit(toy, u):
    h, w, B = toy.kp(u)
    X = B.copy()
    X[0, :] = w
    X[:, 0] = w
    X[0, 0] = h
    v = np.array([8 * np.pi / np.dot(u, u)] + [8 * np.pi / np.dot(g, g) for g in toy.chan[1:]])
    return np.eye(len(v)) - v[:, None] * X


def eps(toy, q):
    return np.eye(len(toy.chan)) - toy.vq(q)[:, None] * toy.chi(q)


class ToyKP(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.toy = Toy()
        cls.u = np.array([0.3, -0.5, 0.8])
        cls.u /= np.linalg.norm(cls.u)
        e = [cls.toy.eig(k)[0] for k in cls.toy.ks]
        cls.gap = min(ee[cls.toy.nv] - ee[cls.toy.nv - 1] for ee in e)

    def test_gapped(self):
        self.assertGreater(self.gap, 0.05)

    def test_chi_structure(self):
        """KPRay.head/wing/body_tendsto: chi_00/t^2, chi_0G/t, chi_GG' -> the k.p values,
        with an O(t) error."""
        h, w, B = self.toy.kp(self.u)
        errs = []
        for t in (1e-3, 1e-4):
            X = self.toy.chi(t * self.u)
            errs.append(max(abs(X[0, 0] / t ** 2 - h),
                            np.abs(X[0, 1:] / t - w[1:]).max(),
                            np.abs(X[1:, 0] / t - w[1:]).max(),
                            np.abs(X[1:, 1:] - B[1:, 1:]).max()))
        self.assertLess(errs[1], 1e-3)
        self.assertLess(errs[1], 0.2 * errs[0])          # linear convergence
        self.assertLessEqual(h, 0.0)                      # head_coef_nonpos

    def test_orthogonality_is_why(self):
        """Without orth (M_x(0,0) = <v|c> = 0) the head would not vanish: check M(0,0) = 0."""
        e, c = self.toy.eig(self.toy.ks[0])
        self.assertLess(abs(self.toy.M(c[0], c[3], np.zeros(3))), 1e-12)

    def test_scaled_inverse_limits(self):
        """q0_limit: head, body, t*row wing, col wing/t of eps^-1 -> entries of E~0^-1;
        the row wing itself diverges and the column wing vanishes."""
        X0 = np.linalg.inv(scaled_limit(self.toy, self.u))
        for t in (1e-4,):
            Y = np.linalg.inv(eps(self.toy, t * self.u))
            self.assertLess(abs(Y[0, 0] - X0[0, 0]), 1e-3)
            self.assertLess(np.abs(Y[1:, 1:] - X0[1:, 1:]).max(), 1e-3)
            self.assertLess(np.abs(t * Y[0, 1:] - X0[0, 1:]).max(), 1e-3)
            self.assertLess(np.abs(Y[1:, 0] / t - X0[1:, 0]).max(), 1e-3)
            self.assertGreater(np.abs(Y[0, 1:]).max(), 10 * np.abs(X0[0, 1:]).max())

    def test_schur(self):
        """schur_body / schur_head."""
        A = scaled_limit(self.toy, self.u)
        X = np.linalg.inv(A)
        P = A[1:, 1:] - np.outer(A[1:, 0], A[0, 1:]) / A[0, 0]
        self.assertLess(np.abs(P @ X[1:, 1:] - np.eye(len(P))).max(), 1e-10)
        Bi = np.linalg.inv(A[1:, 1:])
        epsM = A[0, 0] - A[0, 1:] @ Bi @ A[1:, 0]
        self.assertLess(abs(X[0, 0] * epsM - 1), 1e-10)

    def test_parity(self):
        """chi0s_neg + parity_inv: u -> -u keeps head/body, flips the wings."""
        X = np.linalg.inv(scaled_limit(self.toy, self.u))
        Xm = np.linalg.inv(scaled_limit(self.toy, -self.u))
        S = np.diag([-1.0] + [1.0] * (len(X) - 1))
        self.assertLess(np.abs(Xm - S @ X @ S).max(), 1e-10)

    def test_direction_dependence(self):
        """The body limit depends on u at O(1) in a generic (non-cubic) crystal."""
        X1 = np.linalg.inv(scaled_limit(self.toy, self.u))
        u2 = np.array([1.0, 0.0, 0.0])
        X2 = np.linalg.inv(scaled_limit(self.toy, u2))
        self.assertGreater(np.abs(X1[1:, 1:] - X2[1:, 1:]).max(), 1e-4)

    def test_q0_error_bound(self):
        """q0_error: entries within beta^2 delta/(1 - beta delta) (l-inf operator norm)."""
        t = 1e-3
        A = scaled_limit(self.toy, self.u)
        s = np.array([t] + [1.0] * (len(A) - 1))
        Et = eps(self.toy, t * self.u) * s[:, None] / s[None, :]
        nrm = lambda M: np.abs(M).sum(axis=1).max()
        X0 = np.linalg.inv(A)
        beta, delta = nrm(X0), nrm(Et - A)
        self.assertLess(beta * delta, 1)
        b = beta ** 2 * delta / (1 - beta * delta)
        Y = np.linalg.inv(eps(self.toy, t * self.u))
        self.assertLessEqual(abs(Y[0, 0] - X0[0, 0]), b)
        self.assertLessEqual(np.abs(Y[1:, 1:] - X0[1:, 1:]).max(), b)
        self.assertLessEqual(np.abs(t * Y[0, 1:] - X0[0, 1:]).max(), b)
        self.assertLessEqual(np.abs(Y[1:, 0] / t - X0[1:, 0]).max(), b)


def thK(I, O, x, occ):
    w = np.sqrt(O / I)
    return O / (2 * w * (x + w)) if occ else O / (2 * w * (x - w))


class WingHead(unittest.TestCase):
    def test_thK_odd_and_average(self):
        """thK_odd, wing_sum_zero: the GPP kernel is odd in (I, Omega^2); the leading
        wing integrand averages to 0 over an inversion-closed set of directions."""
        rng = np.random.default_rng(7)
        for _ in range(200):
            I, w = rng.uniform(0.05, 1) * rng.choice([-1, 1]), rng.uniform(0.5, 20)
            O, x = w * w * I, rng.uniform(-30, 30)
            for occ in (True, False):
                self.assertAlmostEqual(thK(-I, -O, x, occ), -thK(I, O, x, occ), places=9)
        a, g = rng.normal(size=3), rng.normal(size=3)
        dirs = rng.normal(size=(50, 3))
        dirs = np.vstack([dirs, -dirs])
        tot = sum((1 + (d @ d)) * thK(a @ d, 3.0 * (a @ d) * (1 + (g @ d) ** 2), 0.7, True)
                  for d in dirs)
        self.assertLess(abs(tot), 1e-9)

    def test_head_average_bound(self):
        """head_avg / head_avg_spec on a cube cell, Monte Carlo measure."""
        rng = np.random.default_rng(11)
        q = rng.uniform(-0.3, 0.3, size=(200000, 3))
        n = np.linalg.norm(q, axis=1)
        v = 8 * np.pi / n ** 2
        g0, K = 0.07, 0.4
        g = g0 + K * n * np.sin(5 * q[:, 0] / n + 1.3)
        lhs = abs(np.mean(v * g) - g0 * np.mean(v))
        self.assertLessEqual(lhs, K * np.mean(v * n))
        q0 = 0.001
        gq0 = g0 + 0.9 * K * q0
        self.assertLessEqual(abs(np.mean(v * g) - np.mean(v) * gq0),
                             K * np.mean(v * n) + np.mean(v) * K * q0)


# ------------------------------------------------------ committed numbers

AX = {(0, 0, 1): "b3", (0, 0, -1): "b3", (0, 1, 0): "b2", (0, -1, 0): "b2",
      (1, 0, 0): "b1", (-1, 0, 0): "b1", (1, 1, 1): "s", (-1, -1, -1): "s"}
# the image of q0 = b3 direction under each of the 48 ops (cert.py's mtrx order),
# recorded from the run (mtrx @ (0,0,1))
OP_AXIS = ["b3", "s", "b3", "s", "b3", "b1", "b1", "b3", "b1", "b2", "b1", "b2", "b3", "b3",
           "s", "s", "b3", "b1", "b1", "b3", "b1", "b1", "b2", "b2", "s", "b1", "b1", "s",
           "b2", "b3", "b3", "b2", "b1", "b1", "s", "s", "b3", "b3", "b2", "b2", "s", "b2",
           "s", "b2", "s", "b2", "s", "b2"]


class Committed(unittest.TestCase):
    def test_reproduces_certificate_per_op(self):
        ops = DATA["O1"]["production_rho"]["q0_block_per_op"]
        for i in range(48):
            lo, hi = ops[str(i)]["O1"]
            clo, chi = CERT["O1_per_q0_op"][str(i)]
            self.assertLessEqual(max(lo, clo), min(hi, chi) + 1e-12, i)

    def classes(self, key, which):
        ops = DATA["O1"][which][key]
        out = {}
        for i in range(48):
            out.setdefault(round(ops[str(i)]["O1"][0] * 1e6, 1), set()).add(OP_AXIS[i])
        return out

    def test_spread_is_rho_asymmetry(self):
        """Production RHO: three classes {b3}, {b2}, {b1, s}; star-symmetrized RHO:
        X is op-independent, L has two classes {b3} (q0 along the L axis) and the rest."""
        c = self.classes("q0_block_per_op", "production_rho")
        self.assertEqual(sorted(sorted(v) for v in c.values()), [["b1", "s"], ["b2"], ["b3"]])
        c = self.classes("q0_block_per_op", "symmetrized_rho")
        self.assertEqual(sorted(sorted(v) for v in c.values()), [["b1", "b2", "s"], ["b3"]])
        ops = DATA["O1"]["symmetrized_rho"]["q0_block_per_op"]
        eX = [ops[str(i)]["eX"][0] for i in range(48)]
        self.assertLess(max(eX) - min(eX), 1e-9)
        r = DATA["rho"]
        self.assertGreater(r["star_asymmetry_max"], 0.1)
        self.assertLess(r["symmetrized_star_asymmetry_max"], 1e-12)
        self.assertLess(r["ibz_reconstruction_max_dev"], 1e-12)

    def test_limit_isotropic_and_bounded(self):
        L = DATA["limit"]
        self.assertLess(DATA["isotropy"]["eps_M_spread"], 1e-8)
        self.assertLess(L["beta_delta"], 1)
        for k in ("actual_head_diff", "actual_body_diff_max", "actual_rowwing_scaled_diff_max",
                  "actual_colwing_scaled_diff_max"):
            self.assertLessEqual(L[k], L["q0_error_bound"], k)
        self.assertGreater(DATA["isotropy"]["body_limit_max_direction_dependence"], 1e-3)

    def test_finite_q0_effect_small(self):
        """q0 block vs the k.p limit block, same op: O1 moves by < 5e-3 meV."""
        for which in ("production_rho", "symmetrized_rho"):
            a = DATA["O1"][which]["q0_block_per_op"]
            b = DATA["O1"][which]["limit_block_per_op"]
            d = max(abs(a[str(i)]["O1"][0] - b[str(i)]["O1"][0]) for i in range(48))
            self.assertLess(d, 5e-6)

    def test_angular_average_inside_direction_range(self):
        for which in ("production_rho", "symmetrized_rho"):
            for nd, r in DATA["O1"][which]["angular_average"].items():
                self.assertLessEqual(r["per_direction_min"], r["O1"][0])
                self.assertLessEqual(r["O1"][1], r["per_direction_max"])


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree not available")
class FreshRun(unittest.TestCase):
    def test_rho_is_unsymmetrized_ibz_sum(self):
        """RHO = 2 sum_{k in IBZ} w_k sum_v |psi_vk|^2 over WFN_co's 3 points, and it is
        not star-symmetric: rho(b3) != rho(b1) on the first shell."""
        import bgwio
        with tempfile.TemporaryDirectory() as d:
            out = pathlib.Path(d) / "run"
            prod.run(out, blas_threads=1)
            rho = bgwio.read_rho(out / "RHO")
            w = bgwio.read_wfn(out / "WFN_inner")
        g = np.asarray(rho["gvec"])
        r = np.asarray(rho["rho"], float)
        acc = np.zeros(len(g))
        for ik in range(len(w["kpt"])):
            G = np.asarray(w["kg"][ik])
            C = np.asarray(w["coef"][ik])[:4].real
            pos = {tuple(x): i for i, x in enumerate(G)}
            for gi, gg in enumerate(g):
                s = 0.0
                for j, g2 in enumerate(G):
                    p = pos.get(tuple(g2 + gg))
                    if p is not None:
                        s += float(C[:, p] @ C[:, j])
                acc[gi] += w["kw"][ik] * s
        self.assertLess(np.abs(r - 2 * acc).max(), 1e-12)
        idx = {tuple(x): i for i, x in enumerate(g)}
        self.assertGreater(abs(r[idx[(0, 0, 1)]] - r[idx[(1, 0, 0)]]), 0.1)


if __name__ == "__main__":
    unittest.main()
