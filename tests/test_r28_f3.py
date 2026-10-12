"""R28-F3: the all-band enclosure for an EXACTLY orthonormal system near the stored rows
(GW/Bridge/CorPerturb.lean, CorPerturbLowdin.lean; bgw/r28_f3/f3.py; docs/reviews/R28-F3.md).

Independent oracle: numpy and fractions only, written from the linear algebra and the
BerkeleyGW mode rules. It never reads Lean output and does not import f3.py.

* Loewdin: R* = (R R^T)^{-1/2} R has orthonormal rows and ||R* - R||_F^2 =
  sum (1 - sqrt(l))^2 <= sum (1 - l)^2 = ||R R^T - 1||_F^2.
* Completion: exactly orthonormal rows are completed by exactly L - k rows; at kappa > 1
  the defect kappa 1 - R^T R has rank L (the review's witness R = [1, 0],
  kappa = 1 + 2^-40, in exact rationals).
* The per-mode bound 751 |IeU| on the spec's computed-band kernel (every branch of
  schM / ssxM, sexcut = 4, LIM1 = 250000).
* The perturbed enclosure by brute force: random systems with exactly orthonormal rows
  R* plus their completion, stored rows R = R* + noise, kernels within their bounds. The
  true all-band Sigma lies in the stored-data centre +- (radP + cenErr + compErr). This is
  checked for the generating R* and for the Loewdin rows of R.
* The committed Si-EPM numbers `bgw/r28_f3/data/f3.json`.
"""
import json
import pathlib
import unittest
from fractions import Fraction as Fr

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA_P = ROOT / "bgw/r28_f3/data/f3.json"
COR_P = ROOT / "bgw/bridge_cor/data/cor.json"


def lowdin(R):
    lam, U = np.linalg.eigh(R @ R.T)
    return (U @ np.diag(lam ** -0.5) @ U.T) @ R, lam


def completion(P):
    """Rows completing orthonormal rows P (k x L) to an orthonormal basis: L - k rows."""
    k, L = P.shape
    _, _, Vt = np.linalg.svd(P, full_matrices=True)
    return Vt[k:]


class Lowdin(unittest.TestCase):
    def test_lowdin_random(self):
        rng = np.random.default_rng(3)
        for _ in range(200):
            L = int(rng.integers(3, 40))
            k = int(rng.integers(1, L + 1))
            Q, _ = np.linalg.qr(rng.normal(size=(L, L)))
            R = Q[:k] + rng.normal(scale=10 ** rng.uniform(-8, -1.5), size=(k, L))
            eta = np.sum((R @ R.T - np.eye(k)) ** 2)
            if eta >= 1:
                continue
            S, lam = lowdin(R)
            self.assertLess(np.abs(S @ S.T - np.eye(k)).max(), 1e-10)
            dist = np.sum((S - R) ** 2)
            self.assertAlmostEqual(dist, np.sum((1 - np.sqrt(lam)) ** 2),
                                   delta=1e-5 * dist + 1e-22)
            self.assertLessEqual(dist, eta * (1 + 1e-8) + 1e-28)
            # the bound is about a factor 4 loose for small eta: (1 - sqrt l)^2 ~ (1 - l)^2 / 4
            if eta < 1e-6:
                self.assertLess(dist, 0.26 * eta + 1e-28)

    def test_sqrt_defect(self):
        lam = np.linspace(0, 4, 4001)
        self.assertTrue(np.all((1 - np.sqrt(lam)) ** 2 <= (1 - lam) ** 2 + 1e-15))

    def test_eta_ge_one_without_full_rank(self):
        """A zero row has eta >= 1: the hypothesis eta < 1 excludes rank deficiency."""
        R = np.zeros((2, 3))
        R[0, 0] = 1.0
        self.assertGreaterEqual(np.sum((R @ R.T - np.eye(2)) ** 2), 1.0)


class Completion(unittest.TestCase):
    def test_exact_completion_has_L_minus_k_rows(self):
        rng = np.random.default_rng(4)
        for _ in range(50):
            L = int(rng.integers(2, 30))
            k = int(rng.integers(1, L + 1))
            Q, _ = np.linalg.qr(rng.normal(size=(L, L)))
            P = Q[:k]
            C = completion(P)
            self.assertEqual(C.shape[0], L - k)
            self.assertLess(np.abs(P.T @ P + C.T @ C - np.eye(L)).max(), 1e-12)

    def test_kappa_above_one_needs_L_rows(self):
        """kappa > lambda_max(R^T R): kappa 1 - R^T R is positive definite, rank L > L - k."""
        rng = np.random.default_rng(5)
        L, k = 12, 5
        Q, _ = np.linalg.qr(rng.normal(size=(L, L)))
        R = Q[:k] * (1 + 1e-15)
        kappa = np.linalg.eigvalsh(R.T @ R).max() + 1e-12
        ev = np.linalg.eigvalsh(kappa * np.eye(L) - R.T @ R)
        self.assertGreater(ev.min(), 0)
        self.assertEqual(int(np.sum(ev > 1e-14)), L)

    def test_review_witness_exact(self):
        eps = Fr(1, 2 ** 40)
        kap = 1 + eps
        M = [[kap - 1, Fr(0)], [Fr(0), kap]]          # kappa 1 - R^T R, R = [1, 0]
        det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
        self.assertGreater(det, 0)                     # rank 2 > L - k = 1
        # one row C = [c0, c1] would need c0^2 = eps, c1^2 = kappa, c0 c1 = 0: impossible
        self.assertGreater(eps * kap, 0)
        # at kappa = 1 the single row [0, 1] completes R exactly
        self.assertEqual([[Fr(1) - 1, 0], [0, Fr(1)]], [[0 * 0, 0 * 1], [1 * 0, 1 * 1]])


# ------------------------------------------------------------ the spec's mode rules
GAM2, LIM1, TZ, S = 0.25, 250000.0, 4951760157141521 / 2 ** 92, 4.0


def schM(J, w, x):
    if (x - w) ** 2 > GAM2 and w ** 2 < (x - w) ** 2 * LIM1:
        return w * J / (x - w)
    return 0.0


def ssxM(J, w, x):
    if (x - w) ** 2 > GAM2 and w ** 2 < (x - w) ** 2 * LIM1:
        if abs(x * x - w * w) < w * w / S and x < 0:
            return 0.0
        return w * w * J / (x * x - w * w)
    if w ** 2 > (x - w) ** 2 * TZ and x - w != 0:
        if abs(2 * (x + w)) < w / S and x < 0:
            return 0.0
        return -(J * w) / (2 * (x + w))
    return 0.0


class KernelBound(unittest.TestCase):
    def test_751(self):
        rng = np.random.default_rng(6)
        worst = 0.0
        for _ in range(200000):
            J = rng.uniform(-3, 3)
            w = 10 ** rng.uniform(-3, 12)
            r = rng.random()
            if r < 0.3:
                x = w + rng.choice([-1, 1]) * 10 ** rng.uniform(-14, 1) * max(w, 1)
            elif r < 0.6:
                x = -w + rng.choice([-1, 1]) * 10 ** rng.uniform(-14, 1) * max(w, 1)
            else:
                x = rng.uniform(-50, 50)
            for occ in (False, True):
                K = J / 4 + 0.5 * schM(J, w, x) - (ssxM(J, w, x) if occ else 0.0)
                worst = max(worst, abs(K) / abs(J))
        self.assertLessEqual(worst, 751.0)
        self.assertGreater(worst, 100.0)       # the generic CH branch reaches ~ 250 |I|


# ------------------------------------------------------------ brute-force enclosure
def quad(u, v, F):
    """sum_ij u_i v_i u_j F[j, i]."""
    return float(np.sum((u * v)[None, :] * u[:, None] * F))


def prod_err(x, y, ex, ey):
    return ex * np.abs(y) + np.abs(x) * ey + ex * ey


def enclosure(R, A, Ab, v, vx, nocc, c, r, B, d):
    """Centre and radius of the theorem from the STORED rows R (k x L) and d."""
    u = R @ A                              # (k, nG)  stored pair densities
    ub = R[:nocc] @ Ab                     # (nocc, nGb)
    clo = A.T @ A
    T = clo - u.T @ u                      # kappa = 1
    e = np.sqrt(np.diag(clo)) * d
    eb = np.sqrt(np.sum(Ab ** 2, axis=0)) * d
    dT = sum(prod_err(u[n][:, None], u[n][None, :], e[:, None], e[None, :]) for n in range(len(u)))
    cen = float(np.sum(v[:, None] * T * c.T))                    # sum_ij v_i T_ij c_ji
    sd = np.sqrt(np.maximum(np.diag(T) + np.diag(dT), 0))
    radP = float(np.sum(np.abs(v)[None, :] * sd[None, :] * sd[:, None] * r))
    sd1 = np.sqrt(np.maximum(np.diag(T), 0))
    radK1 = float(np.sum(np.abs(v)[None, :] * sd1[None, :] * sd1[:, None] * r))
    cenErr = float(np.sum(np.abs(v)[:, None] * dT * np.abs(c).T))
    xErr = float(np.sum(np.abs(vx)[None, :] * (2 * eb[None, :] * np.abs(ub) + eb[None, :] ** 2)))
    comp = xErr + float(sum(np.sum(np.abs(v)[None, :] * B[n] * dT.T) for n in range(len(u))))
    return cen, radP, cenErr, comp, radK1


def sigma(P, Cc, A, Ab, v, vx, nocc, K, F):
    """Exchange + computed bands (rows P, kernels K) + omitted bands (rows Cc, kernels F)."""
    ub = P[:nocc] @ Ab
    s = -float(np.sum(ub ** 2 * vx[None, :]))
    s += sum(quad(P[n] @ A, v, K[n]) for n in range(len(P)))
    s += sum(quad(Cc[m] @ A, v, F[m]) for m in range(len(Cc)))
    return s


class BruteForce(unittest.TestCase):
    def check(self, seed, noise, use_lowdin):
        rng = np.random.default_rng(seed)
        L = int(rng.integers(6, 16))
        k = int(rng.integers(2, L - 1))
        nG, nGb, nocc = int(rng.integers(2, 6)), int(rng.integers(2, 6)), int(rng.integers(1, k + 1))
        Q, _ = np.linalg.qr(rng.normal(size=(L, L)))
        Rstar = Q[:k]
        R = Rstar + rng.normal(scale=noise, size=(k, L))
        if use_lowdin:
            eta = np.sum((R @ R.T - np.eye(k)) ** 2)
            P, _ = lowdin(R)
            d = np.sqrt(eta)
        else:
            P = Rstar
            d = np.sqrt(np.sum((P - R) ** 2, axis=1)).max()
        Cc = completion(P)
        A = rng.normal(size=(L, nG))
        Ab = rng.normal(size=(L, nGb))
        v = rng.normal(size=nG) * rng.choice([-1, 1], size=nG)
        vx = rng.normal(size=nGb)
        c = rng.normal(size=(nG, nG))
        r = rng.uniform(0, 1, size=(nG, nG))
        F = [c + r * rng.uniform(-1, 1, size=(nG, nG)) for _ in range(len(Cc))]
        B = [rng.uniform(0, 2, size=(nG, nG)) for _ in range(k)]
        K = [B[n] * rng.uniform(-1, 1, size=(nG, nG)) for n in range(k)]
        true = sigma(P, Cc, A, Ab, v, vx, nocc, K, F)
        stored = -float(np.sum((R[:nocc] @ Ab) ** 2 * vx[None, :])) + sum(
            quad(R[n] @ A, v, K[n]) for n in range(k))
        cen, radP, cenErr, comp, radK1 = enclosure(R, A, Ab, v, vx, nocc, c, r, B, d)
        dev = abs(true - stored - cen)
        tol = 1e-9 * (1 + abs(true))
        self.assertLessEqual(dev, radP + cenErr + comp + tol)
        return dev, radK1, radP + cenErr + comp

    def test_brute_force_generating_rows(self):
        for s in range(300):
            self.check(s, 10 ** (-1.5 - 3 * (s % 4)), False)

    def test_brute_force_lowdin_rows(self):
        for s in range(300):
            self.check(1000 + s, 10 ** (-1.5 - 3 * (s % 4)), True)

    def test_propagation_is_needed(self):
        """With visible noise the kappa = 1 radius alone (radK1) is exceeded in some cases."""
        fails = 0
        for s in range(300):
            dev, radK1, _ = self.check(5000 + s, 3e-2, False)
            fails += dev > radK1
        self.assertGreater(fails, 0)


# ------------------------------------------------------------ committed Si-EPM numbers
@unittest.skipUnless(DATA_P.exists(), "f3.json not generated")
class SiEPM(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.d = json.loads(DATA_P.read_text())
        cls.cor = json.loads(COR_P.read_text())

    def test_delta_negligible(self):
        for lab in ("X", "L"):
            row = self.d["nb_18"][lab]
            self.assertLess(row["eta_max"], 1e-20)      # hypothesis eta < 1 with room
            self.assertLess(row["d_max"], 1e-12)
            self.assertLess(row["propagation_Sigma_Eo_eV"], 1e-7)
            self.assertLess(row["propagation_dSigma_eV"], 1e-7)
            self.assertGreater(row["propagation_Sigma_Eo_eV"], 0)

    def test_propagation_decomposition(self):
        for lab in ("X", "L"):
            p = self.d["nb_18"][lab]["parts_eV"]
            prop = p["radP_S"] - p["radK1_S"] + p["cenErr_S"] + p["compErr"]
            self.assertAlmostEqual(prop, self.d["nb_18"][lab]["propagation_Sigma_Eo_eV"],
                                   delta=1e-9)
            self.assertGreaterEqual(p["radP_S"], p["radK1_S"])
            self.assertLess(p["xErr"], p["compErr"])

    def test_O1_close_to_bridge_cor(self):
        """The new enclosure contains the kappa = 1 one and differs from BRIDGE-COR's
        (kappa > 1) by far less than 1 meV."""
        o, ok = self.d["nb_18"]["O1_meV"], self.d["nb_18"]["O1_kappa1_no_propagation_meV"]
        self.assertLessEqual(o[0], ok[0])
        self.assertGreaterEqual(o[1], ok[1])
        old = self.cor["rows"]["spec_rule_tail"]["O1_meV"]
        self.assertLess(abs(o[0] - old[0]), 1e-2)
        self.assertLess(abs(o[1] - old[1]), 1e-2)
        self.assertLess(self.d["nb_18"]["O1_width_change_meV"], 1e-2)

    def test_heuristic_half_inside(self):
        o = self.d["nb_18"]["O1_meV"]
        half = self.cor["rows"]["baseline_COR_half"]["O1_meV"]
        self.assertTrue(o[0] <= half[0] and half[1] <= o[1])

    def test_more_bands(self):
        keys = [k for k in self.d if k.startswith("all_bands_nb_")]
        if not keys:
            self.skipTest("no --all-bands diagnostic in f3.json")
        bgw = self.cor["all_bands"]["bgw_cross_check"]["O1_BerkeleyGW_sigma_hp_meV"]
        widths = []
        for key in sorted(keys, key=lambda s: int(s.rsplit("_", 1)[1])):
            row = self.d[key]
            o = row["O1_meV"]
            widths.append(o[1] - o[0])
            for lab in ("X", "L"):
                self.assertLess(row[lab]["eta_max"], 1e-20)
                self.assertLess(row[lab]["propagation_Sigma_Eo_eV"], 1e-6)
            # the 164-band BerkeleyGW O1 (-3.76 meV) is not a bound target, but the
            # finite-basis all-band value is within the nb = 168 enclosure
            if key.endswith("_168"):
                self.assertTrue(o[0] <= bgw <= o[1] or abs(bgw - (o[0] + o[1]) / 2) < 0.5)
        self.assertEqual(widths, sorted(widths, reverse=True))


if __name__ == "__main__":
    unittest.main()
