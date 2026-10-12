"""The cell-averaged Coulomb kernel: production Monte Carlo versus exact.

BerkeleyGW 4.0 replaces 8 pi/|q+G|^2 by its average over the mini-Brillouin
zone (the Wigner-Seitz cell P of the q-grid lattice) whenever |q+G|^2 < avgcut;
this run prints avgcut = 1e12 Ry, so every (q, G) is averaged
(Common/vcoul_generator.f90:387-455). The average is estimated by Monte Carlo:

  points  MT19937 seeded with 5000, 3 nmc draws discarded, then nmc triples
          r = a/(2^32-1) (vcoul_generator.f90:227-239, random.f90:1337-1355),
          each folded to its nearest q-lattice translate in the bdot metric
          (vcoul_generator.f90:261-281), scaled by 1/qgrid; nmc = 2.5e6
          (nrtype.f90:112-114), ncell = 3 (nrtype.f90:109).
  q+G=0   (8 pi/nmc) sum over points outside the inscribed sphere of radius^2
          q0sph2, plus the exact sphere term 32 pi^2 sqrt(q0sph2) / V_P
          (minibzaverage.f90:47-76).
  q+G!=0  the first nn2 = nint(250000 * 4 q0sph2 / |q+G|^2) points, clamped to
          [1, nmc] (minibzaverage.f90:58-68).

`production` replicates that estimator. `exact` evaluates the quantity it
estimates, (1/V_P) int_P 8 pi / |q+G+p|^2 d^3p, by the divergence theorem
(div p/|p|^2 = 1/|p|^2) as a sum of smooth face integrals, with high-order
Gauss quadrature on each face triangle. Float here; certified in E1.4.
"""
import numpy as np
from scipy.spatial import ConvexHull, HalfspaceIntersection

NMC, NMC_COARSE, NCELL, SEED = 2_500_000, 250_000, 3, 5000


def _rng_triples(n):
    bg = np.random.MT19937()
    bg._legacy_seeding(SEED)               # init_genrand(5000), random.f90:399-425
    bg.random_raw(3 * n)                   # discarded (vcoul_generator.f90:232-234)
    a = bg.random_raw(3 * n).astype(np.float64)
    return (a * (1.0 / 4294967295.0)).reshape(n, 3)   # ran(ii, jj), ii fastest


class MiniBZ:
    def __init__(self, bdot, qgrid, celvol):
        self.bdot = np.asarray(bdot, float)
        self.qgrid = np.asarray(qgrid, int)
        self.dd = 1.0 / self.qgrid
        self.nfk = int(np.prod(self.qgrid))
        self.celvol = celvol
        self.volume = 8 * np.pi ** 3 / (celvol * self.nfk)
        rng = range(-NCELL + 1, NCELL + 1)
        cells = np.array([(i, j, k) for i in rng for j in rng for k in rng], float)
        nz = cells[np.any(cells != 0, axis=1)] * self.dd * 0.5
        self.q0sph2 = float(np.min(np.einsum("ni,ij,nj->n", nz, self.bdot, nz)))
        self._cells = cells
        self._qran = None
        # Cartesian frame: any B with B^T B = bdot (Cholesky, like dpotrf 'U')
        self.U = np.linalg.cholesky(self.bdot).T       # bdot = U^T U

    # ---------------------------------------------------------- production
    def qran(self):
        if self._qran is None:
            ran = _rng_triples(NMC)
            best, bestlen = None, None
            for c in self._cells:                # same loop order as the source
                fq = ran - c
                v = fq @ self.U.T
                ln = np.einsum("ni,ni->n", v, v)
                if best is None:
                    best, bestlen = fq.copy(), ln
                else:
                    m = ln < bestlen             # strict: first minimum wins
                    best[m], bestlen[m] = fq[m], ln[m]
            self._qran = best * self.dd
        return self._qran

    def production(self, qk):
        """The production estimate (unscaled by fact), for qk = q+G in crystal coords."""
        qk = np.asarray(qk, float)
        qr = self.qran()
        lqk = qk @ self.bdot @ qk
        if lqk < 1e-12:                          # TOL_Zero
            g = qr + qk
            ln = np.einsum("ni,ij,nj->n", g, self.bdot, g)
            s = np.sum(1.0 / ln[ln > self.q0sph2])
            return s * 8 * np.pi / NMC + 32 * np.pi ** 2 * np.sqrt(self.q0sph2) / self.volume
        nn2 = int(np.rint(NMC_COARSE * 4.0 * self.q0sph2 / lqk))
        nn2 = max(1, min(nn2, NMC))
        g = qr[:nn2] + qk
        ln = np.einsum("ni,ij,nj->n", g, self.bdot, g)
        return np.sum(1.0 / ln) * 8 * np.pi / nn2

    def oneoverq_production(self, q):
        """(8 pi / nmc) sum 1/|q+p| over all points (minibzaverage.f90:192-219),
        the wing factor's average (vcoul_generator.f90:357-365)."""
        g = self.qran() + np.asarray(q, float)
        ln = np.sqrt(np.einsum("ni,ij,nj->n", g, self.bdot, g))
        return np.sum(1.0 / ln) * 8 * np.pi / NMC

    def nn2(self, qk):
        qk = np.asarray(qk, float)
        lqk = qk @ self.bdot @ qk
        if lqk < 1e-12:
            return NMC
        return max(1, min(int(np.rint(NMC_COARSE * 4.0 * self.q0sph2 / lqk)), NMC))

    # ---------------------------------------------------------------- exact
    def faces(self):
        """Wigner-Seitz cell of the q-lattice in the Cartesian frame x = U p:
        list of (unit normal, offset h, vertex array ordered around the face)."""
        if getattr(self, "_faces", None) is None:
            L = self._cells[np.any(self._cells != 0, axis=1)] * self.dd
            Lc = L @ self.U.T
            # half-spaces  x . Lc <= |Lc|^2/2   as  A x + b <= 0
            hs = np.hstack([Lc, -0.5 * np.einsum("ni,ni->n", Lc, Lc)[:, None]])
            hi = HalfspaceIntersection(hs, np.zeros(3))
            V = hi.intersections
            hull = ConvexHull(V)
            faces = {}
            for simplex, eq in zip(hull.simplices, hull.equations):
                key = tuple(np.round(eq, 9))
                faces.setdefault(key, set()).update(simplex.tolist())
            out = []
            for key, idx in faces.items():
                n, off = np.array(key[:3]), -key[3]      # n.x = off
                P = V[sorted(idx)]
                c = P.mean(axis=0)
                e1 = P[0] - c
                e1 /= np.linalg.norm(e1)
                e2 = np.cross(n, e1)
                ang = np.arctan2((P - c) @ e2, (P - c) @ e1)
                out.append((n, off, P[np.argsort(ang)]))
            self._faces = out
            vol = sum(off * _poly_area(P) for n, off, P in out) / 3.0
            if not np.isclose(vol, self.volume, rtol=1e-12):
                raise ValueError(f"WS cell volume {vol} != {self.volume}")
        return self._faces

    def exact(self, qk, order=48):
        """(1/V) int_P 8 pi/|Q+p|^2 via sum_f h_f int_f dA/|x|^2, x over P+Q."""
        Q = self.U @ np.asarray(qk, float)
        total = 0.0
        for n, off, P in self.faces():
            Ps = P + Q
            h = off + n @ Q                      # signed distance of shifted face plane
            if abs(h) < 1e-15:
                continue                         # contributes zero (q.n = 0 on that face)
            c = Ps.mean(axis=0)
            for a, b in zip(Ps, np.roll(Ps, -1, axis=0)):
                total += h * _tri_inv_r2(c, a, b, order)
        return 8 * np.pi * total / self.volume


    def oneoverq_exact(self, q, order=48):
        """(1/V) int_P 8 pi/|q+p| = (1/V) 8 pi (1/2) sum_f h_f int_f dA/|x|
        (div x/|x| = 2/|x|)."""
        Q = self.U @ np.asarray(q, float)
        total = 0.0
        for n, off, P in self.faces():
            Ps = P + Q
            h = off + n @ Q
            if abs(h) < 1e-15:
                continue
            c = Ps.mean(axis=0)
            for a, b in zip(Ps, np.roll(Ps, -1, axis=0)):
                total += h * _tri_inv_r(c, a, b, order)
        return 8 * np.pi * 0.5 * total / self.volume


def _tri_inv_r(A, B, C, order):
    if order not in _GL:
        _GL[order] = np.polynomial.legendre.leggauss(order)
    t, w = _GL[order]
    u = 0.5 * (t + 1)
    wu = 0.5 * w
    uu, vv = np.meshgrid(u, u, indexing="ij")
    ww = np.outer(wu, wu) * uu
    X = A[None, None, :] + uu[..., None] * (B - A) + (uu * vv)[..., None] * (C - B)
    area2 = np.linalg.norm(np.cross(B - A, C - A))
    return float(np.sum(ww / np.sqrt(np.einsum("ijk,ijk->ij", X, X))) * area2)


def _poly_area(P):
    c = P.mean(axis=0)
    return sum(0.5 * np.linalg.norm(np.cross(a - c, b - c)) for a, b in zip(P, np.roll(P, -1, 0)))


_GL = {}


def _tri_inv_r2(A, B, C, order):
    """int over triangle ABC of dA / |x|^2 (collapsed Gauss-Legendre)."""
    if order not in _GL:
        _GL[order] = np.polynomial.legendre.leggauss(order)
    t, w = _GL[order]
    u = 0.5 * (t + 1)
    wu = 0.5 * w
    uu, vv = np.meshgrid(u, u, indexing="ij")
    ww = np.outer(wu, wu) * uu               # Duffy Jacobian
    s, r = uu, uu * vv
    X = A[None, None, :] + s[..., None] * (B - A) + r[..., None] * (C - B)
    area2 = np.linalg.norm(np.cross(B - A, C - A))
    return float(np.sum(ww / np.einsum("ijk,ijk->ij", X, X)) * area2)
