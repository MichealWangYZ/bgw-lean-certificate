#!/usr/bin/env python3
"""Certified enclosures of the exact mini-BZ Coulomb averages (E1.4).

    ~/bgw-src/pyenv-e1/bin/python bgw/endpoint/certcoulomb.py RUNDIR OUT.json

For every Q = q+G that Sigma uses (the exchange spheres, which contain the
screened ones) it encloses

    vbar(Q)     = (1/V_P) int_P 8 pi / |Q+p|^2 d^3p
    oneoverq(q) = (1/V_P) int_P 8 pi / |q+p|   d^3p      (q of the grid, q != 0)

where P is the Wigner-Seitz cell of the q-lattice in the metric bdot of the
file (the cell the Monte Carlo points are folded into). Method, all exact or
ball arithmetic (python-flint / Arb):

  1. P is built in crystal coordinates with rational arithmetic: half-spaces
     p.B.L <= L.B.L/2 for lattice vectors L, vertices from exact 3x3 solves,
     faces from exact incidences; its crystal volume must equal 1/prod(qgrid).
  2. P+Q is cut into signed cones from the origin over outward-oriented face
     triangles (A,B,C): int_{P+Q} f = sum sign(det[A,B,C]) int_cone f.
     With x = r y(s,t), y = A + s(B-A) + t(C-A), f homogeneous of degree -k:
     int_cone f = |det[A,B,C]| * sqrt(det B) * int_0^1 r^{2-k} dr * J,
     J = int_0^1 ds int_0^{1-s} dt |y|^{-k}; the t-integral is closed form
     (k=2: arctan; k=1: log), the s-integral is Arb's rigorous acb.integral.
     The factor sqrt(det B) cancels against V_P = sqrt(det B) / prod(qgrid).
"""
import itertools
import json
import multiprocessing as mp
import pathlib
import sys
from fractions import Fraction as Fr

import numpy as np
from flint import acb, arb, ctx

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bgwio  # noqa: E402

PREC = 96


# ------------------------------------------------------------ exact cell

def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def dot(u, B, v):
    return sum(u[i] * B[i][j] * v[j] for i in range(3) for j in range(3))


def solve3(M, r):
    d = det3(*M)
    if d == 0:
        return None
    cols = [[M[i][j] for i in range(3)] for j in range(3)]
    out = []
    for j in range(3):
        cj = [list(row) for row in M]
        for i in range(3):
            cj[i][j] = r[i]
        out.append(det3(*cj) / d)
    return out


def ws_cell(B, qgrid):
    dd = [Fr(1, g) for g in qgrid]
    Ls = [tuple(n[i] * dd[i] for i in range(3))
          for n in itertools.product(range(-1, 2), repeat=3) if any(n)]
    planes = [([sum(B[i][j] * L[j] for j in range(3)) for i in range(3)],
               dot(L, B, L) / 2, L) for L in Ls]            # n.p <= h
    verts = set()
    for a, b, c in itertools.combinations(range(len(planes)), 3):
        p = solve3([planes[a][0], planes[b][0], planes[c][0]],
                   [planes[a][1], planes[b][1], planes[c][1]])
        if p is None:
            continue
        if all(sum(n[i] * p[i] for i in range(3)) <= h for n, h, _ in planes):
            verts.add(tuple(p))
    verts = [list(v) for v in verts]
    faces = []
    for n, h, L in planes:
        on = [v for v in verts if sum(n[i] * v[i] for i in range(3)) == h]
        if len(on) >= 3:
            faces.append((n, h, L, on))
    return verts, faces


def order_face(on, L):
    """Cyclic order of a convex face's vertices (float angles), verified exactly."""
    c = [sum(v[i] for v in on) / len(on) for i in range(3)]
    Lf = np.array([float(x) for x in L])
    e1 = np.array([float(on[0][i] - c[i]) for i in range(3)])
    e2 = np.cross(Lf, e1)
    ang = [np.arctan2(np.dot([float(v[i] - c[i]) for i in range(3)], e2),
                      np.dot([float(v[i] - c[i]) for i in range(3)], e1)) for v in on]
    P = [on[i] for i in np.argsort(ang)]
    # exact convexity: all consecutive turns have the same orientation about L
    sg = [det3([P[j][i] - c[i] for i in range(3)],
               [P[(j + 1) % len(P)][i] - c[i] for i in range(3)], list(L)) for j in range(len(P))]
    if not (all(s > 0 for s in sg) or all(s < 0 for s in sg)):
        raise ValueError("face vertices not in convex cyclic order")
    return P


def triangles(faces):
    """Outward-oriented fan triangles of the cell centred at 0 (the interior
    point 0 fixes orientation: det(B-A, C-A, 0-A) < 0)."""
    out = []
    for n, h, L, on in faces:
        P = order_face(on, L)
        for j in range(1, len(P) - 1):
            A, Bv, C = P[0], P[j], P[j + 1]
            s = det3([Bv[i] - A[i] for i in range(3)], [C[i] - A[i] for i in range(3)],
                     [-A[i] for i in range(3)])
            out.append((A, Bv, C) if s < 0 else (A, C, Bv))
    return out


# -------------------------------------------------------- the integrals

def _quad(Ba, A, D, E):
    """|A + s D + t E|^2 = a t^2 + b(s) t + c(s) in arb (exact rational inputs)."""
    a = dot(E, Ba, E)
    b0, b1 = 2 * dot(A, Ba, E), 2 * dot(D, Ba, E)
    c0, c1, c2 = dot(A, Ba, A), 2 * dot(A, Ba, D), dot(D, Ba, D)
    return a, b0, b1, c0, c1, c2


def _atan(u, analytic):
    """atan(u) = (i/2)(log(1 - iu) - log(1 + iu)); `log(analytic=True)` returns
    an indeterminate value on its branch cut, as acb.integral requires."""
    i = acb(0, 1)
    return i / 2 * ((1 - i * u).log(analytic=analytic) - (1 + i * u).log(analytic=analytic))


def cone_J(Bq, A, Bv, C, k):
    """J = int_0^1 ds int_0^{1-s} dt |y(s,t)|^{-k}, enclosed by Arb."""
    D = [Bv[i] - A[i] for i in range(3)]
    E = [C[i] - A[i] for i in range(3)]
    a, b0, b1, c0, c1, c2 = (acb(arb(x.numerator) / x.denominator)
                             for x in _quad(Bq, A, D, E))

    def f(s, analytic):
        b = b0 + b1 * s
        c = c0 + c1 * s + c2 * s * s
        T = 1 - s
        if k == 2:
            disc = (4 * a * c - b * b).sqrt(analytic=analytic)
            u1 = (2 * a * T + b) / disc
            u0 = b / disc
            return 2 / disc * (_atan(u1, analytic) - _atan(u0, analytic))
        sa = a.sqrt(analytic=analytic)
        QT = (a * T * T + b * T + c).sqrt(analytic=analytic)
        Q0 = c.sqrt(analytic=analytic)
        up = (2 * sa * QT + 2 * a * T + b).log(analytic=analytic)
        lo = (2 * sa * Q0 + b).log(analytic=analytic)
        return (up - lo) / sa

    return acb.integral(f, 0, 1).real


def _q(x):
    return arb(x.numerator) / x.denominator


def flat_cone_bound(Bq, A, Bv, C, d, k):
    """Rigorous bound on |d| * radial * J for a nearly flat cone, where the
    integrand's branch point sits too close to the real axis for acb.integral.

    With h the apex-to-plane distance and R >= every |vertex| (so every foot
    distance rho <= R):  int_cone |x|^-2 = h int_T dA/|x|^2 <= h pi ln(1 + R^2/h^2),
    int_cone |x|^-1 = (h/2) int_T dA/|x| <= (h/2) 2 pi R. Also |d| J sqrt(det B)
    = int_cone, and h = |d| sqrt(det B) / (2 Area_cart)."""
    D = [Bv[i] - A[i] for i in range(3)]
    E = [C[i] - A[i] for i in range(3)]
    gram = dot(D, Bq, D) * dot(E, Bq, E) - dot(D, Bq, E) ** 2
    area = _q(gram).sqrt() / 2
    detB = _q(det3(*Bq))
    h = _q(abs(d)) * detB.sqrt() / (2 * area)
    R2 = max(dot(v, Bq, v) for v in (A, Bv, C))
    if k == 2:
        cone = h * arb.pi() * (1 + _q(R2) / (h * h)).log()
    else:
        cone = h * arb.pi() * _q(R2).sqrt()
    b = cone / detB.sqrt()
    return arb(0, b.upper())          # the ball [-b, b]


def average(tris, Bq, Q, k, vol_crys, stats=None):
    """(1/V_P) int_P 8 pi |Q+p|^{-k}: sum over signed cones of P+Q."""
    tot = arb(0)
    for A, Bv, C in tris:
        A2 = [A[i] + Q[i] for i in range(3)]
        B2 = [Bv[i] + Q[i] for i in range(3)]
        C2 = [C[i] + Q[i] for i in range(3)]
        d = det3(A2, B2, C2)
        if d == 0:
            continue                      # the cone is flat: contributes nothing
        J = cone_J(Bq, A2, B2, C2, k)
        radial = arb(1) if k == 2 else arb(1) / 2
        if J.is_finite():
            tot += _q(abs(d)) * (1 if d > 0 else -1) * radial * J
        else:
            tot += flat_cone_bound(Bq, A2, B2, C2, d, k)
            if stats is not None:
                stats.append(float(abs(d)))
    return 8 * arb.pi() * tot / (arb(vol_crys.numerator) / vol_crys.denominator)


# ------------------------------------------------------------- the job

_G = {}


def _init(Bq, tris, vol):
    ctx.prec = PREC
    _G.update(Bq=Bq, tris=tris, vol=vol)


def _work(item):
    key, Q, k = item
    flat = []
    v = average(_G["tris"], _G["Bq"], Q, k, _G["vol"], flat)
    lo, hi = v.lower(), v.upper()
    # float endpoints rounded outward
    flo = np.nextafter(float(lo.mid()), -np.inf)
    fhi = np.nextafter(float(hi.mid()), np.inf)
    assert arb(flo) <= lo and arb(fhi) >= hi
    return key, k, flo, fhi, v.str(20, radius=True), flat


def main(rundir, out):
    ctx.prec = PREC
    w = bgwio.read_wfn(pathlib.Path(rundir) / "WFN_inner")
    eps = bgwio.read_eps(pathlib.Path(rundir) / "epsmat")
    qgrid = [int(x) for x in eps["qgrid"]]
    Bq = [[Fr(float(w["bdot"][i][j])) for j in range(3)] for i in range(3)]
    verts, faces = ws_cell(Bq, qgrid)
    tris = triangles(faces)
    vol = Fr(1, int(np.prod(qgrid)))
    # exact volume check: signed cones of P itself
    V = sum(det3(*t) for t in tris) / 6
    if V != vol:
        raise ValueError(f"cell volume {V} != {vol}")
    gvec = w["gvec"]
    ecutb = float(w["ecutwfc"])
    items = []
    for i, j, l in itertools.product(*(range(g) for g in qgrid)):
        q = (Fr(i, qgrid[0]), Fr(j, qgrid[1]), Fr(l, qgrid[2]))
        qf = np.array([float(x) for x in q])
        n2 = np.einsum("ni,ij,nj->n", qf + gvec, w["bdot"], qf + gvec)
        for g in gvec[n2 < ecutb]:
            Q = tuple(q[t] + int(g[t]) for t in range(3))
            items.append((tuple(str(x) for x in Q), Q, 2))
        if any(q):
            items.append((tuple(str(x) for x in q), q, 1))
    with mp.Pool(16, initializer=_init, initargs=(Bq, tris, vol)) as pool:
        res = pool.map(_work, items, chunksize=4)
    doc = {"method": __doc__.strip().splitlines()[0], "prec": PREC,
           "n_vertices": len(verts), "n_faces": len(faces), "n_triangles": len(tris),
           "bdot": [[float(x) for x in r] for r in w["bdot"]], "qgrid": qgrid,
           "vbar": {}, "oneoverq": {}}
    nflat = 0
    for key, k, lo, hi, s, flat in res:
        (doc["vbar"] if k == 2 else doc["oneoverq"])[",".join(key)] = [lo, hi, s]
        nflat += len(flat)
    doc["n_flat_cone_bounds"] = nflat
    pathlib.Path(out).write_text(json.dumps(doc, indent=1) + "\n")
    widths = [(h - l) / abs(l + h) * 2 for l, h, _ in doc["vbar"].values()]
    print(f"{len(doc['vbar'])} vbar, {len(doc['oneoverq'])} oneoverq; "
          f"max relative width {max(widths):.2e}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
