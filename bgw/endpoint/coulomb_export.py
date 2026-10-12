#!/usr/bin/env python3
"""G2-coulomb: kernel certificates for the mini-BZ Coulomb averages.

    python3 bgw/endpoint/coulomb_export.py [--check] [--lean] [--only N]

For every key Q of coulomb_cert.json (vbar: k = 2, oneoverq: k = 1) the Lean side
proves  (1/|P|) int_P 8 pi |Q+p|_B^{-k} dp  in the box of the file, where P is the
Wigner-Seitz cell of the q-lattice in crystal coordinates (26 half-spaces, exact
dyadic metric B of the file).  The Lean proof (GW/Endpoint/Coulomb/) reduces the
average, exactly, to

    64 pi/(3-k) * sum_tau det(A+Q, B+Q, C+Q) * J_tau(Q),
    J_tau(Q) = int_{Delta2} |A+Q + s1 (B-A) + s2 (C-A)|_B^{-k} ds,

over the 72 outer triangles tau = (c_F, V_j, V_{j+1}) of the face fans of P
(signed cones from the origin).  This module plans, for every orbit
representative Q, a quadtree of each Delta2 whose leaves carry a
Grundmann-Moller rule of odd degree d and a hint tn (t <= tn / 2^16); the Lean
checker recomputes every node value with exact integers, bounds the Taylor
remainder by phi_d(t) = ((d+2) t^(d+1) + (d+1) t^(d+2)) / (1-t)^2 and only
compares.  `mirror_*` below is the exact Python image of the Lean checker; a
failed mirror means the Lean check would fail, never that it would pass.
"""
import argparse
import itertools
import json
import math
import pathlib
import sys
from fractions import Fraction as Fr
from math import comb, factorial

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))

SB = 54
KB = 300          # fixed-point bits of the node values (k = 2)
KB1 = 200         # fixed-point bits of the square roots (k = 1)
TB = 16           # bits of the t hints
DEGS = list(range(3, 24, 2))


# ------------------------------------------------------------------ geometry

def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def load_B():
    d = json.loads((HERE / "data/coulomb_cert.json").read_text())
    Bf = [[Fr(x) for x in r] for r in d["bdot"]]
    Bi = [[int(x * 2 ** SB) for x in r] for r in Bf]
    assert all(Fr(Bi[i][j], 2 ** SB) == Bf[i][j] for i in range(3) for j in range(3))
    return d, Bf, Bi


def cell(Bf):
    from certcoulomb import ws_cell, order_face
    verts, faces = ws_cell(Bf, [2, 2, 2])
    out = []
    for n, h, L, on in faces:
        P = order_face(on, L)
        c = [sum(v[i] for v in P) / len(P) for i in range(3)]
        for j in range(len(P)):
            a, b = P[j], P[(j + 1) % len(P)]
            if det3(c, a, b) < 0:
                a, b = b, a
            assert det3(c, a, b) > 0
            out.append((tuple(L), tuple(c), tuple(a), tuple(b)))
    return verts, faces, out


class Geo:
    def __init__(self):
        self.doc, self.Bf, self.Bi = load_B()
        self.verts, self.faces, self.tris = cell(self.Bf)
        dens = [x.denominator for t in self.tris for v in t[1:] for x in v] + [2]
        self.Dv = math.lcm(*dens)
        self.tri_int = [tuple(tuple(int(x * self.Dv) for x in v) for v in t[1:]) for t in self.tris]

    def beta(self, u, v):
        return sum(u[i] * self.Bi[i][j] * v[j] for i in range(3) for j in range(3))


# -------------------------------------------------------------- GM rules

def comps(total, parts):
    if parts == 1:
        yield (total,)
        return
    for i in range(total + 1):
        for r in comps(total - i, parts - 1):
            yield (i,) + r


def gm_rule(d):
    """Grundmann-Moller rule of degree d = 2s+1 on {s1,s2 >= 0, s1+s2 <= 1}:
    nodes (a/m, b/m), weights W/Wd."""
    s = (d - 1) // 2
    nodes = []
    for i in range(s + 1):
        M = d + 2 - 2 * i
        w = Fr((-1) ** i * M ** d, 2 ** (2 * s) * factorial(i) * factorial(d + 2 - i))
        for b in comps(s - i, 3):
            nodes.append((2 * b[1] + 1, 2 * b[2] + 1, M, w))
    Wd = math.lcm(*[w.denominator for *_, w in nodes])
    return [(a, b, m, int(w * Wd)) for a, b, m, w in nodes], Wd


RULES = {d: gm_rule(d) for d in range(3, 32, 2)}
WC = math.lcm(*[gm_rule(d)[1] for d in range(3, 32, 2)])
RULESC = {d: [(a, b, m, W * (WC // Wd)) for a, b, m, W in RULES[d][0]] for d, (nd, Wd) in RULES.items()}
GABS = {d: sum(abs(W) for *_, W in RULESC[d]) for d in RULESC}      # sum |w| = GABS / WC


def check_rule(d):
    nodes, Wd = RULES[d]
    for a1 in range(d + 1):
        for a2 in range(d + 1 - a1):
            lhs = sum(Fr(W, Wd) * Fr(a, m) ** a1 * Fr(b, m) ** a2 for a, b, m, W in nodes)
            if lhs != Fr(factorial(a1) * factorial(a2), factorial(a1 + a2 + 2)):
                return False
    return True


# ----------------------------------------------------------- per triangle

def qcoef(g, t, Q2):
    """Integer quadratic coefficients of |y(s)|_B^2 * Dv^2 * 2^SB for y(s) =
    A+Q + s1 (B-A) + s2 (C-A); Q = Q2/2 (Q2 integer key)."""
    A, Bv, C = t
    h = g.Dv // 2
    a0 = [A[i] + Q2[i] * h for i in range(3)]
    d1 = [Bv[i] - A[i] for i in range(3)]
    d2 = [C[i] - A[i] for i in range(3)]
    return (g.beta(a0, a0), g.beta(a0, d1), g.beta(a0, d2), g.beta(d1, d1), g.beta(d1, d2),
            g.beta(d2, d2)), det3(a0, [A[i] + d1[i] + Q2[i] * h for i in range(3)],
                                   [A[i] + d2[i] + Q2[i] * h for i in range(3)])


def leafL(qc, j, p1, p2, e):
    Q00, Q01, Q02, Q11, Q12, Q22 = qc
    H = 1 << j
    L00 = Q00 * H * H + 2 * Q01 * p1 * H + 2 * Q02 * p2 * H + Q11 * p1 * p1 + 2 * Q12 * p1 * p2 + Q22 * p2 * p2
    L01 = e * (Q01 * H + Q11 * p1 + Q12 * p2)
    L02 = e * (Q02 * H + Q12 * p1 + Q22 * p2)
    return L00, L01, L02, Q11, Q12, Q22


def nodeN(L, a, b, m):
    L00, L01, L02, L11, L12, L22 = L
    return m * m * L00 + 2 * m * (a * L01 + b * L02) + a * a * L11 + 2 * a * b * L12 + b * b * L22


def rmax(L):
    _, _, _, L11, L12, L22 = L
    return max(u * u * L11 + 2 * u * v * L12 + v * v * L22 for u, v in ((-1, -1), (2, -1), (-1, 2)))


def phi(d, t):
    return ((d + 2) * t ** (d + 1) + (d + 1) * t ** (d + 2)) / (1 - t) ** 2


def phiQ(d, tn):
    """phi_d(tn / 2^TB) = pn / pd exactly."""
    T = 1 << TB
    return (d + 2) * tn ** (d + 1) * T + (d + 1) * tn ** (d + 2), T ** d * (T - tn) ** 2


# children of the 4-way split: (dp1, dp2, flip) in units of the child's scale
CHILD = ((0, 0, False), (1, 0, False), (0, 1, False), (1, 1, True))


def child(j, p1, p2, e, c):
    """Leaf map sigma = (p1, p2)/2^j + e sigma'/2^j; child c of it."""
    dp1, dp2, fl = CHILD[c]
    return j + 1, 2 * p1 + e * dp1, 2 * p2 + e * dp2, (-e if fl else e)


def tn_hint(L):
    Nc = nodeN(L, 1, 1, 3)
    R = rmax(L)
    assert Nc > 0
    # smallest tn with tn^2 Nc >= 2^(2TB) R
    tn = math.isqrt((R << (2 * TB)) // Nc)
    while tn * tn * Nc < (R << (2 * TB)):
        tn += 1
    return tn, Nc


def plan_tri(qc, k, errleaf, j=0, p1=0, p2=0, e=1, depth=0):
    """Quadtree: ('L', d, tn) or ('N', [4 children]).  errleaf is in units of
    J (the Delta2 integral); leaf error = h^2 (1/2 + sum|w|) phi / |c|^k."""
    L = leafL(qc, j, p1, p2, e)
    tn, Nc = tn_hint(L)
    H = 1 << j
    t = tn / (1 << TB)
    if t < 0.95:
        qcr = Nc / 9.0 / (H * H)          # |c|^2 in units of 1/(Dv^2 2^SB)
        best = None
        for d in DEGS:
            err = (0.5 + GABS[d] / WC) * phi(d, t) * qcr ** (-k / 2) / (H * H)
            if err <= 0.7 * errleaf and (best is None or len(RULESC[d]) < len(RULESC[best])):
                best = d
        if best is not None:
            return ('L', best, tn)
    assert depth < 14
    return ('N', [plan_tri(qc, k, errleaf, *child(j, p1, p2, e, c), depth + 1) for c in range(4)])


def isqrt_floor(n):
    return math.isqrt(n)


def mirror_tri(qc, k, tree, j=0, p1=0, p2=0, e=1):
    """Exact enclosure [lo, hi] of 2^KB * X where J = X / U_k,
    U_2 = WC / (Dv^2 2^SB), U_1 = WC / (Dv 2^(SB/2)); returns (lo, hi, nodes)."""
    if tree[0] == 'N':
        lo = hi = n = 0
        for c in range(4):
            a, b, m = mirror_tri(qc, k, tree[1][c], *child(j, p1, p2, e, c))
            lo += a; hi += b; n += m
        return lo, hi, n
    _, d, tn = tree
    L = leafL(qc, j, p1, p2, e)
    Nc = nodeN(L, 1, 1, 3)
    assert tn < (1 << TB) and tn * tn * Nc >= (rmax(L) << (2 * TB))
    pn, pd = phiQ(d, tn)
    lo = hi = 0
    H = 1 << j
    for a, b, m, W in RULESC[d]:
        N = nodeN(L, a, b, m)
        assert N > 0
        if k == 2:
            fl = (abs(W) * m * m << KB) // N
        else:
            # f = m H Dv 2^(SB/2) / sqrt(N); h^2 f = m Dv 2^(SB/2) / (H sqrt(N))
            M = (1 << (2 * KB1)) // N          # M <= 2^2KB1 / N < M + 1
            r = math.isqrt(M)                  # r <= 2^KB1 / sqrt(N) < r + 1
            fl = (abs(W) * m * r) >> j
            ce = (abs(W) * m * (r + 1) + (1 << j) - 1) >> j
        if k == 2:
            ce = fl + 1
        if W >= 0:
            lo += fl; hi += ce
        else:
            lo -= ce; hi -= fl
    # remainder: (WC/2 + GABS) * phi / |c|^k * h^2 in the same units
    G2 = WC + 2 * GABS[d]                     # 2 (WC/2 + GABS)
    if k == 2:
        # h^2 (1/2 + sum|w|) phi / |c|^2 = (1/WC) (G2/2) phi 9 / Nc  [units Dv^2 2^SB]
        err = -(-(9 * G2 * pn << KB) // (2 * pd * Nc))
    else:
        # h^2 (..) phi / |c| = (1/WC)(G2/2) phi 3 / (H sqrt(Nc)) [units Dv 2^(SB/2)]
        M = (1 << (2 * KB1)) // Nc
        r = math.isqrt(M)
        err = -(-(3 * G2 * pn * (r + 1)) // (2 * pd * H))
    return lo - err, hi + err, len(RULESC[d])


# ------------------------------------------------------------- cell data

def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


NS = [n for n in itertools.product((-1, 0, 1), repeat=3) if any(n)]


def geom_data(g):
    """The 72 tetrahedra (c, a, b), adjugate rows, lifted forms W, neighbours and the
    single-term certificates checked by `GeomDefs.geomOK`."""
    tr = g.tri_int
    out = []
    dets = [det3(*t) for t in tr]
    adj = [[cross(t[1], t[2]), cross(t[2], t[0]), cross(t[0], t[1])] for t in tr]
    W = [tuple(7 * a[0][m] + 8 * a[1][m] + 8 * a[2][m] for m in range(3)) for a in adj]
    key = lambda i, k: frozenset(v for j, v in enumerate(tr[i]) if j != k)
    for i, t in enumerate(tr):
        assert dets[i] > 0
        nb, nk, kap = [], [], []
        for k in range(3):
            (n, k2), = [(i2, k2) for i2 in range(72) for k2 in range(3) if i2 != i and key(i2, k2) == key(i, k)]
            nb.append(n); nk.append(k2)
            lhs = [Fr(adj[i][k][m], dets[i]) for m in range(3)]
            rhs = [Fr(W[i][m], dets[i]) - Fr(W[n][m], dets[n]) for m in range(3)]
            ks = {l / r for l, r in zip(lhs, rhs) if r != 0}
            assert len(ks) == 1 and all((l == 0) == (r == 0) for l, r in zip(lhs, rhs))
            kv = ks.pop(); assert kv > 0
            kap.append((kv.numerator, kv.denominator))
        e = None
        for fi, n in enumerate(NS):
            ev = [sum(g.Bi[a][b] * n[b] for b in range(3)) for a in range(3)]
            H = sum(n[a] * ev[a] for a in range(3))
            if all(g.Dv * (adj[i][0][m] + adj[i][1][m] + adj[i][2][m]) * H == 4 * dets[i] * ev[m] for m in range(3)):
                e = fi
        assert e is not None
        out.append(dict(c=t[0], a=t[1], b=t[2], d=dets[i], q=adj[i], W=W[i], nb=nb, nk=nk, kap=kap, f=e))
    return out


def lean_iv(v):
    return f"⟨{v[0]}, {v[1]}, {v[2]}⟩"


def lean_geom(g, path):
    ts = geom_data(g)
    L = ["/- Generated by bgw/endpoint/coulomb_export.py --lean (do not edit): the cell data. -/",
         "import GW.Endpoint.Coulomb.GeomDefs", "", "namespace GW.Endpoint.Coulomb", "",
         f"def Dvc : Int := {g.Dv}", "",
         "def Bint : IM := ⟨" + ", ".join(lean_iv(r) for r in g.Bi) + "⟩", "",
         "def cellNs : List IV := [" + ", ".join(lean_iv(n) for n in NS) + "]", ""]
    for i, t in enumerate(ts):
        L.append(f"def td{i} : TD := ⟨{lean_iv(t['c'])}, {lean_iv(t['a'])}, {lean_iv(t['b'])}, {t['d']}, "
                 f"{lean_iv(t['q'][0])}, {lean_iv(t['q'][1])}, {lean_iv(t['q'][2])}, {lean_iv(t['W'])}, "
                 f"{t['nb'][0]}, {t['nb'][1]}, {t['nb'][2]}, {t['nk'][0]}, {t['nk'][1]}, {t['nk'][2]}, "
                 f"{t['kap'][0][0]}, {t['kap'][0][1]}, {t['kap'][1][0]}, {t['kap'][1][1]}, "
                 f"{t['kap'][2][0]}, {t['kap'][2][1]}, {t['f']}⟩")
    L.append("")
    L.append("def cellTs : List TD := [" + ", ".join(f"td{i}" for i in range(len(ts))) + "]")
    L += ["", "end GW.Endpoint.Coulomb", ""]
    pathlib.Path(path).write_text("\n".join(L))


# ------------------------------------------------------------- per Q

class Planner:
    def __init__(self, g):
        self.g = g

    def tris_Q(self, Q2):
        out = []
        for i, t in enumerate(self.g.tri_int):
            qc, dt = qcoef(self.g, t, Q2)
            if dt != 0:
                out.append((i, qc, dt))
        return out

    def value_float(self, Q2, k):
        """Rough value (float) for planning: 64 pi/(3-k) sum det J (centroid rule)."""
        g = self.g
        tot = 0.0
        for i, qc, dt in self.tris_Q(Q2):
            L = leafL(qc, 0, 0, 0, 1)
            J = 0.5 * (nodeN(L, 1, 1, 3) / 9.0) ** (-k / 2)
            tot += dt * J
        scale = (g.Dv ** 2 * 2 ** SB) if k == 2 else (g.Dv * 2 ** (SB / 2))
        return 64 * math.pi / (3 - k) * tot / g.Dv ** 3 * scale

    def plan(self, Q2, k, budget):
        """budget: allowed absolute error of the average."""
        g = self.g
        tr = self.tris_Q(Q2)
        scale = (g.Dv ** 2 * 2 ** SB) if k == 2 else (g.Dv * 2 ** (SB / 2))
        # |avg error| <= 64 pi/(3-k) sum |det|/Dv^3 * scale * err_J ; err_J per tri <= errleaf-sum
        A = 64 * math.pi / (3 - k) * sum(abs(dt) for _, _, dt in tr) / g.Dv ** 3 * scale
        errJ = budget / A                       # per-triangle J error (units of J / scale)
        # leaves: sum over leaves of leaf error <= errJ; a leaf of depth j gets errJ * 4^-j
        trees = []
        for i, qc, dt in tr:
            trees.append((i, dt, self._plan(qc, k, errJ)))
        return trees

    def _plan(self, qc, k, errJ, j=0, p1=0, p2=0, e=1):
        L = leafL(qc, j, p1, p2, e)
        tn, Nc = tn_hint(L)
        H = 1 << j
        t = tn / (1 << TB)
        if t < 0.95:
            qcr = Nc / 9.0 / (H * H)
            best = None
            for d in DEGS:
                err = (0.5 + GABS[d] / WC) * phi(d, t) * qcr ** (-k / 2) / (H * H)
                if err <= 0.7 * errJ / (H * H) and (best is None or len(RULESC[d]) < len(RULESC[best])):
                    best = d
            if best is not None:
                return ('L', best, tn)
        assert j < 14
        return ('N', [self._plan(qc, k, errJ, *child(j, p1, p2, e, c)) for c in range(4)])

    def mirror(self, Q2, k, trees):
        """Exact rational enclosure [lo, hi] of the average."""
        g = self.g
        slo = shi = 0
        nodes = 0
        qcs = {i: (qc, dt) for i, qc, dt in self.tris_Q(Q2)}
        for i, dt, tree in trees:
            qc, dt2 = qcs[i]
            assert dt == dt2
            lo, hi, n = mirror_tri(qc, k, tree)
            nodes += n
            if dt > 0:
                slo += dt * lo; shi += dt * hi
            else:
                slo += dt * hi; shi += dt * lo
        # J = X / U_k with X = value / 2^KB
        if k == 2:
            unit = Fr(g.Dv ** 2 * 2 ** SB, WC * 2 ** KB)
        else:
            unit = Fr(g.Dv * 2 ** (SB // 2), WC * 2 ** KB1)
        c = Fr(64, (3 - k) * g.Dv ** 3) * unit
        return slo * c, shi * c, nodes          # times pi


# ------------------------------------------------------------- Lean emission

LEAN_DEGS = list(range(3, 24, 2))
G12 = [((0, 1, 2), False), ((0, 2, 1), False), ((1, 0, 2), False), ((1, 2, 0), False), ((2, 0, 1), False),
       ((2, 1, 0), False), ((0, 1, 2), True), ((0, 2, 1), True), ((1, 0, 2), True), ((1, 2, 0), True),
       ((2, 0, 1), True), ((2, 1, 0), True)]


def actK(g, key):
    perm, neg = g
    s = -1 if neg else 1
    return tuple(s * key[perm[i]] for i in range(3))


def denN(k):
    return 2 ** 246 * WC * DV_GLOBAL if k == 2 else 2 ** 174 * WC * DV_GLOBAL ** 2


def boxOK(N, SV, SL, SH, lo, hi):
    return (SL >= 0 and N > 0 and lo * N * 10 ** 20 <= 64 * 314159265358979323846 * SL * 2 ** SV
            and 64 * 314159265358979323847 * SH * 2 ** SV <= hi * N * 10 ** 20)


def tree_lean(t):
    if t[0] == 'L':
        return f"(.leaf {t[1]} {t[2]})"
    return "(.node " + " ".join(tree_lean(c) for c in t[1]) + ")"


def rep_faces(g, ts, key, k, trees):
    """[(tree, lo, hi) or None] for the 72 faces, with the Lean integer sums."""
    tmap = {i: tree for i, dt, tree in trees}
    out = []
    SL = SH = 0
    for i, t in enumerate(ts):
        kv = [key[0], key[1], key[2]]
        qs = [t['q'][0][m] + t['q'][1][m] + t['q'][2][m] for m in range(3)]
        al = 2 * t['d'] + g.Dv * sum(qs[m] * kv[m] for m in range(3))
        h = g.Dv // 2
        nc = [tuple(t[c][m] + h * kv[m] for m in range(3)) for c in ('c', 'a', 'b')]
        dN = det3(*nc)
        if al == 0:
            assert dN == 0 and i not in tmap
            out.append(None)
            continue
        assert dN != 0 and i in tmap
        qc, dt = qcoef(g, g.tri_int[i], key)
        assert dt == dN
        lo, hi, nn = mirror_tri(qc, k, tmap[i])
        cN = (1 if al > 0 else -1) * abs(dN)
        if cN >= 0:
            SL += cN * lo; SH += cN * hi
        else:
            SL += cN * hi; SH += cN * lo
        out.append((tmap[i], lo, hi, nn))
    return out, SL, SH


PI_LO = Fr(314159265358979323846, 10 ** 20)
PI_HI = Fr(314159265358979323847, 10 ** 20)


def orbits(doc, tab):
    G = []
    for perm in itertools.permutations(range(3)):
        for sg in (1, -1):
            G.append((perm, sg))

    def act(gp, v):
        perm, sg = gp
        return tuple(sg * v[perm[i]] for i in range(3))
    orb = {}
    for key in doc[tab]:
        Q2 = tuple(int(2 * Fr(x)) for x in key.split(','))
        rep = min(act(gp, Q2) for gp in G)
        orb.setdefault(rep, []).append(key)
    return orb


DATA = ROOT / "GW/Endpoint/Kernel/Data"
NS_LEAN = "GW.Endpoint.Kernel.Coul"
MAXN = 110000


def plan_all(g, cache):
    """Plan every orbit representative of both tables; cached (pickle)."""
    import pickle
    if cache and pathlib.Path(cache).exists():
        return pickle.loads(pathlib.Path(cache).read_bytes())
    pl = Planner(g)
    doc = g.doc
    out = {}
    for tab, k in (("vbar", 2), ("oneoverq", 1)):
        orb = orbits(doc, tab)
        reps = sorted(orb, key=lambda q: (sum(x * x for x in q), q))
        res = []
        for rep in reps:
            mem = orb[rep]
            lo = max(Fr(doc[tab][m][0]) for m in mem)
            hi = min(Fr(doc[tab][m][1]) for m in mem)
            v = pl.value_float(rep, k)
            t1 = pl.plan(rep, k, 1e-13 * v)
            a, b, _ = pl.mirror(rep, k, t1)
            v = float((a * PI_LO + b * PI_HI) / 2)
            budget = 0.85 * min(v - float(lo), float(hi) - v)
            trees = pl.plan(rep, k, budget)
            L, H, n = pl.mirror(rep, k, trees)
            assert lo <= L * PI_LO and H * PI_HI <= hi, (tab, rep)
            res.append((rep, trees, n))
            print(tab, rep, n, flush=True)
        out[tab] = res
    if cache:
        pathlib.Path(cache).write_bytes(pickle.dumps(out))
    return out


def lean_faces(fs):
    parts = []
    for f in fs:
        parts.append("dFace" if f is None else f"({tree_lean(f[0])}, {f[1]}, {f[2]})")
    return "[" + ",\n  ".join(parts) + "]"


def emit_lean(g, plans, SV=51):
    global DV_GLOBAL
    DV_GLOBAL = g.Dv
    ts = geom_data(g)
    doc = g.doc
    chain = []
    # rule certificates
    L = [f"/- Generated by bgw/endpoint/coulomb_export.py --lean (do not edit): the GM rule certificates. -/",
         "import GW.Endpoint.Coulomb.CheckDefs", "", f"namespace {NS_LEAN}", "open GW.Endpoint.Coulomb", ""]
    for d in LEAN_DEGS:
        L.append(f"theorem rn{d} : nodesOK (gmM {d}) (gmRule {d}) = true := by decide +kernel")
        for i in range(d + 1):
            L.append(f"theorem rr{d}_{i} : ruleRow {d} WCc (gmM {d}) (gmRule {d}) {i} = true := by decide +kernel")
    L += ["", f"end {NS_LEAN}", ""]
    (DATA / "CoulRules.lean").write_text("\n".join(L))
    chain.append("CoulRules")
    reps_out = {}
    for tab, k, tag in (("vbar", 2, "V"), ("oneoverq", 1, "O")):
        reps_out[tab] = []
        for j, (rep, trees, n) in enumerate(plans[tab]):
            fs, SL, SH = rep_faces(g, ts, rep, k, trees)
            name = f"Coul{tag}{j}"
            key = f"({rep[0]}, {rep[1]}, {rep[2]})"
            # chunks of at most MAXN cubature nodes per module (the kernel's memory grows per module)
            chunks, cur, cn = [], [], 0
            for i, f in enumerate(fs):
                w = 0 if f is None else f[3]
                if cur and cn + w > MAXN:
                    chunks.append(cur); cur, cn = [], 0
                cur.append(i); cn += w
            chunks.append(cur)
            for c, idxs in enumerate(chunks):
                mod = name if c == 0 else f"{name}_{c}"
                L = [f"/- Generated by bgw/endpoint/coulomb_export.py --lean (do not edit): {tab} at key {key}"
                     f" ({n} cubature nodes), faces {idxs[0]}-{idxs[-1]}. -/",
                     f"import GW.Endpoint.Kernel.Data.{chain[-1]}", "import GW.Endpoint.Coulomb.Core", "",
                     f"namespace {NS_LEAN}", "open GW.Endpoint.Coulomb", ""]
                if c == 0:
                    L += [f"def fs{tag}{j} : List (QT × Int × Int) :=\n  {lean_faces(fs)}", ""]
                for i in idxs:
                    L.append(f"theorem f{tag}{j}_{i} : faceChkC {key} {k} (fs{tag}{j}.getD {i} dFace) {i} = true := "
                             "by decide +kernel")
                if c == len(chunks) - 1:
                    L.append(f"theorem sl{tag}{j} : sumLoC {key} fs{tag}{j} = {SL} := by decide +kernel")
                    L.append(f"theorem sh{tag}{j} : sumHiC {key} fs{tag}{j} = {SH} := by decide +kernel")
                L += ["", f"end {NS_LEAN}", ""]
                (DATA / f"{mod}.lean").write_text("\n".join(L))
                chain.append(mod)
            reps_out[tab].append((rep, SL, SH))
    # table + composition
    def hints(tab, k):
        reps = reps_out[tab]
        idx = {r[0]: j for j, r in enumerate(reps)}
        out = []
        N = denN(k)
        for key_s, (lo, hi, _) in doc[tab].items():
            key = tuple(int(2 * Fr(x)) for x in key_s.split(","))
            lo_i, hi_i = int(Fr(lo) * 2 ** SV), int(Fr(hi) * 2 ** SV)
            assert Fr(lo_i, 2 ** SV) == Fr(lo) and Fr(hi_i, 2 ** SV) == Fr(hi)
            found = None
            for gi, gg in enumerate(G12):
                for rk, j in idx.items():
                    if actK(gg, rk) == key:
                        found = (j, gi)
                        break
                if found:
                    break
            j, gi = found
            _, SL, SH = reps[j]
            assert boxOK(N, SV, SL, SH, lo_i, hi_i), (tab, key)
            out.append(found)
        return out
    hv, ho = hints("vbar", 2), hints("oneoverq", 1)

    def match72(tag, j):
        br = "\n".join(f"    | ⟨{i}, _⟩ => f{tag}{j}_{i}" for i in range(72))
        return f"fun i => match i with\n{br}\n    | ⟨n + 72, h⟩ => absurd h (by omega)"

    L = ["/- Generated by bgw/endpoint/coulomb_export.py --lean (do not edit): the Coulomb tables of",
         "stage 3 discharged (`VbHyp`), and the unconditional O1 enclosure. -/",
         f"import GW.Endpoint.Kernel.Data.{chain[-1]}", "import GW.Endpoint.Coulomb.Table",
         "import GW.Endpoint.Kernel.Data.S3Check", "", f"namespace {NS_LEAN}",
         "open GW.Endpoint.Coulomb GW.Endpoint.Kernel GW.Endpoint.Kernel.Sig", ""]
    L.append("/-- Every Grundmann–Möller rule the checker accepts is exact on all monomials of its degree. -/")
    L.append("theorem deg_ok : ∀ d ∈ degList, ruleOK d WCc (gmM d) (gmRule d) = true := by")
    L.append("  intro d hd")
    L.append("  simp only [degList, List.mem_cons, List.not_mem_nil, or_false] at hd")
    L.append("  rcases hd with " + " | ".join("rfl" for _ in LEAN_DEGS))
    for d in LEAN_DEGS:
        br = "\n".join(f"      | {i}, _ => rr{d}_{i}" for i in range(d + 1))
        L.append(f"  · exact ruleOK_of_rows {d} rn{d} (by decide) (fun i hi => match i, hi with\n{br}\n"
                 f"      | n + {d + 1}, h => absurd h (by omega))")
    L.append("")
    for tab, k, tag in (("vbar", 2, "V"), ("oneoverq", 1, "O")):
        kk = "(Or.inr rfl)" if k == 2 else "(Or.inl rfl)"
        for j, (rep, SL, SH) in enumerate(reps_out[tab]):
            key = f"({rep[0]}, {rep[1]}, {rep[2]})"
            L.append(f"theorem rep{tag}{j} : RepOK {k} ⟨{key}, {SL}, {SH}⟩ :=")
            L.append(f"  rep_of_faces {key} {kk} deg_ok fs{tag}{j} ({match72(tag, j)}) sl{tag}{j} sh{tag}{j}")
            L.append("")
        lst = ", ".join(f"⟨({r[0][0]}, {r[0][1]}, {r[0][2]}), {r[1]}, {r[2]}⟩" for r in reps_out[tab])
        L.append(f"def reps{tag} : List Rep := [{lst}]")
        nested = "List.forall_mem_nil _"
        for j in reversed(range(len(reps_out[tab]))):
            nested = f"List.forall_mem_cons.2 ⟨rep{tag}{j}, {nested}⟩"
        L.append(f"theorem reps{tag}_ok : ∀ r ∈ reps{tag}, RepOK {k} r :=\n  {nested}")
        hs = hv if tab == "vbar" else ho
        L.append(f"def hints{tag} : List (ℕ × ℕ) := [" + ", ".join(f"({a}, {b})" for a, b in hs) + "]")
        T = "S3.vbT" if tab == "vbar" else "S3.oqT"
        L.append(f"theorem tab{tag} : tabChk {k} {SV} reps{tag} {T} hints{tag} = true := by decide +kernel")
        L.append("")
    brows = ", ".join("[" + ", ".join(str(x) for x in r) + "]" for r in g.Bi)
    L += ["theorem SV_eq : S3.eg.SV = 51 := rfl", "",
          "/-- The metric of the averages is the one stage 3 uses (`gl.B / 2^gl.SB`). -/",
          f"theorem metric_same : S3.gl.B = [{brows}] ∧ S3.gl.SB = {SB} ∧",
          "    Bint = ⟨⟨" + ", ".join(str(x) for x in g.Bi[0]) + "⟩, ⟨" + ", ".join(str(x) for x in g.Bi[1]) +
          "⟩, ⟨" + ", ".join(str(x) for x in g.Bi[2]) + "⟩⟩ := by decide +kernel", "",
          "/-- **`VbHyp` discharged**: every Coulomb box of stage 3 contains the true mini-BZ average",
          "`vbar(Q) = (1/|P|) ∫_P 8π/|Q+p|²_B dp` (`Q = key/2`, `P` the Wigner–Seitz cell of the q-grid). -/",
          "theorem vb_hyp : VbHyp S3.vbT S3.eg.SV vbTrue := by",
          "  rw [SV_eq]; intro p hp; exact tab_sound repsV_ok S3.vbT hintsV tabV p hp", "",
          "/-- The same for the wing averages `oneoverq(q) = (1/|P|) ∫_P 8π/|q+p|_B dp`. -/",
          "theorem oq_hyp : VbHyp S3.oqT S3.eg.SV oqTrue := by",
          "  rw [SV_eq]; intro p hp; exact tab_sound repsO_ok S3.oqT hintsO tabO p hp", "",
          "/-- **O1 of spec A, unconditional**: with the true mini-BZ Coulomb averages (no hypothesis left). -/",
          "theorem o1_enclosure_unconditional :",
          "    O1 S3.gl S3.stX S3.stL S3.Etrue vbTrue oqTrue ∈",
          "      Set.Icc ((8880811588953599 : ℝ) / 2 ^ 59) ((8880812351936001 : ℝ) / 2 ^ 59) :=",
          "  S3.o1_enclosure vbTrue oqTrue vb_hyp oq_hyp", "",
          "theorem o1_pos_unconditional : 0 < O1 S3.gl S3.stX S3.stL S3.Etrue vbTrue oqTrue :=",
          "  S3.o1_pos vbTrue oqTrue vb_hyp oq_hyp", "", f"end {NS_LEAN}", ""]
    (DATA / "CoulTab.lean").write_text("\n".join(L))
    # negative controls: a certified face with its lower bound raised by one unit, and a table
    # entry whose box is collapsed to its lower end
    rep, trees, n = plans["vbar"][-1]
    fs, SL, SH = rep_faces(g, ts, rep, 2, trees)
    i0 = next(i for i, f in enumerate(fs) if f is not None)
    f0 = fs[i0]
    key = f"({rep[0]}, {rep[1]}, {rep[2]})"
    lo_e, hi_e, _ = doc["vbar"][next(iter(doc["vbar"]))]
    lo_i = int(Fr(lo_e) * 2 ** SV)
    jv, _ = hv[0]
    _, SL0, SH0 = reps_out["vbar"][jv]
    T = ["/- Generated by bgw/endpoint/coulomb_export.py --lean (do not edit): negative controls. -/",
         "import GW.Endpoint.Coulomb.Core", "import GW.Endpoint.Coulomb.SymmDefs", "", f"namespace {NS_LEAN}",
         "open GW.Endpoint.Coulomb", "",
         "/-- The certified face of the last representative, as certified. -/",
         f"theorem control_face : faceChkC {key} 2 ({tree_lean(f0[0])}, {f0[1]}, {f0[2]}) {i0} = true := "
         "by decide +kernel",
         "/-- The same face with the claimed lower bound raised by one unit: rejected. -/",
         f"theorem tamper_face : faceChkC {key} 2 ({tree_lean(f0[0])}, {f0[1] + 1}, {f0[2]}) {i0} = false := "
         "by decide +kernel",
         "/-- A Grundmann–Möller rule with one weight changed by one unit: rejected (degree 5). -/",
         "theorem tamper_rule : ruleRow 5 WCc (gmM 5) ((gmRule 5).modifyHead fun n => {n with W := n.W + 1}) 0 = false"
         " := by decide +kernel",
         "/-- The first stage-3 entry with its box collapsed to its lower end: rejected. -/",
         f"theorem tamper_box : boxOK (denN WCc Dvc 2) {SV} {SL0} {SH0} {lo_i} {lo_i} = false := by decide +kernel",
         "/-- A tetrahedron with one vertex coordinate moved by one unit: its inverse check fails. -/",
         "theorem tamper_geom : invOK {(cellTs.getD 0 dflt) with c := ⟨(cellTs.getD 0 dflt).c.x + 1, "
         "(cellTs.getD 0 dflt).c.y, (cellTs.getD 0 dflt).c.z⟩} = false := by decide +kernel",
         "", f"end {NS_LEAN}", ""]
    (DATA / "CoulTamper.lean").write_text("\n".join(T))
    return chain, reps_out, hv, ho


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", type=int, default=None)
    ap.add_argument("--tab", default="vbar")
    ap.add_argument("--geom", action="store_true", help="write GW/Endpoint/Coulomb/GeomData.lean")
    ap.add_argument("--lean", action="store_true", help="plan everything and write the Coul* data modules")
    ap.add_argument("--cache", default=None, help="pickle cache of the plans")
    ap.add_argument("--limit", type=int, default=None, help="(testing) only the first N reps per table")
    args = ap.parse_args()
    g = Geo()
    if args.geom:
        lean_geom(g, ROOT / "GW/Endpoint/Coulomb/GeomData.lean")
        return
    if args.lean:
        plans = plan_all(g, args.cache)
        if args.limit is not None:
            plans = {t: v[:args.limit] for t, v in plans.items()}
        chain, reps_out, hv, ho = emit_lean(g, plans)
        tot = sum(n for t in plans.values() for _, _, n in t)
        print(f"{len(chain)} modules, {tot} nodes")
        return
    print(f"Dv bits {g.Dv.bit_length()}, WC bits {WC.bit_length()}, {len(g.tris)} triangles")
    pl = Planner(g)
    doc = g.doc
    tab = args.tab
    k = 2 if tab == "vbar" else 1
    orb = orbits(doc, tab)
    reps = sorted(orb, key=lambda q: sum(x * x for x in q))
    if args.only is not None:
        reps = reps[:args.only]
    tot = 0
    for rep in reps:
        mem = orb[rep]
        lo = max(Fr(doc[tab][m][0]) for m in mem)
        hi = min(Fr(doc[tab][m][1]) for m in mem)
        v = pl.value_float(rep, k)
        # pass 1: a value to 1e-13, then the budget from the true margin
        t1 = pl.plan(rep, k, 1e-13 * v)
        a, b, _ = pl.mirror(rep, k, t1)
        v = float((a * PI_LO + b * PI_HI) / 2)
        budget = 0.85 * min(v - float(lo), float(hi) - v)
        trees = pl.plan(rep, k, budget)
        L, Hh, n = pl.mirror(rep, k, trees)
        L, Hh = L * PI_LO, Hh * PI_HI
        ok = lo <= L and Hh <= hi
        tot += n
        print(rep, len(mem), n, ok, float(L), float(Hh - L), float(lo), float(hi))
    print("nodes", tot)


if __name__ == "__main__":
    main()
