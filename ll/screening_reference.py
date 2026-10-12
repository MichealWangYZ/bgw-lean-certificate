#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Independent exact-rational reference for the LL-C2B screening coefficients.

Written from the mathematics, not from the Lean output: nothing here reads an
artifact, and no expected-answer column is imported. Three genuinely different
routes to the same coefficients are provided so that agreement is evidence:

1. `w_closed`    -- the closed form `W_k = (-1/2)^k v (B v)^k`;
2. `w_recurrence`-- the left/right recurrences `W_{k+1} = -A_L W_k = -W_k A_R`;
3. `w_by_inversion` -- generic formal-power-series inversion of `P_L = I + z A_L`
   using the standard coefficient recurrence, followed by a polynomial-product
   convolution with the constant series `v`. This route does not know that
   `P_L` has only two terms.

Everything is `fractions.Fraction`. There are no tolerances and no floats.
These are formal coefficients; nothing is summed, evaluated at `z = 1`, or
claimed to converge.
"""

from fractions import Fraction as F

HALF = F(1, 2)


def mat(rows):
    return [[F(x) for x in row] for row in rows]


def zeros(n):
    return [[F(0)] * n for _ in range(n)]


def eye(n):
    return [[F(1) if a == b else F(0) for b in range(n)] for a in range(n)]


def matmul(A, B):
    n = len(A)
    return [[sum((A[a][c] * B[c][b] for c in range(n)), F(0)) for b in range(n)]
            for a in range(n)]


def matadd(A, B):
    return [[A[a][b] + B[a][b] for b in range(len(A))] for a in range(len(A))]


def scale(c, A):
    return [[c * x for x in row] for row in A]


def hadamard(A, B):
    return [[A[a][b] * B[a][b] for b in range(len(A))] for a in range(len(A))]


def bubble(G):
    """`B = G (*) G`, the entrywise square."""
    return hadamard(G, G)


def a_left(G, v):
    """`A_L = 1/2 (v B)`."""
    return scale(HALF, matmul(v, bubble(G)))


def a_right(G, v):
    """`A_R = 1/2 (B v)`. Not equal to `A_L` in general."""
    return scale(HALF, matmul(bubble(G), v))


# --- route 1: closed form ---------------------------------------------------

def w_closed(G, v, k):
    """`W_k = (-1/2)^k v (B v)^k`."""
    B = bubble(G)
    Bv = matmul(B, v)
    acc = v
    for _ in range(k):
        acc = matmul(acc, Bv)
    return scale((-HALF) ** k, acc)


# --- route 2: the two recurrences -------------------------------------------

def w_recurrence(G, v, kmax, side="left"):
    """`W_0 = v`, then `W_{k+1} = -A_L W_k` (left) or `-W_k A_R` (right)."""
    A = a_left(G, v) if side == "left" else a_right(G, v)
    out = [v]
    for _ in range(kmax):
        prev = out[-1]
        nxt = matmul(A, prev) if side == "left" else matmul(prev, A)
        out.append(scale(F(-1), nxt))
    return out


# --- route 3: generic series inversion, then convolution ---------------------

def invert_series(P, kmax):
    """Invert a truncated matrix-coefficient series with `P[0] = I`.

    The generic recurrence `S_0 = I`, `S_n = -sum_{m=1..n} P_m S_{n-m}`. It does
    not exploit the shape of `P`, so agreement with the closed form is a real
    check rather than the same computation twice.
    """
    n = len(P[0])
    if P[0] != eye(n):
        raise ValueError("this reference inverts only series with constant term I")
    S = [eye(n)]
    for d in range(1, kmax + 1):
        acc = zeros(n)
        for m in range(1, d + 1):
            Pm = P[m] if m < len(P) else zeros(n)
            acc = matadd(acc, matmul(Pm, S[d - m]))
        S.append(scale(F(-1), acc))
    return S


def pl_series(G, v, kmax):
    """`P_L = I + z A_L` as a truncated coefficient list."""
    n = len(G)
    out = [eye(n), a_left(G, v)] + [zeros(n)] * max(0, kmax - 1)
    return out[:kmax + 1]


def pr_series(G, v, kmax):
    """`P_R = I + z A_R`."""
    n = len(G)
    out = [eye(n), a_right(G, v)] + [zeros(n)] * max(0, kmax - 1)
    return out[:kmax + 1]


def convolve(A, B, kmax):
    """Truncated Cauchy product. Order matters: `A_m B_{k-m}`, never swapped."""
    n = len(A[0])
    out = []
    for d in range(kmax + 1):
        acc = zeros(n)
        for m in range(d + 1):
            if m < len(A) and d - m < len(B):
                acc = matadd(acc, matmul(A[m], B[d - m]))
        out.append(acc)
    return out


def const_series(M, kmax):
    n = len(M)
    return [M] + [zeros(n)] * kmax


def w_by_inversion(G, v, kmax):
    """`W = S_L v` with `S_L` from the generic inversion above."""
    S = invert_series(pl_series(G, v, kmax), kmax)
    return convolve(S, const_series(v, kmax), kmax)


def w_by_right_inversion(G, v, kmax):
    """`W = v S_R`, the other ordering, as a separate check on `W = C(v) S_R`."""
    S = invert_series(pr_series(G, v, kmax), kmax)
    return convolve(const_series(v, kmax), S, kmax)


# --- the ring series --------------------------------------------------------

def t_from_w(G, Wk):
    """`T_k = -(G (*) W_k)`, the entrywise `G`-dressing, negated."""
    return scale(F(-1), hadamard(G, Wk))


def all_routes_agree(G, v, kmax):
    """Every route must produce the same list of coefficients; else raise."""
    closed = [w_closed(G, v, k) for k in range(kmax + 1)]
    routes = {
        "left recurrence": w_recurrence(G, v, kmax, "left"),
        "right recurrence": w_recurrence(G, v, kmax, "right"),
        "generic left inversion": w_by_inversion(G, v, kmax),
        "generic right inversion": w_by_right_inversion(G, v, kmax),
    }
    for label, got in routes.items():
        if got != closed:
            raise AssertionError(f"{label} disagrees with the closed form")
    return closed


def screening_residual(G, v, kmax, side="left"):
    """Coefficients of `P_L W - C(v)` (or `W P_R - C(v)`) up to `kmax`.

    All of them must vanish. The coefficient at `kmax + 1` is not included,
    but NOT because constraining it would be a convergence claim -- it would
    not. Truncating `W` after `W_kmax` simply drops the `W_{kmax+1}` term that
    cancels it, so the degree-`kmax+1` residual of `P_L W` is exactly
    `A_L W_kmax`. That is finite algebra; `first_omitted_residual` computes it.
    """
    W = [w_closed(G, v, k) for k in range(kmax + 1)]
    P = pl_series(G, v, kmax) if side == "left" else pr_series(G, v, kmax)
    prod = convolve(P, W, kmax) if side == "left" else convolve(W, P, kmax)
    target = const_series(v, kmax)
    return [[[prod[d][a][b] - target[d][a][b] for b in range(len(G))]
             for a in range(len(G))] for d in range(kmax + 1)]


def first_omitted_residual(G, v, kmax, side="left"):
    """The degree-`kmax+1` residual left by truncating `W` after `W_kmax`.

    Exactly `A_L W_kmax` (or `W_kmax A_R`), and exactly `-W_{kmax+1}`. Nothing
    about convergence is involved: the full formal series supplies the missing
    coefficient that cancels it.
    """
    Wk = w_closed(G, v, kmax)
    A = a_left(G, v) if side == "left" else a_right(G, v)
    return matmul(A, Wk) if side == "left" else matmul(Wk, A)


# --- mutants ----------------------------------------------------------------

def w_mutant(G, v, kmax, kind):
    """Deliberately wrong coefficient lists, for detection tests."""
    if kind == "sign":
        return [scale(HALF ** k, matmul_pow(v, G, k)) for k in range(kmax + 1)]
    if kind == "no_half":
        return [scale(F(-1) ** k, matmul_pow(v, G, k)) for k in range(kmax + 1)]
    if kind == "wrong_order":
        # `A_R` used on the LEFT: the ordering error commutativity would hide.
        A = a_right(G, v)
        out = [v]
        for _ in range(kmax):
            out.append(scale(F(-1), matmul(A, out[-1])))
        return out
    if kind == "degree_shift":
        # Off by one: the coupling-counting series mislabelled as bubble counting.
        return [zeros(len(G))] + [w_closed(G, v, k) for k in range(kmax)]
    raise ValueError(f"unknown mutant {kind!r}")


def matmul_pow(v, G, k):
    Bv = matmul(bubble(G), v)
    acc = v
    for _ in range(k):
        acc = matmul(acc, Bv)
    return acc
