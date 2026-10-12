#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Independent exact-rational oracle for the LL-C4 finite electronic RPA model.

Written from the specification in `.agent/tasks/LL-C4.md` section 2, not from
the Lean output: nothing here reads an artifact and no expected-answer column is
imported. The screened interaction is obtained by **exact Gaussian elimination**
on `eps W = v` -- a genuinely different route from the Neumann series the Lean
side manipulates, so agreement is evidence rather than a restatement.

Exact `fractions.Fraction`. No tolerances, no floats. Static (zero-frequency)
model only. Nothing here is a BerkeleyGW convention or a BerkeleyGW result.
"""

from fractions import Fraction as F


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


def matsub(A, B):
    return [[A[a][b] - B[a][b] for b in range(len(A))] for a in range(len(A))]


def scale(c, A):
    return [[c * x for x in row] for row in A]


class Transition:
    """One occupied -> empty channel. `weight` carries spin/degeneracy."""

    def __init__(self, occ, emp, weight, m):
        self.occ, self.emp, self.weight = F(occ), F(emp), F(weight)
        self.m = [F(x) for x in m]
        if self.occ == self.emp:
            raise ValueError("vanishing transition energy: outside the model's domain")


def chi0(transitions, n):
    """`chi0 i j = sum_t w_t m_t(i) m_t(j) / (occ_t - emp_t)`."""
    out = zeros(n)
    for t in transitions:
        d = t.occ - t.emp
        for i in range(n):
            for j in range(n):
                out[i][j] += t.weight * t.m[i] * t.m[j] / d
    return out


def epsilon(v, X):
    """`eps = I - v chi0`."""
    return matsub(eye(len(v)), matmul(v, X))


def solve(A, B):
    """Exact solve `A Y = B` by Gaussian elimination with rational pivoting."""
    n = len(A)
    M = [list(A[r]) + list(B[r]) for r in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            raise ZeroDivisionError("singular dielectric matrix: no unique W")
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def screened(v, transitions):
    """`W = eps^{-1} v`, by exact elimination. The independent route."""
    X = chi0(transitions, len(v))
    return solve(epsilon(v, X), v)


def neumann_coeff(v, transitions, k):
    """`(v chi0)^k v`, the k-th formal coefficient. The other route."""
    T = matmul(v, chi0(transitions, len(v)))
    acc = v
    for _ in range(k):
        acc = matmul(T, acc)
    return acc


def partial_sum(v, transitions, kmax):
    n = len(v)
    out = zeros(n)
    for k in range(kmax + 1):
        C = neumann_coeff(v, transitions, k)
        out = [[out[a][b] + C[a][b] for b in range(n)] for a in range(n)]
    return out


def truncation_residual(v, transitions, kmax):
    """`v - eps * partial_sum`, which must equal `(v chi0)^{kmax+1} v` exactly.

    Finite algebra, not a convergence statement: the telescoping identity
    `eps * sum_{k<=K} T^k v = v - T^{K+1} v` holds for every `K`.
    """
    X = chi0(transitions, len(v))
    return matsub(v, matmul(epsilon(v, X), partial_sum(v, transitions, kmax)))


def quad_form(A, x):
    return sum((x[a] * A[a][b] * x[b] for a in range(len(A)) for b in range(len(A))),
               F(0))


def is_symmetric(A):
    return all(A[a][b] == A[b][a] for a in range(len(A)) for b in range(len(A)))


def bubble(G):
    """The CLASSICAL bubble `G (*) G` of C2A/C2B, for the contrast test."""
    return [[G[a][b] * G[a][b] for b in range(len(G))] for a in range(len(G))]


def gpp_inv_eps(omega2, wtilde, omega):
    """Single plasmon pole: `1 + Omega^2 / (omega^2 - wtilde^2)`."""
    if omega ** 2 == wtilde ** 2:
        raise ZeroDivisionError("on the plasmon pole: outside the model's domain")
    return F(1) + F(omega2) / (F(omega) ** 2 - F(wtilde) ** 2)


def gpp_omega2_from_static(inv_eps0, wtilde):
    """The standard identification fixing `Omega^2` from the static value."""
    return (F(1) - F(inv_eps0)) * F(wtilde) ** 2


def mutant(v, transitions, kind, kmax=3):
    """Deliberately wrong screened interactions, for detection tests."""
    n = len(v)
    if kind == "sign_flipped_denominator":
        bad = [Transition(t.emp, t.occ, t.weight, t.m) for t in transitions]
        return screened(v, bad)
    if kind == "weight_dropped":
        bad = [Transition(t.occ, t.emp, 1, t.m) for t in transitions]
        return screened(v, bad)
    if kind == "eps_sign":
        X = chi0(transitions, n)
        return solve([[eye(n)[a][b] + matmul(v, X)[a][b] for b in range(n)]
                      for a in range(n)], v)
    if kind == "truncated_early":
        return partial_sum(v, transitions, kmax - 1)
    raise ValueError(f"unknown mutant {kind!r}")
