#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M1/M2 lineage, superseded by the kernel-checked eps^-1 certificates (GW.Endpoint.Kernel, Data.Q*Check/E*Check); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Independent exact reference for one BerkeleyGW static screening stage.

Solves the represented screening equation in EXACT rational arithmetic by
Gauss-Jordan elimination with rational pivoting. It never reads the production
answer as an expected value: the only input is the pre-inversion `E` exported
from the run.

The numerical acceptance criteria below are PREDECLARED. They are fixed from
the export precision, the matrix dimension and the measured conditioning of the
INPUT, before any reference-versus-production difference is examined. Do not
widen them afterwards.
"""

from fractions import Fraction as F

#: float64 unit roundoff. The production arithmetic and the export are double.
UNIT_ROUNDOFF = F(1, 2 ** 53)

#: Forward-error constant. LAPACK's LU inversion (`dgetrf`/`dgetri`, reached
#: through `invert_serial`) is backward stable, so the computed inverse obeys
#: roughly  ||X - E^-1|| / ||E^-1||  <=  C * n * kappa(E) * u.  We fix the
#: modest constant C HERE, before measuring anything.
FORWARD_CONST = 100

#: Backward-error constant for the normalized residual ||E X - I||, which does
#: not carry a conditioning factor.
RESIDUAL_CONST = 100

#: NOTE on what these are. Both rules are input-dependent ENGINEERING criteria
#: chosen from precision, dimension and measured conditioning. Neither is a
#: universal proved LAPACK forward-error bound, and `normalized_residual` below
#: is a max-entry diagnostic rather than a standard norm residual. The proved
#: statements in this milestone are the Lean theorems on the represented input;
#: these thresholds govern the separate floating-point comparison only.


def eye(n):
    return [[F(1) if a == b else F(0) for b in range(n)] for a in range(n)]


def matmul(A, B):
    n = len(A)
    return [[sum((A[a][c] * B[c][b] for c in range(n)), F(0)) for b in range(n)]
            for a in range(n)]


def matsub(A, B):
    return [[A[a][b] - B[a][b] for b in range(len(A))] for a in range(len(A))]


def transpose(A):
    n = len(A)
    return [[A[b][a] for b in range(n)] for a in range(n)]


def inf_norm(A):
    """Max absolute row sum."""
    return max(sum((abs(x) for x in row), F(0)) for row in A)


def max_abs(A):
    return max(abs(x) for row in A for x in row)


def solve(A, B):
    """Exact `A Y = B` by Gauss-Jordan with rational pivoting."""
    n = len(A)
    M = [list(A[r]) + list(B[r]) for r in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            raise ZeroDivisionError("singular represented dielectric matrix")
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def exact_inverse(E):
    """`R_ref = E^-1`, exactly. The reference."""
    R = solve(E, eye(len(E)))
    # self-check: exact arithmetic must reproduce the identity on both sides
    n = len(E)
    if matmul(E, R) != eye(n) or matmul(R, E) != eye(n):
        raise AssertionError("exact solve failed its own two-sided check")
    return R


def kappa_inf(E, R):
    """Condition number of the INPUT in the infinity norm."""
    return inf_norm(E) * inf_norm(R)


def thresholds(n, kappa):
    """The predeclared pass thresholds. Functions of precision, n, kappa only."""
    return {
        "forward_rel_inf": FORWARD_CONST * n * kappa * UNIT_ROUNDOFF,
        "normalized_residual": RESIDUAL_CONST * n * UNIT_ROUNDOFF,
    }


def metrics(E, X, R):
    """Measured comparison of production `X` against exact reference `R`."""
    n = len(E)
    diff = matsub(X, R)
    resid = matsub(matmul(E, X), eye(n))
    return {
        "entrywise_max_abs": max_abs(diff),
        "forward_rel_inf": inf_norm(diff) / inf_norm(R),
        # max-entry diagnostic, kept unchanged so the original comparison is
        # not retroactively replaced
        "normalized_residual": max_abs(resid) / (max_abs(E) * max_abs(X)),
        # standard infinity-norm normalized residual, reported alongside
        "normalized_residual_inf": inf_norm(resid) / (inf_norm(E) * inf_norm(X)),
    }


def verdict(measured, limits):
    """Pass only if every predeclared criterion holds."""
    return {k: (measured[k] <= limits[k]) for k in limits}


# --- convention mutations -----------------------------------------------------

def recover_chi(E, vcoul):
    """`chi = V^-1 (I - E)` exactly. `E` is the declared input, so this is a
    re-expression of it, not new physics."""
    n = len(E)
    I = eye(n)
    return [[(I[a][b] - E[a][b]) / vcoul[a] for b in range(n)] for a in range(n)]


def mutate(E, vcoul, kind):
    """Convention errors injected into the CHECKED path, as exact matrices."""
    n = len(E)
    if kind == "coulomb_prefactor_doubled":
        # E = I - V chi  ->  I - 2 V chi = 2E - I
        I = eye(n)
        return [[2 * E[a][b] - I[a][b] for b in range(n)] for a in range(n)]
    if kind == "transposed_one_side":
        # E is genuinely non-symmetric here, so this is not a symmetry
        return transpose(E)
    if kind == "row_permutation_one_side":
        M = [row[:] for row in E]
        M[0], M[1] = M[1], M[0]
        return M
    if kind == "sign_of_vchi":
        # I + V chi instead of I - V chi
        I = eye(n)
        chi = recover_chi(E, vcoul)
        return [[I[a][b] + vcoul[a] * chi[a][b] for b in range(n)] for a in range(n)]
    raise ValueError(f"unknown mutation {kind!r}")
