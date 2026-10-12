#!/usr/bin/env python3
"""BGW-M2: exact reference, frozen error budgets, and the three matrices.

Three matrices are kept distinct and are never silently interchanged:

    E_star = I - V_hat * chi_hat     exact rational formation from the
                                     independently exported operands
    E_hat                            the stored production pre-inversion matrix
    Delta  = E_hat - E_star          the formation rounding difference

`chi_hat` is exported at its point of use in `Epsilon/epsinv.f90`; it is never
recovered as `V^-1 (I - E_hat)`, which would make the comparison circular.

ALL budgets below are functions of the inputs and certified references only.
None uses an observed discrepancy. They are frozen here before the comparison.
"""

from fractions import Fraction as F

#: float64 unit roundoff.
U = F(1, 2 ** 53)

#: gamma_2 = 2u/(1-2u), the standard constant for two dependent roundings.
GAMMA2 = (2 * U) / (1 - 2 * U)

#: Engineering constant for the inversion budget. Fixed before measurement.
#: This is NOT a proof of universal LAPACK stability.
INV_CONST = 100


def eye(n):
    return [[F(1) if a == b else F(0) for b in range(n)] for a in range(n)]


def matmul(A, B):
    n = len(A)
    return [[sum((A[a][c] * B[c][b] for c in range(n)), F(0)) for b in range(n)]
            for a in range(n)]


def matsub(A, B):
    return [[A[a][b] - B[a][b] for b in range(len(A))] for a in range(len(A))]


def diagonal(d):
    n = len(d)
    return [[d[a] if a == b else F(0) for b in range(n)] for a in range(n)]


def inf_norm(A):
    """Max absolute ROW SUM. Stated explicitly: every bound below uses this."""
    return max(sum((abs(x) for x in row), F(0)) for row in A)


def max_abs(A):
    return max(abs(x) for row in A for x in row)


def solve(A, B):
    n = len(A)
    M = [list(A[r]) + list(B[r]) for r in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            raise ZeroDivisionError("singular matrix")
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [xx / piv for xx in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [xx - f * y for xx, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def exact_inverse(A):
    R = solve(A, eye(len(A)))
    n = len(A)
    if matmul(A, R) != eye(n) or matmul(R, A) != eye(n):
        raise AssertionError("exact solve failed its own two-sided check")
    return R


# --- the three matrices ------------------------------------------------------

def e_star(chi, vcoul):
    """`E_star = I - V_hat chi_hat`, exactly. `V_hat` is diagonal on the ROW
    index, the convention traced from `eps(i,j) = delta_ij - vcoul(i)*chi(i,j)`."""
    n = len(chi)
    I = eye(n)
    return [[I[a][b] - vcoul[a] * chi[a][b] for b in range(n)] for a in range(n)]


def delta(E_hat, E_star):
    return matsub(E_hat, E_star)


def formation_budget(chi, vcoul):
    """`B_ij = gamma2 * (|delta_ij| + |V_ii * chi_ij|)`.

    Conservative for the traced path `fl(delta - fl(v*chi))` (two roundings)
    and also for a fused `fl(delta - v*chi)` (one rounding), so it does not
    depend on whether the compiler contracted the expression.
    """
    n = len(chi)
    I = eye(n)
    return [[GAMMA2 * (abs(I[a][b]) + abs(vcoul[a] * chi[a][b]))
             for b in range(n)] for a in range(n)]


def b_form(B):
    """Row-sum (infinity-norm) formation budget."""
    return inf_norm(B)


# --- composed budgets, all input-based ---------------------------------------

def b_inv(E_hat, R_hat, n):
    """Inversion budget for the stored problem, engineering rule."""
    return INV_CONST * n * U * inf_norm(E_hat) * inf_norm(R_hat) ** 2


def b_shift(R_hat, bform, R_star):
    """Propagated formation difference: ||R_hat|| * b_form * ||R_star||.

    This is the norm form of the exact identity
    `R_hat - R_star = -R_hat * Delta * R_star`.
    """
    return inf_norm(R_hat) * bform * inf_norm(R_star)


def b_total(binv, bshift):
    return binv + bshift


class FormationClaimError(ValueError):
    """A claimed formation difference is not the one the operands imply."""


def validate_formation_claim(chi, vcoul, E_hat, claimed_delta):
    """Reject a claimed `Delta` that the exported operands do not produce.

    This is the validation boundary a forged "formation error is zero" claim
    has to pass through. It recomputes `Delta` from `chi`, `vcoul` and the
    archived `E_hat` -- none of which the claimant supplies -- and requires
    exact agreement. Added in BGW-M2-R1: the previous negative test was
    vacuous and could not have caught such a claim.
    """
    actual = delta(E_hat, e_star(chi, vcoul))
    if claimed_delta != actual:
        raise FormationClaimError(
            "claimed formation difference does not match the operands")
    return actual


def component_errors(E_hat, X_hat, R_hat, R_star):
    """The three separately budgeted quantities, all in the row-sum norm."""
    return {
        "formation_inf": None,      # filled by the caller, needs chi/vcoul
        "inv_inf": inf_norm(matsub(X_hat, R_hat)),
        "shift_inf": inf_norm(matsub(R_hat, R_star)),
        "total_inf": inf_norm(matsub(X_hat, R_star)),
    }


# --- residual diagnostics, both normalizations kept --------------------------

def residuals(E, X):
    """Both normalizations, reported side by side rather than reconciled away.

    The BGW-M2 acceptance reconciled the two earlier numbers exactly: with
    r = ||EX-I||_inf and p = ||E||_inf*||X||_inf, one convention is r/p and the
    other r/(p+1), the `+1` being the identity right-hand side's norm.
    """
    n = len(E)
    r = inf_norm(matsub(matmul(E, X), eye(n)))
    p = inf_norm(E) * inf_norm(X)
    return {"r_over_p": r / p, "r_over_p_plus_1": r / (p + 1)}
