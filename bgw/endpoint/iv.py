"""Vectorised rigorous interval arithmetic on numpy float64 (inf-sup form).

Soundness rests on one hypothesis, stated here and nowhere weakened: numpy's
elementwise add, subtract, multiply, divide and sqrt on float64 are IEEE-754
binary64 operations rounded to nearest. Then the exact real result r of one
operation on floats satisfies  pred(fl(r)) <= r <= succ(fl(r)),  with pred/succ
= numpy.nextafter toward -inf/+inf, including in the subnormal range. Every
operation below rounds its computed endpoints outward by one such step, so the
exact real result of the corresponding real operation on any points of the
operand intervals lies in the result interval. Reductions are done one
elementwise operation at a time (never np.sum / np.dot / BLAS, whose order and
fused operations are not specified). Non-finite endpoints raise.

`tests/test_endpoint_e1.py::IntervalArithmetic` checks the rules against exact
rational arithmetic (fractions.Fraction) on random and adversarial operands.
"""
import numpy as np

_NINF, _PINF = -np.inf, np.inf

# Soundness also needs gradual underflow: with flush-to-zero a subnormal result
# becomes 0 and succ(0) = 5e-324 could fall below the true value.
if not (np.float64(5e-324) * np.float64(1.0) > 0 and np.float64(2.0 ** -1022) / 2 > 0):
    raise RuntimeError("flush-to-zero / denormals-are-zero is active: iv.py is unsound")


def _down(x):
    return np.nextafter(x, _NINF)


def _up(x):
    return np.nextafter(x, _PINF)


def _check(*arrs):
    for a in arrs:
        if not np.all(np.isfinite(a)):
            raise FloatingPointError("non-finite interval endpoint")


class I:
    __slots__ = ("lo", "hi")
    __array_priority__ = 1000

    def __init__(self, lo, hi=None):
        lo = np.asarray(lo, dtype=np.float64)
        hi = lo if hi is None else np.asarray(hi, dtype=np.float64)
        lo, hi = np.broadcast_arrays(lo, hi)
        _check(lo, hi)
        if np.any(lo > hi):
            raise ValueError("empty interval")
        self.lo, self.hi = lo.copy(), hi.copy()

    # ------------------------------------------------------------ helpers
    @staticmethod
    def exact(x):
        """Point interval of float(s) taken as exact reals."""
        return I(x)

    @staticmethod
    def around(x):
        """Interval containing every real whose nearest double is x (used for
        decimal constants such as pi or 13.60569253 given as the nearest double)."""
        x = np.asarray(x, dtype=np.float64)
        return I(_down(x), _up(x))

    @property
    def shape(self):
        return self.lo.shape

    def __len__(self):
        return len(self.lo)

    def __getitem__(self, k):
        return I(self.lo[k], self.hi[k])

    def __setitem__(self, k, v):
        v = _as(v)
        self.lo[k], self.hi[k] = v.lo, v.hi

    def mid(self):
        return 0.5 * self.lo + 0.5 * self.hi

    def rad(self):
        """An upper bound on the radius."""
        return _up(0.5 * self.hi - 0.5 * self.lo)

    def mag(self):
        return np.maximum(np.abs(self.lo), np.abs(self.hi))

    def copy(self):
        return I(self.lo, self.hi)

    def reshape(self, *s):
        return I(self.lo.reshape(*s), self.hi.reshape(*s))

    @property
    def T(self):
        return I(self.lo.T, self.hi.T)

    def __repr__(self):
        return f"I({self.lo!r}, {self.hi!r})"

    # --------------------------------------------------------- arithmetic
    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __add__(self, o):
        o = _as(o)
        return I(_down(self.lo + o.lo), _up(self.hi + o.hi))

    __radd__ = __add__

    def __sub__(self, o):
        return self + (-_as(o))

    def __rsub__(self, o):
        return _as(o) + (-self)

    def __mul__(self, o):
        o = _as(o)
        p = np.stack(np.broadcast_arrays(self.lo * o.lo, self.lo * o.hi,
                                         self.hi * o.lo, self.hi * o.hi))
        return I(_down(p.min(axis=0)), _up(p.max(axis=0)))

    __rmul__ = __mul__

    def recip(self):
        if np.any((self.lo <= 0) & (self.hi >= 0)):
            raise ZeroDivisionError("interval contains zero")
        return I(_down(1.0 / self.hi), _up(1.0 / self.lo))

    def __truediv__(self, o):
        return self * _as(o).recip()

    def __rtruediv__(self, o):
        return _as(o) * self.recip()

    def sqr(self):
        a, b = self.lo * self.lo, self.hi * self.hi
        straddle = (self.lo <= 0) & (self.hi >= 0)
        lo = np.where(straddle, 0.0, _down(np.minimum(a, b)))
        return I(lo, _up(np.maximum(a, b)))

    def sqrt(self):
        if np.any(self.lo < 0):
            raise ValueError("sqrt of a possibly negative interval")
        return I(np.maximum(_down(np.sqrt(self.lo)), 0.0), _up(np.sqrt(self.hi)))

    def abs(self):
        straddle = (self.lo <= 0) & (self.hi >= 0)
        lo = np.where(straddle, 0.0, np.minimum(np.abs(self.lo), np.abs(self.hi)))
        return I(lo, self.mag())

    # ------------------------------------------------------- comparisons
    def certainly_lt(self, o):
        return self.hi < _as(o).lo

    def certainly_gt(self, o):
        return self.lo > _as(o).hi

    def certainly_le(self, o):
        return self.hi <= _as(o).lo

    def certainly_ge(self, o):
        return self.lo >= _as(o).hi

    def contains_zero(self):
        return (self.lo <= 0) & (self.hi >= 0)

    # -------------------------------------------------------- reductions
    def sum(self, axis=0):
        """Sequential outward-rounded sum along `axis`."""
        lo = np.moveaxis(self.lo, axis, 0)
        hi = np.moveaxis(self.hi, axis, 0)
        slo, shi = lo[0].copy(), hi[0].copy()
        for j in range(1, lo.shape[0]):
            slo = _down(slo + lo[j])
            shi = _up(shi + hi[j])
        return I(slo, shi)


def _as(x):
    return x if isinstance(x, I) else I(x)


def hull(a, b):
    a, b = _as(a), _as(b)
    return I(np.minimum(a.lo, b.lo), np.maximum(a.hi, b.hi))


def select(cond_true, cond_false, a, b):
    """Value of `a if c else b` where the real condition c is known true on
    `cond_true`, false on `cond_false`, and undecided elsewhere (hull)."""
    a, b = _as(a), _as(b)
    a_lo, a_hi = np.broadcast_arrays(a.lo, a.hi)
    b_lo, b_hi = np.broadcast_arrays(b.lo, b.hi)
    lo = np.where(cond_true, a_lo, np.where(cond_false, b_lo, np.minimum(a_lo, b_lo)))
    hi = np.where(cond_true, a_hi, np.where(cond_false, b_hi, np.maximum(a_hi, b_hi)))
    return I(lo, hi)


def matvec(A, x):
    """A (n x m interval) times x (m interval), rigorous, sequential over m."""
    return (A * x[None, :] if x.lo.ndim == 1 else A * x).sum(axis=1)


def matmul(A, B):
    """(n x m) @ (m x p), rigorous: sequential over m."""
    n, m = A.shape
    out = None
    for j in range(m):
        term = I(A.lo[:, j:j + 1], A.hi[:, j:j + 1]) * I(B.lo[j:j + 1, :], B.hi[j:j + 1, :])
        out = term if out is None else out + term
    return out


PI = I.around(np.pi)


def inverse(A):
    """Enclosure of the inverse of every real matrix in the interval matrix A.

    R = float inverse of mid(A); E = I - R A (rigorous); if beta = ||E||_inf < 1
    then for every real A0 in A, A0^-1 = (I - E0)^-1 R and
      |A0^-1 - R|_ij <= ||(I-E0)^-1 E0 R||_inf <= ||E0||_inf ||R||_inf / (1 - beta)
    (Neumann series; every entry is bounded by the matrix inf-norm)."""
    n = A.shape[0]
    R = np.linalg.inv(A.mid())
    Ri = I.exact(R)
    E = I.exact(np.eye(n)) - matmul(Ri, A)
    Emag = E.mag()
    beta = _row_sum_up(Emag).max()
    if not beta < 1:
        raise ValueError(f"inverse not verified: beta = {beta}")
    rR = _row_sum_up(np.abs(R)).max()
    num = _up(beta * rR)
    den = _down(1.0 - beta)
    delta = _up(num / den)
    return I(_down(R - delta), _up(R + delta)), float(beta), float(delta)


def _row_sum_up(M):
    s = M[:, 0].copy()
    for j in range(1, M.shape[1]):
        s = _up(s + M[:, j])
    return s


def _matmul_up(F, P):
    """Upper bound of F @ P for nonnegative float matrices (sequential, rounded up)."""
    n, m = F.shape
    out = np.zeros((n, P.shape[1]))
    for j in range(m):
        out = _up(out + _up(F[:, j:j + 1] * P[j:j + 1, :]))
    return out


def inverse_cw(A, terms=2):
    """Componentwise enclosure of the inverse of every real matrix in A.

    R = float inverse of mid(A), E = I - R A (rigorous), F = |E|, P = |E||R|
    (upper bounds). For A0 in A: A0^-1 - R = sum_{k>=0} E0^k E0 R, so entrywise
      |A0^-1 - R| <= sum_{k=0}^{m} F^k P + tail,
      tail <= beta^(m+1) ||P||_inf / (1 - beta)   (beta = ||F||_inf < 1),
    the tail bounding every entry of sum_{k>m} F^k P by its inf-norm."""
    n = A.shape[0]
    R = np.linalg.inv(A.mid())
    E = I.exact(np.eye(n)) - matmul(I.exact(R), A)
    F = E.mag()
    beta = _row_sum_up(F).max()
    if not beta < 1:
        raise ValueError(f"inverse not verified: beta = {beta}")
    if not _down(1.0 - beta) > 0:
        raise ValueError(f"inverse not verified: 1 - beta not certainly positive ({beta})")
    P = _matmul_up(F, np.abs(R))
    S, term = P.copy(), P
    for _ in range(terms):
        term = _matmul_up(F, term)
        S = _up(S + term)
    bpow = beta
    for _ in range(terms):
        bpow = _up(bpow * beta)                      # beta^(m+1), rounded up each step
    if bpow == 0.0:
        bpow = 5e-324                                # never drop a positive tail
    tail = _up(_up(bpow * _row_sum_up(P).max()) / _down(1.0 - beta))
    B = _up(S + tail)
    return I(_down(R - B), _up(R + B)), float(beta), float(B.max())
