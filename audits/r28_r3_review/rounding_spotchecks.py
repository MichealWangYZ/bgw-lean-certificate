"""Independent arithmetic spot checks for physics_lean_bgw at 47a46c9.

This is not a repository checkout or a replacement for scripts/verify.sh.
The f_up/f_down and meV conversion expressions are copied from the fetched
source. Fraction is used as an exact-real oracle. No Lean builds or production
BerkeleyGW calculations are performed here.
"""
from fractions import Fraction as Fr
import math
import numpy as np


def f_up(x):
    f = float(x)
    return float(np.nextafter(f, np.inf)) if Fr(f) < x else f


def f_down(x):
    f = float(x)
    return float(np.nextafter(f, -np.inf)) if Fr(f) > x else f


def from_mev_endpoints(pair):
    lo, hi = (np.float64(pair[0]) / np.float64(1e3),
              np.float64(pair[1]) / np.float64(1e3))
    for _ in range(2):
        lo, hi = np.nextafter(lo, -np.inf), np.nextafter(hi, np.inf)
    return float(lo), float(hi)


def to_mev_endpoints(pair):
    lo = np.float64(pair[0]) * np.float64(1e3)
    hi = np.float64(pair[1]) * np.float64(1e3)
    return float(np.nextafter(lo, -np.inf)), float(np.nextafter(hi, np.inf))


def main():
    rng = np.random.default_rng(20261008)
    s = float(np.nextafter(0.0, 1.0))
    positive = [0.0, s, 2*s, 3*s, 0.1, 15.405752349,
                2813.0693, math.ldexp(1.0, -1022)]
    vals = positive + [-v for v in positive]
    vals += [math.ldexp(float(rng.uniform(-1, 1)), int(e))
             for e in rng.integers(-1073, 995, size=5000)]
    pairs = [(x, x) for x in vals]
    pairs += [tuple(sorted((vals[i], vals[-i-1]))) for i in range(5000)]
    with np.errstate(under='ignore', over='raise', invalid='raise'):
        for a, b in pairs:
            lo, hi = from_mev_endpoints((a, b))
            assert Fr(lo) <= Fr(a)/1000 <= Fr(b)/1000 <= Fr(hi)
            lo, hi = to_mev_endpoints((a, b))
            assert Fr(lo) <= Fr(a)*1000 <= Fr(b)*1000 <= Fr(hi)
        for i, x in enumerate(vals):
            q = Fr(x) / (i % 23 + 1)
            lo, hi = f_down(q), f_up(q)
            assert Fr(lo) <= q <= Fr(hi)
            assert Fr(float(np.nextafter(lo, np.inf))) > q
            assert Fr(float(np.nextafter(hi, -np.inf))) < q

    # Actual cor.py expression, both new all_bands radius_eV and pre-existing
    # per_band radius_*_eV. It fails as a general outward rule for subnormals.
    r = 2 * s
    reported = float(r) * 13.60569253 * (1 + 1e-12)
    target = Fr(r) * Fr('13.60569253')
    assert Fr(reported) < target
    print(f'PASS: {len(pairs)} intervals, both meV conversion directions')
    print(f'PASS: {len(vals)} rationals, directed conversion and nearest-neighbor checks')
    print('COUNTEREXAMPLE: cor.py padded scalar radius conversion')
    print('input radius / smallest subnormal =', Fr(r)/Fr(s))
    print('reported radius / smallest subnormal =', Fr(reported)/Fr(s))
    print('exact converted radius / smallest subnormal =', target/Fr(s))
    print('exact decimal equivalent =', float(target/Fr(s)))
    print('No claim is made that this subnormal occurs in the pinned run.')


if __name__ == '__main__':
    main()
