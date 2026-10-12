#!/usr/bin/env python3
"""Independent rational reference for the first three Lin-Lindsey ring diagrams.

Source: Lin and Lindsey, Part I, arXiv:1809.02900v1, PDF section 4.7.1,
printed pp. 42-43, Fig. 4.11.

    F_{Gamma_k}(i,j) = - ( [-v (G o G)]^k v )_{ij} G_{ij}          (p. 42)
    contribution_k   = F_{Gamma_k} / S_{Gamma_k},  S_{Gamma_k} = 2^k   (p. 43)

INDEPENDENCE. Nothing here imports, executes, or reads the Lean development,
and no expected-answer column is consulted. Two implementations are given:

  * `ring_contribution_matrix` follows the matrix formula above;
  * `ring_contribution_contraction` sums over assignments of indices to the
    internal sites of the graph, multiplying one factor per edge.

They are written from the two different descriptions in the paper and agree
only if both are right. Exact arithmetic throughout (`fractions.Fraction`);
there are no tolerances.
"""

from fractions import Fraction as F
from itertools import product

Matrix = list          # list[list[Fraction]]


def mat(rows):
    """Build an exact rational matrix from anything Fraction() accepts."""
    return [[F(x) for x in row] for row in rows]


def matmul(A, B):
    n = len(A)
    return [[sum((A[a][k] * B[k][b] for k in range(n)), F(0)) for b in range(n)]
            for a in range(n)]


def hadamard_square(G):
    """`B = G o G`, the entrywise product of `G` with itself."""
    return [[G[a][b] * G[a][b] for b in range(len(G))] for a in range(len(G))]


def chain(v, B, k):
    """`v (B v)^k`, i.e. `k+1` interaction factors separated by `k` bubbles."""
    out = v
    for _ in range(k):
        out = matmul(matmul(out, B), v)
    return out


def symmetry_factor(k):
    """`S = 2^k`: one exchange of the two propagators per bubble (p. 42)."""
    return 2 ** k


def ring_contribution_matrix(G, v, i, j, k):
    """`F/S` from the paper's closed matrix formula."""
    B = hadamard_square(G)
    amplitude = -((-1) ** k) * G[i][j] * chain(v, B, k)[i][j]
    return F(amplitude, 1) / symmetry_factor(k)


def ring_edges(k):
    """Edge data of ring `k`, read off Fig. 4.11.

    Sites: `('e', 0)` and `('e', 1)` are the two external labels; `('a', m)`
    and `('b', m)` are the two sites of bubble `m`. Returns
    `(propagators, interactions)` as lists of unordered site pairs; the two
    parallel propagators of a bubble appear twice, deliberately.
    """
    extI, extJ = ('e', 0), ('e', 1)
    props = [(extI, extJ)]
    for m in range(k):
        props += [(('a', m), ('b', m)), (('a', m), ('b', m))]
    if k == 0:
        ints = [(extI, extJ)]
    else:
        ints = [(extI, ('a', 0))]
        ints += [(('b', m), ('a', m + 1)) for m in range(k - 1)]
        ints += [(('b', k - 1), extJ)]
    return props, ints


def ring_contribution_contraction(G, v, i, j, k):
    """`F/S` by summing over internal index assignments, one factor per edge."""
    n = len(G)
    props, ints = ring_edges(k)
    internal = [s for m in range(k) for s in (('a', m), ('b', m))]
    total = F(0)
    for assignment in product(range(n), repeat=len(internal)):
        idx = dict(zip(internal, assignment))
        idx[('e', 0)], idx[('e', 1)] = i, j
        term = F(1)
        for (u, w) in props:
            term *= G[idx[u]][idx[w]]
        for (u, w) in ints:
            term *= v[idx[u]][idx[w]]
        total += term
    sign = (-1) ** len(ints)
    return sign * total / symmetry_factor(k)


def both_agree(G, v, i, j, k):
    """Value, computed both ways; raises if the two disagree."""
    a = ring_contribution_matrix(G, v, i, j, k)
    b = ring_contribution_contraction(G, v, i, j, k)
    if a != b:
        raise AssertionError(
            f"the two independent Python routes disagree at k={k}: {a} != {b}")
    return a


#: The fixtures, duplicated from `LLMain.lean`. These are INPUTS; no expected
#: output is copied from the Lean side.
FIXTURES = {
    "N1-scalar": dict(G=mat([[2]]), v=mat([[3]]), i=0, j=0),
    "N2-pd-equal-ext": dict(G=mat([[2, 1], [1, 2]]), v=mat([[1, 2], [2, 3]]), i=0, j=0),
    "N2-pd-unequal-ext": dict(G=mat([[2, 1], [1, 2]]), v=mat([[1, 2], [2, 3]]), i=0, j=1),
    "N2-rational": dict(
        G=mat([[F(1, 2), F(-1, 3)], [F(-1, 3), F(3, 2)]]),
        v=mat([[F(2, 5), F(1, 7)], [F(1, 7), F(-4, 3)]]), i=1, j=0),
    "N3-pd-unequal-ext": dict(
        G=mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]),
        v=mat([[1, 2, 3], [2, 0, 1], [3, 1, 2]]), i=0, j=1),
    "N3-pd-equal-ext": dict(
        G=mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]),
        v=mat([[1, 2, 3], [2, 0, 1], [3, 1, 2]]), i=1, j=1),
}


if __name__ == "__main__":
    for name, fx in FIXTURES.items():
        vals = [both_agree(fx["G"], fx["v"], fx["i"], fx["j"], k) for k in (0, 1, 2)]
        print(name, [str(x) for x in vals])
