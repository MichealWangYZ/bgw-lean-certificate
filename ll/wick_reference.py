#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Independent exact-rational reference for the LL-C3 Wick computation.

Written from the definitions, not from the Lean output: nothing here reads an
artifact and no expected-answer column is imported. Perfect matchings are
enumerated by brute force, so the moment is computed the long way round and the
closed Hartree/Fock form is an independent claim to be checked against it.

Everything is `fractions.Fraction`. No tolerances, no floats. These are formal
algebraic identities in a finite-dimensional model; nothing is integrated and
no Gaussian measure is involved -- Wick's theorem is the DEFINITION of the
moment here, exactly as in `GW/LL/Wick.lean`, and is not proved by either side.
"""

from fractions import Fraction as F

INTERACTION_WEIGHT = F(1, 8)


def mat(rows):
    return [[F(x) for x in row] for row in rows]


def matmul(A, B):
    n = len(A)
    return [[sum((A[a][c] * B[c][b] for c in range(n)), F(0)) for b in range(n)]
            for a in range(n)]


def hadamard(A, B):
    return [[A[a][b] * B[a][b] for b in range(len(A))] for a in range(len(A))]


def scale(c, A):
    return [[c * x for x in row] for row in A]


def matsub(A, B):
    return [[A[a][b] - B[a][b] for b in range(len(A))] for a in range(len(A))]


def diagonal(d):
    n = len(d)
    return [[d[a] if a == b else F(0) for b in range(n)] for a in range(n)]


def is_symmetric(A):
    return all(A[a][b] == A[b][a] for a in range(len(A)) for b in range(len(A)))


def matchings(slots):
    """Every perfect matching of a list of positions. Empty if odd."""
    if not slots:
        yield []
        return
    a, rest = slots[0], slots[1:]
    for k in range(len(rest)):
        for m in matchings(rest[:k] + rest[k + 1:]):
            yield [(a, rest[k])] + m


def select(labels):
    """Every way to remove one element, paired with the remainder.

    Mirrors `GW.LL.select`, so the recursion below is the same recursion
    `GW.LL.wickMoment_cons` proves -- checked here against brute force.
    """
    out = []
    for k in range(len(labels)):
        out.append((labels[k], labels[:k] + labels[k + 1:]))
    return out


def moment_recursive(G, labels):
    """The Wick recursion: pair the head with each remaining element.

    An independent route to `moment` below, for any even length.
    """
    if not labels:
        return F(1)
    head, rest = labels[0], labels[1:]
    return sum((G[head][b] * moment_recursive(G, r) for (b, r) in select(rest)),
               F(0))


def moment(G, labels):
    """Wick as a definition: sum over perfect matchings of products of `G`."""
    total = F(0)
    for m in matchings(list(range(len(labels)))):
        p = F(1)
        for (u, w) in m:
            p *= G[labels[u]][labels[w]]
        total += p
    return total


def first_order(G, v, a, b, weight=INTERACTION_WEIGHT, normalize=True):
    """The normalized first-order correction, straight from the definition."""
    n = len(G)
    full = F(0)
    disc = F(0)
    for i in range(n):
        for j in range(n):
            c = weight * v[i][j]
            full += c * moment(G, [a, b, i, i, j, j])
            if normalize:
                disc += c * G[a][b] * moment(G, [i, i, j, j])
    return -(full - disc)


def first_order_matrix(G, v, **kw):
    n = len(G)
    return [[first_order(G, v, a, b, **kw) for b in range(n)] for a in range(n)]


def loop_vec(G, v):
    return [sum((v[i][j] * G[j][j] for j in range(len(G))), F(0))
            for i in range(len(G))]


def hartree_matrix(G, v):
    return matmul(matmul(G, diagonal(loop_vec(G, v))), G)


def fock_matrix(G, v):
    return matmul(matmul(G, hadamard(v, G)), G)


def ring0_matrix(G, v):
    """C2A's order-zero ring contribution: `-(v (*) G)`."""
    return scale(F(-1), hadamard(v, G))


def dressed_ring0(G, v):
    return matmul(matmul(G, ring0_matrix(G, v)), G)


def closed_form(G, v):
    """`-(1/2 Hartree + Fock)`, the claimed closed form."""
    return scale(F(-1), [[F(1, 2) * hartree_matrix(G, v)[a][b] + fock_matrix(G, v)[a][b]
                          for b in range(len(G))] for a in range(len(G))])


def both_agree(G, v):
    """Brute-force matchings and the closed form must agree, or raise."""
    if not is_symmetric(G):
        raise AssertionError("G must be symmetric to be a covariance")
    if not is_symmetric(v):
        raise AssertionError("the closed form assumes symmetric v")
    direct = first_order_matrix(G, v)
    closed = closed_form(G, v)
    if direct != closed:
        raise AssertionError("brute-force Wick disagrees with the closed form")
    return direct


def mutant(G, v, kind):
    """Deliberately wrong first-order matrices, for detection tests."""
    if kind == "unnormalized":
        # disconnected matchings left in: no partition-function subtraction
        return first_order_matrix(G, v, normalize=False)
    if kind == "weight_quarter":
        return first_order_matrix(G, v, weight=F(1, 4))
    if kind == "weight_half":
        return first_order_matrix(G, v, weight=F(1, 2))
    if kind == "hartree_fock_swapped":
        return scale(F(-1), [[hartree_matrix(G, v)[a][b] + F(1, 2) * fock_matrix(G, v)[a][b]
                              for b in range(len(G))] for a in range(len(G))])
    if kind == "fock_only":
        # what the ring family alone would give: Hartree dropped
        return dressed_ring0(G, v)
    raise ValueError(f"unknown mutant {kind!r}")


def matching_count(m):
    """`(2m-1)!!`, the number of perfect matchings of `2m` positions."""
    n = 2 * m
    out = 1
    while n > 1:
        out *= n - 1
        n -= 2
    return out
