#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- The one validator for LL value tables, shared by tests and report generators.

Started as LL-C2A opening cleanup 2.1 for the C1 table. The C2A review then
found that `tests/test_ll_c2a.py` had reintroduced the same defect one layer
over: it built `{row["name"]: row}` directly (so a wrong duplicate placed
before the correct row was silently overwritten), read its order coverage from
the candidate's own `orders` field (so `orders = [0, 3]` hid a wrong `k4`), and
never read each row's `N`/`i`/`j` (so `i = j = 999` passed).

The fix is a boundary, not four more examples: ONE `validate_table` that every
LL evidence path calls, and whose expected inventory -- fixture names, orders,
and value columns -- is supplied by the caller from the specification, never
read out of the table under test.

Validation only: no schema framework, no provenance system, no report
hierarchy. The test modules are never imported into a generator.
"""

from fractions import Fraction as F
import re

#: Every LL evaluator emits `s!"{x.num}/{x.den}"`. A bare integer literal is
#: exact too, so both are accepted. What must NOT be accepted is a `bool` or a
#: `float`: `Fraction` converts both silently (`Fraction(0.1)` is a 55-bit
#: ratio), so `Fraction`-convertibility is a weaker property than the
#: validator's prose claimed.
EXACT_RATIONAL = re.compile(r"^-?\d+(/\d+)?$")

#: Lin-Lindsey Part I, p. 42: `S_{Gamma_k} = 2^k`. Stated here as an
#: independent constant, NOT read from the artifact under test.
EXPECTED_SYMMETRY_FACTORS = {"ring0": 1, "ring1": 2, "ring2": 4}

#: Specification-owned coverage. `LLC2AMain.lean` emits k = 0..4; the task
#: requires evidence at k >= 3. A candidate that emits fewer orders must fail
#: rather than narrow what it is checked against.
EXPECTED_C2A_ORDERS = (0, 1, 2, 3, 4)

#: Specification-owned coverage for the C1 table's three named ring columns.
EXPECTED_C1_ORDERS = (0, 1, 2)

#: Specification-owned coverage for the C2B coefficient table. `LL-C2B.md` 5
#: requires degrees 0..4.
EXPECTED_C2B_ORDERS = (0, 1, 2, 3, 4)

#: Specification-owned series names for the C2B table.
EXPECTED_C2B_SERIES = ("W", "T")

#: LL-C4: the static quantities carry a single order, the Neumann expansion
#: carries 0..3. Two declared order keys, one validator.
EXPECTED_C4_STATIC_ORDERS = (0,)
EXPECTED_C4_STATIC_SERIES = ("chi0", "eps")
EXPECTED_C4_ORDERS = (0, 1, 2, 3)
EXPECTED_C4_SERIES = ("neumann", "partial")

#: LL-C3 is a single-order calculation: the first-order term in `v`.
EXPECTED_C3_ORDERS = (1,)

#: Specification-owned series names for the C3 table. `ringDressed` must be
#: present so the table cannot omit the link back to the ring family.
EXPECTED_C3_SERIES = ("delta", "hartree", "fock", "ringDressed")


class EvidenceError(ValueError):
    """The emitted value table is not a usable piece of evidence."""


def validate_symmetry_factors(data):
    """The artifact's symmetry metadata must match the paper, exactly.

    Previously the generator copied whatever the candidate emitted, so a table
    claiming `ring1: 999` produced a report asserting 999 was the paper's
    value.
    """
    got = data.get("symmetry_factors")
    if got != EXPECTED_SYMMETRY_FACTORS:
        raise EvidenceError(
            f"symmetry metadata {got!r} does not match the paper's "
            f"{EXPECTED_SYMMETRY_FACTORS!r}")
    return dict(EXPECTED_SYMMETRY_FACTORS)


def _check_exact(where, x):
    """An exact value is a rational STRING, not merely `Fraction`-convertible."""
    if type(x) is not str or not EXACT_RATIONAL.match(x):
        raise EvidenceError(
            f"{where}: {x!r} is not exact; want an integer or 'num/den' string")
    try:
        return F(x)
    except (ValueError, ZeroDivisionError) as exc:
        raise EvidenceError(f"{where}: {x!r} is not exact: {exc}")


def _check_orders(data, expected_orders, orders_key):
    """The declared coverage must equal the specification's, exactly.

    A candidate that selects its own `orders` chooses what it is compared
    against. `orders = [0, 3]` previously passed every C2A test while the
    emitted `k4` column was wrong and simply never read.
    """
    want = list(expected_orders)
    if orders_key not in data:
        return want
    got = data[orders_key]
    if not isinstance(got, list):
        raise EvidenceError(f"{orders_key!r} is {type(got).__name__}, not a list")
    if any(type(k) is not int for k in got):
        raise EvidenceError(f"{orders_key!r} contains a non-integer order: {got!r}")
    if len(set(got)) != len(got):
        raise EvidenceError(f"duplicate entries in {orders_key!r}: {got!r}")
    if got != want:
        raise EvidenceError(
            f"declared {orders_key} {got!r} != specification's {want!r}; the "
            f"table may not choose its own comparison coverage")
    return want


def _values_of(data):
    if "values" not in data:
        raise EvidenceError("table has no 'values' array")
    values = data["values"]
    if not isinstance(values, list):
        raise EvidenceError(f"'values' is {type(values).__name__}, not a list")
    return values


def _check_inventory(values, fixtures):
    """Names present exactly once each, and exactly the expected set."""
    names = [row["name"] for row in values]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates:
        raise EvidenceError(f"duplicate fixture rows: {duplicates}")
    if set(names) != set(fixtures):
        raise EvidenceError(
            f"inventory mismatch: emitted-only {sorted(set(names) - set(fixtures))}, "
            f"expected-only {sorted(set(fixtures) - set(names))}")
    if len(values) != len(fixtures):
        raise EvidenceError(
            f"row count {len(values)} != fixture count {len(fixtures)}")


def _check_row_metadata(row, fx):
    """`N`, `i`, `j` must be integers matching the fixture and in range."""
    expected = {"N": len(fx["G"]), "i": fx["i"], "j": fx["j"]}
    for key, want in expected.items():
        if key not in row:
            raise EvidenceError(f"{row['name']}: missing {key!r}")
        got = row[key]
        # `bool` is a subclass of `int`; a float index is not an index.
        if type(got) is not int:
            raise EvidenceError(
                f"{row['name']}: {key} is {type(got).__name__}, not int")
        if got != want:
            raise EvidenceError(
                f"{row['name']}: {key} is {got}, fixture says {want}")
    if not (0 <= row["i"] < row["N"] and 0 <= row["j"] < row["N"]):
        raise EvidenceError(
            f"{row['name']}: external indices ({row['i']},{row['j']}) "
            f"out of bounds for N={row['N']}")


def validate_table(data, fixtures, *, value_prefix, expected_orders,
                   orders_key="orders"):
    """Validate an LL value table against specification-owned expectations.

    `fixtures` supplies the truth for names, dimension and external indices;
    `expected_orders` and `value_prefix` supply the truth for which value
    columns must be present. Returns the rows keyed by fixture name.
    """
    orders = _check_orders(data, expected_orders, orders_key)
    columns = [f"{value_prefix}{k}" for k in orders]
    values = _values_of(data)

    _check_inventory(values, fixtures)

    for row in values:
        fx = fixtures[row["name"]]
        _check_row_metadata(row, fx)

        missing = [c for c in columns if c not in row]
        if missing:
            raise EvidenceError(f"{row['name']}: missing value columns {missing}")
        stray = sorted(k for k in row
                       if k.startswith(value_prefix)
                       and k[len(value_prefix):].isdigit()
                       and k not in columns)
        if stray:
            raise EvidenceError(
                f"{row['name']}: value columns {stray} outside the checked "
                f"coverage {columns}")
        for c in columns:
            _check_exact(f"{row['name']}: {c}", row[c])

    return {row["name"]: row for row in values}


def validate_matrix_table(data, fixtures, *, series_keys, expected_orders,
                          orders_key="orders"):
    """Validate a table whose value per (fixture, order) is a full N*N matrix.

    Same boundary rule as `validate_table`: the series names and the order
    coverage are the caller's (the specification's), never the table's.
    """
    orders = _check_orders(data, expected_orders, orders_key)
    wanted = [str(k) for k in orders]
    values = _values_of(data)

    _check_inventory(values, fixtures)

    for row in values:
        fx = fixtures[row["name"]]
        _check_row_metadata(row, fx)
        n = row["N"]
        for series in series_keys:
            if series not in row:
                raise EvidenceError(f"{row['name']}: missing series {series!r}")
            block = row[series]
            if not isinstance(block, dict):
                raise EvidenceError(
                    f"{row['name']}: series {series!r} is "
                    f"{type(block).__name__}, not an object keyed by order")
            if sorted(block, key=int) != wanted:
                raise EvidenceError(
                    f"{row['name']}: series {series!r} covers "
                    f"{sorted(block, key=lambda x: int(x))}, outside the checked "
                    f"coverage {wanted}")
            for k in wanted:
                M = block[k]
                if (not isinstance(M, list) or len(M) != n
                        or any(not isinstance(r, list) or len(r) != n for r in M)):
                    raise EvidenceError(
                        f"{row['name']}: series {series!r} degree {k} is not an "
                        f"{n}x{n} matrix")
                for r in M:
                    for x in r:
                        _check_exact(f"{row['name']}: {series}[{k}] entry", x)

    return {row["name"]: row for row in values}


def validate_c2b(data, fixtures):
    """The C2B coefficient table: series `W` and `T`, degrees 0..4."""
    return validate_matrix_table(data, fixtures, series_keys=EXPECTED_C2B_SERIES,
                                 expected_orders=EXPECTED_C2B_ORDERS)


def validate_c3(data, fixtures):
    """The C3 first-order table: four matrices per fixture, order 1 only."""
    return validate_matrix_table(data, fixtures, series_keys=EXPECTED_C3_SERIES,
                                 expected_orders=EXPECTED_C3_ORDERS)


def validate_c4(data, fixtures):
    """The C4 electronic table: static `chi0`/`eps`, plus a 0..3 expansion.

    Both halves go through `validate_matrix_table`; neither the series names nor
    either order list is read out of the table.
    """
    validate_matrix_table(data, fixtures, series_keys=EXPECTED_C4_STATIC_SERIES,
                          expected_orders=EXPECTED_C4_STATIC_ORDERS,
                          orders_key="static_orders")
    return validate_matrix_table(data, fixtures, series_keys=EXPECTED_C4_SERIES,
                                 expected_orders=EXPECTED_C4_ORDERS)


def validate_rows(data, fixtures):
    """The C1 table: columns `ring0..ring2`, no declared `orders` field."""
    return validate_table(data, fixtures, value_prefix="ring",
                          expected_orders=EXPECTED_C1_ORDERS)


def validate_c2a(data, fixtures):
    """The C2A structural table: columns `k0..k4`, declared `orders` checked."""
    return validate_table(data, fixtures, value_prefix="k",
                          expected_orders=EXPECTED_C2A_ORDERS)


def validate(data, fixtures):
    """Full C1 validation: symmetry metadata and rows. Returns keyed rows."""
    validate_symmetry_factors(data)
    return validate_rows(data, fixtures)
