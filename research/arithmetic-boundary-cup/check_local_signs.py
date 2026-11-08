#!/usr/bin/env python3
"""Exact finite sign/volume controls; does not verify arithmetic Selmer inputs."""
from fractions import Fraction as F
from itertools import product
import json


def area(x, y):
    return x[0] * y[1] - x[1] * y[0]


def mv(m, v):
    return tuple(sum(a * b for a, b in zip(row, v)) for row in m)


def scale(a, v):
    return tuple(a * x for x in v)


def adj(m):
    return ((m[1][1], -m[0][1]), (-m[1][0], m[0][0]))


def tensor(v, row):
    return tuple(tuple(x * y for y in row) for x in v)


def smul(a, m):
    return tuple(scale(a, row) for row in m)


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def val2(x):
    assert x
    n, d, val = abs(x.numerator), x.denominator, 0
    while n % 2 == 0:
        n //= 2
        val += 1
    while d % 2 == 0:
        d //= 2
        val -= 1
    return val


def run():
    count = 0
    for shear, v, alpha, gamma, kappa in product(
        (-3, -1, 0, 1, 3),
        ((1, 0), (0, 1), (1, 1), (2, 4), (8, -16)),
        (F(1), F(2), F(1, 4)),
        (F(1), F(4), F(1, 2)),
        (F(1), F(8), F(1, 2)),
    ):
        # Odd shears include involutions without an integral eigenbasis at 2.
        J = ((F(1), F(shear)), (F(0), F(-1)))
        v = tuple(map(F, v))
        w = mv(J, v)
        assert mv(J, w) == v
        assert area(J[0], J[1]) == -1

        def q(x, y):
            return area(x, mv(J, y))

        def cup(x, y):
            return q(x[0], y[1]) - q(x[1], y[0])

        zero = (F(0), F(0))
        # Actual opposite boundary matrices in a common two-dimensional target.
        DF = ((-alpha * v[1], alpha * v[0]), zero)
        DS = (zero, (-gamma * w[1], gamma * w[0]))
        lamF, lamS = (F(0), kappa / gamma), (kappa / alpha, F(0))
        assert mv(DF, v) == zero and mv(DS, w) == zero
        for x in ((F(1), F(0)), (F(0), F(1)), (F(3), F(-2))):
            assert q(v, x) == q(x, v)
            assert dot(lamF, mv(DF, x)) == 0
            assert dot(lamS, mv(DS, x)) == 0
            # Evaluate the cone boundary against actual conjugate partners.
            lhsF = kappa * cup((zero, x), (v, zero))
            lhsS = kappa * cup((x, zero), (zero, scale(-1, w)))
            assert lhsF == dot(lamF, mv(DS, x)) == -kappa * q(v, x)
            assert lhsS == dot(lamS, mv(DF, x)) == -kappa * q(x, w)

        # Full tensor/adjugate identities, not just quotient formulas.
        uF, uS = -kappa / (alpha * gamma), kappa / (alpha * gamma)
        assert tensor(v, lamF) == smul(uF, adj(DF))
        assert tensor(w, lamS) == smul(uS, adj(DS))
        assert uS == -uF and val2(uF) == val2(uS)
        # Independent nonunit row rescaling must destroy valuation preservation.
        assert val2(2 * uS) != val2(uF)
        count += 1

    J = ((F(1), F(0)), (F(0), F(-1)))
    v = (F(1), F(1))
    w = mv(J, v)
    # Correct Q(v,Jv)=0 makes the two derivative axes orthogonal.
    assert area(v, mv(J, w)) == 0
    # Inserting J a second time breaks that property in this control.
    assert area(v, mv(J, mv(J, w))) != 0
    # Omitting tame pullback changes the signed adjunction, though it still
    # gives a unit ratio; distinguish sign fidelity from valuation preservation.
    x = (F(0), F(1))
    actual = area(x, mv(J, scale(-1, w)))
    omitted = area(x, mv(J, w))
    assert actual == -omitted and actual != omitted
    return {
        "status": "PASS",
        "exact_cases": count,
        "controls": {
            "independent_nonunit_row_rescaling": "REJECTED_IN_ALL_CASES",
            "double_J": "REJECTED",
            "omitted_tame_pullback": "SIGNED_IDENTITY_REJECTED",
        },
        "scope": "Finite exact sign and tensor checks; no arithmetic-input or Lean certification",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
