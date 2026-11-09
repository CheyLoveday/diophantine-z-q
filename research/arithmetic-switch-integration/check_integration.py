#!/usr/bin/env python3
"""Exact end-to-end *models*, not arithmetic certificates or a proof search.

Generate opposite-boundary evaluations from the local cup, construct the
closed rows on a common W, and check cofactor and strict-line coordinates.
All arithmetic is Fraction arithmetic. No third-party package is required.
"""
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def scale(c, x):
    return tuple(c * a for a in x)


def area(x, y):
    return x[0] * y[1] - x[1] * y[0]


def cols(x, y):
    return ((x[0], y[0]), (x[1], y[1]))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def adj(a):
    return ((a[1][1], -a[0][1]), (-a[1][0], a[0][0]))


def inv(a):
    assert det(a)
    return tuple(tuple(t / det(a) for t in row) for row in adj(a))


def mv(a, x):
    return tuple(sum(a[i][j] * x[j] for j in range(2)) for i in range(2))


def rm(x, a):
    return tuple(sum(x[i] * a[i][j] for i in range(2)) for j in range(2))


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def outer(x, y):
    return tuple(tuple(a * b for b in y) for a in x)


def matrix_scale(c, a):
    return tuple(tuple(c * t for t in row) for row in a)


def cup(j, epsilon, left, right):
    f, s = left
    fp, sp = right
    return epsilon * (area(f, mv(j, sp)) - area(s, mv(j, fp)))


def valuation(x, p=2):
    assert x
    n, d = x.numerator, x.denominator
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    while d % p == 0:
        d //= p
        result -= 1
    return result


def model(j, v, a, b, kappa, transport, epsilon, strict, alpha_f, alpha_s):
    zero = (Q(0), Q(0))
    assert v != zero and det(j) == -1
    assert all(mv(j, mv(j, e)) == e for e in ((Q(1), Q(0)), (Q(0), Q(1))))
    x = (Q(0), 1 / v[0]) if v[0] else (-1 / v[1], Q(0))
    eta = area(v, x)
    theta = area(a, b)
    assert eta and theta and strict and transport and epsilon and kappa
    delta = det(j)
    jv, jx = mv(j, v), mv(j, x)
    # Boundary evaluations use the actual local-transport pattern, BEFORE
    # either normalizer or row is constructed.
    partner_f = (scale(transport, v), zero)
    partner_s = (zero, scale(-transport, jv))
    qf = kappa * cup(j, epsilon, (zero, jx), partner_f)
    qs = kappa * cup(j, epsilon, (x, zero), partner_s)
    assert qf == -kappa * transport * epsilon * eta
    assert qs == kappa * transport * epsilon * eta
    af = outer(a, (-v[1] / eta, v[0] / eta))
    ass = outer(b, (-jv[1] / (delta * eta), jv[0] / (delta * eta)))
    lf = rm((Q(0), qf), inv(cols(a, b)))
    ls = rm((qs, Q(0)), inv(cols(a, b)))
    assert mv(af, v) == mv(ass, jv) == zero
    assert mv(af, x) == a and mv(ass, jx) == b
    assert rm(lf, af) == rm(ls, ass) == zero
    assert dot(lf, b) == qf and dot(ls, a) == qs
    # Check all-vector identities on a spanning grid, including zero and
    # directions on the class line, not just the chosen complement.
    for z in itertools.product(map(Q, (-2, 0, 1, 3)), repeat=2):
        assert dot(lf, mv(ass, z)) == kappa * cup(j, epsilon, (zero, z), partner_f)
        assert dot(ls, mv(af, z)) == kappa * cup(j, epsilon, (z, zero), partner_s)
    uf, us = -eta * qf / theta, delta * eta * qs / theta
    assert outer(v, lf) == matrix_scale(uf, adj(af))
    assert outer(jv, ls) == matrix_scale(us, adj(ass))
    assert us == delta * uf
    # c is the image of the SAME integral strict determinant generator.
    # It is not assumed to be a unit; alpha_i are retained-basis units.
    actual_f, actual_s = uf / strict / alpha_f, us / strict / alpha_s
    assert actual_s == delta * alpha_f / alpha_s * actual_f
    assert valuation(actual_f) == valuation(actual_s)
    return {
        "qf": qf, "qs": qs, "uf": uf, "us": us,
        "actual_f": actual_f, "actual_s": actual_s,
        "j": j, "v": v, "x": x, "partner_f": partner_f,
        "kappa": kappa, "epsilon": epsilon,
    }


def main():
    js = [((Q(0), Q(1)), (Q(1), Q(0))),
          ((Q(1), Q(1)), (Q(0), Q(-1))),
          ((Q(1), Q(3)), (Q(0), Q(-1))),
          ((Q(2), Q(1)), (Q(-3), Q(-2)))]
    vectors = [(Q(2**r), Q(2**r * t)) for r in range(5) for t in (-2, 1, 3)]
    vectors += [(Q(0), Q(8)), (Q(3, 2), Q(5, 4))]
    frames = [((Q(2), Q(1)), (Q(1), Q(3))),
              ((Q(4), Q(0)), (Q(0), Q(2))),
              ((Q(1, 2), Q(2)), (Q(-1), Q(3, 2)))]
    # Common strict factors cover both possible torsion shift parities.
    stricts = [Q(2**r) for r in range(5)] + [Q(1, 2**r) for r in range(1, 5)]
    count = 0
    sample = None
    for j, v, (a, b), strict in itertools.product(js, vectors, frames, stricts):
        sample = model(j, v, a, b, Q(4), Q(3), Q(5), strict, Q(3), Q(5, 7))
        count += 1
    assert sample is not None
    f, s = sample["actual_f"], sample["actual_s"]
    controls = {}
    # Scaling only one stored functional preserves closedness and ranks,
    # but must fail the dyadic unit conclusion.
    controls["one_functional_times_two_changes_v2"] = valuation(2 * s) != valuation(f)
    controls["one_strict_factor_times_two_changes_v2"] = valuation(s / 2) != valuation(f)
    controls["one_cone_sign_breaks_exact_opposite_evaluations"] = sample["qs"] != sample["qf"]
    # An extra J at one coefficient pairing is a type/convention error;
    # use a case where it destroys the nonzero cross evaluation.
    j = js[0]
    v, x, zero = (Q(1), Q(0)), (Q(0), Q(1)), (Q(0), Q(0))
    expected = cup(j, Q(1), (zero, mv(j, x)), (v, zero))
    twice_j = cup(j, Q(1), (zero, mv(j, x)), (mv(j, v), zero))
    controls["extra_J_destroyed_cross_value"] = expected != 0 and twice_j == 0
    controls["zero_partner_has_no_nonzero_cross_witness"] = all(
        cup(j, Q(1), (zero, e), (zero, zero)) == 0
        for e in ((Q(1), Q(0)), (Q(0), Q(1))))
    controls["unit_at_t_is_not_a_dyadic_unit"] = valuation(Q(2)) == 1
    # Characterwise dyadic units need not descend to the integral group ring.
    chars = (Q(1), Q(1), Q(1), Q(3))
    hadamard = ((1, 1, 1, 1), (1, -1, 1, -1),
                (1, 1, -1, -1), (1, -1, -1, 1))
    coeffs = tuple(sum(Q(h) * c for h, c in zip(row, chars)) / 4 for row in hadamard)
    controls["characterwise_units_do_not_establish_integral_descent"] = (
        all(valuation(c) == 0 for c in chars) and any(valuation(c) < 0 for c in coeffs))
    assert all(controls.values()), controls
    print(json.dumps({
        "status": "PASS", "exact_model_count": count,
        "all_vector_grid_checks_per_model": 32,
        "negative_controls_detected": controls,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Exact rational finite models and adverse hypotheses; no arithmetic cohomology or universal proof is computed",
    }, indent=2))


if __name__ == "__main__":
    main()
