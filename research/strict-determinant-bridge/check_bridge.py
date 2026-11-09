#!/usr/bin/env python3
"""Exact finite checks for the strict determinant bridge; no arithmetic oracle.

Standard-library only. Independently computes coordinates from full adjugates,
then compares the separate exact-sequence formulas and common strict scale.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(c, a):
    return [c * x for x in a]


def cols(a, b):
    return [[a[0], b[0]], [a[1], b[1]]]


def mv(m, v):
    return [dot(row, v) for row in m]


def mm(a, b):
    return [[dot(row, col) for col in zip(*b)] for row in a]


def rowmul(r, m):
    return [dot(r, col) for col in zip(*m)]


def det(m):
    if not m:
        return Q(1)
    return sum(((-1) ** j * m[0][j] * det([row[:j] + row[j + 1:]
        for row in m[1:]]) for j in range(len(m))), Q(0))


def adj(m):
    n = len(m)
    return [[(-1) ** (i + j) * det([
        [m[r][c] for c in range(n) if c != i]
        for r in range(n) if r != j]) for j in range(n)] for i in range(n)]


def inv(m):
    d = det(m)
    assert d
    return [[x / d for x in row] for row in adj(m)]


def outer(v, r):
    return [[x * y for y in r] for x in v]


def inferred_coordinate(d, z, lam):
    """Use a nonzero adjugate entry, then check EVERY tensor entry."""
    a, t = adj(d), outer(z, lam)
    candidates = [t[i][j] / a[i][j] for i in range(len(d))
                  for j in range(len(d)) if a[i][j]]
    assert candidates, "nonzero adjugate guard failed"
    u = candidates[0]
    assert all(t[i][j] == u * a[i][j] for i in range(len(d))
               for j in range(len(d))), "full cofactor identity failed"
    return u


def vprime(q, p=2):
    assert q
    n, d = abs(q.numerator), q.denominator
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return v


def embedded_disk(d, m):
    return [[d, Q(0), Q(0)], [Q(0), *m[0]], [Q(0), *m[1]]]


def as_json(x):
    if isinstance(x, Q):
        return str(x)
    if isinstance(x, (tuple, list)):
        return [as_json(v) for v in x]
    if isinstance(x, dict):
        return {k: as_json(v) for k, v in x.items()}
    return x


def main():
    rng = random.Random(20261109)
    counts = {k: 0 for k in ["rank_one_models", "full_adjugate_identities",
        "exact_triangle_formulas", "fractional_complements",
        "complement_changes", "quotient_lift_changes", "strict_nonunit_disks",
        "generic_strict_basis_changes", "integral_basis_unit_changes",
        "rescaled_functional_failures"]}
    controls = {}
    samples = []

    # Fix convention with a direct normal complex, including a nonunit disk.
    normal = [[Q(0), Q(0)], [Q(0), Q(1)]]
    assert inferred_coordinate(normal, [Q(1), Q(0)], [Q(1), Q(0)]) == 1
    assert inferred_coordinate([[Q(0), Q(0)], [Q(0), Q(8)]],
                               [Q(1), Q(0)], [Q(1), Q(0)]) == Q(1, 8)
    # A completely integral pair over Z_(2), with an actual common nonunit
    # strict disk. Generic randomized models below need not themselves have
    # integral boundary matrices in their chosen fractional W-basis.
    integral_f = [[Q(0), Q(0)], [Q(0), Q(1)]]
    integral_s = [[Q(0), Q(-1)], [Q(0), Q(0)]]
    assert inferred_coordinate(embedded_disk(Q(2), integral_f),
        [Q(0), Q(1), Q(0)], [Q(0), Q(-1), Q(0)]) == Q(-1, 2)
    assert inferred_coordinate(embedded_disk(Q(2), integral_s),
        [Q(0), Q(1), Q(0)], [Q(0), Q(0), Q(1)]) == Q(1, 2)

    for k in range(180):
        div = Q(2 ** (k % 7))
        v = [div * Q(rng.choice([-5, -3, -1, 1, 3, 5])),
             div * Q(rng.randint(-5, 5))]
        x = [Q(0), 1 / v[0]]  # det[v,x]=1; often necessarily fractional.
        eta = det(cols(v, x))
        assert eta == 1
        counts["fractional_complements"] += int(any(t.denominator != 1 for t in x))
        j = [[Q(1), Q(rng.randint(-5, 5))], [Q(0), Q(-1)]]
        assert mm(j, j) == [[Q(1), Q(0)], [Q(0), Q(1)]] and det(j) == -1
        delta, jv, jx = det(j), mv(j, v), mv(j, x)
        while True:
            a = [Q(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(2)]
            b = [Q(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(2)]
            theta = det(cols(a, b))
            if theta:
                break
        # Boundary maps are made from cycle/kernel data, rather than from the
        # desired coordinate. Rows are made from local cup values on actual a,b.
        af = outer(a, [-v[1] / eta, v[0] / eta])
        etas = det(cols(jv, jx))
        ass = outer(b, [-jv[1] / etas, jv[0] / etas])
        dual = inv(cols(a, b))
        rho = Q(rng.choice([-9, -5, -3, 1, 3, 7]), 2 ** (k % 4))
        qf, qs = -rho * eta, rho * eta
        rf, rs = scale(qf, dual[1]), scale(qs, dual[0])
        assert mv(af, v) == [0, 0] and mv(ass, jv) == [0, 0]
        assert mv(af, x) == a and mv(ass, jx) == b
        assert rowmul(rf, af) == [0, 0] and rowmul(rs, ass) == [0, 0]
        assert dot(rf, b) == qf and dot(rs, a) == qs
        uf = inferred_coordinate(af, v, rf)
        us = inferred_coordinate(ass, jv, rs)
        counts["rank_one_models"] += 1
        counts["full_adjugate_identities"] += 2
        assert uf == -eta * qf / theta
        assert us == delta * eta * qs / theta
        assert us == delta * uf
        counts["exact_triangle_formulas"] += 2

        # Choice independence of the two short-exact-sequence wedge formula.
        for _ in range(4):
            r = Q(rng.choice([-4, -2, -1, 1, 2, 3]), rng.randint(1, 5))
            s = Q(rng.randint(-5, 5), rng.randint(1, 5))
            xp = add(scale(r, x), scale(s, v))
            ap, bp = mv(af, xp), mv(ass, mv(j, xp))
            ep, tp = det(cols(v, xp)), det(cols(ap, bp))
            assert -ep * dot(rf, bp) / tp == uf
            assert delta * ep * dot(rs, ap) / tp == us
            counts["complement_changes"] += 2
            yf = add(scale(r, b), scale(s, a))
            ys = add(scale(r, a), scale(s, b))
            assert eta * dot(rf, yf) / det(cols(yf, a)) == uf
            assert etas * dot(rs, ys) / det(cols(ys, b)) == us
            counts["quotient_lift_changes"] += 2

        # Independent computation in larger presentations with integral strict
        # disks. The surrounding boundary matrices are generic K-matrices.
        for exponent in (1, 2, 5, 9):
            disk = Q(2 ** exponent)
            fullf, fulls = embedded_disk(disk, af), embedded_disk(disk, ass)
            ufullf = inferred_coordinate(fullf, [Q(0), *v], [Q(0), *rf])
            ufulls = inferred_coordinate(fulls, [Q(0), *jv], [Q(0), *rs])
            assert ufullf == uf / disk and ufulls == us / disk
            assert vprime(ufullf) == vprime(uf) - exponent
            assert vprime(ufullf) == vprime(ufulls)
            counts["strict_nonunit_disks"] += 2
            counts["full_adjugate_identities"] += 2
            if not controls.get("discard_common_strict_torsion"):
                assert ufullf != uf
                controls["discard_common_strict_torsion"] = {
                    "rejected": True, "disk": disk, "actual": ufullf,
                    "incorrect_without_c": uf}

        # A nonintegral choice of basis for generic W is allowed. Its determinant
        # changes the matrix coordinate and c together, keeping actual u fixed.
        change = [[Q(2 ** (1 + k % 4)), Q(rng.randint(-5, 5))], [Q(0), Q(3, 5)]]
        invchange = inv(change)
        for matrix, z, row, u in ((af, v, rf, uf), (ass, jv, rs, us)):
            transformed = inferred_coordinate(mm(invchange, matrix), z, rowmul(row, change))
            c = Q(2 ** (k % 6))
            cprime = c * det(change)
            assert transformed == det(change) * u
            assert transformed / cprime == u / c
            counts["generic_strict_basis_changes"] += 1
            counts["full_adjugate_identities"] += 1

        # Stored integral determinant bases differ from triangle bases by units.
        alpha_f, alpha_s = Q(3, 5), Q(-7, 9)
        c = Q(2 ** (k % 8))
        stored_f, stored_s = uf / (alpha_f * c), us / (alpha_s * c)
        assert stored_s / stored_f == delta * alpha_f / alpha_s
        assert vprime(stored_f) == vprime(stored_s)
        counts["integral_basis_unit_changes"] += 1

        # Actual row identity is indispensable: all kernels/closedness survive.
        wrong_row = scale(Q(2), rs)
        assert rowmul(wrong_row, ass) == [0, 0]
        wrong_u = inferred_coordinate(ass, jv, wrong_row)
        assert vprime(wrong_u) == vprime(uf) + 1
        assert wrong_u != delta * uf
        counts["rescaled_functional_failures"] += 1
        if "independent_functional_rescale" not in controls:
            controls["independent_functional_rescale"] = {
                "rejected": True, "u_finite": uf, "u_singular_rescaled": wrong_u,
                "dyadic_valuation_difference": vprime(wrong_u) - vprime(uf)}
            controls["one_frame_sign_flip"] = {
                "rejected": -us != delta * uf,
                "correct_u_singular": us, "incorrect_one_sided_sign": -us}
        if k < 3:
            samples.append({"v": v, "x": x, "a": a, "b": b, "J": j,
                "qF": qf, "qS": qs, "u_mat_F": uf, "u_mat_S": us,
                "strict_c": c, "stored_uF": stored_f, "stored_uS": stored_s})

    # Separate vanishing-row check, with independence supplied independently.
    zero_row = [Q(0), Q(0)]
    assert inferred_coordinate(normal, [Q(1), Q(0)], zero_row) == 0
    controls["zero_localization"] = {
        "rejected": det(cols([Q(0), Q(0)], [Q(1), Q(2)])) == 0,
        "reason": "area guard cannot hold for v=0"}
    # Characterwise units do not imply an integral dyadic universal element.
    character_values = [Q(1), Q(1), Q(1), Q(3)]
    fourier = [[1, 1, 1, 1], [1, 1, -1, -1],
               [1, -1, 1, -1], [1, -1, -1, 1]]
    coefficients = [dot(row, character_values) / 4 for row in fourier]
    assert all(vprime(q) == 0 for q in character_values)
    assert any(vprime(q) < 0 for q in coefficients)
    controls["characterwise_universal_descent"] = {
        "rejected": True, "character_values": character_values,
        "nonintegral_group_ring_coefficients": coefficients}
    assert all(v["rejected"] for v in controls.values())
    sources = [Path(__file__), HERE / "DERIVATION.md", HERE / "APPLICATION.md"]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sources}
    result = {"status": "PASS", "profile": "exact finite algebra only",
        "seed": 20261109, "counts": counts, "negative_controls": controls,
        "samples": samples, "input_hashes": hashes,
        "not_established": ["actual global Galois cup/trace",
            "orthogonal comparison arithmetic construction",
            "retained-limit coherence", "universal group-ring descent",
            "Lean determinant-functor formalization"]}
    target = HERE / "evidence/checks.json"
    target.write_text(json.dumps(as_json(result), indent=2) + "\n")
    print(json.dumps({"status": result["status"], "counts": counts,
                      "negative_controls": len(controls), "result": str(target)}, indent=2))


if __name__ == "__main__":
    main()
