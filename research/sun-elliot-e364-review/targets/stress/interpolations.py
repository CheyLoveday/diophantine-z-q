#!/usr/bin/env python3
"""Adversarial bounded E364 diagnostics and held-out height interpolations.

The fits are descriptive only. They are not an existence theorem, a uniform
constant, or a route around the missing source-global proof.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path
import numpy as np


def spf_sieve(n):
    spf = list(range(n + 1))
    for p in range(2, math.isqrt(n) + 1):
        if spf[p] == p:
            for j in range(p * p, n + 1, p):
                if spf[j] == j:
                    spf[j] = p
    return spf


def factor(n, spf):
    out = {}
    while n > 1:
        p = spf[n]
        out[p] = out.get(p, 0) + 1
        n //= p
    return out


def marked(N, spf):
    fs = [factor(N + i, spf) for i in (-1, 0, 1)]
    powers = {}
    for f in fs:
        for p, k in f.items():
            powers[p] = powers.get(p, 0) + k
    D = math.prod(p for p, k in powers.items() if k % 2)
    s = math.prod(p ** (k // 2) for p, k in powers.items())
    kernels = tuple(math.prod(p for p, k in f.items() if k % 2) for f in fs)
    return D, s, powers, kernels


def fit(train, test, value):
    xtr = np.array([math.log(n) for n, *rest in train])
    ytr = np.array([value(*row) for row in train])
    a, b = np.linalg.lstsq(np.column_stack((np.ones(len(xtr)), xtr)), ytr, rcond=None)[0]
    def errors(rows):
        if not rows:
            return None
        errs = [a + b * math.log(row[0]) - value(*row) for row in rows]
        actual = [value(*row) for row in rows]
        ss_res = sum(e * e for e in errs)
        mean = sum(actual) / len(actual)
        ss_tot = sum((y - mean) ** 2 for y in actual)
        return {'rmse': math.sqrt(ss_res / len(rows)),
                'r2': 1 - ss_res / ss_tot if ss_tot else None,
                'max_abs_error': max(map(abs, errs))}
    return {'intercept': a, 'log_N_coefficient': b,
            'train': errors(train), 'holdout': errors(test)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scan-limit', type=int, default=200000)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.scan_limit < 20000 or args.scan_limit % 2:
        raise ValueError('scan limit must be even and at least 20000')
    spf = spf_sieve(args.scan_limit + 1)
    scans, depths, powerful_cases = 0, 0, []
    for N in range(2, args.scan_limit + 1, 2):
        D, s, powers, kernels = marked(N, spf)
        scans += 1
        assert N * (N * N - 1) == D * s * s
        # All exact local identities in the attachment, not the unproved
        # existence statement D|s. The shortest pairwise-coprime countercontrol
        # below shows why splitting the product needs the extra hypothesis.
        is_power = D and s % D == 0
        defect = D // math.gcd(D, s)
        assert is_power == (defect == 1)
        expected_depth = 1 + ((s & -s).bit_length() - 1) if s else None
        # z = -x/y has denominator factors which are odd in N; this exact
        # quotient form also keeps N^2+1 explicitly.
        x_num = (N * N + 1) ** 2
        y_num = (N * N + 1) * (N * N - 2 * N - 1) * (N * N + 2 * N - 1)
        assert math.gcd(x_num, 4 * s * s) == 1
        assert math.gcd(abs(y_num), 8 * s ** 3) == 1
        for p, k in powers.items():
            if p != 2 and k % 2:
                depths += 1
                # v_p(s) is (k-1)/2 under the squarefree decomposition.
                assert (k - 1) % 2 == 0
        if is_power:
            powerful_cases.append({'N': N, 'D': D, 's': s,
                                   'left_start_mod_four': (N - 1) % 4,
                                   'kernels': kernels})
            assert N % 4 == 0
        # The B2=2s collision test is collected separately below.
    collisions = {}
    for N in range(2, 10002, 2):
        D, s, powers, kernels = marked(N, spf)
        collisions.setdefault(2 * s, []).append((N, kernels))
    collision_rows = []
    for B2, rows in collisions.items():
        if len(rows) >= 2:
            collision_rows.append({'B2': B2, 'sources': rows[:3]})
            if len(collision_rows) >= 3:
                break

    # Numerical interpolations of exact rational Weil heights, trained on the
    # first 500 even midpoints and evaluated on later even midpoints only.
    fit_rows = []
    for N in range(2, 200002, 2):
        D, s, powers, kernels = marked(N, spf)
        xn, xd = (N * N + 1) ** 2, 4 * s * s
        yn = abs((N * N + 1) * (N * N - 2 * N - 1) * (N * N + 2 * N - 1))
        yd = 8 * s ** 3
        fit_rows.append((N, xn, xd, yn, yd))
    tr, te = fit_rows[:500], fit_rows[500:]
    hx = lambda N, xn, xd, yn, yd: math.log(max(xn, xd))
    hy = lambda N, xn, xd, yn, yd: math.log(max(yn, yd))
    result = {
        'scope': 'Adversarial bounded diagnostics and descriptive fits; no global E364 result',
        'scan': {'even_midpoints': scans, 'limit': args.scan_limit,
                 'odd_prime_support_events': depths,
                 'powerful_cases': powerful_cases,
                 'powerful_case_count_is_bounded_evidence_only': True},
        'pairwise_coprime_countercontrol': {
            'a': 2, 'b': 2, 'product': 4,
            'product_has_no_exponent_one': True,
            'factor_has_no_exponent_one': False,
            'explanation': 'v_2(4)=2 while v_2(2)=1; coprimality is needed for product-to-factor splitting'
        },
        'unmarked_denominator_collisions': collision_rows,
        'held_out_rational_height_interpolations': {
            'training_even_midpoints': len(tr), 'holdout_even_midpoints': len(te),
            'x_2P': fit(tr, te, hx), 'y_2P': fit(tr, te, hy),
            'warning': 'log-linear fits over separate source data do not provide fixed-curve constants, common sources, or a global contradiction'
        }
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
