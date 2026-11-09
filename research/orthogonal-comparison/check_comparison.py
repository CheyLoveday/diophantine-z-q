#!/usr/bin/env python3
"""Exact finite-ring checks of the new cone/homotopy identities.
These are model checks, not arithmetic instances or proofs of Selmer duality.
"""
from pathlib import Path
import hashlib
import json
import random
import sys

ROOT = Path(__file__).resolve().parents[2]
PACKET = Path(__file__).resolve().parent


def run():
    rng = random.Random(20261109)
    cone = 0
    bad_sign_rejected = 0
    for n in [2, 4, 8, 16, 32]:
        for _ in range(160):
            dG, dU, dL, loc, incp, a1, h0, h1 = [rng.randrange(n) for _ in range(8)]
            a0 = rng.choice([x for x in range(n) if x % 2])
            dV = a1 * dU * pow(a0, -1, n) % n
            inc = (incp * a0 + dL * h0 + h1 * dU) % n
            for _ in range(8):
                g, u, q = [rng.randrange(n) for _ in range(3)]
                # D' j versus j D, in H22 convention.
                left = (dG*g % n, dV*a0*u % n,
                        (loc*g-incp*a0*u-dL*(q+h0*u)) % n)
                right = (dG*g % n, a1*dU*u % n,
                         (loc*g-inc*u-dL*q+h1*dU*u) % n)
                assert left == right
                wrong = (loc*g-incp*a0*u-dL*(q-h0*u)) % n
                if wrong != right[2]:
                    bad_sign_rejected += 1
                cone += 1
    assert bad_sign_rejected > 0

    # Two-term complexes Z/n --r--> Z/n. k=id+dH+Hd is chain homotopic
    # to id, even when the matrices differ and no field inversion is possible.
    homotopy = 0
    for n in [2, 4, 8, 16]:
        for r in range(n):
            boundaries = {r*x % n for x in range(n)}
            for h in range(n):
                k = (1+r*h) % n
                for y in range(n):
                    difference = (k*y-y) % n
                    assert difference == r*h*y % n
                    assert difference in boundaries
                    for local in [0, 1, 3]:
                        assert local*difference % n in {local*b % n for b in boundaries}
                    homotopy += 1
    # An arbitrary inverse-shaped map is inadmissible: multiplication by 2 on
    # the zero-differential complex mod 8 changes [1], hence cannot satisfy hk.
    assert (2*1-1) % 8 not in {0}
    bad_inverse = {"modulus": 8, "differential": 0, "purported_inverse": 2,
                   "class": 1, "difference": 1, "rejected": True}

    # Finite Artin rings do not license t^-1: t=2 in Z/8 is nilpotent.
    assert pow(2, 3, 8) == 0
    assert not any(2*x % 8 == 1 for x in range(8))
    return {"status": "PASS", "cone_cases": cone,
            "wrong_cone_sign_counterexamples": bad_sign_rejected,
            "homotopy_class_cases": homotopy,
            "negative_controls": {"arbitrary_map_without_homotopy": bad_inverse,
                                  "nilpotent_t_inverse_rejected": True},
            "scope": "Exact algebraic model checks; no actual arithmetic/Galois computation",
            "sources": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in [Path(__file__), ROOT/'lean/Research/DerivativeSwitch/OrthogonalComparison.lean',
                                  ROOT/'manuscripts/quartic_v13.tex']}}

if __name__ == '__main__':
    result = run()
    output = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if len(sys.argv) == 2:
        Path(sys.argv[1]).write_text(output)
    elif len(sys.argv) != 1:
        raise SystemExit('usage: check_comparison.py [OUTPUT_JSON]')
    print(output, end='')
