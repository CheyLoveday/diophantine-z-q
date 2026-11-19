#!/usr/bin/env python3
"""Independent finite truth-table oracle, not a Lean proof."""
from itertools import product


def coupled(source, f, g, pair):
    return any((f(s), g(s)) == pair for s in source)


def marginal(source, f, g, pair):
    return any(f(s) == pair[0] for s in source) and any(
        g(s) == pair[1] for s in source
    )


def check_all_boolean_maps():
    source = (False, True)
    codomain = (False, True)
    maps = [dict(zip(source, outputs)) for outputs in product(codomain, repeat=2)]
    tests = 0
    for ma, mb, pair in product(maps, maps, product(codomain, repeat=2)):
        f, g = ma.__getitem__, mb.__getitem__
        if coupled(source, f, g, pair):
            assert marginal(source, f, g, pair)
        tests += 1
    ident = lambda s: s
    neg = lambda s: not s
    assert marginal(source, ident, neg, (True, True))
    assert not coupled(source, ident, neg, (True, True))
    return tests


if __name__ == "__main__":
    n = check_all_boolean_maps()
    print(f"PASS {n} boolean-map/pair checks; coupled => marginal; converse rejected")
