#!/usr/bin/env python3
"""Emit the standalone bypass and closure check to stdout. Run from the repository root.

Compose the live bundle conversions below frozenTarget, as in the fold-b105
bypass. Fail if the expected chain shape or reader changes. No board writes.
Pass --counts for the before/after board counts and the composed path.
"""

import csv
import re
import sys
from collections import Counter
from pathlib import Path

H = Path("ZInQKernel/OneProof/H")
CONTRIB = Path("ZInQKernel/Contrib/OneProof")
MAIN = Path("ZInQKernel/OneProof/Main.lean").read_text()
SOURCES = [
    (H / f"TailZ{i}.lean").read_text() for i in (87, 91, 92, 93)
] + [(CONTRIB / "NOSNarrowChain.lean").read_text()]
OLD = "javanpeykarThm111An"
NEW = "javanpeykarThm111JacKEx"
NEW_TYPE = "JavanpeykarJacK.JavanpeykarThm111JacKEx"
NS = "_root_.HDec.HSyn."
NEW_CONV = "openResearchLeaves36EBCFSFU_y3x6_of_67_jp"
NEW_H = "sixContactMin_of_open86_jp"
NEW_TOP = "frozenTarget_jp"


def declaration(kind, name):
    """Return declaration start and indented continuation, skipping the docstring."""
    short = name.rsplit(".", 1)[-1]
    pat = rf"^{kind} (?:[\w.]+\.)?{short}\b[^\n]*(?:\n +[^\n]+)*"
    hits = [m[0] for src in SOURCES for m in re.finditer(pat, src, re.M)]
    if len(hits) != 1:
        raise ValueError(f"{name}: expected one declaration, found {len(hits)}")
    return hits[0]


def split_args(term):
    """Parse top-level whitespace in the parenthesized applications of this chain."""
    term = term.strip()
    depth = start = 0
    args = []
    for i, c in enumerate(term):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c.isspace() and depth == 0:
            if i > start:
                args.append(term[start:i])
            start = i + 1
    assert depth == 0
    if start < len(term):
        args.append(term[start:])
    return args


def unparen(term):
    if term.startswith("(") and term.endswith(")") and len(split_args(term)) == 1:
        return term[1:-1].strip()
    return term


def paren(term):
    return term if re.fullmatch(r"[\w.']+", term) or unparen(term) != term else f"({term})"


def substitute(term, env):
    """Substitute projections of the symbolic research bundle and scalar arguments."""
    if not env:
        return term
    pat = re.compile(r"(?<![\w.'])(" + "|".join(map(re.escape, env)) + r")(?![\w'])(?:\.(\w+))?")

    def replace(match):
        var, field = match.groups()
        value = env[var]
        if isinstance(value, dict):
            if field not in value:
                raise ValueError(f"Unfilled projection in {term}: {match[0]}")
            return paren(value[field])
        return paren(value) + (f".{field}" if field else "")

    return pat.sub(replace, term)


def assignments(body):
    values = {}
    for line in body.splitlines():
        if match := re.fullmatch(r"  (\w+) := (.+)", line):
            values[match[1]] = match[2]
        elif line.startswith("    ") and values:
            values[next(reversed(values))] += " " + line.strip()
        else:
            raise ValueError(f"Unexpected equation: {line}")
    return values


def fields(text):
    return re.findall(r"^  (\w+) :", text, re.M)


def read_conversion(name):
    decl = declaration("theorem", name)
    header, body = decl.split(" where\n", 1)
    binders = re.findall(r"\((\w+) : ([\w.]+)\)", header)
    result = header.rsplit(" : ", 1)[1]
    return [x for x, _ in binders], result, assignments(body)


READ = (
    "(_root_.JavanpeykarRebase.javanpeykarBound_of_printed_rebase_final "
    "(_root_.JavanpeykarDirect.javanpeykarPrintedMap_of_thm111 "
    "(_root_.JavanpeykarAnRetype.javanpeykarThm111_of_an n.javanpeykarThm111An "
    "_root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)) "
)
NEW_READ = f"(_root_.JavanpeykarJacK.javanpeykarBound_of_jacKEx n.{NEW} "
NERON = (
    "(_root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension "
    "(_root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind "
    "n.neronSchemeExtensionDedekind))"
)


def generate():
    top = re.search(r"^theorem _root_\.ZInQ\.OneProof\.frozenTarget\n(?: +[^\n]+\n)+", MAIN, re.M)[0]
    r0 = re.search(r"\(r : HDec.HSyn.(\w+)\)", top)[1]
    old_h = re.search(r"\(HDec\.HSyn\.(sixContactMin_of_open\w+) r t l\)", top)[1]
    new_r = r0 + "_jp"
    structure = declaration("structure", r0)
    new_structure, replaced = re.subn(
        rf"^  /-- [^\n]* -/\n  {OLD} : [^\n]*$",
        "  /-- Javanpeykar's Theorem 1.1.1 with Section 2.3 at the Jacobian over K. -/\n"
        f"  {NEW} : _root_.{NEW_TYPE}",
        structure.replace(f"structure {r0} ", f"structure {new_r} "),
        flags=re.M,
    )
    assert replaced == 1
    walked, readers = [], []

    def apply(term, root, value, locals_):
        term = unparen(term)
        if term == root:
            return value
        name, inner, *extra = split_args(term)
        inner_value = apply(inner, root, value, locals_)
        params, result, equations = read_conversion(name)
        env = dict(zip(params, [inner_value] + [substitute(a, locals_) for a in extra], strict=True))
        out = {}
        for field, rhs in equations.items():
            if field == OLD:
                assert rhs == f"{params[0]}.{OLD}"
                continue
            if f".{OLD}" in rhs:
                assert field == "javanpeykarBound" and rhs.startswith(READ) and rhs.endswith(")")
                rhs = NEW_READ + rhs[len(READ):-1] + f" {NERON} n.faltingsSemistableHeightBC)"
                readers.append(name)
            out[field] = substitute(rhs, env)
        if OLD in equations:
            out[NEW] = inner_value[NEW]
        else:
            assert len(readers) == 1 and not stop
            stop.extend((name, result, out))
        walked.append(name)
        return out

    # The first four H calls only forward (converted research, t, l).
    value = {f: f"n.{f}" for f in fields(new_structure)}
    cur = old_h
    stop = []
    while cur != "sixContactMin_of_open82_nos":
        decl = declaration("theorem", cur)
        header, body = decl.split(":=", 1)
        assert "ZInQ.SixContactMin" in header and "let " not in body
        cur, arg, t, l = split_args(body)
        assert (t, l) == ("t", "l")
        value = apply(arg, "r", value, {"t": "t", "l": "l"})
    assert not stop
    decl = declaration("theorem", cur)
    header, body = decl.split(":=", 1)
    let_t16, call = body.strip().split("\n", 1)
    assert let_t16.startswith("let t16 :=")
    parts = split_args(call)
    [i] = [i for i, arg in enumerate(parts) if "(openResearchLeaves60_y3x6_of_" in arg]

    # Separate the portion of the nested research expression below the live reader;
    # the downstream conversions and the other arguments are reused.
    target = parts[i]
    outers = []
    while True:
        name, inner, *extra = split_args(unparen(target))
        if "openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6_nos" in name:
            break
        outers.append((name, extra))
        target = inner
    apply(target, "r", value, {"t": "t", "l": "l"})
    reader, result, equations = stop
    assert readers == [reader]
    assert result == "OpenResearchLeaves36EBCFSFU_y3x6NOS"
    assert set(equations) == set(fields(declaration("structure", result)))

    rexpr = f"({NEW_CONV} r t l)"
    for name, extra in reversed(outers):
        rexpr = "(" + " ".join([name, rexpr, *extra]) + ")"
    parts[i] = rexpr
    parts = [substitute(p, {"r": {k: substitute(v, {"n": "r"}) for k, v in value.items()}})
             if j != i else p for j, p in enumerate(parts)]
    old_arg = f"(HDec.HSyn.{old_h} r t l)"
    new_top = top.replace("ZInQ.OneProof.frozenTarget\n", f"ZInQ.OneProof.{NEW_TOP}\n")
    new_top = new_top.replace(f"HDec.HSyn.{r0})", f"HDec.HSyn.{new_r})").replace(
        old_arg, f"(HDec.HSyn.{NEW_H} r t l)")
    assert new_top != top and old_arg not in new_top

    out = f"""import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.JavanpeykarJacKEx

/-! Generated by scratch/jp-jack/gen_bypass.py.
The composite joins the unchanged chain at GR9.{result}.
The old Main import makes the closure comparison possible in the same file. -/

namespace HDec.HSyn

set_option linter.style.longLine false

/-- Same open research fields with the Javanpeykar bound over K. -/
{new_structure}

/-- Compose the research conversions up to the first bundle that holds the
bound consumed by the chain. -/
theorem {NEW_CONV} (n : {new_r}) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves28) :
    GR9.{result} where
"""
    out += "".join(f"  {f} := {rhs}\n" for f, rhs in equations.items())
    out += ("\n" + header.replace(cur, NEW_H).replace("OpenResearchLeaves63NOS", new_r) + ":=\n"
            + f"  {let_t16}\n  {parts[0]}\n" + "".join(f"    {p}\n" for p in parts[1:]))
    out += "\nend HDec.HSyn\n\n" + new_top + "\n"
    assert OLD not in out
    return out, structure, new_structure, walked, result


def counts(before, after, walked, stop):
    with Path("docs/one-proof/kinds.tsv").open() as file:
        old = list(csv.DictReader(file, delimiter="\t"))
    research = {r["field"] for r in old if r["bundle"] == "research"}
    added = {r["field"] for r in old if r["bundle"] == "added"}
    assert research == set(fields(before)) and added == set(fields(declaration("structure", "OpenAddedLeaves28")))
    new = [{**r, "field": NEW} if r["field"] == OLD else r for r in old]
    assert {r["field"] for r in new if r["bundle"] == "research"} == set(fields(after))
    assert [r["kind"] for r in old if r["field"] == OLD] == ["consequence"]
    assert len(old) == len(new) == 33
    print("composed:", " -> ".join(walked))
    print("rejoins:", stop)
    for label, rows in [("before", old), ("after", new)]:
        h = [r for r in rows if r["bundle"] != "frozenTarget"]
        print(f"{label}: {len(h)} H + {len(rows) - len(h)} other = {len(rows)} open")
        for k in ["strict", "strictest"]:
            c = Counter(r[k] for r in h)
            total = Counter(r[k] for r in rows)
            print(f"  H {k}: {c['LEAF']} LEAF / {c['GLUE']} GLUE")
            print(f"  overall {k}: {total['LEAF']} LEAF / {total['GLUE']} GLUE")
        assert all(r["strict"] == r["strictest"] == "GLUE" for r in rows if r["field"] in {OLD, NEW})


if __name__ == "__main__":
    out, *args = generate()
    if sys.argv[1:] == ["--counts"]:
        counts(*args)
    elif not sys.argv[1:]:
        print(out, end="")
        print(Path("scratch/jp-jack/ClosureCheck.lean.txt").read_text(), end="")
    else:
        raise SystemExit(__doc__)
