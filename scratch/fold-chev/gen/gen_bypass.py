#!/usr/bin/env python3
"""fold-chev: remove the research field `chevalleyPerfect` (Chevalley over a perfect field) by a bypass.

`ZInQ.ChevFree.semiAbelianDescendsPerfect_proof` (chevalley-free, `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean`)
proves `ZInQ.HeightFix.SemiAbelianDescendsPerfect` outright, the only thing the readers of the field take from it.
autofold cannot remove the field (it needs a proof of `ChevalleyPerfect` itself), and the readers sit several
conversions below the top bundle.  This script, run on any head whose top research bundle still carries the field,

* follows the current top theorem of Main.lean (`sixContactMin_of_open<N>`) down its chain of
  `theorem sixContactMin_... (r : R) (t : T) (l : L) : ZInQ.SixContactMin := callee args` until the first callee whose
  research bundle no longer has the field (on 1a3bab4a: `sixContactMin_of_open53_eb_k954`, bundle
  `OpenResearchLeaves36EB`);
* composes, field by field, the research-bundle conversions applied on the way (symbolic substitution of
  `n.<field>` / `t` / `l`), with the readers of the field replaced:
    `SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley X.chevalleyPerfect` -> `ChevFree.semiAbelianDescendsPerfect_proof`
    `SemiAbDescend.<f>_of_printed_chevalley a b c X.chevalleyPerfect`          -> `ChevFree.<f>_of_printed_free a b c`;
* writes `ZInQKernel/OneProof/H/TailZ<j>.lean` (first free number after Main's last module) with
  the next research bundle (the top one minus `chevalleyPerfect`, docstrings verbatim), the composite conversion
  and `sixContactMin_of_open<N+1>`; switches Main.lean; drops the field's rows from kinds.tsv and claims.tsv
  (autofold's writers, so the row order is autofold's).

No existing declaration is changed.  Usage, from the repository root:

    python3 scratch/fold-chev/gen/gen_bypass.py [--dry-run]

Then the usual fold checks (build Main + Discharges, frozenTarget axioms, hash guard, OpenStatements, render_open,
frontier_crosswalk, DischargesTest, autoform check).
"""
import csv, glob, os, re, sys

sys.path.insert(0, 'scripts/one_proof')
import autofold as af  # noqa: E402  (its parsers and writers)

FIELD = 'chevalleyPerfect'
CONTRIB = 'ZInQKernel.Contrib.OneProof.ChevalleyFree'
H = af.H
NL = '\n'


def die(m):
    print('gen_bypass: ' + m)
    sys.exit(1)


# ---------------------------------------------------------------- Lean source helpers
_SRC = {fn: open(fn).read() for fn in sorted(glob.glob(H + '*.lean'))}


def find_theorem(name):
    """(params [(var, type)], result type, body lines) of `theorem name ...`, single definition under H."""
    hits = []
    for fn, s in _SRC.items():
        for m in re.finditer(r'^theorem ' + re.escape(name) + r'((?: \([^()]*\))*) :\s*(.*?)(?: where| :=)\s*$', s, re.M):
            hits.append((fn, m))
    if len(hits) != 1:
        die(f'theorem {name}: {len(hits)} definitions')
    fn, m = hits[0]
    params = re.findall(r'\((\w+) : ([^()]*)\)', m.group(1))
    L = _SRC[fn][m.end():].split(NL)[1:]
    body = []
    for l in L:
        if l.strip() == '' or not l.startswith('  '):
            break
        body.append(l)
    return params, m.group(2).strip(), body, m.group(0).endswith('where')


def split_args(s):
    """top-level whitespace-separated arguments of an application (parentheses respected)."""
    out, depth, cur = [], 0, ''
    for c in s.strip():
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        if c.isspace() and depth == 0:
            if cur:
                out.append(cur)
            cur = ''
        else:
            cur += c
    if cur:
        out.append(cur)
    return out


def strip_parens(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        d = 0
        for i, c in enumerate(s):
            d += c == '('
            d -= c == ')'
            if d == 0 and i < len(s) - 1:
                return s
        s = s[1:-1].strip()
    return s


def paren(e):
    return e if re.fullmatch(r"[\w.'_]+", e) or (e.startswith('(') and strip_parens(e) != e) else f'({e})'


def subst(expr, env):
    """replace the variables of env (name -> expr) in expr; `v.f` with env[v] a dict -> env[v][f]."""
    def rep(m):
        v, f = m.group(1), m.group(2)
        val = env[v]
        if isinstance(val, dict):
            if f is None:
                die(f'bundle variable {v} used whole in: {expr}')
            if f not in val:
                die(f'field {f} missing (needed in: {expr})')
            if val[f] is None:
                die(f'field {f} is the removed field (needed in: {expr})')
            return paren(val[f])
        return paren(val) + ('.' + f if f else '')
    pat = r"(?<![\w.'])(" + '|'.join(map(re.escape, env)) + r")(?![\w'])(?:\.([\w']+))?"
    return re.sub(pat, rep, expr)


def fields_of(body):
    """[(field, expr)] of a `where` body."""
    out = []
    for l in body:
        m = re.match(r"^  ([\w']+) := (.*)$", l)
        if m:
            out.append([m.group(1), m.group(2)])
        elif l.startswith('    ') and out:
            out[-1][1] += ' ' + l.strip()
        else:
            die('unparsed conversion line: ' + l)
    return out


READERS = [
    (re.compile(r"_root_\.ZInQ\.SemiAbDescend\.semiAbelianDescendsPerfect_of_chevalley (\w+)\.chevalleyPerfect"),
     lambda m: '_root_.ZInQ.ChevFree.semiAbelianDescendsPerfect_proof'),
    (re.compile(r"_root_\.ZInQ\.SemiAbDescend\.(\w+)_of_printed_chevalley ((?:\S+ ){3})(\w+)\.chevalleyPerfect"),
     lambda m: f'_root_.ZInQ.ChevFree.{m.group(1)}_of_printed_free {m.group(2).strip()}'),
]


def reroute(expr):
    for pat, f in READERS:
        expr = pat.sub(f, expr)
    expr = re.sub(r'\(\s*(_root_\.ZInQ\.ChevFree\.semiAbelianDescendsPerfect_proof)\s*\)', r'\1', expr)
    return expr


def apply_conv(name, args_vals):
    params, res, body, is_where = find_theorem(name)
    if not is_where or len(params) != len(args_vals):
        die(f'{name}: not a `where` conversion with {len(args_vals)} arguments')
    env = {v: a for (v, _), a in zip(params, args_vals)}
    out = {}
    for f, e in fields_of(body):
        if f == FIELD:
            out[f] = None  # the field itself; must not be read below
            continue
        out[f] = subst(reroute(e), env)
    return res, out


def eval_bundle(expr, env):
    """value (dict) of a research-bundle argument expression."""
    e = strip_parens(expr)
    if re.fullmatch(r'\w+', e):
        if not isinstance(env.get(e), dict):
            die(f'research argument {e} is not the bundle variable')
        return env[e]
    parts = split_args(e)
    head, args = parts[0], parts[1:]
    vals = [eval_bundle(args[0], env)] + [subst(a, {k: v for k, v in env.items() if not isinstance(v, dict)})
                                         for a in args[1:]]
    return apply_conv(head, vals)[1]


def struct_fields(sname):
    fn, block = af.find_struct(sname)
    return af.field_groups(block)


# ---------------------------------------------------------------- the fold
def main():
    dry = '--dry-run' in sys.argv
    main_src, binders, top, N, last_mod, k = af.main_state()
    if len(binders) != 3:
        die(f'expected frozenTarget bundles (r, t, l), got {binders}')
    (rv, R0), (tv, T0), (lv, L0) = binders
    groups = struct_fields(R0)
    names = [f for f, _ in groups]
    if FIELD not in names:
        die(f'{R0} has no field {FIELD}: nothing to do')
    newR = af.bump(R0)
    # the top bundle, symbolically: every field n.f except the removed one
    env = {'r': {f: (None if f == FIELD else f'n.{f}') for f in names}, 't': tv, 'l': lv}
    cur = top
    chain = []
    while True:
        params, res, body, is_where = find_theorem(cur)
        if is_where or res != 'ZInQ.SixContactMin' or len(params) != 3 or len(body) != 1:
            die(f'{cur}: not a one-line sixContactMin step: {params} {res} {body}')
        (pr, PR), (pt, _), (pl, _) = params
        call = split_args(body[0])
        callee, cargs = call[0], call[1:]
        loc = {pr: env['r'], pt: env['t'], pl: env['l']}
        cparams = find_theorem(callee)[0]
        if len(cparams) != 3 or len(cargs) != 3:
            die(f'{callee}: expected (r t l)')
        rval = eval_bundle(cargs[0], loc)
        scal = {k2: v for k2, v in loc.items() if not isinstance(v, dict)}
        tval, lval = subst(cargs[1], scal), subst(cargs[2], scal)
        chain.append(callee)
        env = {'r': rval, 't': strip_parens(tval) if re.fullmatch(r'\w+', strip_parens(tval)) else tval,
               'l': strip_parens(lval) if re.fullmatch(r'\w+', strip_parens(lval)) else lval}
        RS = cparams[0][1]
        if FIELD not in [f for f, _ in struct_fields(RS)]:
            break
        cur = callee
    # stop: callee takes RS (no field)
    RSf = [f for f, _ in struct_fields(RS)]
    vals = env['r']
    if set(vals) - {FIELD} != set(RSf):
        die(f'conversion fields differ from {RS}: {sorted(set(vals) ^ set(RSf))}')
    for f in RSf:
        if vals[f] is None or FIELD in vals[f] or 'SemiAbDescend' in vals[f] and 'chevalley' in vals[f]:
            die(f'{RS}.{f} still reads the removed field: {vals[f]}')
    used = ' '.join(vals[f] for f in RSf) + ' ' + env['t'] + ' ' + env['l']
    convname = f'openResearchLeaves{RS[len("OpenResearchLeaves"):]}_of_{newR}'
    cparams_s = f'(n : {newR})' + (f' ({tv} : {T0})' if re.search(rf"(?<![\w.']){tv}(?![\w'])", ' '.join(vals[f] for f in RSf)) else '') \
        + (f' ({lv} : {L0})' if re.search(rf"(?<![\w.']){lv}(?![\w'])", ' '.join(vals[f] for f in RSf)) else '')
    cargs_s = ' '.join(['r'] + [v for v in (tv, lv) if f'({v} :' in cparams_s])
    j = k + 1
    while os.path.exists(os.path.join(H, f'TailZ{j}.lean')):
        j += 1
    new_mod = f'TailZ{j}'
    readers = sorted(f for f in RSf if 'ChevFree' in vals[f])
    out = [f'import ZInQKernel.OneProof.H.{last_mod}', f'import {CONTRIB}', '',
           f'/-! # OneProof H, fold-chev (chevalley-free): `sixContactMin_of_open{N + 1}` (generated by scratch/fold-chev/gen/gen_bypass.py)',
           '',
           f'Field removed: the research field `{FIELD}` (`ZInQ.SemiAbDescend.ChevalleyPerfect`, Chevalley\'s structure theorem',
           'over a perfect field; GLUE). Fields added: none. The chain read the field only through',
           '`ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley`, and chevalley-free proved',
           '`ZInQ.HeightFix.SemiAbelianDescendsPerfect` outright (`ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`:',
           'spreading out to a finite subextension, rigidity of tori in abelian varieties, effective finite flat descent;',
           '`Contrib/OneProof/ChevalleyFree.lean`). A proof of `ChevalleyPerfect` itself is not available, so this is a',
           f'bypass, not an autofold: `{newR}` is `{R0}` without the field, and',
           f'`{convname}` composes, field by field, the conversions on the way from `{top}` down to',
           f'`{chain[-1]}` (the first step whose research bundle `{RS}` has no `{FIELD}`), with the',
           'readers ' + ', '.join(f'`{f}`' for f in readers) + ' taking `semiAbelianDescendsPerfect` from chevalley-free.',
           'Every existing declaration is unchanged. -/', '', 'namespace HDec', '', 'namespace HSyn', '',
           f'/-- `{R0}` without `{FIELD}` (fold-chev; `ZInQ.HeightFix.SemiAbelianDescendsPerfect` is proved by',
           f'chevalley-free, no replacement field). {len(names) - 1} fields. -/',
           f'structure {newR} : Prop where']
    stale = 'the leaf chevalleyPerfect (semiab-descend)'
    for f, lines in groups:
        if f != FIELD:
            out.extend(x.replace(stale, 'semiAbelianDescendsPerfect, proved by chevalley-free') for x in lines)
    out += ['', f'/-- `{RS}` from `{newR}`: the conversions from `{top}` down to `{chain[-1]}` composed, with',
            '`semiAbelianDescendsPerfect` proved (chevalley-free) where they read `chevalleyPerfect`. -/',
            f'theorem {convname} {cparams_s} : {RS} where']
    out += [f'  {f} := {vals[f]}' for f in RSf]
    tcall, lcall = env['t'], env['l']
    out += ['', f'/-- **G0 with only the open leaves and the open glue** (fold-chev; `{FIELD}` removed with no new leaf). -/',
            f'theorem sixContactMin_of_open{N + 1} (r : {newR}) ({tv} : {T0}) ({lv} : {L0}) : ZInQ.SixContactMin :=',
            f'  {chain[-1]} ({convname} {cargs_s}) {paren(tcall)} {paren(lcall)}',
            '', 'end HSyn', '', 'end HDec', '', f'#print axioms HDec.HSyn.sixContactMin_of_open{N + 1}', '']
    text = NL.join(out)
    if re.search(r'n\.chevalleyPerfect|chevalleyPerfect :', text):
        die('the module still mentions the field')
    ms = main_src.replace(f'import ZInQKernel.OneProof.H.{last_mod}', f'import ZInQKernel.OneProof.H.{new_mod}', 1)
    ms = ms.replace(f'HDec.HSyn.{R0})', f'HDec.HSyn.{newR})', 1)
    ms = ms.replace(f'HDec.HSyn.{top} ', f'HDec.HSyn.sixContactMin_of_open{N + 1} ', 1)
    anchor = 'The hypotheses of `frozenTarget` are therefore exactly the open statements.'
    if anchor not in ms:
        die('Main.lean docstring anchor not found')
    para = (f'fold-chev (chevalley-free) removed the research field `{FIELD}` (Chevalley over a perfect field) with no new\n'
            'leaf: the chain read it only through `SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley`, and\n'
            '`ZInQ.HeightFix.SemiAbelianDescendsPerfect` is proved (`ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`,\n'
            f'`Contrib/OneProof/ChevalleyFree.lean`). `{newR}` (`{new_mod}`) is `{R0}` without it, and\n'
            f'`HDec.HSyn.sixContactMin_of_open{N + 1}` enters the existing chain at `{chain[-1]}` through the composite\n'
            f'conversion `{convname}` (bypass, generated by `scratch/fold-chev/gen/gen_bypass.py`); no\n'
            'declaration is copied or changed.\n\n')
    ms = ms.replace(anchor, para + anchor, 1)
    rows, cols = af.load_kinds()
    before = af.counts(rows)
    kept = [r for r in rows if r['field'] != FIELD]
    after = af.counts(kept)
    print(f'chain: {top} -> ' + ' -> '.join(chain))
    print(f'{R0} ({len(names)} fields) -> {newR} ({len(names) - 1}); stop bundle {RS} ({len(RSf)} fields); readers {readers}')
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    if after[2] > before[2] or after[4] > before[4]:
        die('a GLUE count rises')
    if dry:
        print(text)
        return
    open(H + new_mod + '.lean', 'w').write(text)
    open(af.MAIN, 'w').write(ms)
    with open(af.KINDS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows(kept)
    with open(af.CLAIMS, newline='') as fh:
        rd = csv.DictReader(fh, delimiter='\t')
        crows, ccols = list(rd), rd.fieldnames
    with open(af.CLAIMS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=ccols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(r for r in crows if r['field'] != FIELD)
    print(f'wrote {H}{new_mod}.lean, switched {af.MAIN} to sixContactMin_of_open{N + 1}, updated {af.KINDS} and {af.CLAIMS}')


if __name__ == '__main__':
    main()
