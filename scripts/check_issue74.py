"""Focused source/import guards for #74; does not compile or prove Lean claims."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'docs/openmath/issue74-manuscript-pole'


def lean_code(text):
    # Lean block comments nest. Strings cannot supply an import or theorem here.
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('unclosed Lean comment')
    return ''.join(out)


def polynomial_body(text):
    code = lean_code(text)
    start = code.index('def polePoly ')
    end = code.index('def PoleSoluble', start)
    return re.sub(r'\s+', '', code[start:end])


def source_guards(root):
    get = lambda p: (root / p).read_text()
    reference = (EVIDENCE / 'reference/PoleManuscript-original.lean.txt').read_text()
    assert polynomial_body(get('ZInQKernel/Hypotheses/Pole.lean')) == polynomial_body(reference), 'manuscript polynomial drift'
    core = lean_code(get('ZInQKernel/Syntax/Templates/Core.lean'))
    for term in ('A * (A - e) * (A + 3 * e)', '(A * z ^ 2 + 3 * e * H)',
                 'poleTemplate.witnesses = 11', 'poleTemplate.Rel a ↔ PoleSoluble (a 0)'):
        assert term in core, f'template correspondence missing: {term}'
    aliases = lean_code(get('ZInQKernel/Hypotheses/PoleManuscript.lean'))
    for name in ('polePoly', 'PoleSoluble', 'PoleCompleteness'):
        assert f'abbrev {name} := ZInQ.{name}' in aliases
    obstruction = lean_code(get('ZInQKernel/Assembly/Local/PoleObstruction.lean'))
    assert 'open ZInQ.ValuationObstruction' in obstruction
    assert '(hB : B ≠ 0)' in obstruction and '(hp2730 : ¬ p ∣ 2730)' in obstruction
    one = lean_code(get('ZInQKernel/OneProof/Main.lean'))
    assert '(hPC : PoleCompleteness)' in one
    for name in ('h21S', 'hCM', 'h33c', 'hBFH', 'hGZss'):
        assert not re.search(r'\b' + name + r'\b', one), f'retired premise {name}'
    assert 'sixContactMin_of_open67 r t l' in one


def imports(root):
    files = {'.'.join(p.relative_to(root).with_suffix('').parts): p
             for p in (root / 'ZInQKernel').rglob('*.lean')}
    files['ZInQKernel'] = root / 'ZInQKernel.lean'
    deps = {m: re.findall(r'^import\s+(\S+)', lean_code(p.read_text()), re.M)
            for m, p in files.items()}
    retired = set(json.loads((EVIDENCE / 'RETIREMENT.json').read_text())['retired_assemblies'])
    result = {}
    for target in ('ZInQKernel', 'ZInQKernel.OneProof.Main', 'ZInQKernel.Contrib.AllContrib'):
        seen, todo = set(), [target]
        while todo:
            module = todo.pop()
            if module not in seen:
                seen.add(module)
                todo.extend(deps.get(module, []))
        assert not (seen & retired), f'{target} imports retired assemblies: {seen & retired}'
        result[target] = sorted(seen & files.keys())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    source_guards(ROOT)
    graph = imports(ROOT)
    # H and the accepted helper snapshot must remain exactly at the recorded base.
    base = 'bf691da2236b494bb429caabc2f907d4ea428c4d'
    for prefix in ('lean', 'ZInQKernel/OneProof/H'):
        tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', base, prefix], cwd=ROOT, text=True).splitlines()
        for name in tracked:
            expected = subprocess.check_output(['git', 'rev-parse', f'{base}:{name}'], cwd=ROOT, text=True).strip()
            actual = subprocess.check_output(['git', 'hash-object', name], cwd=ROOT, text=True).strip()
            assert actual == expected, f'protected baseline changed: {name}'
    if args.self_test:
        original = (ROOT / 'ZInQKernel/Hypotheses/Pole.lean').read_text()
        wrong = original.replace('(A + 3 * e)', '(A + e)')
        assert polynomial_body(wrong) != polynomial_body(original), 'wrong-route control was not rejected'
        assert lean_code('/- outer /- inner -/ comment -/\nimport X\n-- import Y') == '\nimport X\n'
    print(json.dumps({'source_guards': 'PASS', 'protected_sources': 'PASS',
                      'negative_controls': 'PASS' if args.self_test else 'NOT_RUN',
                      'import_counts': {m: len(ds) for m, ds in graph.items()},
                      'lean_compilation': 'NOT_ESTABLISHED_BY_THIS_CHECK'}, indent=2))


if __name__ == '__main__':
    main()
