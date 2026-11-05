#!/usr/bin/env python3
"""Validate inventory structure and byte bindings, not mathematical correctness.

Run with Python 3.10+. No third-party packages or network access are needed.
--workspace additionally checks the primary sources in the research workspace.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--workspace', type=Path)
    args = parser.parse_args()
    folder = Path(__file__).resolve().parent
    errors = []

    def check(ok, message):
        if not ok:
            errors.append(message)

    def read(name):
        return json.loads((folder / (name + '.json')).read_text(encoding='utf-8'))

    cov, apps, cites, sources, evidence, refs, sites, named = map(read, [
        'coverage', 'applications', 'citations', 'sources', 'evidence',
        'internal-references', 'application-sites', 'named-input-index'])
    raw = (args.repo / cov['manuscript_path']).read_bytes()
    check(sha(raw) == cov['manuscript_sha256'], 'Frozen manuscript hash changed')
    text = raw.decode('utf-8-sig')
    lines = text.splitlines()
    check(len(lines) == cov['manuscript_lines'], 'Manuscript line count changed')
    end = next(i for i, line in enumerate(lines) if r'\begin{thebibliography}' in line)
    clean = re.sub(r'(?<!\\)%[^\n]*', '', '\n'.join(lines[:end]))
    pattern = re.compile(r'\\cite(?:[a-zA-Z*]*)\s*(?:\[([^]]*)\])?\s*\{([^}]+)\}')
    actual = [(clean.count('\n', 0, m.start()) + 1, m[1],
               [k.strip() for k in m[2].split(',')]) for m in pattern.finditer(clean)]
    check(actual == [(c['line'], c['locator'], c['keys']) for c in cites],
          'Citation extraction differs from manuscript')

    def indexed(rows, label):
        result = {x['id']: x for x in rows}
        check(len(result) == len(rows), 'Duplicate ' + label + ' ID')
        return result

    am, cm, sm, em, site_map = (indexed(rows, label) for rows, label in [
        (apps, 'application'), (cites, 'citation'), (sources, 'source'),
        (evidence, 'evidence'), (sites, 'site')])
    for c in cites:
        check(c['role'] in {'application', 'summary', 'provenance', 'source-scope declaration'},
              c['id'] + ': unclassified citation')
        excerpt = '\n'.join(lines[c['paragraph_start'] - 1:c['paragraph_end']])
        check(sha(excerpt.encode()) == c['paragraph_sha256'], c['id'] + ': paragraph hash')
        check(excerpt == c['paragraph'], c['id'] + ': paragraph text')
        expected = [a['id'] for a in apps if c['id'] in a['citations']]
        check(expected == c['application_ids'], c['id'] + ': application backlink')
        check(all(key in sm for key in c['keys']), c['id'] + ': unknown bibliography source')
        check(c['role'] != 'application' or bool(expected), c['id'] + ': application unassigned')
    for a in apps:
        for field in ['source_locator', 'objects_and_maps', 'hypotheses_and_discharge',
                      'conventions', 'translation_justification', 'status']:
            check(bool(a[field]), a['id'] + ': missing ' + field)
        check(a['manuscript_sha256'] == sha(raw), a['id'] + ': manuscript binding')
        check(all(c in cm for c in a['citations']), a['id'] + ': unknown citation')
        check(all(s in sm for s in a['sources']), a['id'] + ': unknown source')
        check(all(e in em for e in a['prior_evidence']), a['id'] + ': unknown evidence')
        check(bool(a['manuscript_anchors']), a['id'] + ': no manuscript anchor')
        for j, anchor in enumerate(a['manuscript_anchors'], 1):
            lo, hi = anchor['line_start'], anchor['line_end']
            check(1 <= lo <= hi <= len(lines), a['id'] + ': invalid anchor')
            excerpt = '\n'.join(lines[lo - 1:hi])
            check(sha(excerpt.encode()) == anchor['excerpt_sha256'], a['id'] + ': anchor hash')
            site = site_map.get(f"{a['id']}-S{j:02}")
            check(site is not None and site['anchor'] == anchor and
                  site['application_id'] == a['id'], a['id'] + ': site mapping')
    for e in evidence:
        p = folder / e['path']
        check(p.is_file() and sha(p.read_bytes()) == e['sha256'], e['id'] + ': evidence hash')
    source_files = 0
    if args.workspace:
        root = args.workspace.resolve()
        for s in sources:
            for f in s['files']:
                if 'sha256' not in f:
                    check(False, s['id'] + ': source was missing when inventoried')
                    continue
                p = (root / f['workspace_relative_path']).resolve()
                check(p.is_relative_to(root), s['id'] + ': source outside workspace')
                if not p.is_relative_to(root):
                    continue
                check(p.is_file() and sha(p.read_bytes()) == f['sha256'], s['id'] + ': source hash')
                source_files += 1
    labels = {}
    for i, line in enumerate(lines, 1):
        for m in re.finditer(r'\\label\{([^}]+)\}', re.sub(r'(?<!\\)%[^\n]*', '', line)):
            labels.setdefault(m[1], []).append(i)
    actual_refs = []
    for m in re.finditer(r'\\(?:eqref|ref|autoref|cref|Cref)\{([^}]+)\}', clean):
        for key in m[1].split(','):
            actual_refs.append(dict(line=clean.count('\n', 0, m.start()) + 1,
                                    label=key, target_lines=labels.get(key, [])))
    check(refs == actual_refs, 'Internal reference index differs')
    check(all(len(r['target_lines']) == 1 for r in refs), 'Unresolved or ambiguous reference')
    for n in named:
        check(lines[n['line'] - 1] == n['text'], 'Named-input line changed')
        check(all(a in am for a in n['related_application_ids']), 'Unknown named-input application')
    checks = {
        'citation_occurrences': len(cites), 'applications': len(apps),
        'citation_key_occurrences': sum(len(c['keys']) for c in cites),
        'cited_works': len({k for c in cites for k in c['keys']}),
        'source_records': len(sources),
        'sources_byte_pinned': sum(s['source_status'] == 'bytes_pinned' for s in sources),
        'uncited_application_records': sum(not a['citations'] for a in apps),
        'applications_with_open_items': sum(bool(a['open_items']) for a in apps),
        'fresh_source_interface_checks': sum('fresh_source_check' in a for a in apps),
        'anchored_application_contexts': len(sites),
        'internal_reference_occurrences': len(refs), 'named_input_signals': len(named),
        'citation_roles': dict(Counter(c['role'] for c in cites)),
    }
    for key, value in checks.items():
        check(cov[key] == value, 'Coverage count mismatch: ' + key)
    check(len(sites) == sum(len(a['manuscript_anchors']) for a in apps), 'Extra sites')
    print(json.dumps(dict(structural_validation='PASS' if not errors else 'FAIL',
                         mathematical_validation='NOT PERFORMED BY THIS SCRIPT',
                         source_files_checked=source_files, counts=checks, errors=errors), indent=2))
    return 1 if errors else 0


if __name__ == '__main__':
    raise SystemExit(main())
