#!/usr/bin/env python3
"""Build or check a source restoration manifest. Does not download or publish."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(root, relative):
    p = PurePosixPath(relative)
    if p.is_absolute() or '..' in p.parts or '\\' in relative or ':' in relative:
        raise ValueError('Unsafe relative path: ' + relative)
    target = (root / relative).resolve()
    if not target.is_relative_to(root.resolve()) or target == root.resolve():
        raise ValueError('Path escapes root: ' + relative)
    return target


def make(repo):
    audit = repo / 'docs/theorem-application-audit'
    sources = json.loads((audit / 'sources.json').read_text(encoding='utf-8'))
    coverage = json.loads((audit / 'coverage.json').read_text(encoding='utf-8'))
    if digest(repo / coverage['manuscript_path']) != coverage['manuscript_sha256']:
        raise ValueError('Inventory does not match manuscript')
    files, unpinned = {}, []
    for source in sources:
        if not source['files']:
            unpinned.append(source['id'])
        for f in source['files']:
            relative = f['workspace_relative_path']
            safe_path(Path.cwd(), relative)
            if 'sha256' not in f:
                unpinned.append(source['id'] + ':' + relative)
                continue
            if relative in files and files[relative]['sha256'] != f['sha256']:
                raise ValueError('Conflicting hashes for ' + relative)
            item = files.setdefault(relative, dict(path=relative, sha256=f['sha256'],
                                                   bytes=f.get('bytes'), sources=[]))
            item['sources'].append(dict(id=source['id'], version=source['version_notes'],
                                        urls=sorted(set(source.get('urls', []) +
                                                       ([f['retrieval_url']] if f.get('retrieval_url') else [])))))
    return dict(schema='source-restoration-manifest-v1',
                manuscript_sha256=coverage['manuscript_sha256'],
                source_registry_sha256=digest(audit / 'sources.json'),
                scope='Declared primary source files only; not an authoring-workspace archive or a license grant.',
                sources_without_file_pins=sorted(set(unpinned)),
                files=sorted(files.values(), key=lambda x: x['path']))


def verify(manifest, root):
    for f in manifest['files']:
        path = safe_path(root, f['path'])
        if not path.is_file() or digest(path) != f['sha256']:
            raise ValueError('Missing or mismatched source: ' + f['path'])
        if f['bytes'] is not None and path.stat().st_size != f['bytes']:
            raise ValueError('Byte count mismatch: ' + f['path'])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    a = sub.add_parser('create')
    a.add_argument('--repo', type=Path, required=True)
    a.add_argument('--output', type=Path, required=True)
    for command in ['verify', 'restore']:
        a = sub.add_parser(command)
        a.add_argument('--manifest', type=Path, required=True)
        a.add_argument('--workspace', type=Path, required=True)
        if command == 'restore':
            a.add_argument('--destination', type=Path, required=True)
    args = ap.parse_args()
    if args.command == 'create':
        manifest = make(args.repo)
        with args.output.open('x', encoding='utf-8') as f:
            json.dump(manifest, f, indent=2, ensure_ascii=False)
            f.write('\n')
    else:
        manifest = json.loads(args.manifest.read_text(encoding='utf-8'))
        verify(manifest, args.workspace)
        if args.command == 'restore':
            args.destination.mkdir(parents=True, exist_ok=False)
            for f in manifest['files']:
                destination = safe_path(args.destination, f['path'])
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(safe_path(args.workspace, f['path']), destination)
            verify(manifest, args.destination)
    print(json.dumps(dict(result='PASS', operation=args.command,
                          files=len(manifest['files']),
                          sources_without_file_pins=manifest['sources_without_file_pins'],
                          mathematical_validation='NOT PERFORMED')))


if __name__ == '__main__':
    main()
