"""Prepare pinned source/reference projects for Open Math OS; Python/Git only."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
REL = Path('docs/openmath/issue74-manuscript-pole')


def index(directory):
    return {p.relative_to(directory).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(directory.rglob('*')) if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.absolute()
    if output.exists():
        parser.error('output already exists; choose a new directory')
    if output == ROOT or ROOT in output.parents:
        parser.error('output must be outside the source checkout')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT).strip():
        parser.error('source checkout must be clean and committed')
    expected = json.loads((ROOT / REL / 'SOURCE.json').read_text())
    for name, digest in expected['sha256'].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            parser.error(f'frozen input mismatch: {name}')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    output.mkdir(parents=True)
    solution = output / 'solution'
    solution.mkdir()
    # No dependencies/build artifacts are copied. The accepted local dependency
    # and vendor sources are part of the selected committed tree.
    command = ['git', 'archive', '--format=tar', head, 'ZInQKernel',
               'ZInQKernel.lean', 'ThirdParty', 'lean', 'lakefile.toml',
               'lake-manifest.json', 'lean-toolchain']
    with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE) as proc:
        with tarfile.open(fileobj=proc.stdout, mode='r|') as archive:
            for member in archive:
                path = PurePosixPath(member.name)
                if path.is_absolute() or '..' in path.parts or not (member.isfile() or member.isdir()):
                    raise ValueError(f'unsupported archive member: {member.name}')
                archive.extract(member, solution, filter='data')
        if proc.wait() != 0:
            raise RuntimeError('git archive failed')
    shutil.copyfile(ROOT / REL / 'Packet.lean', solution / 'Issue74Packet.lean')
    with (solution / 'lakefile.toml').open('a') as f:
        f.write('\n# Verification-only packet root.\n[[lean_lib]]\nname = "Issue74Packet"\n')
    reference = output / 'reference'
    shutil.copytree(solution, reference)
    for path in (ROOT / REL / 'reference/overlay').rglob('*.lean.txt'):
        destination = reference / str(path.relative_to(ROOT / REL / 'reference/overlay'))[:-4]
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
    for name in ('comparator.json', 'export-roots.txt', 'SPEC.md', 'SOURCE.json',
                 'AxiomCheck.lean', 'DischargeCheck.lean'):
        shutil.copyfile(ROOT / REL / name, output / name)
    manifest = {'source_commit': head, 'base_commit': expected['base_commit'],
                'source_index_sha256': hashlib.sha256((ROOT / REL / 'SOURCE.json').read_bytes()).hexdigest(),
                'solution': index(solution), 'reference': index(reference),
                'status': 'PREPARED_ONLY', 'lean_executed': False}
    (output / 'INPUTS.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PREPARED_ONLY', 'commit': head,
                      'solution_files': len(manifest['solution']),
                      'reference_files': len(manifest['reference'])}, indent=2))


if __name__ == '__main__':
    main()
