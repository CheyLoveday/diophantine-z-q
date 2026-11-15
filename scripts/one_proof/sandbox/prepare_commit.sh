#!/usr/bin/env bash
# Usage: prepare_commit.sh BASE HEAD [PR]
#        prepare_commit.sh --measure BASE
#        prepare_commit.sh --sandbox-main BASE [PREVIOUS_MAIN]
#
# --measure builds a measurement commit: BASE's tree with .github replaced as below and the manifest
# {base, measure: true}, no added files; push it to a scratch/measure-* branch. --sandbox-main builds the
# sandbox's long-lived main: BASE's tree without .github (so no workflow runs on it), with parents
# PREVIOUS_MAIN (when given, so the push is a fast-forward) and BASE. Both print the new commit's SHA.
#
# Builds the prepared commit for the discharge check, in a repository that already has both commits, with
# git plumbing only: no checkout, no build, nothing from HEAD is run. The tree is BASE's tree plus each file
# the pull request adds (blobs from HEAD, same paths), with .github replaced by a tree holding only
# .github/workflows/contrib-check.yml (BASE's scripts/one_proof/sandbox/contrib-check.yml), plus
# .sandbox/manifest.json {base, head, pr, added}. Its parent is BASE. Everything trusted (the scripts, the
# OneProof modules) comes from BASE. Refuses unless scan_contrib.py finds the pair in scope.
# Prints the new commit's SHA.
set -euo pipefail

usage() {
  echo "usage: prepare_commit.sh BASE HEAD [PR] | --measure BASE | --sandbox-main BASE [PREVIOUS_MAIN]" >&2
  exit 1
}
mode=contrib
case "${1:-}" in
  --measure ) mode=measure; [ $# -eq 2 ] || usage ;;
  --sandbox-main ) mode=main; [ $# -eq 2 ] || [ $# -eq 3 ] || usage ;;
  * ) [ $# -ge 2 ] && [ $# -le 3 ] || usage ;;
esac
if [ "$mode" != contrib ]; then
  shift
fi
pr=""
if [ "$mode" = contrib ]; then
  pr="${3:-}"
fi
case "$pr" in
  '' ) ;;
  *[!0-9]* ) echo "prepare_commit: PR must be a number" >&2; exit 1 ;;
esac

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# Paths given to git below are relative to the top of the repository.
top="$(git rev-parse --show-toplevel 2>/dev/null || true)"
if [ -n "$top" ]; then
  cd "$top"
fi
base="$(git rev-parse --verify "$1^{commit}")"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

if [ "$mode" != contrib ]; then
  export GIT_INDEX_FILE="$tmp/index"
  git read-tree "$base"
  git ls-tree -r -z --full-tree --name-only "$base" -- .github .sandbox | git update-index -z --force-remove --stdin
  if [ "$mode" = main ]; then
    parents=(-p "$base")
    if [ $# -eq 2 ]; then
      parents=(-p "$(git rev-parse --verify "$2^{commit}")" -p "$base")
    fi
    git commit-tree "$(git write-tree)" "${parents[@]}" -m "Sandbox main: $base without .github"
    exit 0
  fi
  workflow="$(git rev-parse --verify "$base:scripts/one_proof/sandbox/contrib-check.yml")"
  printf '{\n  "base": "%s",\n  "measure": true,\n  "added": []\n}\n' "$base" > "$tmp/manifest.json"
  git update-index --add --cacheinfo "100644,$workflow,.github/workflows/contrib-check.yml"
  git update-index --add --cacheinfo "100644,$(git hash-object -w "$tmp/manifest.json"),.sandbox/manifest.json"
  git commit-tree "$(git write-tree)" -p "$base" -m "Build measurement at $base"
  exit 0
fi

head="$(git rev-parse --verify "$2^{commit}")"

scan_status=0
python3 -I "$here/scan_contrib.py" "$base" "$head" --json "$tmp/scan.json" > "$tmp/scan.txt" || scan_status=$?
cat "$tmp/scan.txt" >&2
if [ "$scan_status" -ne 0 ]; then
  echo "prepare_commit: refused: scan_contrib.py exit status $scan_status (out of scope or error)" >&2
  exit 1
fi

# One line per added file: blob SHA, a tab, the path. Paths were restricted by the scope gate.
python3 -I - "$tmp/scan.json" "$tmp/added.tsv" "$tmp/manifest.json" "$base" "$head" "$pr" <<'PY'
import json, sys
scan_path, added_path, manifest_path, base, head, pr = sys.argv[1:7]
scan = json.load(open(scan_path))
if scan.get('scope_ok') is not True or scan.get('base') != base or scan.get('head') != head:
    sys.exit('prepare_commit: refused: the scan does not report scope_ok for this pair')
with open(added_path, 'w') as fh:
    for f in scan['files']:
        if '\t' in f['path'] or '\n' in f['path']:
            sys.exit('prepare_commit: refused: odd path %r' % f['path'])
        fh.write('%s\t%s\n' % (f['blob'], f['path']))
manifest = {'base': base, 'head': head, 'pr': int(pr) if pr else None,
            'added': [f['path'] for f in scan['files']]}
with open(manifest_path, 'w') as fh:
    json.dump(manifest, fh, indent=2)
    fh.write('\n')
PY

workflow="$(git rev-parse --verify "$base:scripts/one_proof/sandbox/contrib-check.yml")"

export GIT_INDEX_FILE="$tmp/index"
git read-tree "$base"

# Drop .github and .sandbox as BASE has them.
git ls-tree -r -z --full-tree --name-only "$base" -- .github .sandbox | git update-index -z --force-remove --stdin

while IFS="$(printf '\t')" read -r blob path; do
  # The blob must be HEAD's file at that path.
  if [ "$(git rev-parse --verify "$head:$path")" != "$blob" ]; then
    echo "prepare_commit: $path in HEAD is not the scanned blob" >&2
    exit 1
  fi
  git update-index --add --cacheinfo "100644,$blob,$path"
done < "$tmp/added.tsv"

git update-index --add --cacheinfo "100644,$workflow,.github/workflows/contrib-check.yml"
manifest_blob="$(git hash-object -w "$tmp/manifest.json")"
git update-index --add --cacheinfo "100644,$manifest_blob,.sandbox/manifest.json"

tree="$(git write-tree)"
msg="Discharge check of pull request ${pr:-(none)}

base $base
head $head
pr ${pr:-none}"
commit="$(git commit-tree "$tree" -p "$base" -m "$msg")"
echo "$commit"
