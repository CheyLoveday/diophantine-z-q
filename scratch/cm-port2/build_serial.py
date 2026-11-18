"""Compile selected modules one at a time with the installed package caches.

Run with `lake env python3 scratch/cm-port2/build_serial.py [--plan] MODULE ...`.
Reuse modules from local caches only when the module and its source imports
match the associated snapshot. For the two known fork-only renames, reuse
unchanged downstream objects only if none of their serialized artifacts
mentions the old name, and rebuild the renamed declarations from current
sources. All other dependency changes invalidate the old object. Build replacements in this worktree's ignored overlay.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path.cwd()
out = root / ".lake/build/cm-port2-checked"
cache_specs = (
    ("conrad-b3-verbatim", "04e41c885", ".lake/build/lib/lean"),
    ("conrad-bridges", "b092da9cc", ".lake/build/lib/lean"),
    ("ht-merge", "39a4de612", ".lake/build/lib/lean"),
    ("c8-conrad3", "95350930b", ".lake/build/lib/lean"),
    ("cm-fibre-split", "fe5ad6a96", ".lake/build/lib/lean"),
    ("cm-fold-rebase", "664e00417", ".lake/build/lib/lean"),
    ("kolyv-weil", "cfe47c6e7", ".lake/build/lib/kolyv-weil-sequential"),
    ("kolyv-weil", "0caafe661", ".lake/build/lib/lean"),
)
names_only = {
    p: "divisorSum" for p in subprocess.check_output(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", "52e113d72"], text=True
    ).splitlines()
}
names_only["ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/RingTheory/MvPolynomial/"
           "HomogeneousCharts.lean"] = "eval₂_const_mul"
renamed = {"divisorSum": "placeDivisorSum", "eval₂_const_mul": "eval₂_const_mul_chart"}

def strip_header_and_port_note(src):
    # The AnthropicFLT rename adds only a header paragraph and inline -- [port] notes.
    src = re.sub(r"(?s)\A\s*/-.*?-/\n", "", src, count=1)
    return re.sub(r"[ \t]+-- \[port\][^\n]*", "", src)

caches = []
for name, rev, rel_cache in cache_specs:
    worktree = root.parent / name
    lib = worktree / rel_cache
    if not lib.is_dir():
        continue
    changed = set(subprocess.check_output(
        ["git", "diff", "--name-only", rev, "--", "*.lean"], text=True
    ).splitlines())
    paths = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", rev], text=True
    ).splitlines())
    name_changes = {}
    for path, before in names_only.items():
        if path not in (paths & changed):
            continue
        original = subprocess.check_output(["git", "show", f"{rev}:{path}"], text=True)
        current = (root / path).read_text()
        expected = re.sub(r"(?<!\w)" + before + r"(?!\w)", renamed[before],
                          strip_header_and_port_note(original))
        if expected == strip_header_and_port_note(current):
            name_changes[path] = before.encode()
    caches.append((lib, worktree / "lean/.lake/build/lib/lean", paths - changed, name_changes))
args = sys.argv[1:]
plan = args.pop(0) == "--plan" if args and args[0] == "--plan" else False
imports = re.compile(r"^(?:(?:public|private|meta|all) )*import +(?:all +)?([\w.]+)", re.M)
artifacts = ("olean", "olean.private", "olean.server", "ilean", "ir", "ir.sig")
visited = {}
queue = []

def walk(module):
    if module in visited:
        return visited[module]
    stem = module.replace(".", "/")
    rel = next((p / f"{stem}.lean" for p in (Path("."), Path("lean"), Path("ThirdParty/GreenTao"))
                if (p / f"{stem}.lean").is_file()), None)
    if rel is None:
        visited[module] = ({i: set() for i in range(len(caches))}, None)
        return visited[module]
    src = root / rel
    deps = imports.findall(src.read_text())
    dep_results = [walk(dep) for dep in deps]
    dest = out / f"{stem}.olean"
    matching = {}
    candidates = []
    for i, (lib, vendor, same, name_changes) in enumerate(caches):
        if not all(i in match for match, _ in dep_results):
            continue
        dep_names = set().union(*(match[i] for match, _ in dep_results))
        path = str(rel)
        if path in name_changes:
            matching[i] = dep_names | {name_changes[path]}
        if path not in same:
            continue
        matching[i] = dep_names | ({names_only[path].encode()} if path in names_only else set())
        src_obj = (vendor if rel.parts[0] == "lean" else lib) / f"{stem}.olean"
        if not src_obj.is_file() or module == "ZInQKernel.OneProof.Main":
            continue
        if path in names_only and renamed[names_only[path]].encode() not in src_obj.read_bytes():
            continue
        # A uniform renaming preserves old terms that do not use the name.
        # Scan all serialized parts, conservatively including substring hits.
        if dep_names:
            encoded = [a.read_bytes() for ext in artifacts
                       if (a := src_obj.with_suffix(f".{ext}")).is_file()]
            if any(token in data for token in dep_names for data in encoded):
                continue
        candidates.append(src_obj)
    cached = next(iter(candidates), None)
    if cached is not None:
        if not plan:
            dest.parent.mkdir(parents=True, exist_ok=True)
            for ext in artifacts:
                a = dest.with_suffix(f".{ext}")
                b = cached.with_suffix(f".{ext}")
                if b.is_file() and not a.exists():
                    a.symlink_to(b)
        visited[module] = (matching, cached)
    else:
        pending = {job[2] for job in queue}
        latest = max([src.stat().st_mtime] + [
            obj.stat().st_mtime for _, obj in dep_results if obj is not None and obj.is_file()
        ])
        if (not dest.is_file() or dest.is_symlink() or dest.stat().st_mtime < latest
                or any(obj in pending for _, obj in dep_results)):
            queue.append((module, src, dest, root / ("lean" if rel.parts[0] == "lean" else
                          "ThirdParty/GreenTao" if rel.parts[0] == "ThirdParty" else ".")))
        visited[module] = (matching, dest)
    return visited[module]

for target in args:
    walk(target)
    if visited[target][1] is None:
        sys.exit(f"No source for {target}")

print(f"{len(queue)} modules to build in order ({len(visited)} import names visited)", flush=True)
if plan:
    print("\n".join(module for module, *_ in queue))
    sys.exit(0)
os.environ["LEAN_PATH"] = str(out) + ":" + os.environ["LEAN_PATH"]
for i, (module, source, dest, pkg) in enumerate(queue, 1):
    hold = time.monotonic()
    while True:
        load_text = subprocess.check_output(["uptime"], text=True).strip()
        mem_text = subprocess.check_output(["free", "-g"], text=True)
        available = int(next(line for line in mem_text.splitlines() if line.startswith("Mem:")).split()[-1])
        if os.getloadavg()[0] <= 150 and available >= 20:
            break
        if time.monotonic() - hold >= 3600:
            sys.exit("Resource limits blocked this build for an hour")
        print(f"Holding before {module}: {load_text}; {available} GiB available", flush=True)
        time.sleep(300)
    print(f"[{i}/{len(queue)}] {module}: {load_text}; {available} GiB available", flush=True)
    dest.parent.mkdir(parents=True, exist_ok=True)
    for ext in artifacts:
        link = dest.with_suffix(f".{ext}")
        if link.is_symlink():
            link.unlink()
    subprocess.run(["lean", "--root=" + str(pkg), "-o", str(dest), str(source)], check=True)
