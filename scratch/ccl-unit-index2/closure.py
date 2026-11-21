"""Compute project-module import closures from the branch base with git grep."""

import collections
import re
import subprocess
import sys

BASE = "c4d9b28eaf47ca591f1428fe97ca0a2d1ea5100f"
RC = "ZInQKernel.Contrib.OneProof.RC"
H20 = "ZInQKernel.Contrib.CloudB3E2Norm"
IMPORT = re.compile(r"^(?:public |private )?(?:meta )?import\s+([\w.]+)", re.ASCII)


def git(*args):
    return subprocess.check_output(["git", *args], text=True)


def imports(revision):
    ref = [revision] if revision else []
    prefix = revision + ":" if revision else ""
    graph = collections.defaultdict(set)
    rows = git("grep", "-I", "-n", "-E", "^[[:space:]]*((public|private|meta) )*import[[:space:]]", *ref, "--", "*.lean", ":!scratch")
    for row in rows.splitlines():
        path, _, line = row.removeprefix(prefix).split(":", 2)
        match = IMPORT.match(line.lstrip())
        if match and path.startswith(("ZInQKernel", "CMSerreTateSupport/")):
            mod = path.removeprefix("CMSerreTateSupport/").removesuffix(".lean").replace("/", ".")
            graph[mod].add(match[1])
    return graph


def closure(graph, root):
    seen, queue = set(), [root]
    while queue:
        name = queue.pop()
        if name not in seen:
            seen.add(name)
            queue.extend(graph.get(name, ()))
    return seen


def main():
    graph = imports("" if len(sys.argv) > 1 else BASE)
    leaf = f"{RC}.PrintsArith.Heegner"
    older = {leaf, f"{RC}.PrintsArith.Bundle"}
    older.update(f"{H20}.H20{name}" for name in (
        "HeegnerNorm", "Transport", "Dictionary", "Anchor", "DictFields",
        "PresClass", "PresClassOf", "PresClassMatch",
    ))
    older.update(f"{RC}.Wiring.CommonCoordinate{name}" for name in ("18E2", "18LeafE2"))
    for root in (
        "ZInQKernel.Contrib.OneProof.SelmerTwoPower",
        "ZInQKernel.OneProof.Main",
        "ZInQKernel",
        f"{RC}.Wiring.Leaves",
        f"{RC}.Wiring.CommonCoordinate19Leaf",
    ):
        modules = closure(graph, root)
        print(root, len(modules & graph.keys()), "project modules including root")
        for module in sorted(older & modules):
            print("  ", module)
        if not older & modules:
            print("   no intersection")
    print("Direct importers of Heegner:")
    for name in sorted(name for name in graph if leaf in graph[name]):
        print("  ", name)


if __name__ == "__main__":
    main()
