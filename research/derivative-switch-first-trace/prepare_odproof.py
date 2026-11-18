#!/usr/bin/env python3
"""Stage the exact source closure for odProof without compiling or dispatching."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import tomllib


REPO = Path(__file__).resolve().parents[2]
SUPPLIER_REVISIONS = {
    "4606b900ec8e5c26dd989d9ba8e8dd18e73e8773",
    "5f1fac79094cd58ee393824db1d5c38058150036",
}
ENTRY = "Research.DerivativeSwitch.LocalTraceTwo"
TARGETS = (
    "FirstSelmerPrecision.scalarEquiv_quotient",
    "FirstSelmerPrecision.coefficientLine_action",
    "LocalInvariantTwo.circleInvariant_injective",
    "LocalInvariantTwo.invariant_normalization",
    "LocalTraceTwo.restrictedSign_eq",
    "LocalTraceTwo.exists_compact_support_trace",
    "LocalTraceTwo.exists_local_trace",
    "LocalTraceTwo.duality02_apply",
    "LocalTraceTwo.trace_duality02",
)
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta) )?import[ \t]+([\w.]+)", re.M)


def git(checkout, *args):
    return subprocess.check_output(["git", "-C", str(checkout), *args])


def source_closure(supplier, revision, supplier_revision):
    sources = {}

    def visit(module):
        path = Path(module.replace(".", "/") + ".lean")
        if path in sources:
            return
        if module.startswith("Research."):
            data = git(REPO, "show", f"{revision}:lean/{path.as_posix()}")
        elif module.startswith("ZInQKernel."):
            data = git(supplier, "show", f"{supplier_revision}:{path.as_posix()}")
        else:
            return
        sources[path] = data
        for name in IMPORT.findall(data.decode()):
            visit(name)

    visit(ENTRY)
    return sources


def metadata(revision):
    files = {Path(name): git(REPO, "show", f"{revision}:lean/{name}") for name in (
        "lean-toolchain", "lake-manifest.json",
    )}
    original_lakefile = git(REPO, "show", f"{revision}:lean/lakefile.toml").decode()
    original = tomllib.loads(original_lakefile)
    if original["defaultTargets"] != ["ZInQ"] or original["lean_lib"] != [{"name": "ZInQ"}]:
        raise ValueError("unexpected source Lake layout")
    header, _ = original_lakefile.split("[[lean_lib]]", 1)
    header = header.replace('defaultTargets = ["ZInQ"]', 'defaultTargets = ["Research", "ZInQKernel"]')
    header = header.replace("requiresModuleSystem = true\n", "")
    lakefile = header + '[[lean_lib]]\nname = "Research"\n\n[[lean_lib]]\nname = "ZInQKernel"\n'
    files[Path("lakefile.toml")] = lakefile.encode()
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="a new directory outside the checkout")
    parser.add_argument("--supplier-checkout", type=Path, required=True)
    parser.add_argument("--revision", default="HEAD", help="research Git commit or tree")
    parser.add_argument("--supplier-revision", default="HEAD", help="one of the two pinned supplier commits")
    args = parser.parse_args()
    revision = git(REPO, "rev-parse", "--verify", "--end-of-options", args.revision + "^{tree}").decode().strip()
    supplier_revision = git(args.supplier_checkout, "rev-parse", "--verify", "--end-of-options",
                            args.supplier_revision + "^{commit}").decode().strip()
    if supplier_revision not in SUPPLIER_REVISIONS:
        parser.error("select one of the pinned supplier commits")
    output = args.output.resolve()
    if output.is_relative_to(REPO):
        parser.error("stage sources outside the checkout")
    files = source_closure(args.supplier_checkout, revision, supplier_revision)
    files.update(metadata(revision))
    project = output / "project"
    output.mkdir()
    for path, data in sorted(files.items()):
        destination = project / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    receipt = {
        "status": "SOURCE_PREPARED",
        "research_tree": revision,
        "supplier_commit": supplier_revision,
        "targets": [f"Research.DerivativeSwitch.{target}" for target in TARGETS],
        "input_sha256": {path.as_posix(): sha256(data).hexdigest() for path, data in sorted(files.items())},
    }
    (output / "SOURCE.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Prepared {sum(path.suffix == '.lean' for path in files)} Lean source files at {project}")


if __name__ == "__main__":
    main()
