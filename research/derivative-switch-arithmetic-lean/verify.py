#!/usr/bin/env python3
"""Compile the derivative-switch research modules from source in a fresh directory."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


PACKET = Path(__file__).resolve().parent
REPO = PACKET.parents[1]
LEAN_ROOT = REPO / "lean"
MODULES = (
    "DerivativeSwitchBoundary",
    *(
        f"DerivativeSwitch/{name}"
        for name in (
            "Coordinate", "CommonStrict", "UnitCriterion", "BoundaryCup", "ArithmeticBridge",
            "ActualBoundaryCup", "OrthogonalComparison", "ConjugateLocalTransport", "ConjugateLocalH1",
            "NativeSelmerCone", "NativeBoundaryTrace", "TameFactor", "TameLocalH1",
            "CompactSupportTrace", "ContractibleLocalCondition", "CommonStrictAxes",
            "RetainedBoundaryRows", "TerminalRankReduction", "OuterCoordinateBound",
            "ContinuousSelmer", "ArithmeticSelmer", "FiniteSelmerCoefficients", "FiniteSelmerInjective",
            "RetainedCoefficients", "RetainedSelmerModels", "ConjugateWeilPairing", "ContinuousCup",
            "FiniteTateTwist", "ContinuousSelmerTrace", "SelmerDualityMap", "ArithmeticSelmerAdjoint",
        )
    ),
)
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
COORDINATE_WARNINGS = {
    f"Research/DerivativeSwitch/Coordinate.lean:{line}:0: warning: automatically included "
    f"section variable(s) unused in theorem `Research.DerivativeSwitch.ScalarRatio.{name}`:"
    for line, name in ((34, "tensor_mul"), (43, "mul_tensor"), (147, "row_mul_assoc"))
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="a new directory for artifacts and diagnostics")
    parser.add_argument("--dependency-cache", type=Path, default=LEAN_ROOT / ".lake/packages")
    args = parser.parse_args()
    out = args.output.resolve()
    cache = args.dependency_cache.resolve()
    version = subprocess.check_output(["lean", "--version"], cwd=LEAN_ROOT, text=True).strip()
    if "version 4.35.0," not in version or "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" not in version:
        parser.error(f"expected the pinned Lean 4.35.0 compiler, found {version}")

    manifest = LEAN_ROOT / "lake-manifest.json"
    dependencies = {}
    libraries = []
    for package in json.loads(manifest.read_text())["packages"]:
        name = package["name"]
        directory = cache / name
        git = ["git", "-C", str(directory)]
        revision = subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip()
        if revision != package["rev"]:
            parser.error(f"{name} has a different revision from the project manifest")
        subprocess.run([*git, "diff", "--quiet", "HEAD", "--"], check=True)
        dependencies[name] = revision
        library = directory / ".lake/build/lib/lean"
        if library.is_dir():
            libraries.append(library)

    sources = [LEAN_ROOT / f"Research/{module}.lean" for module in MODULES]
    roots_path = PACKET / "roots.txt"
    roots = [f"Research.DerivativeSwitch.{line}" for line in roots_path.read_text().splitlines() if line]
    if not roots or len(roots) != len(set(roots)):
        parser.error("expected distinct selected declaration names")
    inputs = [*sources, manifest, LEAN_ROOT / "lean-toolchain", roots_path, Path(__file__).resolve()]
    before = {str(path.relative_to(REPO)): digest(path) for path in inputs}
    out.mkdir(parents=True, exist_ok=False)
    lib = out / "lib"
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [lib, *libraries])))
    env.pop("LEAN_SRC_PATH", None)
    base = ["lean", "-j1", "-Ddebug.skipKernelTC=false", "-DautoImplicit=false"]

    def run(label, arguments, warnings_as_errors):
        flags = ["-DwarningAsError=true"] if warnings_as_errors else []
        completed = subprocess.run([*base, *flags, *arguments], cwd=LEAN_ROOT, env=env,
                                   capture_output=True, text=True)
        log = out / f"{label}.log"
        diagnostics = completed.stdout + completed.stderr
        log.write_text(diagnostics)
        warnings = {line for line in diagnostics.splitlines() if "warning:" in line}
        allowed = set() if warnings_as_errors else COORDINATE_WARNINGS
        if completed.returncode or warnings - allowed:
            raise RuntimeError(f"{label} failed; see {log}")
        print(f"PASS {label}", flush=True)
        return diagnostics, sorted(warnings)

    baseline_warnings = []
    for source in sources:
        artifact = lib / source.relative_to(LEAN_ROOT).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        _, warnings = run(source.stem, ["-o", str(artifact), str(source.relative_to(LEAN_ROOT))],
                          source.stem != "Coordinate")
        baseline_warnings.extend(warnings)

    audit = out / "Check.lean"
    audit.write_text("".join(f"import Research.{m.replace('/', '.')}\n" for m in MODULES) + "\n" +
                     "".join(f"#check @{name}\n#print axioms {name}\n" for name in roots))
    diagnostics, _ = run("statements-and-axioms", [str(audit)], True)
    found = {}
    for name, axioms in re.findall(r"'([^']+)' (?:does not depend on any axioms|"
                                   r"depends on axioms:\s*\[([^]]*)\])", diagnostics):
        names = {axiom.strip() for axiom in axioms.split(",")} if axioms else set()
        if name in found or names - ALLOWED_AXIOMS:
            raise RuntimeError(f"unexpected axiom result for {name}: {sorted(names)}")
        found[name] = sorted(names)
    if set(found) != set(roots):
        raise RuntimeError("the axiom report did not cover the selected declarations")
    if before != {str(path.relative_to(REPO)): digest(path) for path in inputs}:
        raise RuntimeError("inputs changed during the check")

    result = {
        "status": "PASS",
        "scope": "fresh research-source compilation and selected transitive axiom audit",
        "lean_version": version,
        "dependencies": dependencies,
        "modules_compiled": len(sources),
        "declarations_audited": len(roots),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "axioms": found,
        "baseline_warnings": baseline_warnings,
        "input_sha256": before,
        "statements_and_axioms_sha256": digest(out / "statements-and-axioms.log"),
    }
    (out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS {len(sources)} modules and {len(roots)} declarations", flush=True)


if __name__ == "__main__":
    main()
