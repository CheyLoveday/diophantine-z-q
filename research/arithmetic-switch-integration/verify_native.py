#!/usr/bin/env python3
"""Fresh native build and transitive axiom audit of two new helper modules.

The original packet, comparator inputs, dependency pins and source files are
never written. This does not run --paranoid or an external proof checker.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean"
PACKET = Path(__file__).resolve().parent
MODULES = ["ActualBoundaryCup", "OrthogonalComparison"]
TARGETS = {
    "ActualBoundaryCup": [
        "closed_cup_differential", "pure_boundary_correction", "traced_pure_boundary",
        "traced_left_boundary", "traced_right_boundary", "traced_change_left",
        "traced_change_right",
    ],
    "OrthogonalComparison": [
        "fibreComparison_commutes", "fibreComparison_global", "fibreComparison_sign_change",
        "inverse_preserves_global_homotopy", "inverse_preserves_global_homology",
        "inverse_preserves_local_homotopy", "inverse_preserves_local_homology",
    ],
}
NAMES = ["Research.DerivativeSwitch." + m + "." + t
         for m, targets in TARGETS.items() for t in targets]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: verify_native.py NEW_OUTPUT_DIRECTORY")
    output = Path(sys.argv[1]).resolve()
    output.mkdir(parents=True, exist_ok=False)
    lib = output / "lib"
    (lib / "Research/DerivativeSwitch").mkdir(parents=True)
    commands = []

    def run(label, args, env=None):
        r = subprocess.run(args, cwd=PROJECT, env=env, capture_output=True)
        (output / (label + ".stdout.txt")).write_bytes(r.stdout)
        (output / (label + ".stderr.txt")).write_bytes(r.stderr)
        commands.append({"label": label, "command": args, "cwd": str(PROJECT),
                         "exit_code": r.returncode})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if r.returncode:
            raise RuntimeError(label + " failed; see " + str(output))
        return r.stdout.decode()

    sources = [PROJECT / "Research/DerivativeSwitch" / (m + ".lean") for m in MODULES]
    inputs = sources + [Path(__file__), PACKET / "SPEC.md", PACKET / "DERIVATION.md",
        PROJECT / "lean-toolchain", PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json"]
    before = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    lock = json.loads((PROJECT / "lake-manifest.json").read_text())
    libraries, dependencies = [], []
    for package in lock["packages"]:
        folder = PROJECT / ".lake/packages" / package["name"]
        rev = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
        if rev != package["rev"]:
            raise RuntimeError("Dependency revision drift: " + package["name"])
        subprocess.run(["git", "-C", str(folder), "diff", "--quiet", "HEAD", "--"], check=True)
        dependencies.append({"name": package["name"], "revision": rev})
        cache = folder / ".lake/build/lib/lean"
        if cache.exists():
            libraries.append(cache)
    version = run("lean-version", ["lean", "--version"]).strip()
    if "version 4.35.0," not in version or "eb6cafb" not in version:
        raise RuntimeError("Wrong Lean version: " + version)
    run("lake-version", ["lake", "--version"])
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [lib, *libraries]))
    base = ["lean", "-j1", "-Ddebug.skipKernelTC=false"]
    for module, source in zip(MODULES, sources):
        relative = source.relative_to(PROJECT)
        run(module, base + ["-o", str(lib / relative.with_suffix(".olean")), str(relative)], env)
    audit = output / "Audit.lean"
    audit.write_text("\n".join([
        *["import Research.DerivativeSwitch." + m for m in MODULES],
        "import Lean.Util.CollectAxioms", "set_option pp.universes true",
        "set_option pp.explicit true",
        "#print Research.DerivativeSwitch.ActualBoundaryCup.LocalCupData",
        "#print Research.DerivativeSwitch.OrthogonalComparison.fibreD",
        "#print Research.DerivativeSwitch.OrthogonalComparison.fibreComparison",
        "open Lean Elab Command in", "run_cmd do",
        "  let names : Array Name := #[" + ", ".join("`" + n for n in NAMES) + "]",
        "  for name in names do",
        "    let declaration ← getConstInfo name",
        '    logInfo m!"STATEMENT {name}: {declaration.type}"',
        "    let axioms ← collectAxioms name",
        "    for ax in axioms do",
        "      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do",
        '        throwError "Unexpected axiom {ax} in {name}"',
        '    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"',
        f'  logInfo "AXIOM_AUDIT_PASS proof_roots={len(NAMES)}"', ""]))
    printed = run("axioms-and-statements", base + [str(audit)], env)
    actual = {n: sorted(a.strip() for a in values.split(",") if a.strip())
              for n, values in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", printed)}
    if set(actual) != set(NAMES) or any(set(a) - ALLOWED for a in actual.values()):
        raise RuntimeError("Incomplete or unexpected axiom audit")
    after = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    if before != after:
        raise RuntimeError("Proof/specification inputs changed during native verification")
    result = {
        "status": "PASS", "profile": "development", "lean": version,
        "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "modules_freshly_compiled": MODULES, "proof_roots": NAMES,
        "theorem_axioms": actual, "permitted_axioms": sorted(ALLOWED),
        "dependencies": dependencies,
        "dependency_cache": "Existing official pinned Mathlib import cache; no full source rebuild",
        "input_hashes_before": before, "input_hashes_after": after,
        "artifact_hashes": {str(p.relative_to(lib)): sha(p) for p in lib.rglob("*.olean")},
        "paranoid": "NOT_RUN", "protected_comparison": "NOT_RUN",
        "export_replay": "NOT_RUN", "external_checkers": "NOT_RUN",
        "actual_galois_selmer_construction": "SOURCE_APPLICATION_ONLY_NOT_FORMALIZED",
        "determinant_functor": "HUMAN_PROOF_ONLY_NOT_FORMALIZED",
    }
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "new_proof_roots": len(NAMES), "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
