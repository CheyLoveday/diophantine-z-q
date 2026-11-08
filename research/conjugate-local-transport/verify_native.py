#!/usr/bin/env python3
"""Build only the two new local-conjugation modules and audit their proof roots."""
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
MODULES = ["ConjugateLocalTransport", "ConjugateLocalH1"]
NS = "Research.DerivativeSwitch.ConjugateLocalTransport."
TARGETS = [NS + n for n in [
    "crossed_conjugation", "crossed_pow_of_trivial",
    "LocalData.tate_transporter", "LocalData.twist_transporter",
    "LocalData.twist_transporter_inv", "LocalData.tate_finite",
    "LocalData.twist_finite", "LocalData.twist_inertia",
    "LocalData.rawConjugate_isCrossed", "LocalData.conjugation_finite",
    "LocalData.conjugation_inertia", "LocalData.rawConjugate_finite",
    "LocalData.rawConjugate_inertia", "LocalData.coordinates_rawConjugate",
    "LocalData.coordinates_rawConjugate_of_neg_one", "LocalData.twist_conjugation_finite",
    "LocalData.twist_conjugation_inertia", "LocalData.coordinates_add_coboundary",
    "LocalData.conjugate_coordinates_add_coboundary",
    "h1_projection_surjective", "cocycleEvaluation_kills_kernel",
    "h1Evaluation_projection", "cocyclePullback_kills_kernel",
    "h1Pullback_projection", "LocalData.h1Coordinates_projection",
    "LocalData.conjugateH1Coordinates_projection", "LocalData.h1_local_transport",
]]
DEFS = [NS + n for n in [
    "twist", "conjugation", "IsCrossed", "LocalData", "LocalData.transportUnit",
    "LocalData.coordinates", "LocalData.rawConjugate", "cocycleEvaluation",
    "h1Evaluation", "cocyclePullback", "h1Pullback", "LocalData.h1Coordinates",
    "LocalData.conjugateH1Coordinates",
]]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
            raise RuntimeError(f"{label} failed; see {output}")
        return r.stdout.decode()

    sources = [PROJECT / "Research/DerivativeSwitch" / (m + ".lean") for m in MODULES]
    inputs = sources + [Path(__file__), PACKET / "SPEC.md", PACKET / "APPLICATION.md",
        PACKET / "DERIVATION.md", PACKET / "evidence/source-bindings.json",
        PROJECT / "lean-toolchain", PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json"]
    before = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    lock = json.loads((PROJECT / "lake-manifest.json").read_text())
    libraries, dependencies = [], []
    for package in lock["packages"]:
        folder = PROJECT / ".lake/packages" / package["name"]
        rev = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
        if rev != package["rev"]:
            raise RuntimeError("Dependency drift: " + package["name"])
        subprocess.run(["git", "-C", str(folder), "diff", "--quiet", "HEAD", "--"], check=True)
        dependencies.append({"name": package["name"], "revision": rev})
        path = folder / ".lake/build/lib/lean"
        if path.exists():
            libraries.append(path)
    version = run("lean-version", ["lean", "--version"]).strip()
    if "version 4.35.0," not in version or "eb6cafb" not in version:
        raise RuntimeError("Wrong Lean version")
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
        "import Research.DerivativeSwitch.ConjugateLocalH1", "import Lean.Util.CollectAxioms",
        "set_option pp.universes true", "set_option pp.explicit true",
        *["#print " + n for n in DEFS],
        "open Lean Elab Command in", "run_cmd do",
        "  let names : Array Name := #[" + ", ".join("`" + n for n in TARGETS) + "]",
        "  for name in names do",
        "    let declaration ← getConstInfo name",
        '    logInfo m!"STATEMENT {name}: {declaration.type}"',
        "    let axioms ← collectAxioms name",
        "    for ax in axioms do",
        "      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do",
        '        throwError "Unexpected axiom {ax} in {name}"',
        '    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"',
        f'  logInfo "AXIOM_AUDIT_PASS declarations={len(TARGETS)}"', ""]))
    printed = run("axioms-and-statements", base + [str(audit)], env)
    actual = {name: sorted(x.strip() for x in values.split(",") if x.strip())
              for name, values in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", printed)}
    if set(actual) != set(TARGETS) or any(set(a) - ALLOWED for a in actual.values()):
        raise RuntimeError("Incomplete or unexpected axiom audit")
    after = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    if before != after:
        raise RuntimeError("Inputs changed during native verification")
    result = {
        "status": "PASS", "profile": "development", "lean": version,
        "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "modules_freshly_compiled": MODULES, "targets": TARGETS, "theorem_axioms": actual,
        "permitted_axioms": sorted(ALLOWED), "dependencies": dependencies,
        "dependency_cache": "Pinned Mathlib master cache import closures; not source-rebuilt here",
        "additional_cache_command": "MATHLIB_CACHE_DIR=$PWD/.lake/mathlib-cache lake exe cache get --cache-from=master Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree",
        "input_hashes_before": before, "input_hashes_after": after,
        "artifact_hashes": {str(p.relative_to(lib)): sha(p) for p in lib.rglob("*.olean")},
        "protected_comparison": "NOT_RUN", "export_replay": "NOT_RUN",
        "external_checkers": "NOT_RUN", "paranoid": "NOT_RUN",
        "actual_group_cohomology": "Mathlib groupCohomology.H1 of the inhomogeneous cochain complex",
        "continuous_galois_and_selmer_construction": "SOURCE_APPLICATION_ONLY_NOT_FORMALIZED",
        "retained_inner_limit": "SOURCE_APPLICATION_ONLY_NOT_FORMALIZED",
    }
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "new_theorem_roots": len(TARGETS),
                      "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
