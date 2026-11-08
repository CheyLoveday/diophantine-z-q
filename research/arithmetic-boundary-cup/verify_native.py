#!/usr/bin/env python3
"""Scoped native build/axiom audit of the new bridge; no cloud or comparator."""
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
MODULES = ["Coordinate", "CommonStrict", "UnitCriterion", "BoundaryCup", "ArithmeticBridge"]
NS = "Research.DerivativeSwitch.ArithmeticBridge."
TARGETS = [NS + s for s in [
    "cocycle_conjugation", "cocycle_transport_shared_unit",
    "area_smul_left", "area_smul_right", "coefficient_pairing_symmetric",
    "cone_pure_boundary", "PairedBoundaryData.partner_local",
    "transported_boundary_cup", "arithmetic_unit_comparison",
]]
DEFS = [NS + s for s in ["LocalPair", "rawCup", "localTransport",
    "coneProductThird", "PairedBoundaryData", "PairedBoundaryData.partner",
    "PairedBoundaryData.functional"]]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


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

    def run(name, args, cwd=PROJECT, env=None):
        r = subprocess.run(args, cwd=cwd, env=env, capture_output=True)
        (output / (name + ".txt")).write_bytes(r.stdout + r.stderr)
        commands.append({"label": name, "command": args, "cwd": str(cwd),
                         "exit_code": r.returncode})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if r.returncode:
            raise RuntimeError(f"{name} failed; see {output / (name + '.txt')}")
        return (r.stdout + r.stderr).decode()

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
    sources = []
    for module in MODULES:
        relative = Path("Research/DerivativeSwitch") / (module + ".lean")
        sources.append(PROJECT / relative)
        run(module, base + ["-o", str(lib / relative.with_suffix(".olean")), str(relative)], env=env)
    audit = output / "Audit.lean"
    audit.write_text("\n".join([
        "import Research.DerivativeSwitch.ArithmeticBridge", "import Lean.Util.CollectAxioms",
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
        '  logInfo "AXIOM_AUDIT_PASS declarations=9"', ""]))
    printed = run("axioms-and-statements", base + [str(audit)], env=env)
    actual = {name: sorted(x.strip() for x in values.split(",") if x.strip())
              for name, values in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", printed)}
    if set(actual) != set(TARGETS) or any(set(a) - ALLOWED for a in actual.values()):
        raise RuntimeError("Incomplete or unexpected axiom audit")
    inputs = sources + [Path(__file__), PACKET / "FORMAL_SPEC.md", PACKET / "APPLICATION.md",
        PACKET / "manuscript-insertion.tex", PROJECT / "lean-toolchain",
        PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json"]
    result = {"status": "PASS", "profile": "development", "lean": version,
        "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "modules_freshly_compiled": MODULES, "targets": TARGETS, "theorem_axioms": actual,
        "permitted_axioms": sorted(ALLOWED), "dependencies": dependencies,
        "dependency_cache": "Previously provisioned pinned Mathlib master import closures",
        "input_hashes": {str(p.relative_to(ROOT)): sha(p) for p in inputs},
        "artifact_hashes": {str(p.relative_to(lib)): sha(p) for p in lib.rglob("*.olean")},
        "protected_comparison": "NOT_RUN", "export_replay": "NOT_RUN",
        "external_checkers": "NOT_RUN", "paranoid": "NOT_RUN",
        "actual_arithmetic_selmer_construction": "NOT_FORMALIZED"}
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "selected_declarations": len(TARGETS),
                      "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
