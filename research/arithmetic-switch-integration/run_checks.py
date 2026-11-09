#!/usr/bin/env python3
"""Run the four exact-check scripts and verify preservation of the old tree."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
BASE = "fb29fe2bc6968e178a6458357c437574221b5338"
SCRIPTS = {
    "cochains": "research/actual-boundary-cup/check_cochains.py",
    "comparison": "research/orthogonal-comparison/check_comparison.py",
    "determinant": "research/strict-determinant-bridge/check_bridge.py",
    "integration": "research/arithmetic-switch-integration/check_integration.py",
}
FROZEN_ROOTS = ("research/determinant-switch/", "research/boundary-scalar/",
                "research/scalar-ratio/")
FROZEN_MODULES = {
    "lean/Research/DerivativeSwitchBoundary.lean", "lean/Research/BoundaryScalar.lean",
    "lean/Research/BoundaryCupAdapter.lean", "lean/Research/DerivativeSwitch/Coordinate.lean",
    "lean/Research/DerivativeSwitch/CommonStrict.lean", "lean/Research/DerivativeSwitch/UnitCriterion.lean",
    "lean/Research/DerivativeSwitch/BoundaryCup.lean",
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def preservation():
    tree = subprocess.check_output(["git", "ls-tree", "-rz", BASE], cwd=ROOT)
    total, frozen, differences = 0, {}, []
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        meta, name = entry.split(b"\t", 1)
        mode, kind, oid = meta.decode().split()
        if kind != "blob":
            continue
        name = name.decode()
        path = ROOT / name
        total += 1
        if not path.is_file():
            differences.append(name)
            continue
        content = path.read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()
        if actual != oid:
            differences.append(name)
        if name in FROZEN_MODULES or name.startswith(FROZEN_ROOTS):
            frozen[name] = hashlib.sha256(content).hexdigest()
    if differences:
        raise RuntimeError("Existing source drift: " + repr(differences))
    return {"status": "PASS", "base_commit": BASE,
            "old_tracked_files_checked": total, "old_tracked_files_changed": differences,
            "frozen_files_checked": len(frozen), "frozen_sha256": frozen,
            "scope": "Byte preservation, not revalidation of historical mathematical claims"}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: run_checks.py NEW_OUTPUT_DIRECTORY")
    output = Path(sys.argv[1]).resolve()
    output.mkdir(parents=True, exist_ok=False)
    before = {name: sha(ROOT / script) for name, script in SCRIPTS.items()}

    def run(item):
        label, script = item
        args = [sys.executable, "-B", script]
        r = subprocess.run(args, cwd=ROOT, capture_output=True)
        (output / (label + ".stdout.json")).write_bytes(r.stdout)
        (output / (label + ".stderr.txt")).write_bytes(r.stderr)
        command = {"command": args, "cwd": str(ROOT), "exit_code": r.returncode}
        try:
            data = json.loads(r.stdout)
        except (ValueError, UnicodeDecodeError):
            data = {"status": "FAIL", "reason": "No JSON result"}
        return label, {"command": command, "result": data}

    with ThreadPoolExecutor(max_workers=4) as pool:
        checks = dict(pool.map(run, SCRIPTS.items()))
    after = {name: sha(ROOT / script) for name, script in SCRIPTS.items()}
    result = {"status": "PASS", "checks": checks,
              "script_hashes_before": before, "script_hashes_after": after,
              "python": sys.version, "runner_sha256": sha(Path(__file__))}
    if before != after or any(c["command"]["exit_code"] or c["result"]["status"] != "PASS"
                              for c in checks.values()):
        result["status"] = "FAIL"
    result["preservation"] = preservation()
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "checks": list(checks),
                      "old_tracked_files_preserved": result["preservation"]["old_tracked_files_checked"],
                      "frozen_files_preserved": result["preservation"]["frozen_files_checked"],
                      "output": str(output)}, indent=2))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
