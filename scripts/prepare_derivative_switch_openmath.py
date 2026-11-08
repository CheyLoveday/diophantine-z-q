#!/usr/bin/env python3
"""Prepare the frozen six-lemma project from a repository checkout, offline.

This does not install dependencies, invoke Lean, run --paranoid, or dispatch a
cloud job. Open Math performs those operations after pulling the repository.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "research/determinant-switch"
REVIEWED_SOURCE_COMMIT = "2c15940380520d6b6de72c2a1b6700ed192a7a87"
PACKET_MANIFEST_SHA256 = "de9e04423f3ccafa9690e6ff53c1f0bb79f5f91406ee3e4e89246ce2cf97fa12"
PROJECT_MANIFEST_SHA256 = "e37368316a682d30f9358d7cf1c1ebd01e622e7896c99ca020ae5f94288f6188"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(manifest, base, expected):
    if digest(manifest) != expected:
        raise SystemExit(f"Frozen manifest changed: {manifest}")
    count = 0
    for line in manifest.read_text().splitlines():
        wanted, relative = line.split("  ", 1)
        path = (base / relative).resolve()
        if not path.is_relative_to(base.resolve()) or not path.is_file():
            raise SystemExit(f"Missing or outside-root manifest input: {relative}")
        if digest(path) != wanted:
            raise SystemExit(f"Frozen input changed: {relative}")
        count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("lean/.checks/openmath-derivative-switch"),
                        help="New output directory, relative to repository root unless absolute")
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    if output.exists():
        raise SystemExit("Output must be new; choose another --output directory")
    count = check_manifest(PACKET / "MANIFEST.sha256", ROOT, PACKET_MANIFEST_SHA256)
    checkout = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    generator = PACKET / "verification/prepare.py"
    subprocess.run([sys.executable, "-B", str(generator), "--output", str(output)],
                   check=True, cwd=ROOT)
    generated_count = check_manifest(output / "MANIFEST.sha256", output,
                                     PROJECT_MANIFEST_SHA256)
    receipt = {
        "status": "PREPARED_FROM_REPOSITORY",
        "checkout_commit": checkout,
        "reviewed_source_commit": REVIEWED_SOURCE_COMMIT,
        "packet_manifest_sha256": PACKET_MANIFEST_SHA256,
        "packet_inputs_checked": count,
        "generated_manifest_sha256": PROJECT_MANIFEST_SHA256,
        "generated_inputs_checked": generated_count,
        "preparation_script_sha256": digest(Path(__file__).resolve()),
        "lean_invoked": False,
        "network_used": False,
        "paranoid_run": "NOT_RUN; owned by Open Math in the cloud",
        "cloud_command": ["lake", "comparator", "--config", "comparator.json", "--paranoid"],
    }
    (output / "OPENMATH_PREPARATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
