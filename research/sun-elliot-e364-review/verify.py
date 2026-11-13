#!/usr/bin/env python3
"""Fresh local replay and Lean audit for the integrated interface packet."""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / "research" / "sun-elliot-e364-review"
SOURCE = PACKET / "source"
LEAN_SRC = PACKET / "lean"
MODULES = ["Core", "E364", "GroupRing", "Models", "Q2Descent", "PowerfulBridge", "Audit"]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
EXPECTED_AXIOM_REPORTS = 28
FORBIDDEN = re.compile(r"\b(?:sorry|admit|unsafe|native_decide|axiom)\b")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(cmd: list[str], log: Path, env: dict[str, str] | None = None) -> None:
    log.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(cmd, cwd=ROOT, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(proc.stdout)
    if proc.returncode:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(cmd)}; see {log}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path,
                    default=ROOT / ".scratch" / "sun-elliot-e364-review-check")
    args = ap.parse_args()
    out = args.output if args.output.is_absolute() else ROOT / args.output
    if out.exists():
        raise SystemExit(f"refusing to reuse output: {out}")
    out.mkdir(parents=True)

    manifest = json.loads((SOURCE / "MANIFEST.json").read_text())
    for row in manifest["files"]:
        path = SOURCE / row["path"]
        if path.stat().st_size != row["bytes"] or sha256(path) != row["sha256"]:
            raise SystemExit(f"source receipt mismatch: {path.name}")

    replay = out / "replay"
    replay.mkdir()
    normal_cmd = [sys.executable, "-B", str(SOURCE / "replay.py"),
                  "--output", str(replay / "results.json")]
    optimized_cmd = [sys.executable, "-B", "-O", str(SOURCE / "replay.py"),
                     "--output", str(replay / "results_optimized.json")]
    run(normal_cmd, replay / "replay.stdout.txt")
    run(optimized_cmd, replay / "replay_optimized.stdout.txt")
    if (replay / "results.json").read_bytes() != (replay / "results_optimized.json").read_bytes():
        raise SystemExit("normal and optimized replay results differ")
    for name in ("results.json", "replay.stdout.txt"):
        produced = replay / name
        if produced.read_bytes() != (SOURCE / name).read_bytes():
            raise SystemExit(f"fresh replay does not reproduce attached {name}")
    if (replay / "results_optimized.json").read_bytes() != (SOURCE / "results_optimized.json").read_bytes():
        raise SystemExit("optimized replay differs from attached result receipt")
    if (replay / "replay_optimized.stdout.txt").read_bytes() != (SOURCE / "replay_optimized.stdout.txt").read_bytes():
        raise SystemExit("optimized stdout differs from attached receipt")

    for path in LEAN_SRC.rglob("*.lean"):
        text = path.read_text()
        match = FORBIDDEN.search(text)
        if match:
            raise SystemExit(f"forbidden Lean token {match.group()!r} in {path}")

    env = os.environ.copy()
    lib = out / "lib"
    lib.mkdir()
    env["LEAN_PATH"] = str(lib) + os.pathsep + env.get("LEAN_PATH", "")
    commands = []
    for module in MODULES:
        src = LEAN_SRC / "SunElliotE364" / f"{module}.lean"
        dst = lib / "SunElliotE364" / f"{module}.olean"
        dst.parent.mkdir(parents=True, exist_ok=True)
        cmd = ["lean", "-t0", "-j1", "-Ddebug.skipKernelTC=false",
               "-R", str(LEAN_SRC), "-o", str(dst), str(src)]
        commands.append(cmd)
        run(cmd, out / "logs" / f"{module}.log", env)

    axiom_text = (out / "logs" / "Audit.log").read_text()
    report_count = axiom_text.count("depends on axioms:")
    if report_count != EXPECTED_AXIOM_REPORTS:
        raise SystemExit(f"expected {EXPECTED_AXIOM_REPORTS} axiom reports, got {report_count}")
    for line in axiom_text.splitlines():
        if "depends on axioms:" not in line:
            continue
        match = re.search(r"depends on axioms: \[([^]]*)\]", line)
        if not match:
            raise SystemExit(f"unparsed axiom output: {line}")
        axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
        if not axioms <= ALLOWED:
            raise SystemExit(f"unexpected axioms {sorted(axioms - ALLOWED)} in {line}")
    if re.search(r"sorryAx|\badmit\b|\bunsafe\b|native_decide", axiom_text):
        raise SystemExit("forbidden axiom or shortcut in Audit.log")

    result = {
        "status": "PASS",
        "scope": "Local exact replay and native Lean checks of the formalized interfaces only; no global arithmetic theorem is established.",
        "lean_modules": MODULES,
        "compiler_flags": ["-t0", "-j1", "-Ddebug.skipKernelTC=false"],
        "axiom_reports": EXPECTED_AXIOM_REPORTS,
        "allowed_axioms": sorted(ALLOWED),
        "python_replay": "normal and optimized outputs match each other and attached receipts byte-for-byte",
        "source_files_checked": len(manifest["files"]),
        "commands": commands,
        "source_sha256": {str(p.relative_to(PACKET)): sha256(p)
                           for p in sorted(PACKET.rglob("*"))
                           if p.is_file() and p.name not in {"RESULT.json", "verify.log"}
                           and not p.is_relative_to(args.output.resolve())
                           and "evidence" not in p.relative_to(PACKET).parts},
        "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "limitations": [
            "not external-kernel or multi-checker replay",
            "not independent mathematical review",
            "no proof of Erdos 364, the Diophantine theorem, restricted converse, prime-pattern theorem, or complete symbolic compiler atlas",
            "no Kummer-profile, explicit defect-product formula, generalized separator-bound, or continuous-cohomology formalization",
        ],
    }
    (out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "status": result["status"],
        "lean_modules": len(MODULES),
        "axiom_reports": EXPECTED_AXIOM_REPORTS,
        "allowed_axioms": sorted(ALLOWED),
        "replay": "byte-identical normal/optimized outputs and attached receipts",
        "result": str(out / "RESULT.json"),
    }, indent=2))


if __name__ == "__main__":
    main()
