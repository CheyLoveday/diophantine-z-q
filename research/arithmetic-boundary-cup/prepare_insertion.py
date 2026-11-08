#!/usr/bin/env python3
"""Generate, but never apply, the source-pinned manuscript insertion patch."""
import difflib
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
PACKET = Path(__file__).resolve().parent
SOURCE = ROOT / "manuscripts/quartic_v13.tex"
EXPECTED = "9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd"
START = "The determinant comparison is exact even if $v$ is divisible.\n"
END = "Requiring $x$ integral would be wrong when $v$ is divisible.\n"


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: prepare_insertion.py OUTPUT.patch")
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED:
        raise SystemExit("V13 source drift: review insertion against new source first")
    old = raw.decode()
    if old.count(START) != 1 or old.count(END) != 1:
        raise SystemExit("Insertion anchor is not unique")
    begin = old.index(START)
    end = old.index(END, begin) + len(END)
    insertion = (PACKET / "manuscript-insertion.tex").read_bytes()
    new = old[:begin] + insertion.decode() + old[end:]
    header = (
        "Generated non-authoritative patch; edit manuscript-insertion.tex instead.\n"
        "Source: research/arithmetic-boundary-cup/manuscript-insertion.tex\n"
        "Generate: python -B research/arithmetic-boundary-cup/prepare_insertion.py OUTPUT.patch\n"
        f"Insertion SHA-256: {hashlib.sha256(insertion).hexdigest()}\n"
        f"Base manuscript SHA-256: {EXPECTED}\n\n"
    )
    patch = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
        fromfile="a/manuscripts/quartic_v13.tex", tofile="b/manuscripts/quartic_v13.tex"))
    Path(sys.argv[1]).write_text(header + patch)


if __name__ == "__main__":
    main()
