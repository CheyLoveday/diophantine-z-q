# h29-split results log

## Setup (2026-11-15 02:17 PST)
- Base 6edf020d (wip/h29-split). Build: `cp -r ~/dzq-check2/.lake/build` and `lean/.lake/build`
  (dzq-check2 at the same commit 6edf020d).
- **TYZ source absent**: `~/tyz-src/Period7.tex` does not exist; `find / -xdev` and `find ~ /tmp /data /var/tmp
  -maxdepth 6` for `*period7*`, `*1411.4728*` found nothing (VERIFIED). No network allowed. So every TYZ line
  number and statement below is quoted from earlier notes that read the source: `docs/research/nt-tyz.md` §1.2
  (states "VERIFIED against the source"), `rv-nt-tyz.md` (I2 row, B1), `rv-tyz-inputs.md` §1.2 and
  `scratch/rv-tyz-inputs/log.md` Step 1 (read L496–1162). Marked QUOTED below, not re-read.

## Target
- `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` (ZInQKernel/Contrib/TYZDecomp/Leaves.lean:273):
  `∀ ℓ, (∀ m sqfree, m%8∈{1,3} → (ℓ m:ℂ)² = lcalSq m) → PropN.LemmaTwoEight ℓ`.
