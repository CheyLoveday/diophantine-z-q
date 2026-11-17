# fold33-copy log

Base wip/leaf-fold33b 30674d98 (origin/main c1e4ed1b is an ancestor: not merged).

## Step 0: merge
- Merged origin/wip/sga3-nbhd and origin/wip/goodmodel-iso; applied fold33-combine aac7b2a6's hygiene diff (scratch bundle copies renamed .lean.txt: scratch/sga3-nbhd/fold/TailZ46.lean, FoldCheck.lean, scratch/neron-ext/AutofoldDry.lean; host paths removed from merged logs/scripts). VERIFIED: the merged scratch/ and ZInQKernel/ trees equal aac7b2a6's on those paths.

## Build tree
- `.lake/build` and `lean/.lake/build` copied (reflink) from ~/dzq-wt/etaw32-proof (same H tree). Base build
  `lake build +Main +Discharges +SGA3NbhdDVR +SemistableNeronBaseChangeNoSGA3 +NeronGoodModelIso +MumfordGroupLawRed`:
  OK, 14192 jobs; frozenTarget [propext, Classical.choice, Quot.sound] (VERIFIED).
- Base hash dump `hashes_0_base.txt`: 14107 constants (VERIFIED).

## Tools
- `Taint.lean` (imports TailZ48): closure of `sixContactMin_of_open41` (241711 constants); carriers = the structures
  `OpenResearchLeaves14`..`29` (16; each has `sga3_VIB_3_10`/`_Nbhd` and `mumfordGroupLaw`/`mumfordGroupLawConn`);
  tainted (type or value mentions a carrier, transitively) 519, of which 66 source declarations: the 16 research
  generations, 11 research conversions in TailZ25–46, 39 copies in HomFreeFiniteAlgClosedReroute (the `_hf` chain
  `sixContactMin_of_open17_hf`..`40_hf`, `researchLeaves9_of_open14_hf`, `x6Rows_of_open14_hf`, the `_hf` research
  conversions 19←20, 20←21, 21←22, 23←24, 25←26, SGRFold's two `_hf` theorems, …) and TailZ48's
  `sixContactMin_of_open41` (the old top: not copied, replaced by the new top module). `taint_0_base.txt` (VERIFIED).
  The same carriers serve both folds (every generation carries both fields), so both copies use this one taint list.
- `gen/gen.py` (homfree-noemb's copylib with a taint-driven item list): copies the 65 declarations verbatim up to the
  renaming `X ↦ XNS`/`x ↦ x_ns` (field 1) or `XGM`/`x_gm` (field 2, both folds), applying the fold edits; asserts that
  no removed field is left in the code. `gen/top.py` writes the top module and patches Main.
- Finding (VERIFIED by compile): copylib emits each source block's top-level `open`/`set_option` context again; copying
  out of the HF reroute repeated 220 `open … MonObj` lines, and the late conversions (19←20 … 25←26) then timed out
  at `isDefEq` even at 1000000 heartbeats. Emitting each top-level context command once fixed it: the module
  compiles at default heartbeats in 51 s.

## Step 1: sga3-nbhd (`sga3_VIB_3_10_Nbhd`) as a copy reroute
- `ZInQKernel/Contrib/OneProof/NoSGA3Reroute.lean` (generated: `python3 scratch/fold33-copy/gen/gen.py
  scratch/fold33-copy/taint_0_base.txt sga3 ZInQKernel/Contrib/OneProof/NoSGA3Reroute.lean`): 65 blocks. Edit counts:
  13 `sga3_VIB_3_10` fields (gens 14–26), 3 `sga3_VIB_3_10_Nbhd` fields (27–29), 12 + 2 pass-through lines, the five
  readers once each (`semistableNeronBaseChange_noSGA3` in `researchLeaves9_of_open14_hf_ns`, `NF.sga7_IX_3_3_of_SH'`,
  `Persists.semistablePersistsSHcp_of_SH'`, TailZ44's conversion line deleted, `Pre.sga7_IX_3_3_SH_of_pre'`), 2
  docstrings. No hNBC threading is needed: the copy imports SemistableNeronBaseChangeNoSGA3 directly.
- `ZInQKernel/OneProof/H/TailZ49.lean` (top.py sga3): `OpenResearchLeaves30` (24 fields = OpenResearchLeaves29 without
  `sga3_VIB_3_10_Nbhd`), `openResearchLeaves29NS_of_OpenResearchLeaves30`, `sixContactMin_of_open42 (r :
  OpenResearchLeaves30) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves20) := sixContactMin_of_open40_hf_ns …`.
  Main: import TailZ49, binder `OpenResearchLeaves30`, `sixContactMin_of_open42 r t l`; docstring paragraph.
- Checks (VERIFIED):
  - `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +…NoSGA3Reroute +…TailZ49`: OK, 14186 jobs
    (`build_1_sga3-tail.txt`).
  - `#print axioms ZInQ.OneProof.frozenTarget` and `HDec.HSyn.sixContactMin_of_open42`: [propext, Classical.choice, Quot.sound].
  - Closure (`closure_1_sga3.txt`, 270696 constants): none of `CToPrinted.SGA3_VIB_3_10`, `SGA3IdComp.SGA3_VIB_3_10_Nbhd`,
    `sga3_VIB_3_10_of_nbhd`, `idComp_baseChange`, `semistableNeronBaseChange_of_printed_full`; no HomFree, no sorryAx;
    the originals `OpenResearchLeaves14`, `OpenResearchLeaves29`, `sixContactMin_of_open41` are out of it,
    `OpenResearchLeaves29NS` and `sixContactMin_of_open42` in it. Bundle `OpenResearchLeaves30`: 24 fields.
  - Hash guard (`hashes_0_base.txt` → `hashes_1_sga3.txt`, `hashdiff_1_sga3.txt`): before 14107, after 14139; only
    before 0; only after 32 (TailZ49: `OpenResearchLeaves30` with its 24 projections and constructor family,
    `openResearchLeaves29NS_of_OpenResearchLeaves30`, `sixContactMin_of_open42`); changed 1: `ZInQ.OneProof.frozenTarget`.
  - `lake env lean scripts/one_proof/OpenStatements.lean`: 40 open hypotheses (41 before).
  - kinds.tsv row `sga3_VIB_3_10_Nbhd` dropped (no claims row). `render_open.py` then `--check`: ok, 40 open
    hypotheses, all classified; **32 H hypotheses, strictest 12/20, 8 others** (33, 13/20 before).
  - `frontier_crosswalk.py` then `--check`: ok (232 IDs, 31 matched).
  - `scratch/contrib-kit/DischargesTest.lean` rerun into `DischargesTest-output.txt`.
  - `uvx --offline … autoform check blueprint --lean-root .`: runs on this host; "OK: 781 articles, 2343
    dependencies, 705 fully proved, 2531 declaration name(s) resolved" (`autoform_1_sga3.txt`).
