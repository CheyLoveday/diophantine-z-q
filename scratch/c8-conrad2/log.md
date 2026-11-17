# c8-conrad2 results log

Base: wip/c8-conrad a411466b4, merged origin/main 97247ce1c (merge cff986a75). Top: `frozenTarget` via
`HDec.HSyn.sixContactMin_of_open71 r t l` (TailZ78), `l : OpenAddedLeaves27` = the two Picard rows.

## 0. Source access (VERIFIED: tool refusals)
- WebFetch www.jmilne.org/math/CourseNotes/AV.pdf, jmilne.org/..., web.archive.org/...: refused by the sandbox domain
  check. External web search tool: auth failure. No local copy of Milne's notes on the host (find ~ -maxdepth 3).
  => Milne v2.00 locator for Poincaré reducibility stays UNVERIFIED.

## 1. Consumer map at the current top (VERIFIED by reading the source)
- open71 (TailZ78) -> open70 (TailZ77) -> open48_eb_k954 (TailZ69) -> open45_pz_eb (EichlerBoundCopy L3291).
- open45_pz_eb builds t13HF by `openTextbookLeaves13HF_of_open16_22_pz t _ l` (PicZeroCharZeroCopy L2211):
  `poincareComplement := poincareComplement_of_open0 l.picRepresentableAbVar l.picZeroAbVar ...` = consumer (ii).
- open45_pz_eb builds l18 by `openAddedLeaves18_of_OpenAddedLeaves22_pz` (phiAmpleIsogeny, weilPairingMumford from
  the rows); l17..l4 carry `t09SymmIsogenyExists`; `gluePieces_of_open4_hf_pz_eb` (EichlerBoundCopy L2659) fills
  `GaloisPieces.detTate` by `detTate_of_leaves4_pz l.t09SymmIsogenyExists ...`; read by `g12Det_of_pz` in
  `g8_g12_of_leaves3_hf_pz_eb` (L2473) = consumer (i).
- open70 also passes l26 to `openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf` = consumer (iii) (r10 path).

## 2. Build and dry run (VERIFIED, compiled)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.C8Conrad` on the
  merged base: ok, 16225 jobs; `frozenTarget` standard axioms (`build_main.txt`).
- `scratch/c8-conrad2/Taint.lean` (seeds t09SymmIsogenyExists, phiAmpleIsogeny, weilPairingMumford, detTate):
  closure 304616, 70 tainted, 13 carriers (OpenAddedLeaves4PZ..18PZ, GaloisPieces) (`taint_out.txt`).
- `ZInQKernel/Contrib/OneProof/C8Poincare.lean`: `C8Inputs`, `g12DetPZ_of_inputs`, `t8_of_poincareComplement`,
  `openTextbookLeaves13HF_of_open16_P`. lake build ok.
- `gen/gen.py` -> `C8DryRunGen.lean` (70 blocks, 13 structures, both readers replaced, row fields stripped from
  copied structures) + `gen/top.lean` (handwritten open45/48/70/71 copies and `frozenTarget_c8`) = `C8DryRun.lean`.
  `lake env lean`: no errors; `frozenTarget_c8` and `sixContactMin_of_open71_c8`: [propext, Classical.choice,
  Quot.sound] (`dryrun_out.txt`).
- Field taint from `frozenTarget_c8` with seeds picRepresentableAbVar, kleimanPicZeroProper954SiteQ
  (`C8DryRunTaint.lean`, `dryrun_taint_out.txt`): tainted fields {kleimanPicZeroProper954SiteQ,
  kleimanPicZeroProper954, picRepresentableAbVar, picZeroAbVar, hodgeTateDecompAbVar, r10}; terminal consumers only
  through `r10` (g8_g12_c8, afterG7_c8, gluePieces_c8 read `ResearchLeaves3EB.r10` / `OpenResearchLeaves2EB.r10`),
  i.e. consumer (iii) only. `phiAmpleIsogeny`, `weilPairingMumford`, `t09SymmIsogenyExists`, `poincareComplement`,
  `t8` are no longer tainted.

## 3. LocAlgExponentEqWeight (VERIFIED, compiled)
- `scratch/c8-conrad2/C8LocAlg.lean`: `locAlgExponentEqWeight_of_tateInertia : TateTwistInvariantsInertia →
  LocAlgExponentEqWeight`, standard axioms. New leaf `TateTwistInvariantsInertia` (Tate 1967 §3.3 Thm 2 at
  L = completion of K^ur, G_L = G_K ∩ I_{Q_p}; locator UNVERIFIED). Helpers proved: `norm_eq_one_of_valuation_eq_one`,
  `exists_unit_isArtinLift` (Tau Ceti `map_artinMap_unitFiltration_zero`), `cyc_of_isArtinLift` (Tau Ceti
  `localCyclotomicCharacter_artinMap_padic`; PkgI4.cyc = localCyclotomicCharacter by rfl), `toZModPow_cyc_eq_one`.
