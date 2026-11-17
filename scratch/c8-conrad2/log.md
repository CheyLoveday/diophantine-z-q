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
