# pb-dimform results log

- base: wip/lane74b 6b404a20c. Before-copy of PanBergerFontaine.lean: scratch/pb-dimform/PanBergerFontaine.before.lean.txt
- build0.txt: an interrupted earlier `lake build` (first run, stopped by the host); no result.
- bc-reading.md: host note on Brinon-Conrad / survey readings (copied).
- Step (a)+(d) in place: PanBergerFontaine.lean restated (IsPstF := ∃ K finite, IsAdmissible (BstFOf) G_K ρ, dimension form;
  pb-p1's basis form kept as IsPstFBasis / LocalIsPstFBasis / BergerSurveyFBasis / PanPrintedFBasis; comparison lemmas
  isPstF_of_basis, localIsPstF_of_basis, bergerSurveyF_of_basis, panPrintedFBasis_of_F, bstFOf_eq_xi; docstrings re-cited to
  Brinon-Conrad). `lake build ZInQKernel.Contrib.OneProof.PanBergerFontaine`: Build completed successfully (build2.txt). VERIFIED.
  panBerger_of_F compiles unchanged (Berger's conclusion IsPstF on the de Rham model is Pan's hypothesis LocalIsPstF verbatim).
