import ZInQKernel.Contrib.OneProof.ColmezProperModel.MilneModel
import ZInQKernel.Contrib.OneProof.ColmezProperModel.ModelRow

/-!
# The row `colmez1992DeRhamAbVar` from Milne's Theorem 7.1 and the model row

`colmez1992DeRhamAbVar_iff_model` (`ModelRow.lean`) identifies the row with
`Colmez1992DeRhamAbVarModel` (the row with `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]`, for every proper model
`𝒳` of `A` over `O_F`) under `ProperModelExists`, and `properModelExists_of_milne`
(`MilneModel.lean`) proves `ProperModelExists` from Milne's Theorem 7.1
(`MilneThm71Projective`). Together they prove the row from these two inputs.

Flatness: if Colmez's "modèle propre" (p. 638) is read as a proper model that is flat over `O_K`,
the model form still follows from the print: replace `𝒳` by the schematic closure of its generic
fibre, which is proper and flat with the same generic fibre and through which every
`O_{C_p}`-point factors uniquely (`O_{C_p}` has no `O_F`-torsion), compatibly with the transported
group law and `G_F` (background).
-/

set_option autoImplicit false

namespace ZInQ.Contrib.ColmezProperModel

/-- **The row `colmez1992DeRhamAbVar`** from Milne's Theorem 7.1 (`MilneThm71Projective`: every
abelian variety is projective) and the row on `𝒳(O_{C_p})` for every proper model
(`Colmez1992DeRhamAbVarModel`). -/
theorem colmez1992DeRhamAbVar_of_model_milne (hM : MilneThm71Projective)
    (h : Colmez1992DeRhamAbVarModel) : DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar :=
  (colmez1992DeRhamAbVar_iff_model (properModelExists_of_milne hM)).2 h

end ZInQ.Contrib.ColmezProperModel
