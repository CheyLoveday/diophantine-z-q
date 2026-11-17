# derham-direct results log

Base: wip/leaf-fold33b 2da302cd7. Build tree copied (reflink) from ~/dzq-wt/leaf-fold33b/.lake/build (only added
files vs base); `lake build ZInQKernel.Contrib.OneProof.DeRhamPrint` replayed in 6 s (VERIFIED).

## Findings (VERIFIED by reading the tree)
- Target: `DeRhamPrint.DeRhamVpAbVarPrinted` (ZInQKernel/Contrib/OneProof/DeRhamPrint.lean:85) =
  `∀ p F A, IsDeRhamTensorOver p (A.galRep p)` (IsDeRhamTensorOver: TailS.lean:1983,
  `finrank ℚ_p (ddrTensorOver p ρ) = finrank ℚ_p F * finrank ℚ_p W`).
- Existing `iotaDR` (Contrib/G9/G9.lean:91) embeds `fieldF p F` into `B_dR` only for `IsGalois ℚ_p F`
  (needs `gammaF`). Its ingredients `exists_hensel_lift`, `hensel_lift_natural`, `root_eq_of_theta`
  (Contrib/G9/HenselEmb.lean), `thetaAlg`, `sPlus`, `isUnit_of_thetaAlg_ne_zero`, `algPlus` (G9.lean, before the
  `IsGalois` variable) work for any finite `F`; `iotaCp` (Local.lean:165) needs no Galois hypothesis.
- `range_gfToGqp_eq` (TailS.lean:374): `range (gfToGqp p F) = (fieldF p F).fixingSubgroup`.
- `Module.finrank_mul_finrank` (Mathlib 4.35, Dimension/Free.lean:68) has no finiteness hypotheses.

## Compile log
- 01:00 `lake env lean scratch/derham-direct/DeRhamDirect.lean`: no errors, no warnings; axioms of
  `deRhamVpAbVarPrinted_of_direct`, `direct_of_deRhamVpAbVarPrinted`, `iotaPlusF_unique`: [propext,
  Classical.choice, Quot.sound] (VERIFIED, output in DeRhamDirect-output.txt). Earlier attempts: `Module.Free`
  of `ddrF` not found by instance search (IntermediateField semiring path mismatch), fixed by `exact
  Module.Free.of_divisionRing ...`.

## Statements proved (VERIFIED, compiled)
- `iotaPlusF p F : fieldF p F →ₐ[ℚ_p] B_dR^+` for any finite `F/ℚ_p` (no Galois hypothesis), `θ⁺ ∘ ι = F' ⊆ ℂ_p`;
  `iotaPlusF_unique` (canonical); `bdrAct_iotaF`: `G_F` (through gfToGqp) fixes `iotaF x` in `B_dR`.
- `ddrF p ρW : Submodule F' (B_dR ⊗ W)`, `restrictScalars_ddrF : ... = ddrTensorOver p ρW` (Iff.rfl).
- `finrank_ddrTensorOver`: `finrank ℚ_p (ddrTensorOver p ρW) = finrank ℚ_p F * finrank F' (ddrF p ρW)`.
- `isDeRhamTensorOver_iff`: `IsDeRhamTensorOver p ρW ↔ finrank F' (ddrF p ρW) = finrank ℚ_p W`.
- New leaf `DeRhamVpAbVarDirect` (∀ p F A, `finrank F' (ddrF p (A.galRep p)) = finrank ℚ_p (A.V p)`);
  `deRhamVpAbVarPrinted_of_direct` and the converse (equivalent Props).
