import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.Transfer
import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.MinimalModelsExist
import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.TransferFinal

/-!
# Lane RC22 (glue sweep, limits): the transfer of (5.1) with the minimal model produced

Lemma `ex:limits-residual-bound`, tex 4598–4647 ("It remains to transfer this estimate to the
original support").

Lane RC6 states the existence of minimal models over a local ring as the GLUE proposition
`ZInQ.Manuscript.RC.Limits.MinimalModelsExist R` (`RC/Limits/ResidualAlgebra.lean`, tex 4633–4647).
It is PROVED for every local ring by `ZInQ.Contrib.CloudB3RC53.ResidualTransfer.minimalModelsExist_proof`
(`CloudB3RC53/ResidualTransfer/MinimalModelsExist.lean`). In the tree, `transferOfModels_final` and
`transferOfSupportChange_final` (`CloudB3RC53/ResidualTransfer/TransferFinal.lean`) already remove
it from `transferOfModels` and `transferOfSupportChange`, and `transfer_final` also discharges the
contractibility of the active comparison cone. This file adds what is still missing downstream:
* `minimal_rank_le_lim`, `transferBaseChange_lim`: `MinimalRankLe` and `transferBaseChange`
  (`CloudB3RC53/ResidualTransfer/Transfer.lean`) without the hypothesis `MinimalModelsExist S`;
* `transfer_residualDims_lim`, `transfer_final_residualDims_lim`: RC6's field `transfer` with
  `genericRank` the genuine residual quantity of the lemma, the total dimension of the cohomology of
  the original-support complex after reduction to the residue field, the minimal model being
  produced by `minimalModelsExist_proof` instead of assumed.
Kind: PROVED for every theorem, from the inputs in its type.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open CategoryTheory CategoryTheory.Limits ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.PairedFunctional

universe u

/-- **A minimal model has ranks at most those of any homotopy-equivalent finite free model**
(tex 4633–4647). PROVED, from no remaining hypothesis beyond the data.

Consumer: `ZInQ.Contrib.CloudB3RC53.ResidualTransfer.MinimalRankLe` (it takes RC6's GLUE
`MinimalModelsExist S`); discharger: `ResidualTransfer.minimalModelsExist_proof`. -/
theorem minimal_rank_le_lim {S : Type u} [CommRing S] [IsLocalRing S]
    (L K₀ : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b] [K₀.IsStrictlyGE a] [K₀.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    [∀ i, Module.Free S (K₀.X i)] [∀ i, Module.Finite S (K₀.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (e : HomotopyEquiv L K₀) (i : ℤ) :
    Module.finrank S (L.X i) ≤ Module.finrank S (K₀.X i) :=
  minimalRankLe_proof S (minimalModelsExist_proof S) L K₀ a b hLmin e i

/-- **RC6's field `transfer` with `rankTot` the rank before inverting `t`** (tex 4598–4600,
4633–4647). PROVED, from: `K₀` the scalar extension along `f : B →+* S` of a finite free model
`K₀ᴮ` over `B` (strong rank condition), `L` a minimal bounded finite free model with `L ≃ f_* K₀ᴮ`.

Consumer: `ResidualTransfer.transferBaseChange` (hypothesis `MinimalModelsExist S` removed);
discharger: `ResidualTransfer.minimalModelsExist_proof`. -/
theorem transferBaseChange_lim {B S : Type u} [CommRing B] [CommRing S] [IsLocalRing S]
    [StrongRankCondition B] (f : B →+* S)
    (L : CochainComplex (ModuleCat.{u} S) ℤ) (K₀B : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ)
    [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free S (L.X i)] [∀ i, Module.Finite S (L.X i)]
    [∀ i, Module.Free B (K₀B.X i)] [∀ i, Module.Finite B (K₀B.X i)]
    [(extCx f K₀B).IsStrictlyGE a] [(extCx f K₀B).IsStrictlyLE b]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S (L.X j)))
    (e : HomotopyEquiv L (extCx f K₀B)) (s : Finset ℤ) (genericRank rankTot : ℕ)
    (hgen : genericRank = ∑ n ∈ s, Module.finrank S (L.X n))
    (htot : rankTot = ∑ n ∈ s, Module.finrank B (K₀B.X n)) :
    genericRank ≤ rankTot :=
  transferBaseChange f (minimalModelsExist_proof S) L K₀B a b hLmin e s genericRank rankTot hgen
    htot

/-- The cohomology of `C` after extension of scalars to the residue field `k` of `S`, in degree
`n` (the "residual cohomology" of tex 4637–4647). -/
noncomputable abbrev residualCohomology (S : Type u) [CommRing S] [IsLocalRing S]
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    ModuleCat.{u} (IsLocalRing.ResidueField S) :=
  ((((ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue S)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C).homology n)

/-- **RC6's field `transfer` with the generic rank the genuine residual quantity** (tex 4598–4647:
"its ranks are the dimensions of the cohomology after augmentation", 4637–4640). PROVED, from the
inputs of the tree's `transferOfSupportChange_final` (the GLUE input `SupportChangeInput`, Nekovář
7.8.8(ii), tex 4612–4618; the contractible active comparison cone `hact`, tex 4619–4631; bounded
free Selmer models) except the minimal model, which is now produced by `minimalModelsExist_proof`:
for the original-support complex `C` (bounded in `[a, b]`, finite free),

  `∑_{n ∈ s} dim_k Hⁿ(k ⊗_S C) ≤ ∑_{n ∈ s} rank_S (selCx T.D)ⁿ`.

Consumers: RC6's field `ResidualRankCounts.transfer` (with `genericRank` the left side) and the
hypothesis `L`/`hLmin`/`eL` of `ResidualTransfer.transferOfSupportChange_final`; dischargers:
`minimalModelsExist_proof`, `transferOfSupportChange_final`. -/
theorem transfer_residualDims_lim {S : Type u} [CommRing S] [IsLocalRing S]
    (T : SupportChangeData S) (H : SupportChangeUnramified T)
    (hSC : SupportChangeInput T H) (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx T.D).toCC.X n)] [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)]
    [∀ n, Module.Finite S ((selCx T.D).toCC.X n)]
    (C : CochainComplex (ModuleCat.{u} S) ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i, Module.Free S (C.X i)] [∀ i, Module.Finite S (C.X i)]
    (jact : C ⟶ (selCx T.Dp).toCC)
    (hact : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone jact)) 0)) (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (IsLocalRing.ResidueField S) (residualCohomology S C n) ≤
      ∑ n ∈ s, Module.finrank S ((selCx T.D).X n) := by
  have hbdd : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (C.X i) := by
    refine ⟨a, b, fun i hi => ?_⟩
    rcases hi with hi | hi
    · exact ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyGE a i hi)
    · exact ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyLE b i hi)
  obtain ⟨L, ⟨e⟩, hfree, hmin, hle, hdim⟩ :=
    minimalModelsExist_proof S C (fun i => ⟨inferInstance, inferInstance⟩) hbdd
  have : ∀ i, Module.Free S (L.X i) := fun i => (hfree i).1
  have : ∀ i, Module.Finite S (L.X i) := fun i => (hfree i).2
  have hzero : ∀ i, Subsingleton (C.X i) → IsZero (L.X i) := by
    intro i hi
    have h0 : Module.finrank S (C.X i) = 0 := Module.finrank_zero_of_subsingleton
    have : Module.finrank S (L.X i) = 0 := Nat.eq_zero_of_le_zero (h0 ▸ hle i)
    have := subsingleton_of_finrank_eq_zero this
    exact ModuleCat.isZero_of_subsingleton _
  have : L.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hzero i (ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyGE a i hi))
  have : L.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hzero i (ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyLE b i hi))
  refine transferOfSupportChange_final T H hSC a b C jact hact L hmin e.symm s _ _ ?_ rfl
  exact Finset.sum_congr rfl fun n _ => (hdim n).symm

/-- **RC6's field `transfer`, final form with the genuine residual quantity** (tex 4598–4647).
PROVED, from the inputs of the tree's `transfer_final` except the minimal model `L`, which is
produced by `minimalModelsExist_proof`: over a local ring `S : Type`, with the support change
(`SupportChangeInput`, GLUE: Nekovář 7.8.8(ii), tex 4612–4618) and the change of local conditions
`0 → U' → T.Dp.U → W → 0` at the active places with acyclic singular quotient `W` (tex 4619–4631;
e.g. `twoTerm_acyclic` with `activeSingular_bijective`), the original-support complex is
`C(U') = selCx (restrictData T.Dp f)` and

  `∑_{n ∈ s} dim_k Hⁿ(k ⊗_S C(U')) ≤ ∑_{n ∈ s} rank_S (selCx T.D)ⁿ`.

Consumers: RC6's field `ResidualRankCounts.transfer`, `ResidualTransfer.transfer_final` (its `L`,
`hLmin`, `eL` removed); dischargers: `minimalModelsExist_proof`, `hact_of_singularQuotient`,
`transfer_residualDims_lim`. -/
theorem transfer_final_residualDims_lim {S : Type} [CommRing S] [IsLocalRing S]
    (T : SupportChangeData S) (H : SupportChangeUnramified T)
    (hSC : SupportChangeInput T H) (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx T.D).toCC.X n)] [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)]
    [∀ n, Module.Finite S ((selCx T.D).toCC.X n)]
    (U' W : GCx S) (f : GHom U' T.Dp.U) (g : GHom T.Dp.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : T.Dp.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic)
    [(selCx (restrictData T.Dp f)).toCC.IsStrictlyGE a]
    [(selCx (restrictData T.Dp f)).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx (restrictData T.Dp f)).toCC.X n)]
    [∀ n, Module.Finite S ((selCx (restrictData T.Dp f)).toCC.X n)] (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (IsLocalRing.ResidueField S)
        (residualCohomology S (selCx (restrictData T.Dp f)).toCC n) ≤
      ∑ n ∈ s, Module.finrank S ((selCx T.D).X n) :=
  transfer_residualDims_lim T H hSC a b (selCx (restrictData T.Dp f)).toCC
    (GHom.toCC (changeMap T.Dp f))
    (hact_of_singularQuotient T.Dp U' W f g hfg hinj hsurj hex hW a b) s

end ZInQ.Manuscript.RC.GlueSweep.Lim
