import ZInQKernel.Contrib.OneProof.SSFaltings
import ZInQKernel.Contrib.OneProof.PrintedStableHeight
import ZInQKernel.Contrib.OneProof.GaRigiditySGA7
import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3
import ZInQKernel.Contrib.OneProof.BLRLocalizes
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.SZRaynaud
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron

/-! Faltings' height invariance for a semiabelian scheme and the separate comparison
with Néron models. -/

set_option linter.style.haveILetI false

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry NumberField
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.H5Neron ZInQ.SSFaltings
open ZInQ.HeightFix DictModels.RaynaudOr

/-- The special fibres of Faltings' semiabelian model (Invent. Math. 73 (1983), p. 350)
are connected extensions of abelian varieties by tori over the residue fields.
Smoothness and an abelian generic fibre are already part of `GroupModel`.
For a connected group over a field the open connected subgroup in
`HasSemiAbelianIdCompTorus) is the whole group. -/
def IsSemiabelianModel {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
    {A : PkgI3.AbVar K} (G : GroupModel A L) : Prop :=
  ∀ (p : Ideal (𝓞 L)) [p.IsMaximal],
    ConnectedSpace (resFibre G p).left ∧ HasSemiAbelianIdCompTorus (resFibre G p)

/-- Faltings 1983, §3 p. 354 (asserted there without proof), with p. 351 Bem. b):
the normalized height of a semiabelian model with proper generic fibre agrees
with the height of its base change. Both pages read by the reading desk. -/
def FaltingsHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type)
    [Field L] [NumberField L] [Algebra K L] (G : GroupModel A L), IsSemiabelianModel G →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
      [IsScalarTower K L L'] (G' : GroupModel A L'), IsBaseChangeOf G' G → G'.height = G.height

/-- The existing height base change theorem applies even without the semiabelian hypothesis. -/
theorem faltingsHeightBaseChange : FaltingsHeightBaseChange := by
  intro K _ _ A L _ _ _ G _ L' _ _ _ _ _ G' hG'
  exact Contrib.HeightBC.modelHeightBaseChange K A L L' G G' hG'

/-- **Consequence (GLUE).** The Néron comparison needed for height: two semistable
Néron models over an extension admit a common open subgroup model after base change.
This is SS2 restricted to cases where both models are semistable. It follows from
SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (page read; uncited in the manuscript), or
from Faltings 1983, Lemma 1, p. 350 (page read), with the semiabelian dictionary.
The common open subgroup need only contain an open neighbourhood of the identity;
this statement does not require a global identity-component construction. -/
def SemistableNeronIdentification : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type)
    [Field L] [NumberField L] [Algebra K L] (N : GroupModel A L), N.IsNeronModel → IsSemistable N →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
      [IsScalarTower K L L'] (N' : GroupModel A L'), N'.IsNeronModel → IsSemistable N' →
      ∃ U V : GroupModel A L', IsBaseChangeOf V N ∧ IsOpenSubgroupModel U N' ∧ IsOpenSubgroupModel U V

/-- SS2 supplies the comparison without needing target semistability. -/
theorem semistableNeronIdentification_of_ss2 (h : SemistableNeronBaseChange) :
    SemistableNeronIdentification := by
  intro K _ _ A L _ _ _ N hN hs L' _ _ _ _ _ N' hN' _
  exact h K A L N hN hs L' N' hN'

/-- Corollary 3.3 supplies SS2 by the existing localization argument. -/
theorem semistableNeronIdentification_of_cor33 (h : GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34) :
    SemistableNeronIdentification :=
  semistableNeronIdentification_of_ss2
    (SGA3Nbhd.semistableNeronBaseChange_noSGA3 GapBLR.blr_1_2_4
      (SGA3Nbhd.NF.sga7_IX_3_3_of_SH'
        (SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre'
          (SGA33Steps.shpre_of_cor33 (GaRigidity.SGA7.sga7_IX_Cor3_3_of_def34 h))
          geomConnOfRationalPoint_proof)
        NeronSH.neronBaseChangeStrictHenselization_proof geomConnOfRationalPoint_proof)
      geomConnOfRationalPoint_proof)

private theorem height_eq_of_two_semistable (h : SemistableNeronIdentification)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L L' : Type)
    [Field L] [NumberField L] [Algebra K L] [Field L'] [NumberField L'] [Algebra K L']
    [Algebra L L'] [IsScalarTower K L L'] (N : GroupModel A L) (N' : GroupModel A L')
    (hN : N.IsNeronModel) (hs : IsSemistable N) (hN' : N'.IsNeronModel)
    (hs' : IsSemistable N') : N'.height = N.height := by
  obtain ⟨U, V, hV, hUN', hUV⟩ := h K A L N hN hs L' N' hN' hs'
  calc
    N'.height = U.height := (Contrib.HeightBC.openSubgroupHeight K A L' U N' hUN').symm
    _ = V.height := Contrib.HeightBC.openSubgroupHeight K A L' U V hUV
    _ = N.height := Contrib.HeightBC.modelHeightBaseChange K A L L' N V hV

/-- Compare the heights over a common larger semistable field, using minimality for
the intermediate Néron model. No persistence of semistability is required. -/
theorem faltingsSemistableHeightBC_of_identification (h : SemistableNeronIdentification)
    (hSS : SemistableReductionThmIF) (hN1 : NeronModelExists) : FaltingsSemistableHeightBC := by
  intro K _ _ A L _ _ _ N hN hs L' _ _ _ _ _ N' hN'
  obtain ⟨K₀, hfin, hK₀⟩ := hSS K A
  haveI : FiniteDimensional K K₀ := hfin
  haveI : Module.Finite K L' := Module.Finite.of_restrictScalars_finite ℚ K L'
  let e : L' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let E : IntermediateField K (AlgebraicClosure K) := e.fieldRange ⊔ K₀
  haveI : FiniteDimensional K e.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField e).toLinearEquiv
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField E := NumberField.of_module_finite K E
  let f : L' →ₐ[K] E := (IntermediateField.inclusion le_sup_left).comp
    (AlgEquiv.ofInjectiveField e).toAlgHom
  letI : Algebra L' E := f.toRingHom.toAlgebra
  letI : IsScalarTower K L' E := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : Algebra L E := ((algebraMap L' E).comp (algebraMap L L')).toAlgebra
  letI : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K L E := IsScalarTower.to₁₂₄ K L L' E
  obtain ⟨N'', hN''⟩ := hN1 K A E
  have hs'' : IsSemistable N'' := hK₀ E le_sup_right N'' hN''
  have hei : N''.height = N.height := height_eq_of_two_semistable h K A L E N N'' hN hs hN'' hs''
  obtain ⟨V, hV⟩ := groupModelBaseChangeExists K A L L' N
  obtain ⟨V', hV'⟩ := groupModelBaseChangeExists K A L' E N'
  apply le_antisymm
  · calc
      N'.height ≤ V.height := Contrib.HeightBC.neronModelMinimal K A L' N' V hN'
      _ = N.height := Contrib.HeightBC.modelHeightBaseChange K A L L' N V hV
  · calc
      N.height = N''.height := hei.symm
      _ ≤ V'.height := Contrib.HeightBC.neronModelMinimal K A E N'' V' hN''
      _ = N'.height := Contrib.HeightBC.modelHeightBaseChange K A L' E N' V' hV'

/-- The old field from the separate Néron comparison and the two existing fields
for Raynaud's criterion and existence of Néron models. -/
theorem faltingsSemistableHeightBC_of_leaves (h : SemistableNeronIdentification)
    (hR : SZRaynaud.SilverbergZarhinThm35) (hD : Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    FaltingsSemistableHeightBC :=
  let hE := Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind hD
  faltingsSemistableHeightBC_of_identification h
    (semistableReductionThmIF_of_raynaud (SZRaynaud.raynaudSemistable_of_sz35 hR)
      Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
      Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
      (GapNeron.neronSchemeModelExistsNF hE)
      (ReductGlue.semistableLocalGlobal_leaf GapBLR.neronLocalizesDVR_proved))
    (Contrib.NeronC.neronModelExists_of_extension hE)

end ZInQ.FaltingsRestate
