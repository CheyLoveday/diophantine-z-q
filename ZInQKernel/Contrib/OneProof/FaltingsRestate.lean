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

end ZInQ.FaltingsRestate
