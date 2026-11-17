import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30

set_option linter.all false

noncomputable section

namespace Y3P1j

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open Y3Fix SGRSplit HDec.VertWitness HDec.ModelGlue Y3Audit Y3RouteA
open scoped CategoryTheory.Obj

section T
variable {S : Scheme.{0}}
theorem zm (u : Oˣ) : (0 : O) * (u : O) = 0 := MulZeroClass.zero_mul _
def famRightMul (u : Oˣ) (𝒜 : QMFamily S) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota a
  iota_over a := 𝒜.iota_over a
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec _

def famA (α : O ≃+* O) (u : O) (𝒜 : QMFamily S) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over _
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec _

def famB (α : O ≃+* O) (𝒜 : QMFamily S) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota a
  iota_over a := 𝒜.iota_over _
  eta a := 𝒜.eta (α a)
  eta_sec a := 𝒜.eta_sec _

def r_A (α : O ≃+* O) (u : O) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA α u 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := sorry
  iota_hom := sorry
  iota_one := sorry
  iota_mul := sorry
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def r_B (α : O ≃+* O) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famB α 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := sorry
  iota_hom := sorry
  iota_one := sorry
  iota_mul := sorry
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def rC_geomConn (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA (RingEquiv.refl O) (u : O) 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := sorry
  iota_hom := sorry
  iota_one := sorry
  iota_mul := sorry
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def rC_one_eq (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA (RingEquiv.refl O) (u : O) 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := 𝒜.one_eq.trans (congrArg 𝒜.eta (zm u).symm)
  iota_hom := sorry
  iota_one := sorry
  iota_mul := sorry
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def rC_iota_hom (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA (RingEquiv.refl O) (u : O) 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := sorry
  iota_hom := fun a => 𝒜.iota_hom a
  iota_one := sorry
  iota_mul := sorry
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def rC_iota_one (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA (RingEquiv.refl O) (u : O) 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := sorry
  iota_hom := sorry
  iota_one := 𝒜.iota_one
  iota_mul := sorry
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def rC_iota_mul (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA (RingEquiv.refl O) (u : O) 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := sorry
  iota_hom := sorry
  iota_one := sorry
  iota_mul := fun a b => 𝒜.iota_mul a b
  iota_add := sorry
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

def rC_iota_add (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S where
  toQMFamily := famA (RingEquiv.refl O) (u : O) 𝒜.toQMFamily
  grp := 𝒜.grp
  geomConn := sorry
  one_eq := sorry
  iota_hom := sorry
  iota_one := sorry
  iota_mul := sorry
  iota_add := fun a b => 𝒜.iota_add a b
  eta_add := sorry
  eta_linear := sorry
  eta_three := sorry

end T
end Y3P1j
