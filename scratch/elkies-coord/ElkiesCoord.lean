import ZInQKernel.Contrib.OneProof.ElkiesX6Star

namespace HDec.QMSplit.Moduli.ElkiesCoord

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

section FF

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem gen_specializes (g : Z ≅ Z) : g.hom (genericPoint Z) ⤳ genericPoint Z := by
  rw [genericPoint_eq_of_isOpenImmersion g.hom]

/-- The comorphism `g^* : ℚ(Z) → ℚ(Z)`, `φ ↦ φ ∘ g`, of an automorphism `g` of an integral scheme on
its function field (the stalk at the generic point; `g` fixes the generic point). -/
noncomputable def ffPullback (g : Z ≅ Z) : Z.functionField →+* Z.functionField :=
  (Z.presheaf.stalkSpecializes (gen_specializes g) ≫ g.hom.stalkMap (genericPoint Z)).hom

theorem ffPullback_germ (g : Z ≅ Z) (A : Z.Opens) (hA : genericPoint Z ∈ A)
    (hA' : genericPoint Z ∈ g.hom ⁻¹ᵁ A) (s : Γ(Z, A)) :
    ffPullback g (Z.presheaf.germ A _ hA s) = Z.presheaf.germ (g.hom ⁻¹ᵁ A) _ hA' (g.hom.app A s) := by
  unfold ffPullback
  rw [CommRingCat.comp_apply, ← ConcreteCategory.comp_apply (Z.presheaf.germ A _ hA),
    TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap_apply]

/-- Sections over two opens with the same germ at the generic point agree on the intersection. -/
theorem res_eq_of_germ_eq {A B : Z.Opens} (hA : genericPoint Z ∈ A) (hB : genericPoint Z ∈ B)
    (a : Γ(Z, A)) (b : Γ(Z, B)) (h : Z.presheaf.germ A _ hA a = Z.presheaf.germ B _ hB b) :
    Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a =
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b := by
  have hAB : genericPoint Z ∈ A ⊓ B := ⟨hA, hB⟩
  apply germ_injective_of_isIntegral Z (genericPoint Z) hAB
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact h

end FF

/-- `ℚ(X₆)^W`: the rational functions on `X₆` fixed by every `g ∈ W` (`g^*φ = φ`). -/
def fixedByW {X : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left]
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Set X.left.functionField :=
  {φ | ∀ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, ffPullback (Z := X.left) ((Over.forget _).mapIso g) φ = φ}

/-- LEAF draft. -/
def ElkiesX6StarFF : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∃ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
      fixedByW Ψ = (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

end HDec.QMSplit.Moduli.ElkiesCoord
