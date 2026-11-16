import ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted

set_option linter.style.longLine false

namespace HDec.QMSplit.Moduli.ElkiesPrint

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

/-! ## 1. The leaf and the discharge -/

/-- The witness of the moduli clause lists for `X₀(6,1)` on abelian schemes. -/
def X6WitnessAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY

/-- LEAF (docstring in the contribution file). -/
def ElkiesX6StarEvery : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        ElkiesCoord.fixedByW Ψ =
          (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
      X6Glue.ElkiesCharts X t

theorem x6WitnessAb_of_gonzalezRotgerX6Ab (h : GonzalezRotgerX6Ab) : X6WitnessAb := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

theorem elkiesX6StarFunctionField_of_every (h : ElkiesX6StarEvery) (hW : X6WitnessAb) :
    ElkiesCoord.ElkiesX6StarFunctionField := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := hW
  obtain ⟨t, hff, hcm, hc⟩ := h Y Φ X Ψ fY h1 h6
  exact ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hff, hcm, hc⟩

theorem elkiesX6StarFunctionField_of_every_gr (h : ElkiesX6StarEvery) (hX : GonzalezRotgerX6Ab) :
    ElkiesCoord.ElkiesX6StarFunctionField :=
  elkiesX6StarFunctionField_of_every h (x6WitnessAb_of_gonzalezRotgerX6Ab hX)

/-! ## 2. Comorphisms on function fields -/

section FFMap

theorem gen_spec {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (h : X ⟶ Z) [IsOpenImmersion h] :
    h (genericPoint X) ⤳ genericPoint Z := by
  rw [genericPoint_eq_of_isOpenImmersion h]

/-- The comorphism `h^* : ℚ(Z) → ℚ(X)` of an open immersion of integral schemes. -/
noncomputable def ffMap {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (h : X ⟶ Z) [IsOpenImmersion h] :
    Z.functionField →+* X.functionField :=
  (Z.presheaf.stalkSpecializes (gen_spec h) ≫ h.stalkMap (genericPoint X)).hom

theorem ffMap_germ {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (h : X ⟶ Z) [IsOpenImmersion h]
    (A : Z.Opens) (hA : genericPoint Z ∈ A) (hA' : genericPoint X ∈ h ⁻¹ᵁ A) (s : Γ(Z, A)) :
    ffMap h (Z.presheaf.germ A _ hA s) = X.presheaf.germ (h ⁻¹ᵁ A) _ hA' (h.app A s) := by
  unfold ffMap
  rw [CommRingCat.comp_apply, ← ConcreteCategory.comp_apply (Z.presheaf.germ A _ hA),
    TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap_apply]

theorem ffMap_ext {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] {φ ψ : Z.functionField →+* X.functionField}
    (H : ∀ (A : Z.Opens) (hA : genericPoint Z ∈ A) (s : Γ(Z, A)),
      φ (Z.presheaf.germ A _ hA s) = ψ (Z.presheaf.germ A _ hA s)) : φ = ψ := by
  ext a
  obtain ⟨A, hA, s, rfl⟩ := TopCat.Presheaf.germ_exist Z.presheaf a
  exact H A hA s

theorem ffMap_comp {X Z W : Scheme.{0}} [IsIntegral X] [IsIntegral Z] [IsIntegral W]
    (h : X ⟶ Z) (g : Z ⟶ W) [IsOpenImmersion h] [IsOpenImmersion g] :
    ffMap (h ≫ g) = (ffMap h).comp (ffMap g) := by
  apply ffMap_ext
  intro A hA s
  have hA1 : genericPoint Z ∈ g ⁻¹ᵁ A := by
    show g (genericPoint Z) ∈ A
    rw [genericPoint_eq_of_isOpenImmersion g]; exact hA
  have hA2 : genericPoint X ∈ h ⁻¹ᵁ (g ⁻¹ᵁ A) := by
    show h (genericPoint X) ∈ g ⁻¹ᵁ A
    rw [genericPoint_eq_of_isOpenImmersion h]; exact hA1
  rw [RingHom.comp_apply, ffMap_germ g A hA hA1, ffMap_germ h _ hA1 hA2, ffMap_germ (h ≫ g) A hA hA2]
  rw [Scheme.Hom.comp_app]
  rfl

theorem ffMap_id {X : Scheme.{0}} [IsIntegral X] : ffMap (𝟙 X) = RingHom.id _ := by
  apply ffMap_ext
  intro A hA s
  rw [ffMap_germ (𝟙 X) A hA hA]
  rfl

theorem ffMap_congr {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] {h h' : X ⟶ Z} [IsOpenImmersion h]
    [IsOpenImmersion h'] (e : h = h') : ffMap h = ffMap h' := by
  subst e; rfl

end FFMap

end HDec.QMSplit.Moduli.ElkiesPrint
