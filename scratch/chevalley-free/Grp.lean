import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Descent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # chevalley-free, step G: a group structure through an fpqc quotient map

If `π : U → X` is an fpqc morphism over `S` from a group scheme and the relation `π a = π b` is a congruence,
`X` carries a group structure making `π` a homomorphism. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.MilneQuasiInverse.Descent.GroupDescent.Construction GrpObj

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.ChevFree

section GrpQuot

variable {S : Scheme.{0}}

theorem tensor_left_prop {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (hf : P f.left) (hg : P g.left) :
    P (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

instance flat_tensor {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) [Flat f.left] [Flat g.left] :
    Flat (f ⊗ₘ g).left := tensor_left_prop f g @Flat inferInstance inferInstance
instance surjective_tensor {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) [Surjective f.left]
    [Surjective g.left] : Surjective (f ⊗ₘ g).left :=
  tensor_left_prop f g @Surjective inferInstance inferInstance
instance quasiCompact_tensor {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) [QuasiCompact f.left]
    [QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left :=
  tensor_left_prop f g @QuasiCompact inferInstance inferInstance

instance flat_id (A : Over S) : Flat (Over.Hom.left (𝟙 A)) := by rw [Over.id_left]; infer_instance
instance surjective_id (A : Over S) : Surjective (Over.Hom.left (𝟙 A)) := by
  rw [Over.id_left]; infer_instance
instance quasiCompact_id (A : Over S) : QuasiCompact (Over.Hom.left (𝟙 A)) := by
  rw [Over.id_left]; infer_instance

variable {U X : Over S} [GrpObj U] (π : U ⟶ X) [Flat π.left] [Surjective π.left] [QuasiCompact π.left]

/-- The relation `π a = π b` is a congruence for the group law of `U`. -/
def Cong : Prop :=
  ∀ (T : Over S) (a b c : T ⟶ U), a ≫ π = b ≫ π →
    (a * c) ≫ π = (b * c) ≫ π ∧ (c * a) ≫ π = (c * b) ≫ π ∧ a⁻¹ ≫ π = b⁻¹ ≫ π

theorem epi_of_fpqc {A B : Over S} (f : A ⟶ B) [Flat f.left] [Surjective f.left] [QuasiCompact f.left] :
    Epi f := by
  haveI := effectiveEpi_over_of_fpqc f
  infer_instance

/-- **A group structure through an fpqc quotient map.** -/
theorem exists_grpObj (hC : Cong π) : ∃ _ : GrpObj X, IsMonHom π := by
  haveI : EffectiveEpi π := effectiveEpi_over_of_fpqc π
  haveI : EffectiveEpi (π ⊗ₘ π) := effectiveEpi_over_of_fpqc (π ⊗ₘ π)
  have hmc : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ U ⊗ U), g₁ ≫ (π ⊗ₘ π) = g₂ ≫ (π ⊗ₘ π) →
      g₁ ≫ μ ≫ π = g₂ ≫ μ ≫ π := by
    intro Z g₁ g₂ hg
    have ha : (g₁ ≫ fst U U) ≫ π = (g₂ ≫ fst U U) ≫ π := by
      have := congrArg (· ≫ fst X X) hg
      simpa only [Category.assoc, tensorHom_fst] using this
    have hb : (g₁ ≫ snd U U) ≫ π = (g₂ ≫ snd U U) ≫ π := by
      have := congrArg (· ≫ snd X X) hg
      simpa only [Category.assoc, tensorHom_snd] using this
    have e₁ : g₁ ≫ μ = (g₁ ≫ fst U U) * (g₁ ≫ snd U U) := by
      rw [Hom.mul_def]; congr 1; ext <;> simp
    have e₂ : g₂ ≫ μ = (g₂ ≫ fst U U) * (g₂ ≫ snd U U) := by
      rw [Hom.mul_def]; congr 1; ext <;> simp
    rw [← Category.assoc, ← Category.assoc, e₁, e₂, (hC _ _ _ _ ha).1, (hC _ _ _ _ hb).2.1]
  have hic : ∀ {Z : Over S} (a b : Z ⟶ U), a ≫ π = b ≫ π → a ≫ ι ≫ π = b ≫ ι ≫ π := by
    intro Z a b hab
    have := (hC _ a b a hab).2.2
    rwa [Hom.inv_def, Hom.inv_def, Category.assoc, Category.assoc] at this
  let m : X ⊗ X ⟶ X := EffectiveEpi.desc (π ⊗ₘ π) (μ ≫ π) (fun g₁ g₂ hg => hmc g₁ g₂ hg)
  let i : X ⟶ X := EffectiveEpi.desc π (ι ≫ π) (fun a b hab => hic a b hab)
  have hm : (π ⊗ₘ π) ≫ m = μ ≫ π := EffectiveEpi.fac _ _ _
  have hi : π ≫ i = ι ≫ π := EffectiveEpi.fac _ _ _
  haveI : Epi π := inferInstance
  haveI : Epi (π ⊗ₘ π) := inferInstance
  haveI : Epi ((π ⊗ₘ π) ⊗ₘ π) := epi_of_fpqc _
  haveI : Epi (𝟙 (𝟙_ (Over S)) ⊗ₘ π) := epi_of_fpqc _
  haveI : Epi (π ⊗ₘ 𝟙 (𝟙_ (Over S))) := epi_of_fpqc _
  letI G : GrpObj X :=
    { one := η ≫ π
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_epi (𝟙 (𝟙_ (Over S)) ⊗ₘ π), ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id,
          show (η ≫ π) ⊗ₘ π = (η ⊗ₘ 𝟙 U) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, ← Category.assoc, tensorHom_id, MonObj.one_mul, id_tensorHom,
          leftUnitor_naturality]
      mul_one := by
        rw [← cancel_epi (π ⊗ₘ 𝟙 (𝟙_ (Over S))), ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id,
          show π ⊗ₘ (η ≫ π) = (𝟙 U ⊗ₘ η) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, ← Category.assoc, id_tensorHom, MonObj.mul_one, tensorHom_id,
          rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_epi ((π ⊗ₘ π) ⊗ₘ π)]
        conv_lhs => rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id, hm,
          show (μ ≫ π) ⊗ₘ π = (μ ⊗ₘ 𝟙 U) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, ← Category.assoc, tensorHom_id, MonObj.mul_assoc]
        conv_rhs => rw [associator_naturality_assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, hm,
          show π ⊗ₘ (μ ≫ π) = (𝟙 U ⊗ₘ μ) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, id_tensorHom]
        simp only [Category.assoc]
      left_inv := by
        rw [← cancel_epi π]
        rw [← Category.assoc, show π ≫ lift i (𝟙 X) = lift ι (𝟙 U) ≫ (π ⊗ₘ π) by ext <;> simp [hi]]
        rw [Category.assoc, hm, ← Category.assoc, GrpObj.left_inv]
        simp
      right_inv := by
        rw [← cancel_epi π]
        rw [← Category.assoc, show π ≫ lift (𝟙 X) i = lift (𝟙 U) ι ≫ (π ⊗ₘ π) by ext <;> simp [hi]]
        rw [Category.assoc, hm, ← Category.assoc, GrpObj.right_inv]
        simp }
  exact ⟨G, ⟨rfl, hm.symm⟩⟩

end GrpQuot

end ZInQ.ChevFree

#print axioms ZInQ.ChevFree.exists_grpObj
