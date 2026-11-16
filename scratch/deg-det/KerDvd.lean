import ZInQKernel.Contrib.OneProof.DegEqDetTate

/-!
# deg-det: `#ker ψ ∣ deg ψ` (translations by the kernel act on the function field; Artin)
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace DegDet.KerDvd

open ZInQ.Contrib.OneProof.CharPolyEll

attribute [local instance] isIntegral_left

variable {k : Type} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k)

local notation "Kb" => AlgebraicClosure k

/-- `k ≃ k̄` (`k` algebraically closed). -/
def eBar : k ≃+* AlgebraicClosure k :=
  RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem eBar_symm_algebraMap (x : k) : (eBar (k := k)).symm (algebraMap k Kb x) = x :=
  (eBar (k := k)).symm_apply_apply x

theorem algebraMap_eBar_symm (y : Kb) : algebraMap k Kb ((eBar (k := k)).symm y) = y :=
  (eBar (k := k)).apply_symm_apply y

/-- The structure morphism `A → Spec k → Spec k̄` (over `k`). -/
def toPt : A.X ⟶ PkgI3.AbVar.ptObj (K := k) Kb :=
  Over.homMk (A.X.hom ≫ Spec.map (CommRingCat.ofHom (eBar (k := k)).symm.toRingHom)) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have : ((eBar (k := k)).symm.toRingHom.comp (algebraMap k Kb)) = RingHom.id k := by
      ext x; exact eBar_symm_algebraMap x
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

theorem pt_comp_toPt (Q : A.Pt Kb) : Q ≫ toPt A = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [toPt, Over.comp_left, Over.homMk_left, Over.id_left]
  erw [← Category.assoc, Over.w Q]
  simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (algebraMap k Kb).comp (eBar (k := k)).symm.toRingHom = RingHom.id Kb := by
    ext y; exact algebraMap_eBar_symm y
  rw [this, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- Translation by a `k̄`-point. -/
def τ (P : A.Pt Kb) : A.X ⟶ A.X := (toPt A ≫ P) * 𝟙 A.X

theorem pt_comp_τ (Q P : A.Pt Kb) : Q ≫ τ A P = P * Q := by
  rw [τ, MonObj.comp_mul, ← Category.assoc, pt_comp_toPt, Category.id_comp, Category.comp_id]

theorem τ_comp_toPt (P : A.Pt Kb) : τ A P ≫ toPt A = toPt A := by
  apply Over.OverMorphism.ext
  simp only [toPt, Over.comp_left, Over.homMk_left]
  erw [← Category.assoc, Over.w (τ A P)]

theorem τ_mul (P Q : A.Pt Kb) : τ A (P * Q) = τ A Q ≫ τ A P := by
  have h1 : τ A Q ≫ τ A P = (toPt A ≫ P) * τ A Q := by
    conv_lhs => rw [show τ A P = (toPt A ≫ P) * 𝟙 A.X from rfl]
    rw [MonObj.comp_mul, ← Category.assoc, τ_comp_toPt, Category.comp_id]
  rw [h1]
  change (toPt A ≫ (P * Q)) * 𝟙 A.X = (toPt A ≫ P) * ((toPt A ≫ Q) * 𝟙 A.X)
  rw [MonObj.comp_mul, _root_.mul_assoc]

theorem τ_one : τ A 1 = 𝟙 _ := by
  rw [τ, MonObj.comp_one, _root_.one_mul]

theorem τ_comp_hom {ψ : PkgI3.AbVar.End A} (P : A.Pt Kb) (hP : P ≫ ψ.hom = 1) :
    τ A P ≫ ψ.hom = ψ.hom := by
  rw [τ, MonObj.mul_comp, Category.assoc, hP, MonObj.comp_one, Category.id_comp, _root_.one_mul]

theorem eq_one_of_τ_eq_id (P : A.Pt Kb) (h : τ A P = 𝟙 _) : P = 1 := by
  have := pt_comp_τ A 1 P
  rw [h, Category.comp_id, _root_.mul_one] at this
  exact this.symm

end DegDet.KerDvd
