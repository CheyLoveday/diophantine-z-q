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

section Stalk

variable {X : Scheme} [IsIntegral X]

/-- The action on the function field of an endomorphism fixing the generic point. -/
def σ (f : X ⟶ X) (hf : f (genericPoint X) = genericPoint X) :
    X.presheaf.stalk (genericPoint X) ⟶ X.presheaf.stalk (genericPoint X) :=
  X.presheaf.stalkSpecializes (show f (genericPoint X) ⤳ genericPoint X by rw [hf]) ≫
    f.stalkMap (genericPoint X)

theorem Spec_σ (f : X ⟶ X) (hf : f (genericPoint X) = genericPoint X) :
    Spec.map (σ f hf) ≫ X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [σ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

omit [IsIntegral X] in
theorem eq_of_Spec_comp {R : CommRingCat} (x : X) (a b : X.presheaf.stalk x ⟶ R)
    (h : Spec.map a ≫ X.fromSpecStalk x = Spec.map b ≫ X.fromSpecStalk x) : a = b :=
  Spec.map_injective ((cancel_mono _).mp h)

theorem σ_comp (f g : X ⟶ X) (hf : f (genericPoint X) = genericPoint X)
    (hg : g (genericPoint X) = genericPoint X) (hfg : (f ≫ g) (genericPoint X) = genericPoint X) :
    σ (f ≫ g) hfg = σ g hg ≫ σ f hf := by
  apply eq_of_Spec_comp
  rw [Spec_σ, Spec.map_comp, Category.assoc, Spec_σ]
  conv_rhs => rw [← Category.assoc, Spec_σ]
  rw [Category.assoc]

theorem σ_id (h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X) : σ (𝟙 X) h = 𝟙 _ := by
  apply eq_of_Spec_comp
  rw [Spec_σ, Spec.map_id, Category.id_comp, Category.comp_id]

instance isDominant_fromSpecStalk_genericPoint :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  refine Dense.mono ?_ (dense_iff_closure_eq.mpr (genericPoint_spec X))
  rintro _ rfl
  rw [Scheme.range_fromSpecStalk]
  exact specializes_rfl

/-- Faithfulness: an endomorphism (over a separated base) acting trivially on the function field is `𝟙`. -/
theorem eq_id_of_σ_eq {S : Scheme} (s : X ⟶ S) [IsSeparated s] (f : X ⟶ X) (hfs : f ≫ s = s)
    (hf : f (genericPoint X) = genericPoint X) (h : σ f hf = 𝟙 _) : f = 𝟙 X := by
  refine ext_of_isDominant_of_isSeparated s (by rw [hfs, Category.id_comp])
    (X.fromSpecStalk (genericPoint X)) ?_
  rw [← Spec_σ f hf, h, Spec.map_id, Category.id_comp, Category.comp_id]

end Stalk

section Kernel

open PkgI3.AbVar

theorem σ_congr {X : Scheme} [IsIntegral X] (f g : X ⟶ X) (h : f = g)
    (hf : f (genericPoint X) = genericPoint X) (hg : g (genericPoint X) = genericPoint X) :
    σ f hf = σ g hg := by
  subst h; rfl

variable {A}

theorem τ_left_genericPoint (P : A.Pt Kb) :
    (τ A P).left (genericPoint A.X.left) = genericPoint A.X.left := by
  apply ZInQ.Contrib.OneProof.DegDet.map_genericPoint
  intro y
  refine ⟨(τ A P⁻¹).left y, ?_⟩
  have h : (τ A P⁻¹ ≫ τ A P) = 𝟙 _ := by rw [← τ_mul, _root_.mul_inv_cancel, τ_one]
  have h2 := congrArg (fun t => t.left) h
  simp only [Over.comp_left, Over.id_left] at h2
  rw [← Scheme.Hom.comp_apply, h2]
  rfl

/-- The action of a `k̄`-point on the function field. -/
def σP (P : A.Pt Kb) :
    A.X.left.presheaf.stalk (genericPoint A.X.left) ⟶ A.X.left.presheaf.stalk (genericPoint A.X.left) :=
  σ (τ A P).left (τ_left_genericPoint P)

theorem σP_mul (P Q : A.Pt Kb) : σP (P * Q) = σP P ≫ σP Q := by
  have h := σ_comp (τ A Q).left (τ A P).left (τ_left_genericPoint Q) (τ_left_genericPoint P)
    (by rw [Scheme.Hom.comp_apply, τ_left_genericPoint, τ_left_genericPoint])
  rw [σP, σ_congr (τ A (P * Q)).left ((τ A Q).left ≫ (τ A P).left)
    (by rw [τ_mul]; rfl) _ (by rw [Scheme.Hom.comp_apply, τ_left_genericPoint, τ_left_genericPoint]), h]
  rfl

theorem σP_one : σP (1 : A.Pt Kb) = 𝟙 _ := by
  have h1 : (𝟙 A.X.left : A.X.left ⟶ A.X.left) (genericPoint A.X.left) = genericPoint A.X.left := rfl
  rw [σP, σ_congr (τ A 1).left (𝟙 _) (by rw [τ_one]; rfl) _ h1, σ_id h1]

theorem stalkMap_comp_σP (ψ : End A) (P : A.Pt Kb) (hP : P ≫ ψ.hom = 1) :
    ψ.hom.left.stalkMap (genericPoint A.X.left) ≫ σP P = ψ.hom.left.stalkMap (genericPoint A.X.left) := by
  apply eq_of_Spec_comp
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, σP,
    Spec_σ, Category.assoc]
  congr 1
  have := congrArg (fun t => t.left) (τ_comp_hom A P hP)
  simpa only [Over.comp_left] using this

theorem eq_one_of_σP_eq (P : A.Pt Kb) (h : σP P = 𝟙 _) : P = 1 := by
  apply eq_one_of_τ_eq_id A P
  apply Over.OverMorphism.ext
  exact eq_id_of_σ_eq A.X.hom (τ A P).left (Over.w (τ A P)) _ h

end Kernel

end DegDet.KerDvd
