import ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! The cotangent classes pulled back from the two factors span the
cotangent space at a rational point of a product. Test the quotient by
their span using its associated square-zero infinitesimal point. -/

namespace ZInQ.Manuscript.RC.HCMV21.PointedScheme

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped CategoryTheory.MonObj

noncomputable section

variable {k : Type} [Field k] {P Q : PointedScheme k}
variable {M : Type} [AddCommGroup M] [Module k M]

local instance : Module kᵐᵒᵖ M :=
  Module.compHom M
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_zero' := rfl
      map_mul' := fun x y => mul_comm y.unop x.unop
      map_add' := fun _ _ => rfl }

local instance : IsCentralScalar k M := ⟨fun _ _ => rfl⟩

local instance evaluation_isLocalHom (P : PointedScheme k) : IsLocalHom P.evaluation.hom := by
  change IsLocalHom (Scheme.stalkClosedPointTo P.sectionMap.left).hom
  infer_instance

local instance : IsLocalRing (TrivSqZeroExt k M) := by
  apply IsLocalRing.of_nonunits_add
  intro x y hx hy
  rw [mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at hx hy ⊢
  simp [not_not.mp hx, not_not.mp hy]

private theorem evaluation_eq_zero_iff (P : PointedScheme k) (x : P.localRing) :
    P.evaluation x = 0 ↔ x ∈ maximalIdeal P.localRing := by
  change P.evaluation x = 0 ↔ ¬ IsUnit x
  rw [← isUnit_map_iff P.evaluation.hom, isUnit_iff_ne_zero, not_ne_iff]

/-- The class of a local function after subtracting its value at the point. -/
private def deviation (P : PointedScheme k) (x : P.localRing) : maximalIdeal P.localRing :=
  ⟨x - algebraMap k P.localRing (P.evaluation x), (evaluation_eq_zero_iff P _).mp (by
    rw [map_sub, evaluation_constant, sub_self])⟩

private def jetAlgebra (P : PointedScheme k) (v : P.cotangent →ₗ[k] M) :
    P.localRing →ₐ[k] TrivSqZeroExt k M where
  toFun x := (P.evaluation x, v ((maximalIdeal P.localRing).toCotangent (deviation P x)))
  map_zero' := by
    have h : deviation P 0 = 0 := Subtype.ext (by simp [deviation])
    apply TrivSqZeroExt.ext <;> simp [h]
  map_one' := by
    have h : deviation P 1 = 0 := Subtype.ext (by simp [deviation])
    apply TrivSqZeroExt.ext <;> simp [h]
  map_add' x y := by
    have h : deviation P (x + y) = deviation P x + deviation P y := by
      apply Subtype.ext
      change x + y - _ = (x - _) + (y - _)
      simp only [map_add]
      abel
    apply TrivSqZeroExt.ext
    · change P.evaluation (x + y) = P.evaluation x + P.evaluation y
      exact map_add P.evaluation.hom x y
    · change v ((maximalIdeal P.localRing).toCotangent (deviation P (x + y))) =
        v ((maximalIdeal P.localRing).toCotangent (deviation P x)) +
          v ((maximalIdeal P.localRing).toCotangent (deviation P y))
      rw [h, map_add, map_add]
  map_mul' x y := by
    let I := maximalIdeal P.localRing
    let a := deviation P x
    let b := deviation P y
    have h : deviation P (x * y) = (P.evaluation x) • b + (P.evaluation y) • a + a * b := by
      apply Subtype.ext
      change x * y - _ = algebraMap k P.localRing (P.evaluation x) * (b : P.localRing) +
        algebraMap k P.localRing (P.evaluation y) * (a : P.localRing) + (a : P.localRing) * b
      simp only [a, b, deviation, map_mul]
      ring
    have hab : I.toCotangent (a * b) = 0 :=
      (I.toCotangent_eq_zero _).mpr (by
        rw [pow_two]
        exact Ideal.mul_mem_mul a.2 b.2)
    apply TrivSqZeroExt.ext
    · change P.evaluation (x * y) = P.evaluation x * P.evaluation y
      exact map_mul P.evaluation.hom x y
    · let lin := v.comp (I.toCotangent.restrictScalars k)
      change lin (deviation P (x * y)) = P.evaluation x • lin b + P.evaluation y • lin a
      have hzero : lin (a * b) = 0 := by
        change v (I.toCotangent (a * b)) = 0
        rw [hab, map_zero]
      rw [h, map_add, hzero, add_zero, map_add, map_smul, map_smul]
  commutes' c := by
    have h : deviation P (algebraMap k P.localRing c) = 0 := by
      apply Subtype.ext
      change algebraMap k P.localRing c - algebraMap k P.localRing (P.evaluation _) = 0
      rw [evaluation_constant, sub_self]
    apply TrivSqZeroExt.ext
    · exact evaluation_constant P c
    · change v ((maximalIdeal P.localRing).toCotangent (deviation P (algebraMap k _ c))) = 0
      rw [h, map_zero, map_zero]

local instance jetAlgebra_isLocalHom (v : P.cotangent →ₗ[k] M) :
    IsLocalHom (jetAlgebra P v).toRingHom := by
  constructor
  intro x hx
  exact isUnit_of_map_unit P.evaluation.hom x
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hx)

private theorem jetAlgebra_natural (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap)
    (v : P.cotangent →ₗ[k] M) :
    (jetAlgebra P v).comp (pullStalk f hf) =
      jetAlgebra Q (v.comp (pullCotangent f hf)) := by
  apply AlgHom.ext
  intro x
  have h := evaluation_pullStalk f hf x
  apply TrivSqZeroExt.ext
  · exact h
  change v ((maximalIdeal P.localRing).toCotangent (deviation P (pullStalk f hf x))) =
    v (pullCotangent f hf ((maximalIdeal Q.localRing).toCotangent (deviation Q x)))
  rw [pullCotangent_mk]
  congr 2
  apply Subtype.ext
  change pullStalk f hf x - algebraMap k _ (P.evaluation (pullStalk f hf x)) =
    pullStalk f hf (x - algebraMap k _ (Q.evaluation x))
  rw [map_sub, (pullStalk f hf).commutes, h]

private theorem jetAlgebra_injective (P : PointedScheme k) :
    Function.Injective (jetAlgebra P : (P.cotangent →ₗ[k] M) → _) := by
  intro v w h
  ext t
  obtain ⟨x, rfl⟩ := (maximalIdeal P.localRing).toCotangent_surjective t
  have hx : deviation P x = x := by
    apply Subtype.ext
    simp [deviation, (evaluation_eq_zero_iff P _).mpr x.property]
  have he := congrArg (fun e => (e (x : P.localRing)).snd) h
  change v ((maximalIdeal P.localRing).toCotangent (deviation P x)) =
    w ((maximalIdeal P.localRing).toCotangent (deviation P x)) at he
  rwa [hx] at he

private abbrev infinitesimalBase (k M : Type) [Field k] [AddCommGroup M] [Module k M] :
    Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))))

/-- The infinitesimal point represented by a linear map from the
cotangent space to the square-zero ideal. -/
private def infinitesimalPoint (P : PointedScheme k) (v : P.cotangent →ₗ[k] M) :
    infinitesimalBase k M ⟶ P.X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (jetAlgebra P v).toRingHom) ≫
    P.X.left.fromSpecStalk P.point) (by
      rw [Category.assoc]
      change _ ≫ P.X.left.fromSpecStalk P.point ≫ (P.X.left ↘ Spec (.of k)) = _
      rw [Scheme.fromSpecStalk_comp_over, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact RingHom.ext fun x => (jetAlgebra P v).commutes x)

private theorem infinitesimalPoint_natural (f : P.X ⟶ Q.X)
    (hf : P.sectionMap ≫ f = Q.sectionMap) (v : P.cotangent →ₗ[k] M) :
    infinitesimalPoint P v ≫ f = infinitesimalPoint Q (v.comp (pullCotangent f hf)) := by
  apply Over.OverMorphism.ext
  change (_ ≫ P.X.left.fromSpecStalk P.point) ≫ f.left = _
  rw [Category.assoc, ← specMap_pullStalk f hf, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((jetAlgebra P v).comp (pullStalk f hf)).toRingHom) ≫ _ = _
  rw [jetAlgebra_natural f hf v]
  rfl

private theorem infinitesimalPoint_injective (P : PointedScheme k) :
    Function.Injective (infinitesimalPoint P : (P.cotangent →ₗ[k] M) → _) := by
  intro v w h
  apply jetAlgebra_injective P
  let Z := CommRingCat.of (TrivSqZeroExt k M)
  let loc (d : P.cotangent →ₗ[k] M) :
      Σ x : P.X.left, {f : P.X.left.presheaf.stalk x ⟶ Z // IsLocalHom f.hom} :=
    ⟨P.point, CommRingCat.ofHom (jetAlgebra P d).toRingHom, jetAlgebra_isLocalHom d⟩
  have hi : loc v = loc w := (SpecToEquivOfLocalRing P.X.left Z).symm.injective
    (congrArg (fun f : infinitesimalBase k M ⟶ P.X => f.left) h)
  change (Sigma.mk P.point (loc v).2 : Σ x, {f : P.X.left.presheaf.stalk x ⟶ Z //
    IsLocalHom f.hom}) = Sigma.mk P.point (loc w).2 at hi
  have hh := eq_of_heq (Sigma.mk.inj_iff.mp hi).2
  exact AlgHom.ext fun x => ConcreteCategory.congr_hom (congrArg Subtype.val hh) x

/-- For a product in schemes over the field, the two contravariant
cotangent maps have ranges spanning the cotangent space at the point. -/
theorem cotangent_ranges_sup_eq_top {I : Type} (J : PointedScheme k)
    (P : I → PointedScheme k)
    (f : ∀ i, J.X ⟶ (P i).X)
    (hf : ∀ i, J.sectionMap ≫ f i = (P i).sectionMap)
    (hprod : ∀ {S : Over (Spec (.of k))} (g h : S ⟶ J.X),
      (∀ i, g ≫ f i = h ≫ f i) → g = h) :
    (⨆ i, LinearMap.range (pullCotangent (f i) (hf i))) = ⊤ := by
  let W : Submodule k J.cotangent := ⨆ i, LinearMap.range (pullCotangent (f i) (hf i))
  have hpoint : infinitesimalPoint J W.mkQ = infinitesimalPoint J
      (0 : J.cotangent →ₗ[k] (J.cotangent ⧸ W)) := by
    apply hprod
    intro i
    rw [infinitesimalPoint_natural _ (hf i), infinitesimalPoint_natural _ (hf i)]
    congr 1
    ext x
    change W.mkQ (pullCotangent (f i) (hf i) x) = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr
      ((le_iSup (fun j => LinearMap.range (pullCotangent (f j) (hf j))) i)
        (LinearMap.mem_range_self _ _))
  have he := infinitesimalPoint_injective J hpoint
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero W).mp (DFunLike.congr_fun he x)

end

end ZInQ.Manuscript.RC.HCMV21.PointedScheme
