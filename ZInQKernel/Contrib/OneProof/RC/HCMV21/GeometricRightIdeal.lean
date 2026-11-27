import ZInQKernel.Contrib.OneProof.RC.HCMV21.QuotientHomLattice
import ZInQKernel.Contrib.OneProof.RC.Eichler.Local

/-! In rational quaternion coordinates the enhanced Hom group of an
actual coprime quotient is a full right lattice. Its integral
coordinates are obtained by clearing the denominator of the reverse
isogeny. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler PkgI3.AbVar ZInQ.DefFaltings
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {A B : PkgI3.AbVar k} {a b : ℚ}

/-- The geometric endomorphisms preserving the level form a full
quaternion order in the coordinates of the level-one endomorphisms. -/
noncomputable def levelOrderOfEndOrder (S : Order a b) (embed : A.End ≃+* S.ring)
    (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0) (hC : ∀ P ∈ C, P ^ N = 1) : Order a b where
  ring := (levelEnd A C).map (S.ring.subtype.comp embed.toRingHom)
  full := by
    let f := S.ring.subtype.comp embed.toRingHom
    let T := (levelEnd A C).map f
    have hTS : T ≤ S.ring := fun _ ⟨x, _, hx⟩ => hx ▸ (embed x).property
    refine ⟨S.full.fg.of_le hTS, ?_⟩
    change Submodule.span ℚ (f.toAddMonoidHom '' (levelEnd A C : Set A.End)) = ⊤
    have hN' : IsUnit (N : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN)
    rw [span_levelEnd_eq_span_end A C N hC hN' f.toAddMonoidHom, ← S.full.span_eq_top]
    congr 1
    ext x
    exact ⟨fun ⟨y, h⟩ => h ▸ (embed y).property,
      fun hx => ⟨embed.symm ⟨x, hx⟩, congrArg Subtype.val (embed.apply_symm_apply ⟨x, hx⟩)⟩⟩

/-- The geometric level order and the level-one order have the same
completion wherever the level is a unit, in particular at the detector. -/
theorem levelOrderOfEndOrder_completion_eq (S : Order a b) (embed : A.End ≃+* S.ring)
    (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0) (hC : ∀ P ∈ C, P ^ N = 1)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (N : ℤ_[p])) :
    (levelOrderOfEndOrder S embed C N hN hC).completion p = S.completion p := by
  let f := S.ring.subtype.comp embed.toRingHom
  let φ := ((toLocal p : Eichler.B a b →+* Bp p a b).comp f).toAddMonoidHom
  have hsurj : Set.range f = (S.ring : Set (Eichler.B a b)) := by
    ext x
    exact ⟨fun ⟨y, h⟩ => h ▸ (embed y).property,
      fun hx => ⟨embed.symm ⟨x, hx⟩, congrArg Subtype.val (embed.apply_symm_apply ⟨x, hx⟩)⟩⟩
  apply Subalgebra.toSubmodule_injective
  rw [Order.completion_toSubmodule, Order.completion_toSubmodule, localLattice, localLattice]
  change Submodule.span ℤ_[p] (toLocal p '' (f '' (levelEnd A C : Set A.End))) =
    Submodule.span ℤ_[p] (toLocal p '' (S.ring : Set (Eichler.B a b)))
  rw [Set.image_image, ← hsurj, ← Set.range_comp]
  exact span_levelEnd_eq_span_end A C N hC hp φ

/-- The integral representative of the geometric right lattice.
Composition with the reverse isogeny clears the denominator; the
quasi-isogeny coordinates differ by the rational scalar `1/m`. -/
noncomputable def quotientRightIdeal (R : Order a b) (embed : A.End →+* Eichler.B a b)
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m)
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b))) : RightIdeal R := by
  let J := (levelHom C (C.map (ptMap u))).toIntSubmodule.map
    (embed.toAddMonoidHom.comp (postcomposeToEnd v)).toIntLinearMap
  have hJ : (J : Set (Eichler.B a b)) =
      embed '' (postcomposeToEnd v '' (levelHom C (C.map (ptMap u)) : Set (Hom A B))) := by
    rw [Submodule.map_coe, Set.image_image]
    rfl
  have hmem {x : Eichler.B a b} : x ∈ J ↔
      ∃ f : A.End, f ∈ levelEnd A C ∧
        (∀ P : A.Pt (AlgebraicClosure k), P ^ m = 1 → (P ≫ f.hom) ≫ u.hom = 1) ∧ embed f = x := by
    change x ∈ (J : Set (Eichler.B a b)) ↔ _
    rw [hJ]
    exact exists_congr fun f => by
      rw [mem_postcomposeToEnd_levelHom_image_iff u v m hm hu hv C hC]
      tauto
  have hJR : J ≤ R.lattice := by
    intro x hx
    obtain ⟨f, hf, _, rfl⟩ := hmem.mp hx
    change embed f ∈ (R.ring : Set (Eichler.B a b))
    rw [← hR]
    exact ⟨f, hf, rfl⟩
  refine ⟨J, ⟨R.full.fg.of_le hJR, ?_⟩, ?_⟩
  · apply top_unique
    rw [← R.full.span_eq_top]
    apply Submodule.span_le.mpr
    intro r hr
    change r ∈ (R.ring : Set (Eichler.B a b)) at hr
    rw [← hR] at hr
    obtain ⟨f, hf, rfl⟩ := hr
    have hmf : m • embed f ∈ J := hmem.mpr ⟨m • f, (levelEnd A C).nsmul_mem hf m, by
      intro P hP
      change (P ≫ (f.hom ^ m)) ≫ u.hom = 1
      rw [MonObj.comp_pow, ← MonObj.pow_comp, hP, MonObj.one_comp, MonObj.one_comp],
      map_nsmul embed _ _⟩
    have hspan := Submodule.subset_span (R := ℚ) (s := (J : Set (Eichler.B a b))) hmf
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hspan
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 from fun h => hm (by simp [h]))
    have h := (Submodule.span ℚ (J : Set (Eichler.B a b))).smul_mem (m : ℚ)⁻¹ hspan
    rwa [smul_smul, inv_mul_cancel₀ hm', one_smul] at h
  · intro x r hx hr
    obtain ⟨f, hf, hker, rfl⟩ := hmem.mp hx
    change r ∈ (R.ring : Set (Eichler.B a b)) at hr
    rw [← hR] at hr
    obtain ⟨g, hg, rfl⟩ := hr
    refine hmem.mpr ⟨f * g, (levelEnd A C).mul_mem hf hg, ?_, map_mul embed _ _⟩
    intro P hP
    change (P ≫ (g.hom ≫ f.hom)) ≫ u.hom = 1
    rw [← Category.assoc]
    apply hker
    rw [← MonObj.pow_comp, hP, MonObj.one_comp]

/-- The completed right ideal is the span of the actual enhanced maps
composed with the reverse isogeny and evaluated in local coordinates. -/
theorem localLattice_quotientRightIdeal_eq_span (R : Order a b)
    (embed : A.End →+* Eichler.B a b) (u : Hom A B) (v : Hom B A)
    (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m)
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b)))
    (p : ℕ) [Fact p.Prime] :
    localLattice p (quotientRightIdeal R embed u v m hm hu hv C hC hR).lattice =
      Submodule.span ℤ_[p] ((((toLocal p : Eichler.B a b →+* Bp p a b).comp
        embed).toAddMonoidHom.comp (postcomposeToEnd v)) ''
          (levelHom C (C.map (ptMap u)) : Set (Hom A B))) := by
  unfold localLattice
  change Submodule.span ℤ_[p] (toLocal p '' (((levelHom C (C.map (ptMap u))).toIntSubmodule.map
    (embed.toAddMonoidHom.comp (postcomposeToEnd v)).toIntLinearMap :
      Submodule ℤ (Eichler.B a b)) : Set (Eichler.B a b))) = _
  rw [Submodule.map_coe, Set.image_image]
  rfl

/-- At every prime away from the kernel exponent, including the
detector and level primes of a coprime quotient, the completed Hom
lattice in the reverse-isogeny frame is the source level order. -/
theorem localLattice_quotientRightIdeal_eq_completion (R : Order a b)
    (embed : A.End →+* Eichler.B a b) (u : Hom A B) (v : Hom B A)
    (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m)
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b)))
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (m : ℤ_[p])) :
    localLattice p (quotientRightIdeal R embed u v m hm hu hv C hC hR).lattice =
      (R.completion p).toSubmodule := by
  rw [localLattice_quotientRightIdeal_eq_span, R.completion_toSubmodule, localLattice]
  rw [span_quotient_levelHom_eq_source_order u v m hp hu C]
  change _ = Submodule.span ℤ_[p] (toLocal p '' (R.ring : Set (Eichler.B a b)))
  rw [← hR, Set.image_image]
  rfl

end ZInQ.Manuscript.RC.HCMV21
