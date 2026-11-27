import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.Index

/-! The conductor-one ideal action on the analytic quotient. The coefficient ring is a
Dedekind domain with fraction field `K`; in the application it is the maximal order.
The map into `V` is the fixed CM embedding into `ℂ`, viewed as a linear map. -/

namespace ZInQ.Manuscript.RC.HCMV21

open scoped nonZeroDivisors
open FractionalIdeal

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V]

local notation "FI" => FractionalIdeal R⁰ K

/-- The image of a fractional ideal in the ambient space of a CM lattice. -/
def imageLattice (e : K →ₗ[R] V) (I : FI) : Submodule R V :=
  (I : Submodule R K).map e

/-- The lattice after the ideal action of `a`: `a⁻¹ I`. -/
noncomputable def idealTranslate (a : Ideal R) (I : FI) : FI :=
  I / (a : FI)

/-- The original lattice lies in its translate by a nonzero integral ideal. -/
theorem le_idealTranslate (a : Ideal R) (ha : a ≠ ⊥) (I : FI) :
    I ≤ idealTranslate a I := by
  have ha' : (a : FI) ≠ 0 := by simpa [coeIdeal_eq_zero] using ha
  exact (le_div_iff_mul_le ha').mpr <| by
    calc
      I * (a : FI) ≤ I * 1 := mul_le.mpr fun _ hx _ hy =>
        mul_mem_mul hx (coeIdeal_le_one hy)
      _ = I := mul_one I

/-- The map induced by the identity on the ambient space. -/
noncomputable def idealQuotientMap (e : K →ₗ[R] V) (a : Ideal R) (ha : a ≠ ⊥) (I : FI) :
    (V ⧸ imageLattice e I) →ₗ[R] V ⧸ imageLattice e (idealTranslate a I) :=
  Submodule.factor (Submodule.map_mono (le_idealTranslate a ha I))

/-- The ideal isogeny on the quotient is onto. -/
theorem idealQuotientMap_surjective (e : K →ₗ[R] V) (a : Ideal R) (ha : a ≠ ⊥) (I : FI) :
    Function.Surjective (idealQuotientMap e a ha I) :=
  Submodule.factor_surjective (Submodule.map_mono (le_idealTranslate a ha I))

/-- Points killed by the action of every element of `a`. -/
def idealTorsion (a : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : Submodule R M where
  carrier := {x | ∀ r ∈ a, r • x = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy r hr; rw [smul_add, hx r hr, hy r hr, add_zero]
  smul_mem' := by intro r x hx s hs; rw [smul_comm, hx s hs, smul_zero]

/-- For a nonzero ideal the quotient kernel is precisely the ideal torsion. -/
theorem ker_idealQuotientMap [Module.IsTorsionFree R V] (e : K →ₗ[R] V)
    (heInj : Function.Injective e) (a : Ideal R) (ha : a ≠ ⊥) (I : FI) :
    LinearMap.ker (idealQuotientMap e a ha I) = idealTorsion a (V ⧸ imageLattice e I) := by
  have ha' : (a : FI) ≠ 0 := by simpa [coeIdeal_eq_zero] using ha
  ext p
  obtain ⟨z, rfl⟩ := (imageLattice e I).mkQ_surjective p
  change (idealQuotientMap e a ha I ((imageLattice e I).mkQ z) = 0) ↔
    ∀ r ∈ a, r • (imageLattice e I).mkQ z = 0
  change (Submodule.Quotient.mk z : V ⧸ imageLattice e (idealTranslate a I)) = 0 ↔
    ∀ r ∈ a, (Submodule.Quotient.mk (r • z) : V ⧸ imageLattice e I) = 0
  simp only [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩ r hr
    refine ⟨r • x, ?_, e.map_smul r x⟩
    have h := (mem_div_iff_of_ne_zero ha').mp hx (algebraMap R K r)
      ((mem_coeIdeal R⁰).mpr ⟨r, hr, rfl⟩)
    simpa [Algebra.smul_def, mul_comm] using h
  · intro h
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
    obtain ⟨x, hx, hxe⟩ := h r hr
    have hunit : algebraMap R K r ≠ 0 :=
      fun hzero => hr0 ((IsFractionRing.injective R K) (hzero.trans (map_zero _).symm))
    let y : K := (algebraMap R K r)⁻¹ * x
    have hry : r • y = x := by
      simp [y, Algebra.smul_def, hunit]
    have he : e y = z := by
      apply smul_right_injective V hr0
      change r • e y = r • z
      rw [← e.map_smul, hry, hxe]
    refine ⟨y, (mem_div_iff_of_ne_zero ha').mpr ?_, he⟩
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (mem_coeIdeal R⁰).mp hs
    obtain ⟨w, hw, hwe⟩ := h t ht
    have hty : t • y = w := heInj (by rw [e.map_smul, he, hwe])
    simpa [mul_comm, ← Algebra.smul_def, hty] using hw

/-- For coprime ideals, the ideal isogeny carries the level torsion isomorphically
onto the level torsion of the translated lattice. -/
theorem idealQuotientMap_bijOn_level [Module.IsTorsionFree R V] (e : K →ₗ[R] V)
    (he : Function.Injective e) {a n : Ideal R} (ha : a ≠ ⊥) (hcop : IsCoprime a n) (I : FI) :
    Set.BijOn (idealQuotientMap e a ha I)
      (idealTorsion n (V ⧸ imageLattice e I) : Set _)
      (idealTorsion n (V ⧸ imageLattice e (idealTranslate a I)) : Set _) := by
  let f := idealQuotientMap e a ha I
  have hker := ker_idealQuotientMap e he a ha I
  obtain ⟨r, hr, s, hs, hrs⟩ := Ideal.isCoprime_iff_exists.mp hcop
  refine ⟨?_, ?_, ?_⟩
  · intro x hx t ht
    change t • f x = 0
    rw [← f.map_smul, (show t • x = 0 from hx t ht), map_zero]
  · intro x hx y hy hxy
    have hxy' : x - y ∈ LinearMap.ker f := by
      change f (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hxya : r • (x - y) = 0 := (show x - y ∈ idealTorsion a _ by
      rw [← hker]; exact hxy') r hr
    have hxyn : s • (x - y) = 0 := (idealTorsion n _).sub_mem hx hy s hs
    exact sub_eq_zero.mp (by rw [← one_smul R (x - y), ← hrs, add_smul, hxya, hxyn, add_zero])
  · intro y hy
    obtain ⟨x, hx⟩ := idealQuotientMap_surjective e a ha I y
    refine ⟨r • x, ?_, ?_⟩
    · intro t ht
      have htx : t • x ∈ LinearMap.ker f := by
        change f (t • x) = 0
        rw [f.map_smul, hx, (show t • y = 0 from hy t ht)]
      rw [smul_comm]
      exact (show t • x ∈ idealTorsion a _ by rw [← hker]; exact htx) r hr
    · change f (r • x) = y
      rw [f.map_smul, hx]
      conv_rhs => rw [← one_smul R y, ← hrs, add_smul, (show s • y = 0 from hy s hs), add_zero]

/-- Products of nonzero ideals compose their actions on lattices. -/
theorem idealTranslate_mul (a b : Ideal R) (I : FI) :
    idealTranslate (a * b) I = idealTranslate b (idealTranslate a I) := by
  simp [idealTranslate, coeIdeal_mul, div_eq_mul_inv, mul_assoc, mul_comm]

/-- The unit ideal acts by the identity. -/
theorem idealTranslate_top (I : FI) : idealTranslate (⊤ : Ideal R) I = I := by
  have ht : ((⊤ : Ideal R) : FI) = 1 := coeIdeal_eq_one.mpr Ideal.one_eq_top.symm
  rw [idealTranslate, ht, FractionalIdeal.div_one]

/-- An integral principal ideal acts by homothety by the inverse of its
generator. For a nonzero generator this does not change the labelled class. -/
theorem idealTranslate_principal (r : R) (I : FI) :
    idealTranslate (Ideal.span {r}) I = spanSingleton R⁰ (algebraMap R K r)⁻¹ * I := by
  rw [idealTranslate, div_eq_mul_inv, coeIdeal_span_singleton, spanSingleton_inv, mul_comm]

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- A nonzero scalar that takes one embedded nonzero ideal into another is
already the image of a scalar in the fraction field. In the application this
restricts complex homotheties between normalized CM lattices to `Kˣ`. -/
theorem homothety_scalar_in_fractionField {E : Type*} [Field E] (ι : K →+* E)
    {I J : FI} (hI : I ≠ 0) (z : E) (hz : z ≠ 0)
    (h : ∀ x ∈ (I : Set K), z * ι x ∈ ι '' (J : Set K)) :
    ∃ u : Kˣ, ι (u : K) = z := by
  have hi : (I : Submodule R K) ≠ ⊥ := fun he => hI (coeToSubmodule_injective (he.trans coe_zero.symm))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
  obtain ⟨y, _, hy⟩ := h x hx
  have hy0 : y ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hy
    exact (mul_ne_zero hz ((map_ne_zero ι).2 hx0)) hy.symm
  refine ⟨Units.mk0 (y / x) (div_ne_zero hy0 hx0), ?_⟩
  change ι (y / x) = z
  rw [map_div₀, div_eq_iff ((map_ne_zero ι).2 hx0), hy]

omit [IsDedekindDomain R] in
/-- The kernel of the quotient map for nested submodules has cardinality equal
to the relative index of the two additive subgroups. -/
theorem card_ker_factor (L L' : Submodule R V) (h : L ≤ L') :
    Nat.card (LinearMap.ker (Submodule.factor h)) = L.toAddSubgroup.relIndex L'.toAddSubgroup := by
  let g := L.mkQ.toAddMonoidHom
  have hg : g.ker = L.toAddSubgroup := by
    ext z
    exact Submodule.Quotient.mk_eq_zero L
  have hmap : L'.toAddSubgroup.map g = (LinearMap.ker (Submodule.factor h)).toAddSubgroup := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero L').mpr hz
    · intro hp
      obtain ⟨z, rfl⟩ := L.mkQ_surjective p
      exact ⟨z, (Submodule.Quotient.mk_eq_zero L').mp hp, rfl⟩
  rw [← hg, AddSubgroup.relIndex_ker, hmap]
  rfl

omit [IsDedekindDomain R] in
/-- Multiplying the additive group of a fractional ideal by a scalar is the
underlying additive group of the product with the principal fractional ideal. -/
theorem scale_toAddSubgroup (d : K) (I : FI) :
    (I : Submodule R K).toAddSubgroup.map (AddMonoidHom.mulLeft d) =
      ((spanSingleton R⁰ d * I : FI) : Submodule R K).toAddSubgroup := by
  ext x
  change (∃ y ∈ (I : Submodule R K), d * y = x) ↔ _
  simp only [coe_mul, coe_spanSingleton, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_singleton_mul]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The kernel has cardinality `N(a)` (the degree of the analytic isogeny).
Multiplying both lattices by the same denominator reduces to the index of `aB` in `B`. -/
theorem card_ker_idealQuotientMap [Infinite R] [Ring.HasFiniteQuotients R]
    (e : K →ₗ[R] V) (he : Function.Injective e) (a : Ideal R) (ha : a ≠ ⊥)
    (I : FI) (hI : I ≠ 0) :
    Nat.card (LinearMap.ker (idealQuotientMap e a ha I)) = a.absNorm := by
  let J := idealTranslate a I
  have ha' : (a : FI) ≠ 0 := coeIdeal_ne_zero.mpr ha
  have hIJ : J * (a : FI) = I := by
    change (I / (a : FI)) * (a : FI) = I
    exact div_mul_cancel₀ I ha'
  let d := algebraMap R K J.den
  have hd : d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors J.den.2
  let B := J.num
  have hB : spanSingleton R⁰ d * J = (B : FI) := den_mul_self_eq_num' R⁰ K J
  have hAB : spanSingleton R⁰ d * I = ((B * a : Ideal R) : FI) := by
    calc
      _ = spanSingleton R⁰ d * (J * (a : FI)) :=
        congrArg (fun X : FI => spanSingleton R⁰ d * X) hIJ.symm
      _ = _ := by rw [← mul_assoc, hB, coeIdeal_mul]
  have hB0 : B ≠ ⊥ := by
    intro h
    apply hI
    have hJ : J = 0 := num_eq_zero_iff.mp (show J.num = 0 from h)
    simpa [hJ] using hIJ.symm
  have h₁ := AddSubgroup.relIndex_map_map_of_injective
    (f := e.toAddMonoidHom) (I : Submodule R K).toAddSubgroup
    (J : Submodule R K).toAddSubgroup he
  have h₂ := AddSubgroup.relIndex_map_map_of_injective
    (f := AddMonoidHom.mulLeft d) (I : Submodule R K).toAddSubgroup
    (J : Submodule R K).toAddSubgroup (show Function.Injective (d * ·) from
      fun x y h => mul_left_cancel₀ hd h)
  rw [scale_toAddSubgroup, scale_toAddSubgroup, hAB, hB] at h₂
  have h₃ := AddSubgroup.relIndex_map_map_of_injective
    (f := (algebraMap R K).toAddMonoidHom) (B * a).toAddSubgroup B.toAddSubgroup
    (IsFractionRing.injective R K)
  change (((B * a : Ideal R) : FI) : Submodule R K).toAddSubgroup.relIndex
      ((B : FI) : Submodule R K).toAddSubgroup = _ at h₃
  rw [idealQuotientMap, card_ker_factor, imageLattice, imageLattice,
    Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  change ((I : Submodule R K).toAddSubgroup.map e.toAddMonoidHom).relIndex
    ((J : Submodule R K).toAddSubgroup.map e.toAddMonoidHom) = _
  rw [h₁, ← h₂, h₃]
  have hidx := AddSubgroup.relIndex_mul_index (show (B * a).toAddSubgroup ≤ B.toAddSubgroup
    from Ideal.mul_le_left)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, map_mul, mul_comm B.absNorm] at hidx
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff B).mpr
      (Ring.HasFiniteQuotients.finiteQuotient hB0))) hidx

end ZInQ.Manuscript.RC.HCMV21
