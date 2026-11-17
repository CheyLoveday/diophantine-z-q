import Research.DerivativeSwitch.FiniteSelmerCoefficients
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Self-injectivity of the retained finite coefficient rings

Over `ZMod n`, an ideal lifts to a principal ideal of `ℤ`. For the
truncation and group ring, the top polynomial coefficient and the
identity group coefficient give perfect multiplication pairings.
These algebraic functionals allow extension of linear maps on ideals.
-/

namespace Research.DerivativeSwitch.FiniteSelmerCoefficients

open Polynomial

noncomputable section

theorem zmod_selfInjective (n : ℕ) (hn : n ≠ 0) : Module.Injective (ZMod n) (ZMod n) := by
  apply Module.Baer.injective
  intro I f
  let c : ℤ →+* ZMod n := Int.castRingHom _
  let J := I.comap c
  obtain ⟨d, hd⟩ := Submodule.IsPrincipal.principal J
  change J = Ideal.span {d} at hd
  have hc : c (n : ℤ) = 0 := ZMod.intCast_zmod_eq_zero_iff_dvd _ _ |>.2 (dvd_refl _)
  have hnj : (n : ℤ) ∈ J := by change c (n : ℤ) ∈ I; rw [hc]; exact I.zero_mem
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (hd ▸ hnj)
  have hw0 : w ≠ 0 := by
    intro h
    exact Int.ofNat_ne_zero.mpr hn (by simpa [h] using hw)
  have hdI : c d ∈ I := by
    change d ∈ J
    rw [hd]
    exact Ideal.mem_span_singleton_self d
  let a : I := ⟨c d, hdI⟩
  have hwa : c w • a = 0 := by
    apply Subtype.ext
    change c w * c d = 0
    rw [mul_comm, ← map_mul, ← hw, hc]
  have hy := f.map_smul (c w) a
  rw [hwa, map_zero] at hy
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (f a)
  change c z = f a at hz
  have hcz : c (w * z) = 0 := by
    rw [map_mul, hz]
    exact hy.symm
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcz
  have hzq : z = d * q := mul_left_cancel₀ hw0 <| by
    calc
      w * z = (n : ℤ) * q := hq
      _ = w * (d * q) := by rw [hw, mul_comm d w, mul_assoc]
  have hfa : f a = c d * c q := by rw [← hz, hzq, map_mul]
  have hI : I = Ideal.span {c d} := by
    rw [← Ideal.map_comap_of_surjective c ZMod.intCast_surjective I]
    change J.map c = Ideal.span {c d}
    rw [hd, Ideal.map_span, Set.image_singleton]
  refine ⟨(LinearMap.id : ZMod n →ₗ[ZMod n] ZMod n).smulRight (c q), ?_⟩
  intro x hx
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hI ▸ hx)
  have hxa : (⟨x, hx⟩ : I) = r • a := Subtype.ext hr.symm
  rw [hxa, map_smul, hfa]
  change x * c q = r * (c d * c q)
  rw [← hr, mul_assoc]

private theorem selfInjective_of_mulTrace {B A : Type} [CommRing B] [Ring A] [Algebra B A]
    [Module.Injective B B] (tr : A →ₗ[B] B)
    (detect : ∀ a : A, (∀ x : A, tr (x * a) = 0) → a = 0)
    (represent : ∀ f : A →ₗ[B] B, ∃ a : A, ∀ x : A, tr (x * a) = f x) :
    Module.Injective A A := by
  apply Module.Baer.injective
  intro I g
  obtain ⟨f, hf⟩ := Module.Injective.out (I.subtype.restrictScalars B) Subtype.val_injective
    (tr.comp (g.restrictScalars B))
  obtain ⟨a, ha⟩ := represent f
  refine ⟨(LinearMap.id : A →ₗ[A] A).smulRight a, ?_⟩
  intro x hx
  change x * a = g ⟨x, hx⟩
  symm
  apply sub_eq_zero.mp
  apply detect
  intro y
  have h := hf (y • (⟨x, hx⟩ : I))
  change f (y * x) = tr (g (y • (⟨x, hx⟩ : I))) at h
  rw [map_smul, smul_eq_mul] at h
  rw [mul_sub, map_sub, ← mul_assoc, ha, h, sub_self]

/-- The coefficient in degree `i` descends to the truncation at `i+1`. -/
def topCoefficient (i : ℕ) : Scalar (i + 1) →ₗ[Base (i + 1)] Base (i + 1) :=
  ((truncationIdeal (i + 1)).restrictScalars (Base (i + 1))).liftQ (lcoeff _ i) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp
      (show p ∈ truncationIdeal (i + 1) from hp)
    change (X ^ (i + 1) * q).coeff i = 0
    simp [coeff_X_pow_mul'])

@[simp] theorem topCoefficient_quotient (i : ℕ) (p : Polynomial (Base (i + 1))) :
    topCoefficient i (quotient (i + 1) p) = p.coeff i := rfl

instance scalar_selfInjective (i : ℕ) : Module.Injective (Scalar (i + 1)) (Scalar (i + 1)) := by
  classical
  let inst : Module.Injective (Base (i + 1)) (Base (i + 1)) := zmod_selfInjective _ (by positivity)
  apply selfInjective_of_mulTrace (topCoefficient i)
  · intro a h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    apply X_pow_dvd_iff.mpr
    intro j hj
    have hv := h (quotient (i + 1) (X ^ (i - j)))
    rw [← map_mul, topCoefficient_quotient] at hv
    have he := coeff_X_pow_mul p (i - j) j
    rw [add_comm j (i - j), Nat.sub_add_cancel (Nat.le_of_lt_succ hj)] at he
    exact he ▸ hv
  · intro f
    let term (j : Fin (i + 1)) : Scalar (i + 1) := quotient (i + 1)
      (monomial (i - j) (f (quotient (i + 1) (X ^ (j : ℕ)))))
    let a := ∑ j : Fin (i + 1), term j
    have hterm (k j : Fin (i + 1)) :
        topCoefficient i (quotient (i + 1) (X ^ (k : ℕ)) * term j) =
          if j = k then f (quotient (i + 1) (X ^ (k : ℕ))) else 0 := by
      unfold term
      rw [← map_mul, topCoefficient_quotient, ← C_mul_X_pow_eq_monomial, mul_left_comm,
        ← pow_add, coeff_C_mul_X_pow]
      split_ifs with h h' h'
      · rw [h']
      · exact (h' (Fin.ext (by omega))).elim
      · exact (h (by have := j.isLt; have := Fin.ext_iff.mp h'; omega)).elim
      · rfl
    have hpow (j : Fin (i + 1)) :
        topCoefficient i (quotient (i + 1) (X ^ (j : ℕ)) * a) =
          f (quotient (i + 1) (X ^ (j : ℕ))) := by
      simp only [a, Finset.mul_sum, map_sum, hterm]
      simp
    refine ⟨a, ?_⟩
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, add_mul, map_add, map_add, hp, hq]
    | monomial j r =>
      have hmon : quotient (i + 1) (monomial j r) =
          r • quotient (i + 1) (X ^ j) := by
        change (Ideal.Quotient.mkₐ (Base (i + 1)) (truncationIdeal (i + 1))) (monomial j r) = _
        rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul]
        rfl
      rw [hmon, smul_mul_assoc, map_smul, map_smul]
      by_cases hj : j < i + 1
      · rw [hpow ⟨j, hj⟩]
      · have hzero : quotient (i + 1) (X ^ j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton.mpr (pow_dvd_pow _ (Nat.le_of_not_gt hj)))
        rw [hzero, zero_mul, map_zero, map_zero]

/-- The identity coefficient is linear over the truncated scalar ring. -/
def identityCoefficient (i : ℕ) (A : Type) [Group A] : Binary i A →ₗ[Scalar i] Scalar i where
  toFun x := x.coeff 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance binary_selfInjective (i : ℕ) (A : Type) [CommGroup A] [Fintype A] :
    Module.Injective (Binary (i + 1) A) (Binary (i + 1) A) := by
  classical
  let inst := scalar_selfInjective i
  apply selfInjective_of_mulTrace (identityCoefficient (i + 1) A)
  · intro a h
    ext g
    change a.coeff g = 0
    have hg := h (MonoidAlgebra.single g⁻¹ 1)
    change (MonoidAlgebra.single g⁻¹ 1 * a).coeff 1 = 0 at hg
    simpa only [MonoidAlgebra.coeff_single_mul_apply, inv_inv, mul_one, one_mul] using hg
  · intro f
    let a : Binary (i + 1) A := ∑ g : A, MonoidAlgebra.single g⁻¹
      (f (MonoidAlgebra.of (Scalar (i + 1)) A g))
    refine ⟨a, fun x => ?_⟩
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      change (MonoidAlgebra.single g 1 * a).coeff 1 = f (MonoidAlgebra.of _ _ g)
      rw [MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul]
      simp [a, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy]
    | smul r x hx => rw [smul_mul_assoc, map_smul, map_smul, hx]

end

end Research.DerivativeSwitch.FiniteSelmerCoefficients
