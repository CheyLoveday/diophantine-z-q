import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Coefficients
import ZInQKernel.Contrib.TauCeti.Algebra.Module.CharacterModule
import ZInQKernel.Contrib.TauCeti.Algebra.AddCircle

/-!
# Selmer duality, part 6: the coefficient rings `A_i` are self-injective

Manuscript `diophantine_zq.tex`: the finite coefficient rings `A_i = (ℤ/2^i)[t]/t^i` (tex L2725) are
finite Frobenius rings (tex L3461–3463). Self-injectivity is what makes the termwise dual
`Hom_{A_i}(C, A_i)` compute `RHom_{A_i}(C, A_i)` in the finite Selmer duality
(`SelmerDuality/Duality.lean`, DEPARTURE there).

* `selfInjective_of_frobeniusForm`: a finite commutative ring `A` with an additive form
  `λ : A → ℚ/ℤ` such that `λ(a b) = 0` for all `b` forces `a = 0` is self-injective: `a ↦ λ(a ·)` is
  an `A`-linear injection `A → Hom_ℤ(A, ℚ/ℤ)`, bijective by counting, and the character module
  `Hom_ℤ(A, ℚ/ℤ)` of the flat module `A` is injective (Mathlib, `Module.Flat.iff_characterModule_injective`).
* `acoef_selfInjective`: `A_i` (RC10's `Acoef i`) is self-injective, with the Frobenius form
  "coefficient of `t^{i−1}`" (followed by `ℤ/2^i ↪ ℚ/ℤ`).

**Classification.** PROVED.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open Polynomial

/-! ### Frobenius forms -/

open Module

/-- The `A`-linear map `A → Hom_ℤ(A, ℚ/ℤ)`, `a ↦ (b ↦ λ(a b))`. -/
def frobeniusAdjoint {A : Type} [CommRing A] (lam : A →+ AddCircle (1 : ℚ)) :
    A →ₗ[A] CharacterModule A where
  toFun a := lam.comp (AddMonoidHom.mulLeft a)
  map_add' a a' := by
    ext b
    change lam ((a + a') * b) = lam (a * b) + lam (a' * b)
    rw [add_mul, map_add]
  map_smul' r a := by
    ext b
    change lam (r * a * b) = lam (a * (r * b))
    rw [mul_left_comm, ← mul_assoc]

/-- **A finite commutative ring with a nondegenerate Frobenius form is self-injective.** -/
theorem selfInjective_of_frobeniusForm {A : Type} [CommRing A] [Finite A]
    (lam : A →+ AddCircle (1 : ℚ)) (hlam : ∀ a, (∀ b, lam (a * b) = 0) → a = 0) :
    Module.Injective A A := by
  have hinj : Function.Injective (frobeniusAdjoint lam) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hlam a fun b => by
      have := congrArg (fun c : CharacterModule A => c b) ha
      exact this
  have hbij : Function.Bijective (frobeniusAdjoint lam) :=
    hinj.bijective_of_nat_card_le (TauCeti.natCard_characterModule A).le
  let e := LinearEquiv.ofBijective (frobeniusAdjoint lam) hbij
  have hC : Module.Injective A (CharacterModule A) :=
    Module.Flat.iff_characterModule_injective.mp inferInstance
  exact (Module.Baer.of_equiv e.symm (Module.Baer.of_injective hC)).injective

/-- A subsingleton module is injective. -/
theorem injective_of_subsingleton {A : Type} [CommRing A] [Subsingleton A] :
    Module.Injective A A :=
  Module.Baer.injective fun _ _ => ⟨0, fun _ _ => Subsingleton.elim _ _⟩

/-! ### Power bases with a nilpotent generator -/

section PowerBasis

variable {n : ℕ} [NeZero n] {A : Type} [CommRing A] [Algebra (ZMod n) A]
  (pb : PowerBasis (ZMod n) A) (hd : 0 < pb.dim)

/-- The coordinate of `gen^{d−1}`. -/
def topCoord : A →ₗ[ZMod n] ZMod n := pb.basis.coord ⟨pb.dim - 1, by omega⟩

variable (hnil : pb.gen ^ pb.dim = 0)

include hnil in
theorem topCoord_gen_pow (e : ℕ) :
    topCoord pb hd (pb.gen ^ e) = if e = pb.dim - 1 then 1 else 0 := by
  by_cases he : e < pb.dim
  · have : pb.gen ^ e = pb.basis ⟨e, he⟩ := by rw [PowerBasis.coe_basis]
    rw [this, topCoord, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases h : e = pb.dim - 1
    · simp [h]
    · rw [if_neg (by intro h'; exact h (by simpa using congrArg Fin.val h')), if_neg h]
  · have : pb.gen ^ e = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp he)
      rw [pow_add, hnil, zero_mul]
    rw [this, map_zero, if_neg (by omega)]

include hnil in
/-- The coordinate of `gen^{d−1}` in `a · gen^{d−1−k}` is the `k`-th coordinate of `a`. -/
theorem topCoord_mul_gen_pow (a : A) (k : Fin pb.dim) :
    topCoord pb hd (a * pb.gen ^ (pb.dim - 1 - k)) = pb.basis.repr a k := by
  have hterm : ∀ j : Fin pb.dim,
      topCoord pb hd ((pb.basis.repr a j • pb.basis j) * pb.gen ^ (pb.dim - 1 - k)) =
        if j = k then pb.basis.repr a j else 0 := by
    intro j
    rw [smul_mul_assoc, map_smul, PowerBasis.coe_basis, ← pow_add, topCoord_gen_pow pb hd hnil,
      smul_eq_mul]
    have hj := j.2
    have hk := k.2
    by_cases h : j = k
    · subst h
      rw [if_pos (by omega), if_pos rfl, mul_one]
    · have : (j : ℕ) ≠ k := fun h' => h (Fin.ext h')
      rw [if_neg (by omega), if_neg h, mul_zero]
  conv_lhs => rw [← pb.basis.sum_repr a]
  rw [Finset.sum_mul, map_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq']
  simp

include hnil in
/-- **The top coordinate is a nondegenerate Frobenius form.** -/
theorem topCoord_nondegenerate (a : A) (h : ∀ b, ZMod.toRatAddCircle n (topCoord pb hd (a * b)) = 0) :
    a = 0 := by
  apply pb.basis.repr.injective
  ext k
  have := h (pb.gen ^ (pb.dim - 1 - k))
  rw [topCoord_mul_gen_pow pb hd hnil, ZMod.toRatAddCircle_eq_zero] at this
  simpa using this

end PowerBasis

/-! ### The coefficient rings `A_i` -/

open ZInQ.Manuscript.RC.HeegnerAlgebra in
/-- **`A_i = (ℤ/2^i)[t]/t^i` is self-injective** (Frobenius form: the coefficient of `t^{i−1}`). -/
theorem acoef_selfInjective (i : ℕ) : Module.Injective (Acoef i) (Acoef i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have : Subsingleton (ZMod (2 ^ 0)) := by
      rw [pow_zero]; infer_instance
    have : Subsingleton (Acoef 0) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Subsingleton.elim p q]
    exact injective_of_subsingleton
  · have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi.ne'⟩
    let pb : PowerBasis (ZMod (2 ^ i)) (Acoef i) :=
      AdjoinRoot.powerBasis' (monic_X_pow i)
    have hdim : pb.dim = i := by
      change (X ^ i : (ZMod (2 ^ i))[X]).natDegree = i
      exact natDegree_X_pow i
    have hd : 0 < pb.dim := by rw [hdim]; exact hi
    have hnil : pb.gen ^ pb.dim = 0 := by
      rw [hdim]
      change (AdjoinRoot.root (X ^ i : (ZMod (2 ^ i))[X])) ^ i = 0
      rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
    have : Module.Finite (ZMod (2 ^ i)) (Acoef i) := pb.finite
    have : Finite (Acoef i) := Module.finite_of_finite (ZMod (2 ^ i))
    exact selfInjective_of_frobeniusForm
      ((ZMod.toRatAddCircle (2 ^ i)).comp (topCoord pb hd).toAddMonoidHom)
      (fun a ha => topCoord_nondegenerate pb hd hnil a ha)

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
