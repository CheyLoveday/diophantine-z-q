import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The scalar coefficient rings of the finite Selmer diagrams

`Scalar i` is `(ℤ/2^i)[t]/(t^i)`. Its reductions change both the
coefficient precision and the polynomial truncation. The finite group
ring is available over the same coefficient ring.
-/

namespace Research.DerivativeSwitch.FiniteSelmerCoefficients

open Polynomial

noncomputable section

abbrev Base (i : ℕ) := ZMod (2 ^ i)

abbrev truncationIdeal (i : ℕ) : Ideal (Polynomial (Base i)) := Ideal.span {X ^ i}

abbrev Scalar (i : ℕ) := Polynomial (Base i) ⧸ truncationIdeal i

abbrev Binary (i : ℕ) (A : Type*) := MonoidAlgebra (Scalar i) A

abbrev quotient (i : ℕ) : Polynomial (Base i) →+* Scalar i := Ideal.Quotient.mk _

def parameter (i : ℕ) : Scalar i := quotient i X

theorem parameter_nilpotent (i : ℕ) : parameter i ^ i = 0 := by
  rw [parameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Every class has a representative supported in the first `i` degrees. -/
instance scalarFinite (i : ℕ) : Finite (Scalar i) := by
  classical
  refine Finite.of_surjective (fun a : Fin i → Base i =>
    quotient i (∑ j : Fin i, monomial (j : ℕ) (a j))) ?_
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let q : Polynomial (Base i) := X ^ i
  refine ⟨fun j => (p %ₘ q).coeff j, ?_⟩
  have hq : q.Monic := monic_X.pow i
  have hdegree : q.degree ≤ i := degree_X_pow_le i
  change quotient i (∑ j : Fin i, monomial (j : ℕ) ((p %ₘ q).coeff j)) = quotient i p
  rw [sum_modByMonic_coeff hq hdegree]
  have hzero : quotient i q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have h := congrArg (quotient i) (p.modByMonic_add_div q)
  simpa only [map_add, map_mul, hzero, zero_mul, add_zero] using h

abbrev baseReduction {n m : ℕ} (h : n ≤ m) : Base m →+* Base n :=
  ZMod.castHom (pow_dvd_pow 2 h) (Base n)

private def polynomialReduction {n m : ℕ} (h : n ≤ m) : Polynomial (Base m) →+* Scalar n :=
  (quotient n).comp (Polynomial.mapRingHom (baseReduction h))

def reduce {n m : ℕ} (h : n ≤ m) : Scalar m →+* Scalar n :=
  Ideal.Quotient.lift _ (polynomialReduction h) (by
    intro p hp
    have hker : truncationIdeal m ≤ RingHom.ker (polynomialReduction h) := by
      apply Ideal.span_le.mpr
      intro a ha
      change polynomialReduction h a = 0
      have hX : polynomialReduction h X = parameter n := by
        simp [polynomialReduction, parameter]
      rw [Set.mem_singleton_iff.mp ha, map_pow, hX]
      conv_lhs => rw [← Nat.add_sub_of_le h]
      rw [pow_add, parameter_nilpotent, zero_mul]
    exact RingHom.mem_ker.mp (hker hp))

theorem reduce_polynomial {n m : ℕ} (h : n ≤ m) (p : Polynomial (Base m)) :
    reduce h (quotient m p) = quotient n (p.map (baseReduction h)) :=
  Ideal.Quotient.lift_mk _ _ _

@[simp] theorem reduce_parameter {n m : ℕ} (h : n ≤ m) :
    reduce h (parameter m) = parameter n := by
  rw [parameter, reduce_polynomial, Polynomial.map_X]
  rfl

theorem reduce_comp {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    (reduce hnm).comp (reduce hml) = reduce (hnm.trans hml) := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.comp_apply]
  change reduce hnm (reduce hml (quotient l p)) = reduce (hnm.trans hml) (quotient l p)
  rw [reduce_polynomial, reduce_polynomial, reduce_polynomial, Polynomial.map_map]
  congr 2
  exact Subsingleton.elim _ _

def padicScalars (i : ℕ) : ℤ_[2] →+* Scalar i :=
  (quotient i).comp (Polynomial.C.comp (PadicInt.toZModPow i))

end

end Research.DerivativeSwitch.FiniteSelmerCoefficients
