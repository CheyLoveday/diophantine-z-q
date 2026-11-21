module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.Ring

/-! # The degree-zero algebra on the short Weierstrass locus -/

@[expose] public section

namespace RC.ModelInvariants.ShortWeierstrass

open MvPolynomial HomogeneousLocalization
open scoped BigOperators

noncomputable section

variable (R : Type*) [CommRing R]

/-- The two Weierstrass coefficients have weights four and six, respectively. -/
def weights : Bool → ℕ := fun i => if i then 6 else 4

abbrev coefficientGrading := weightedHomogeneousSubmodule R weights

instance : GradedAlgebra (coefficientGrading R) := weightedGradedAlgebra R weights

/-- The discriminant of the short Weierstrass equation. -/
def discriminant : MvPolynomial Bool R :=
  C (-16 : R) * (C (4 : R) * X false ^ 3 + C (27 : R) * X true ^ 2)

theorem a4_cubed_mem : (X false ^ 3 : MvPolynomial Bool R) ∈ coefficientGrading R 12 :=
  (isWeightedHomogeneous_X R weights false).pow 3

theorem a6_squared_mem : (X true ^ 2 : MvPolynomial Bool R) ∈ coefficientGrading R 12 :=
  (isWeightedHomogeneous_X R weights true).pow 2

theorem discriminant_mem : discriminant R ∈ coefficientGrading R 12 := by
  have h4 : IsWeightedHomogeneous weights (X false ^ 3 : MvPolynomial Bool R) 12 := a4_cubed_mem R
  have h6 : IsWeightedHomogeneous weights (X true ^ 2 : MvPolynomial Bool R) 12 := a6_squared_mem R
  exact ((h4.C_mul 4).add (h6.C_mul 27)).C_mul (-16)

/-- This homogeneous localization consists of fractions (s/\Delta^n) with (s) of weight
(12n). It is the degree-zero ring of the discriminant-open chart. -/
abbrev CoordinateRing := HomogeneousLocalization.Away (coefficientGrading R) (discriminant R)

instance : Algebra R (CoordinateRing R) :=
  ((algebraMap (coefficientGrading R 0) (CoordinateRing R)).comp
    (algebraMap R (coefficientGrading R 0))).toAlgebra

instance : IsScalarTower R (coefficientGrading R 0) (MvPolynomial Bool R) :=
  IsScalarTower.of_algebraMap_eq
    (R := R) (S := coefficientGrading R 0) (A := MvPolynomial Bool R) fun _ => rfl

/-- The degree-zero fraction (a_4^3/\Delta). -/
def a4Ratio : CoordinateRing R :=
  Away.mk (coefficientGrading R) (discriminant_mem R) 1 (X false ^ 3) (a4_cubed_mem R)

/-- The degree-zero fraction (a_6^2/\Delta). -/
def a6Ratio : CoordinateRing R :=
  Away.mk (coefficientGrading R) (discriminant_mem R) 1 (X true ^ 2) (a6_squared_mem R)

set_option maxHeartbeats 800000 in
/-- The two indicated fractions generate the degree-zero algebra, over any base ring. -/
theorem ratios_generate :
    Algebra.adjoin R ({a4Ratio R, a6Ratio R} : Set (CoordinateRing R)) = ⊤ := by
  classical
  let A := Algebra.adjoin R ({a4Ratio R, a6Ratio R} : Set (CoordinateRing R))
  have h4 : a4Ratio R ∈ A := Algebra.subset_adjoin (by simp)
  have h6 : a6Ratio R ∈ A := Algebra.subset_adjoin (by simp)
  have hgen : Algebra.adjoin (coefficientGrading R 0) (Set.range (X : Bool → MvPolynomial Bool R)) =
      ⊤ := by
    have hle : Algebra.adjoin R (Set.range (X : Bool → MvPolynomial Bool R)) ≤
        (Algebra.adjoin (coefficientGrading R 0) (Set.range X)).restrictScalars R :=
      Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
    rw [MvPolynomial.adjoin_range_X] at hle
    exact Algebra.eq_top_iff.2 fun x => hle (Algebra.mem_top (x := x))
  have span_all := Away.span_mk_prod_pow_eq_top (discriminant_mem R) (X : Bool → MvPolynomial Bool R)
    hgen weights (fun i => isWeightedHomogeneous_X R weights i)
  apply eq_top_iff.2
  intro x _
  change x ∈ A
  have hx : x ∈ _ := show x ∈ (⊤ : Submodule (coefficientGrading R 0) (CoordinateRing R)) from trivial
  rw [← span_all] at hx
  refine Submodule.span_induction (p := fun y _ => y ∈ A) ?_ (zero_mem A)
    (fun _ _ _ _ hy hz => add_mem hy hz) ?_ hx
  · rintro _ ⟨n, exponents, hweight, rfl⟩
    have h : 4 * exponents false + 6 * exponents true = 12 * n := by
      simpa [Fintype.sum_bool, weights, mul_comm, add_comm] using hweight
    have he4 : exponents false = 3 * (exponents false / 3) := by omega
    have he6 : exponents true = 2 * (exponents true / 2) := by omega
    have hen : n = exponents false / 3 + exponents true / 2 := by omega
    have he :
        Away.mk (coefficientGrading R) (discriminant_mem R) n
          (∏ i, X i ^ exponents i)
          (hweight ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ =>
            isWeightedHomogeneous_X R weights i) =
          a4Ratio R ^ (exponents false / 3) * a6Ratio R ^ (exponents true / 2) := by
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk, val_mul, val_pow, a4Ratio, a6Ratio, Localization.mk_pow,
        Localization.mk_mul, pow_one, Fintype.prod_bool]
      congr 1
      · rw [← pow_mul, ← pow_mul, ← he4, ← he6, mul_comm]
      · apply Subtype.ext
        change discriminant R ^ n =
          discriminant R ^ (exponents false / 3) * discriminant R ^ (exponents true / 2)
        rw [hen, pow_add]
    rw [he]
    exact mul_mem (pow_mem h4 _) (pow_mem h6 _)
  · intro r y _ hy
    rw [Algebra.smul_def]
    apply mul_mem _ hy
    have hr : (r : MvPolynomial Bool R) = C ((r : MvPolynomial Bool R).coeff 0) := by
      have hm : IsWeightedHomogeneous weights (r : MvPolynomial Bool R) 0 := r.property
      calc
        (r : MvPolynomial Bool R) = weightedHomogeneousComponent weights 0 r :=
          hm.weightedHomogeneousComponent_same.symm
        _ = C ((r : MvPolynomial Bool R).coeff 0) :=
          weightedHomogeneousComponent_zero _ (by intro i; cases i <;> decide)
    have hr' : r = algebraMap R (coefficientGrading R 0) ((r : MvPolynomial Bool R).coeff 0) :=
      Subtype.ext hr
    have he : algebraMap (coefficientGrading R 0) (CoordinateRing R) r =
        algebraMap R (CoordinateRing R) ((r : MvPolynomial Bool R).coeff 0) :=
      congrArg (algebraMap (coefficientGrading R 0) (CoordinateRing R)) hr'
    rw [he]
    exact algebraMap_mem A _

/-- The short Weierstrass (j)-invariant (c_4^3/\Delta), with (c_4=-48a_4). -/
def j : CoordinateRing R := algebraMap R (CoordinateRing R) ((-48 : R) ^ 3) * a4Ratio R

#print axioms weights
#print axioms coefficientGrading
#print axioms discriminant
#print axioms CoordinateRing
#print axioms a4Ratio
#print axioms a6Ratio
#print axioms j
#print axioms discriminant_mem
#print axioms a4_cubed_mem
#print axioms a6_squared_mem
#print axioms ratios_generate

end

end RC.ModelInvariants.ShortWeierstrass
