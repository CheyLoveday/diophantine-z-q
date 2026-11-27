import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Classify
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Reference
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Basic

/-! Specialize the local tests to the splitting and detecting conditions
of the manuscript's admissible filter. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open Eichler LocalWeights O7Actual

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- For the local monogenic quadratic model, conjugacy on the generator
is equivalent to conjugacy of the entire algebra maps. -/
theorem quadratic_hom_conj_iff {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {a b : R} (f g : QuadraticAlgebra R a b →ₐ[R] A) :
    UnitConj (f QuadraticAlgebra.omega) (g QuadraticAlgebra.omega) ↔
      ∃ u : Aˣ, ∀ z : QuadraticAlgebra R a b, (u : A) * f z = g z * (u : A) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun z => ?_⟩
    rw [← QuadraticAlgebra.re_smul_add_im_smul z]
    simp only [map_add, map_smul, map_one, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, hu]
  · rintro ⟨u, hu⟩
    exact ⟨u, hu _⟩

theorem levelPrime_exp (hN : 0 < N) (j : Fin N.primeFactors.card) :
    0 < N.factorization (levelPrime N j).val :=
  (levelPrime N j).prop.factorization_pos_of_dvd hN.ne'
    (Nat.dvd_of_mem_primeFactors ((N.primeFactors.orderIsoOfFin rfl) j).prop)

theorem split_branch_of_splitsIn {p : ℕ} [Fact p.Prime] {d c : ℤ}
    (hc : d = 1 - 4 * c) (hs : Nonvanishing.SplitsIn d p) :
    ∃ a : ℤ_[p], a ^ 2 - a + (c : ℤ_[p]) = 0 ∧ IsUnit (2 * a - 1) := by
  subst d
  by_cases h : p = 2
  · subst p
    exact split_branch_two hs.two
  · obtain ⟨hnd, hsq⟩ := hs.2 h
    have hne : ((1 - 4 * c : ℤ) : ZMod p) ≠ 0 :=
      fun hz => hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    exact split_branch_odd h ((legendreSym.eq_one_iff p hne).mpr hsq)

/-- The positive-level local test on the manuscript's split filter; this
applies also when the prime is two. -/
theorem level_bit_of_filter (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (h8 : disc s D % 8 = 1) (hd : disc s D < 0) (j : Fin N.primeFactors.card)
    (hs : Nonvanishing.SplitsIn (disc s D) (levelPrime N j).val)
    (z w : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (y : ActualSupport s D w) :
    let p := levelPrime N j
    let e := splitOrderChart s p (levelPrime_ne_detecting s j)
    UnitConj (e (localGenerator s H z x p)) (e (localGenerator s H w y p)) ↔
      generatorOrientation s H z x j.castSucc = generatorOrientation s H w y j.castSucc := by
  let c := (1 - disc s D) / 4
  have hc : disc s D = 1 - 4 * c := by dsimp [c]; omega
  obtain ⟨a, ha, hu⟩ := split_branch_of_splitsIn hc hs
  exact actual_level_bit_iff s H hc hd.ne j (levelPrime_exp hN j) a ha hu z w x y

/-- The division local test needs just the two detecting Legendre symbols
from the admissible row. -/
theorem division_bit_of_filter (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (hD : legendreSym s.ell D = 1) (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (z w : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (y : ActualSupport s D w) :
    UnitConj (divisionGenerator s H z x) (divisionGenerator s H w y) ↔
      generatorOrientation s H z x (Fin.last _) = generatorOrientation s H w y (Fin.last _) := by
  have h := detecting_nonsquare hD hh
  exact actual_division_bit_iff s H (fun hz => h (hz ▸ IsSquare.zero)) z w x y

end ZInQ.Manuscript.RC.O7Orbits
