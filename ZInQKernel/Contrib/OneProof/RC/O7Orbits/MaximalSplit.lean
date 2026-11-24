import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Local
import Mathlib.Algebra.Squarefree.Basic

/-! At a split maximal order, the maximal quadratic generator has a cyclic
integral basis. This also handles the ramified primes of the quadratic field. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open Matrix LocalWeights

/-- A squarefree rational integer remains indivisible by the square of the
local uniformizer. -/
theorem padic_prime_sq_not_dvd {p : ℕ} [Fact p.Prime] {d : ℤ} (hd : Squarefree d) :
    ¬ (p : ℤ_[p]) ^ 2 ∣ (d : ℤ_[p]) := by
  intro h
  have hz : PadicInt.toZModPow 2 (d : ℤ_[p]) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact h
  have hz' : (d : ZMod (p ^ 2)) = 0 := by simpa only [map_intCast] using hz
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd d (p ^ 2)).mp hz'
  apply (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_isUnit
  exact hd (p : ℤ) ⟨j, by simpa only [pow_two, Int.natCast_mul] using hj⟩

/-- The change of columns `(v, Xv)`. -/
def cyclicColumns {A : Type*} [CommRing A] (X : Mat A) (v w : A) : Mat A :=
  !![v, X 0 0 * v + X 0 1 * w; w, X 1 0 * v + X 1 1 * w]

/-- On-the-spot (c), tex 9136–9139: a discriminant prime of multiplicity
at most one excludes a scalar matrix modulo that prime. One of three
elementary vectors then gives a cyclic integral basis. -/
theorem exists_cyclicColumns {p : ℕ} [Fact p.Prime] (X : Mat ℤ_[p])
    (h : ¬ (p : ℤ_[p]) ^ 2 ∣ X.trace ^ 2 - 4 * X.det) :
    ∃ v w, IsUnit (cyclicColumns X v w) := by
  have toDvd (z : ℤ_[p]) (hz : ¬ IsUnit z) : (p : ℤ_[p]) ∣ z :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hz)
  by_cases hc : IsUnit (X 1 0)
  · exact ⟨1, 0, (Matrix.isUnit_iff_isUnit_det _).mpr
      (by simpa [cyclicColumns, det_fin_two] using hc)⟩
  by_cases hb : IsUnit (X 0 1)
  · exact ⟨0, 1, (Matrix.isUnit_iff_isUnit_det _).mpr
      (by simpa [cyclicColumns, det_fin_two] using hb.neg)⟩
  have hd : IsUnit (X 1 1 - X 0 0) := by
    by_contra hd
    obtain ⟨b, hb'⟩ := toDvd _ hb
    obtain ⟨c, hc'⟩ := toDvd _ hc
    obtain ⟨d, hd'⟩ := toDvd _ hd
    apply h
    refine ⟨d ^ 2 + 4 * b * c, ?_⟩
    rw [trace_fin_two, det_fin_two]
    calc
      _ = (X 1 1 - X 0 0) ^ 2 + 4 * X 0 1 * X 1 0 := by ring
      _ = _ := by rw [hb', hc', hd']; ring
  refine ⟨1, 1, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
  have hr (z : ℤ_[p]) (hz : ¬ IsUnit z) : PadicInt.toZModPow 1 z = 0 := by
    by_contra hn
    exact hz ((unit_iff_red_ne_zero _).mpr hn)
  rw [unit_iff_red_ne_zero] at hd ⊢
  simpa [cyclicColumns, det_fin_two, map_sub, map_add, hr _ hb, hr _ hc] using hd

/-- The companion matrix for a trace-one quadratic generator of determinant
`d`. In a cyclic basis the second column follows from Cayley–Hamilton. -/
theorem cyclicColumns_companion {A : Type*} [CommRing A] (X : Mat A)
    (h : X.trace = 1) (v w : A) :
    X * cyclicColumns X v w = cyclicColumns X v w * !![0, -X.det; 1, 1] := by
  have h11 : X 1 1 = 1 - X 0 0 := by rw [trace_fin_two] at h; linear_combination h
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicColumns, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, h11] <;> ring

/-- Tex 9136–9139: there is exactly one integral conjugacy class of the
maximal quadratic generator with the given trace and determinant in the
maximal split order. The displayed companion matrix realizes it. -/
theorem maximal_split_normalForm {p : ℕ} [Fact p.Prime] (X : Mat ℤ_[p]) {d : ℤ_[p]}
    (htr : X.trace = 1) (hdet : X.det = d) (hd : ¬ (p : ℤ_[p]) ^ 2 ∣ 1 - 4 * d) :
    UnitConj (!![0, -d; 1, 1] : Mat ℤ_[p]) X := by
  obtain ⟨v, w, hu⟩ := exists_cyclicColumns X (by simpa [htr, hdet] using hd)
  exact ⟨hu.unit, by rw [hu.unit_spec, ← hdet, cyclicColumns_companion X htr]⟩

end ZInQ.Manuscript.RC.O7Orbits
