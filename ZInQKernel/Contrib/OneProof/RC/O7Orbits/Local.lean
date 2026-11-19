import ZInQKernel.Contrib.OneProof.RC.O7Actual.SplitLocal
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Residue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Conjugacy tests for the local image of the generator of the maximal
quadratic order (tex 9136–9148). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open Matrix LocalWeights O7Actual

/-- Integral conjugacy, with the intertwining equation in its equivalent
form without an inverse. -/
def UnitConj {A : Type*} [Monoid A] (x y : A) : Prop :=
  ∃ u : Aˣ, (u : A) * x = y * (u : A)

theorem unitConj_iff_level_of_projectors {p e : ℕ} [Fact p.Prime] (he : 0 < e)
    (P Q : eichler p e) (hP : P * P = P) (hQ : Q * Q = Q)
    (htP : P.val.trace = 1) (htQ : Q.val.trace = 1)
    (hlP : level p e P = 0 ∨ level p e P = 1)
    (hlQ : level p e Q = 0 ∨ level p e Q = 1) :
    UnitConj P Q ↔ level p e P = level p e Q := by
  constructor
  · rintro ⟨u, hu⟩
    apply ((u.isUnit.map (level p e)).mul_left_cancel)
    simpa only [map_mul, mul_comm (level p e Q)] using congrArg (level p e) hu
  · intro h
    let E := firstProjector p e
    have hE : level p e E = 0 := map_zero (PadicInt.toZModPow e)
    have hc (u : (eichler p e)ˣ) (Z : eichler p e) :
        level p e ((u : eichler p e) * Z * ↑u⁻¹) = level p e Z := by
      rw [map_mul, map_mul, mul_comm (level p e (u : eichler p e)), mul_assoc,
        ← map_mul, Units.mul_inv, map_one, mul_one]
    have assemble (Z : eichler p e) (u v : (eichler p e)ˣ)
        (hp : P = (u : eichler p e) * Z * ↑u⁻¹)
        (hq : Q = (v : eichler p e) * Z * ↑v⁻¹) : UnitConj P Q := by
      refine ⟨v * u⁻¹, ?_⟩
      rw [hp, hq]
      simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
    obtain ⟨u, hu | hu⟩ := projector_two_normalForms he P hP htP hlP
    all_goals obtain ⟨v, hv | hv⟩ := projector_two_normalForms he Q hQ htQ hlQ
    · exact assemble E u v hu hv
    · rw [hu, hv, hc, hc, map_sub, map_one, hE, sub_zero] at h
      have : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt⟩
      exact (zero_ne_one h).elim
    · rw [hu, hv, hc, hc, map_sub, map_one, hE, sub_zero] at h
      have : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt⟩
      exact (one_ne_zero h).elim
    · exact assemble (1 - E) u v hu hv

/-- A split level root with unit separation gives a trace-one projector;
the generator and projector determine one another integrally. -/
theorem projector_recovers {p e : ℕ} [Fact p.Prime] {a : ℤ_[p]}
    (u : IsUnit (2 * a - 1)) (y : eichler p e) (hy : y.val.trace = 1) :
    (projector u y).val.trace = 1 ∧
    y = (2 * a - 1) • projector u y + algebraMap ℤ_[p] (eichler p e) (1 - a) := by
  have hunit : (2 * a - 1) * (↑u.unit⁻¹ : ℤ_[p]) = 1 := by
    exact (congrArg (· * (↑u.unit⁻¹ : ℤ_[p])) u.unit_spec).symm.trans
      (Units.mul_inv u.unit)
  constructor
  · change trace ((↑u.unit⁻¹ : ℤ_[p]) •
      (y.val - algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a))) = 1
    rw [Matrix.trace_smul, Matrix.trace_sub, hy, Algebra.algebraMap_eq_smul_one,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    change (↑u.unit⁻¹ : ℤ_[p]) * (1 - (1 - a) * 2) = 1
    rw [show 1 - (1 - a) * 2 = 2 * a - 1 by ring, mul_comm, hunit]
  · rw [projector, smul_smul, hunit, one_smul, sub_add_cancel]

/-- On-the-spot (c), tex 9140–9146: equality of the level image of the
affine generator is equivalent to conjugacy by units of the split order. -/
theorem split_level_conj_iff {p e : ℕ} [Fact p.Prime] (he : 0 < e)
    (x y : eichler p e) {a : ℤ_[p]} (ha : IsUnit (2 * a - 1))
    (hx : x.val.trace = 1) (hy : y.val.trace = 1)
    (hax : a ^ 2 - a + x.val.det = 0) (hay : a ^ 2 - a + y.val.det = 0) :
    UnitConj x y ↔ level p e x = level p e y := by
  constructor
  · rintro ⟨v, hv⟩
    apply (v.isUnit.map (level p e)).mul_left_cancel
    simpa only [map_mul, mul_comm (level p e y)] using congrArg (level p e) hv
  · intro h
    let P := projector ha x
    let Q := projector ha y
    have rp := projector_recovers ha x hx
    have rq := projector_recovers ha y hy
    have hpq : level p e P = level p e Q := by
      simp only [P, Q, projector, Algebra.smul_def, map_mul, map_sub, h]
    have branches (w : eichler p e) (hw : w.val.trace = 1)
        (haw : a ^ 2 - a + w.val.det = 0) :
        level p e (projector ha w) = 0 ∨ level p e (projector ha w) = 1 := by
      obtain ⟨b, hb⟩ := (splitSupport_selected he w hw).mp ⟨a, haw, ha⟩
      have hfac : (b - a) * (b + a - 1) = 0 := by linear_combination hb.1 - haw
      rcases mul_eq_zero.mp hfac with hba | hba
      · have hba' := sub_eq_zero.mp hba
        subst b
        exact Or.inr (projector_level w hb).1
      · have hb' : b = 1 - a := by linear_combination hba
        left
        rw [projector, Algebra.smul_def, map_mul, map_sub, level_scalar, level_scalar, ← hb.2.2, hb',
          sub_self, mul_zero]
    obtain ⟨v, hv⟩ := (unitConj_iff_level_of_projectors he P Q
      (projector_idempotent x hx hax ha) (projector_idempotent y hy hay ha)
      rp.1 rq.1 (branches x hx hax) (branches y hy hay)).mpr hpq
    refine ⟨v, ?_⟩
    rw [rp.2, rq.2, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hv]
    exact congrArg (_ + ·) (Algebra.commutes (R := ℤ_[p]) (1 - a) (v : eichler p e)).symm

/-- The two level labels really occur: the two diagonal matrices have the
same trace and determinant and distinct images on the cyclic quotient. -/
theorem split_level_labels {p e : ℕ} [Fact p.Prime] (he : 0 < e)
    (a : ℤ_[p]) (ha : IsUnit (2 * a - 1)) :
    ∃ x y : eichler p e, x.val.trace = 1 ∧ y.val.trace = 1 ∧
      x.val.det = a * (1 - a) ∧ y.val.det = a * (1 - a) ∧
      level p e x = PadicInt.toZModPow e a ∧
      level p e y = PadicInt.toZModPow e (1 - a) ∧ level p e x ≠ level p e y := by
  let x : eichler p e := ⟨!![1 - a, 0; 0, a], dvd_zero _⟩
  let y : eichler p e := ⟨!![a, 0; 0, 1 - a], dvd_zero _⟩
  refine ⟨x, y, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [x, trace_fin_two]
  · simp [y, trace_fin_two]
  · simp [x, det_fin_two, mul_comm]
  · simp [y, det_fin_two]
  · intro h
    change PadicInt.toZModPow e a = PadicInt.toZModPow e (1 - a) at h
    have h' := congrArg (fun z : ZMod (p ^ e) => (ZMod.cast z : ZMod (p ^ 1))) h
    rw [PadicInt.cast_toZModPow 1 e he, PadicInt.cast_toZModPow 1 e he] at h'
    apply (unit_iff_red_ne_zero _).mp ha
    rw [show 2 * a - 1 = a - (1 - a) by ring, map_sub, h', sub_self]

/-- On-the-spot (c), tex 9146–9148: for two integral images of a common
square root with nonzero residue, equality of the reduced images is exactly
conjugacy by division-order units. -/
theorem division_conj_iff_red {p : ℕ} [Fact p.Prime] [Fact (p % 4 = 3)]
    (x y : LocalDivision.order p) (hsq : x * x = y * y)
    (hx : LocalDivision.red x ≠ 0) :
    UnitConj x y ↔ LocalDivision.red x = LocalDivision.red y := by
  constructor
  · rintro ⟨u, hu⟩
    apply (u.isUnit.map LocalDivision.red).mul_left_cancel
    simpa only [map_mul, mul_comm (LocalDivision.red y)] using congrArg LocalDivision.red hu
  · intro h
    have h2 : (2 : GaloisField p 2) ≠ 0 := by
      have hp : p ≠ 2 := by have := (Fact.out : p % 4 = 3); omega
      intro hz
      have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p 2) p 2).mp hz
      exact hp (le_antisymm (Nat.le_of_dvd (by decide) hd) (Fact.out : p.Prime).two_le)
    have hsum : IsUnit (x + y) := by
      by_contra hn
      have hz := (LocalDivision.red_nonunit (x + y)).mpr hn
      rw [map_add, ← h, ← two_mul] at hz
      exact (mul_ne_zero h2 hx) hz
    refine ⟨hsum.unit, ?_⟩
    rw [hsum.unit_spec, add_mul, mul_add, hsq, add_comm]

/-- At the division prime a nonzero reduced root and its negative give all
the labels. For an inert source these are the values of the two residue
embeddings on the square root. -/
theorem division_labels {p : ℕ} [Fact p.Prime] [Fact (p % 4 = 3)]
    (x : LocalDivision.order p) (hx : LocalDivision.red x ≠ 0) :
    LocalDivision.red (-x) ≠ LocalDivision.red x ∧
      ∀ y : LocalDivision.order p, y * y = x * x →
        LocalDivision.red y = LocalDivision.red x ∨
        LocalDivision.red y = LocalDivision.red (-x) := by
  have h2 : (2 : GaloisField p 2) ≠ 0 := by
    have hp : p ≠ 2 := by have := (Fact.out : p % 4 = 3); omega
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p 2) p 2).mp hz
    exact hp (le_antisymm (Nat.le_of_dvd (by decide) hd) (Fact.out : p.Prime).two_le)
  refine ⟨?_, ?_⟩
  · intro h
    rw [map_neg] at h
    exact (mul_ne_zero h2 hx) (by linear_combination -h)
  · intro y h
    rw [map_neg, ← sq_eq_sq_iff_eq_or_eq_neg, pow_two, pow_two, ← map_mul, ← map_mul, h]

end ZInQ.Manuscript.RC.O7Orbits
