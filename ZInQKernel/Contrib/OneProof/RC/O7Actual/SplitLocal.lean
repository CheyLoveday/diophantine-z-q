import ZInQKernel.Contrib.OneProof.RC.LocalWeights.LevelSupport
import Mathlib.FieldTheory.Finite.GaloisField

/-! A rank-one integral projector in the split Eichler order is classified
by the summand it selects on the cyclic level quotient (tex 9136–9146). -/

noncomputable section

open Matrix

namespace ZInQ.Manuscript.RC.O7Actual

open LocalWeights

variable {p e : ℕ} [Fact p.Prime]

/-- The projector with zero action on the cyclic level quotient. -/
def firstProjector (p e : ℕ) [Fact p.Prime] : eichler p e :=
  ⟨!![1, 0; 0, 0], by change (p : ℤ_[p]) ^ e ∣ (0 : ℤ_[p]); exact dvd_zero _⟩

/-- Tex 9140–9146, on-the-spot (c): an explicit change of integral basis
diagonalizes the projector whose level action is zero, including at two. -/
theorem projector_first_normalForm (he : 0 < e) (P : eichler p e)
    (hP : P * P = P) (htr : P.val.trace = 1) (hlev : level p e P = 0) :
    ∃ u : (eichler p e)ˣ, P = (u : eichler p e) * firstProjector p e * ↑u⁻¹ := by
  let a := P.val 0 0
  let b := P.val 0 1
  let c := P.val 1 0
  let d := P.val 1 1
  have had : a + d = 1 := by simpa only [a, d, Matrix.trace_fin_two] using htr
  have ha : IsUnit a := by
    have hd : PadicInt.toZModPow 1 d = 0 := by
      rw [← PadicInt.cast_toZModPow 1 e he d]
      change ZMod.cast (level p e P) = _
      rw [hlev, ZMod.cast_zero]
    rw [unit_iff_red_ne_zero, show a = 1 - d by linear_combination had, map_sub, hd]
    have : Fact (1 < p ^ 1) := ⟨by simpa using (Fact.out : p.Prime).one_lt⟩
    simpa only [map_one, sub_zero] using (one_ne_zero : (1 : ZMod (p ^ 1)) ≠ 0)
  have haa : a * a + b * c = a := by
    have h := congrArg (fun q : eichler p e => q.val 0 0) hP
    change (P.val * P.val) 0 0 = P.val 0 0 at h
    simpa only [a, b, c, Matrix.mul_apply, Fin.sum_univ_two] using
      h
  let r : ℤ_[p] := ↑ha.unit⁻¹
  have hra : r * a = 1 := by
    rw [← ha.unit_spec]
    exact Units.inv_mul ha.unit
  let U : eichler p e := ⟨!![a, -b; c, a], P.prop⟩
  let V : eichler p e := ⟨!![r*a, r*b; -(r*c), r*a], by
    change (p : ℤ_[p]) ^ e ∣ -(r * c)
    exact dvd_neg.mpr (dvd_mul_of_dvd_right P.prop r)⟩
  have huv : U * V = 1 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination r * haa + hra
    · ring
    · ring
    · linear_combination r * haa + hra
  have hvu : V * U = 1 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination r * haa + hra
    · ring
    · ring
    · linear_combination r * haa + hra
  let u : (eichler p e)ˣ := ⟨U, V, huv, hvu⟩
  have hPU : P * U = U * firstProjector p e := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [U, firstProjector, Matrix.mul_apply, Fin.sum_univ_two]
    · exact haa
    · ring
    · change c * a + d * c = c
      linear_combination c * had
    · change -(c * b) + d * a = 0
      linear_combination a * had - haa
  refine ⟨u, ?_⟩
  change P = U * firstProjector p e * V
  rw [← hPU, mul_assoc, huv, mul_one]

/-- The two normal forms are distinct under order-unit conjugation: the
cyclic level quotient is commutative and sees zero versus one. -/
theorem projector_forms_distinct (he : 0 < e) (u : (eichler p e)ˣ) :
    (u : eichler p e) * firstProjector p e * ↑u⁻¹ ≠ 1 - firstProjector p e := by
  intro h
  have hh := congrArg (level p e) h
  have hzero : level p e (firstProjector p e) = 0 := by
    change PadicInt.toZModPow e 0 = 0
    exact map_zero _
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt⟩
  simp [map_mul, map_sub, hzero] at hh

/-- Tex 9140–9146: any trace-one projector has one of the two normal forms.
For the projectors of the split integral generator, the level premise is
`LocalWeights.projector_level`, including at the dyadic prime. -/
theorem projector_two_normalForms (he : 0 < e) (P : eichler p e)
    (hP : P * P = P) (htr : P.val.trace = 1)
    (hlev : level p e P = 0 ∨ level p e P = 1) :
    ∃ u : (eichler p e)ˣ, P = (u : eichler p e) * firstProjector p e * ↑u⁻¹ ∨
      P = (u : eichler p e) * (1 - firstProjector p e) * ↑u⁻¹ := by
  rcases hlev with hlev | hlev
  · obtain ⟨u, hu⟩ := projector_first_normalForm he P hP htr hlev
    exact ⟨u, Or.inl hu⟩
  · have hh : (1 - P) * (1 - P) = 1 - P := by
      rw [sub_mul, mul_sub, mul_sub, hP]
      simp
    have ht : (1 - P : eichler p e).val.trace = 1 := by
      change ((1 : Mat ℤ_[p]) - P.val).trace = 1
      rw [Matrix.trace_sub, htr, Matrix.trace_one, Fintype.card_fin]
      norm_num
    obtain ⟨u, hu⟩ := projector_first_normalForm he (1 - P) hh ht (by simp [hlev])
    refine ⟨u, Or.inr ?_⟩
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, ← hu, sub_sub_cancel]

/-- Apply the split calculation to the actual integral spectral projector
used for the local weight. Its selected root has level image one. -/
theorem levelRoot_projector_normalForm (he : 0 < e) (y : eichler p e)
    (hy : y.val.trace = 1) {a : ℤ_[p]} (ha : LevelRoot y a) :
    ∃ u : (eichler p e)ˣ,
      projector ha.2.1 y = (u : eichler p e) * (1 - firstProjector p e) * ↑u⁻¹ := by
  have htr : (projector ha.2.1 y).val.trace = 1 := by
    change trace ((↑ha.2.1.unit⁻¹ : ℤ_[p]) •
      (y.val - algebraMap ℤ_[p] (Mat ℤ_[p]) (1 - a))) = 1
    rw [Matrix.trace_smul, Matrix.trace_sub, hy, Algebra.algebraMap_eq_smul_one,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    change (↑ha.2.1.unit⁻¹ : ℤ_[p]) * (1 - (1 - a) * 2) = 1
    rw [show 1 - (1 - a) * 2 = 2 * a - 1 by ring]
    calc
      _ = (↑ha.2.1.unit⁻¹ : ℤ_[p]) * (ha.2.1.unit : ℤ_[p]) :=
        congrArg (fun v : ℤ_[p] => (↑ha.2.1.unit⁻¹ : ℤ_[p]) * v) ha.2.1.unit_spec.symm
      _ = 1 := Units.inv_mul ha.2.1.unit
  obtain ⟨u, h | h⟩ := projector_two_normalForms he (projector ha.2.1 y)
    (projector_idempotent y hy ha.1 ha.2.1) htr (Or.inr (projector_level y ha).1)
  · have hu := congrArg (level p e) h
    have hz : level p e (firstProjector p e) = 0 :=
      map_zero (PadicInt.toZModPow e)
    have : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt⟩
    simp [map_mul, hz, (projector_level y ha).1] at hu
  · exact ⟨u, h⟩

/-- Tex 9146–9148: once the two residue fields are identified with the
quadratic finite field, there are exactly two residue embeddings. -/
theorem card_residue_embeddings (ell : ℕ) [Fact ell.Prime] :
    Nat.card (GaloisField ell 2 →ₐ[ZMod ell] GaloisField ell 2) = 2 :=
  (FiniteField.natCard_algHom_of_finrank_dvd (dvd_refl _)).trans
    (GaloisField.finrank ell (by decide))

end ZInQ.Manuscript.RC.O7Actual
