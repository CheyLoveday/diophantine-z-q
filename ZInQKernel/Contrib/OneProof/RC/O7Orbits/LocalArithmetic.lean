import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Local
import ZInQKernel.RouteK.Selmer.PadicSquare

/-! Realize the local roots used by the two conjugacy tests, with the
affine generator at two and a nonzero reduced root at the division place. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open LocalWeights

/-- A simple residue root of the affine quadratic polynomial lifts
with an integral unit gap between the two roots. -/
theorem split_branch_of_residue {p : ℕ} [Fact p.Prime] {c : ℤ}
    {a : ZMod (p ^ 1)} (ha : a ^ 2 - a + (c : ZMod (p ^ 1)) = 0)
    (hu : 2 * a - 1 ≠ 0) :
    ∃ b : ℤ_[p], b ^ 2 - b + (c : ℤ_[p]) = 0 ∧ IsUnit (2 * b - 1) := by
  obtain ⟨r, hr⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) 1) a
  refine (lift_branch (a := r) (d := (c : ℤ_[p])) ?_ ?_).imp (fun _ hb => ⟨hb.1, hb.2.2⟩)
  · rw [unit_iff_red_ne_zero, map_sub, map_mul, map_ofNat, map_one, hr]
    exact hu
  · simpa only [map_sub, map_add, map_pow, map_intCast, hr] using ha

/-- Tex 9140–9146: at an odd split level prime, the two affine roots are
integral and their difference is a unit. -/
theorem split_branch_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {c : ℤ} (hs : legendreSym p (1 - 4 * c) = 1) :
    ∃ a : ℤ_[p], a ^ 2 - a + (c : ℤ_[p]) = 0 ∧ IsUnit (2 * a - 1) := by
  have hn : ((1 - 4 * c : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have := (legendreSym.eq_zero_iff p _).mpr h
    rw [hs] at this
    norm_num at this
  have hsq := (legendreSym.eq_one_iff p hn).mp hs
  have hn' : ((1 - 4 * c : ℤ) : ZMod (p ^ 1)) ≠ 0 := by rwa [pow_one]
  have hsq' : IsSquare ((1 - 4 * c : ℤ) : ZMod (p ^ 1)) := by rwa [pow_one]
  let _ : Fact ((p ^ 1).Prime) := ⟨by simpa only [pow_one] using (Fact.out : p.Prime)⟩
  obtain ⟨b, hb⟩ := hsq'
  have hb0 : b ≠ 0 := fun h => hn' (by rw [hb, h, zero_mul])
  have h2 : (2 : ZMod (p ^ 1)) ≠ 0 := by
    intro h
    have hd : p ^ 1 ∣ 2 := (CharP.cast_eq_zero_iff (ZMod (p ^ 1)) (p ^ 1) 2).mp h
    rw [pow_one] at hd
    exact hp (le_antisymm (Nat.le_of_dvd (by decide) hd) (Fact.out : p.Prime).two_le)
  let a := (1 + b) / 2
  have ha : 2 * a - 1 = b := by dsimp [a]; field_simp; ring
  apply split_branch_of_residue (a := a) ?_ (ha.trans_ne hb0)
  have h4 : (4 : ZMod (p ^ 1)) ≠ 0 := by
    rw [show (4 : ZMod (p ^ 1)) = 2 * 2 by ring]
    exact mul_ne_zero h2 h2
  apply mul_left_cancel₀ h4
  push_cast at hb
  linear_combination (2 * a - 1 + b) * ha + (Eq.symm hb)

/-- Tex 9144–9146: if the discriminant is 1 modulo 8, the affine
equation already has the simple root 0 modulo 2. -/
theorem split_branch_two {c : ℤ} (h : (1 - 4 * c) % 8 = 1) :
    ∃ a : ℤ_[2], a ^ 2 - a + (c : ℤ_[2]) = 0 ∧ IsUnit (2 * a - 1) := by
  have hc : (2 : ℤ) ∣ c := ⟨c / 2, by omega⟩
  apply split_branch_of_residue (a := (0 : ZMod (2 ^ 1)))
  · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd c 2).mpr hc
  · decide

/-- Tex 9146–9148: for an inert discriminant at the actual odd division
prime, a trace-zero square root exists in the maximal order and has
nonzero residue. It and its negative realize the two labels. -/
theorem division_root_exists {p : ℕ} [Fact p.Prime] [Fact (p % 4 = 3)]
    {d : ℤ} (hd : legendreSym p d = -1) :
    ∃ x : LocalDivision.order p, LocalDivision.tr x.val = 0 ∧
      x * x = (d : LocalDivision.order p) ∧ LocalDivision.red x ≠ 0 := by
  have hp : p ≠ 2 := by have := (Fact.out : p % 4 = 3); omega
  have hneg : legendreSym p (-1) = -1 :=
    (legendreSym.eq_neg_one_iff p).mpr
      (by simpa using LocalDivision.neg_one_nonsquare (Fact.out : p % 4 = 3))
  have hs : legendreSym p (-d) = 1 := by
    rw [neg_eq_neg_one_mul, legendreSym.mul, hneg, hd]
    norm_num
  have hn : ((-d : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have := (legendreSym.eq_zero_iff p _).mpr h
    rw [hs] at this
    norm_num at this
  obtain ⟨r, hr⟩ := ZInQ.RouteK.Selmer.isSquare_intCast_of_residue hp
    (fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))
    ((legendreSym.eq_one_iff p hn).mp hs)
  have hnorm : ‖r‖ ≤ 1 := by
    have h := Padic.norm_int_le_one (p := p) (-d)
    rw [hr, norm_mul] at h
    nlinarith [norm_nonneg r]
  let t : ℤ_[p] := ⟨r, hnorm⟩
  have ht : t * t = (-d : ℤ) := by
    apply Subtype.ext
    exact hr.symm
  let x : LocalDivision.IntegralD p := ⟨0, t, 0, 0⟩
  refine ⟨LocalDivision.orderEquiv x, ?_, ?_, ?_⟩
  · rw [LocalDivision.coe_orderEquiv, LocalDivision.tr_apply]
    change (2 : ℚ_[p]) * (↑(0 : ℤ_[p]) : ℚ_[p]) = 0
    simp
  · rw [← map_mul, ← map_intCast LocalDivision.orderEquiv]
    congr 1
    simp only [x, QuaternionAlgebra.mk_mul_mk]
    apply QuaternionAlgebra.ext <;> simp
    rw [ht, Int.cast_neg, neg_neg]
  · intro hz
    have ht0 : PadicInt.toZMod t = 0 := by
      have hh := (LocalDivision.red_eq_zero_iff (LocalDivision.orderEquiv x)).mp hz
      simpa only [AlgEquiv.symm_apply_apply, x] using hh.2
    apply hn
    rw [← map_intCast PadicInt.toZMod, ← ht, map_mul, ht0, zero_mul]

end ZInQ.Manuscript.RC.O7Orbits
