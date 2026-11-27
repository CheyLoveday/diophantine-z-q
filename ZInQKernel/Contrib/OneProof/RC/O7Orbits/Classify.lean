import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Coordinates
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.MaximalSplit
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.LocalArithmetic

/-! Read the local conjugacy criteria on the actual affine generators. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open Eichler Visibility Matrix LocalWeights

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- Exchanging the two distinct residues flips their orientation bit. -/
theorem residueBit_swap_ne {C : Type*} [Finite C] {x y : C} (h : x ≠ y) :
    residueBit x y ≠ residueBit y x := by
  unfold residueBit
  let _ : Fintype C := Fintype.ofFinite C
  have h' : Fintype.equivFin C x ≠ Fintype.equivFin C y :=
    fun e => h ((Fintype.equivFin C).injective e)
  rcases lt_or_gt_of_ne h' with hlt | hgt
  · simp [hlt, not_lt_of_gt hlt]
  · simp [hgt, not_lt_of_gt hgt]

/-- The level quotient sees exactly the two roots of the chosen split
affine polynomial. -/
theorem split_level_residue_cases {p e : ℕ} [Fact p.Prime] (he : 0 < e)
    (Y : eichler p e) (ht : Y.val.trace = 1) {a : ℤ_[p]} (hu : IsUnit (2 * a - 1))
    (hh : a ^ 2 - a + Y.val.det = 0) :
    level p e Y = PadicInt.toZModPow e a ∨
      level p e Y = PadicInt.toZModPow e (1 - a) := by
  obtain ⟨b, hb⟩ := (splitSupport_selected he Y ht).mp ⟨a, hh, hu⟩
  have hf : (b - a) * (b + a - 1) = 0 := by linear_combination hb.1 - hh
  rcases mul_eq_zero.mp hf with hb' | hb'
  · exact Or.inl (by rw [← sub_eq_zero.mp hb', hb.2.2])
  · have hb'' : b = 1 - a := by linear_combination hb'
    exact Or.inr (by rw [← hb'', hb.2.2])

/-- At positive level the bit is a complete test for local order-unit
conjugacy of the affine generators. -/
theorem split_level_bit_iff {p e : ℕ} [Fact p.Prime] (he : 0 < e)
    (X Y : eichler p e) {a : ℤ_[p]} (hu : IsUnit (2 * a - 1))
    (hx : X.val.trace = 1) (hy : Y.val.trace = 1)
    (hax : a ^ 2 - a + X.val.det = 0) (hay : a ^ 2 - a + Y.val.det = 0) :
    UnitConj X Y ↔ residueBit (level p e X) (1 - level p e X) =
      residueBit (level p e Y) (1 - level p e Y) := by
  rw [split_level_conj_iff he X Y hu hx hy hax hay]
  refine ⟨fun h => by rw [h], ?_⟩
  let r := PadicInt.toZModPow e a
  have hr : PadicInt.toZModPow e (1 - a) = 1 - r := by simp [r]
  have hn : r ≠ 1 - r := by
    obtain ⟨x, y, _, _, _, _, hx', hy', hne⟩ := split_level_labels he a hu
    rwa [hx', hy', hr] at hne
  intro h
  rcases split_level_residue_cases he X hx hu hax with hX | hX <;>
    rcases split_level_residue_cases he Y hy hu hay with hY | hY
  · rw [hX, hY]
  · rw [hX, hY, hr, sub_sub_cancel] at h
    exact (residueBit_swap_ne hn h).elim
  · rw [hX, hY, hr, sub_sub_cancel] at h
    exact (residueBit_swap_ne hn h.symm).elim
  · rw [hX, hY]

/-- The division bit is a complete test for local order-unit conjugacy of
the trace-zero roots. -/
theorem division_bit_iff {p : ℕ} [Fact p.Prime] [Fact (p % 4 = 3)]
    (X Y : LocalDivision.order p) (hsq : X * X = Y * Y)
    (hx : LocalDivision.red X ≠ 0) :
    UnitConj X Y ↔ residueBit (LocalDivision.red X) (-LocalDivision.red X) =
      residueBit (LocalDivision.red Y) (-LocalDivision.red Y) := by
  rw [division_conj_iff_red X Y hsq hx]
  refine ⟨fun h => by rw [h], ?_⟩
  intro h
  obtain ⟨hne, hy⟩ := division_labels X hx
  rcases hy Y hsq.symm with hY | hY
  · exact hY.symm
  · have hred : (LocalDivision.red (p := p)) (-X) = -LocalDivision.red X :=
      (LocalDivision.red (p := p)).map_neg X
    rw [hred] at hne hY
    rw [hY, neg_neg] at h
    exact (residueBit_swap_ne hne h.symm).elim

/-- On actual support, the positive-level coordinate detects precisely
the conjugacy class of the affine generator in the split order chart. -/
theorem actual_level_bit_iff (s : O7Actual.StageAt O N M hN m) {D c : ℤ}
    (H : SupportBridge s D) (hc : disc s D = 1 - 4 * c) (hd : disc s D ≠ 0)
    (j : Fin N.primeFactors.card)
    (he : 0 < N.factorization (levelPrime N j).val)
    (a : ℤ_[(levelPrime N j).val]) (ha : a ^ 2 - a + (c : ℤ_[(levelPrime N j).val]) = 0)
    (hu : IsUnit (2 * a - 1))
    (z w : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (y : ActualSupport s D w) :
    let p := levelPrime N j
    let e := splitOrderChart s p (levelPrime_ne_detecting s j)
    UnitConj (e (localGenerator s H z x p)) (e (localGenerator s H w y p)) ↔
      generatorOrientation s H z x j.castSucc = generatorOrientation s H w y j.castSucc := by
  let p := levelPrime N j
  let hp := levelPrime_ne_detecting s j
  obtain ⟨htX, hdX⟩ := split_generator_trace_det s H hc hd p hp z x
  obtain ⟨htY, hdY⟩ := split_generator_trace_det s H hc hd p hp w y
  simpa only [generatorOrientation, Fin.lastCases_castSucc] using
    split_level_bit_iff he _ _ hu htX htY (hdX.symm ▸ ha) (hdY.symm ▸ ha)

/-- The root in the actual division-order chart. -/
def divisionGenerator (s : O7Actual.StageAt O N M hN m) {D : ℤ}
    (H : SupportBridge s D) (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    LocalDivision.order s.ell :=
  let p : Adelic.Prime := ⟨s.ell, Fact.out⟩
  divisionOrderChart s (2 * localGenerator s H z x p - 1)

theorem divisionGenerator_square (s : O7Actual.StageAt O N M hN m) {D : ℤ}
    (H : SupportBridge s D) (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    divisionGenerator s H z x * divisionGenerator s H z x =
      (disc s D : LocalDivision.order s.ell) := by
  let p : Adelic.Prime := ⟨s.ell, Fact.out⟩
  let a := 2 * localGenerator s H z x p - 1
  let f := divisionOrderChart s
  change f a * f a = _
  rw [← map_mul f, ← pow_two]
  exact (congrArg f (localGenerator_square s H z x p)).trans (map_intCast f _)

theorem division_red_ne_zero_of_sq {p : ℕ} [Fact p.Prime] [Fact (p % 4 = 3)]
    {d : ℤ} (hd : (d : ZMod p) ≠ 0) {X : LocalDivision.order p}
    (hX : X * X = (d : LocalDivision.order p)) :
    LocalDivision.red X ≠ 0 := by
  intro h
  let f : LocalDivision.order p →+* GaloisField p 2 := LocalDivision.red
  have he := congrArg f hX
  have he' : (d : GaloisField p 2) = 0 := by
    rw [map_mul f, map_intCast f] at he
    change f X = 0 at h
    rw [h, zero_mul] at he
    exact he.symm
  exact hd ((CharP.intCast_eq_zero_iff (ZMod p) p d).mpr
    ((CharP.intCast_eq_zero_iff (GaloisField p 2) p d).mp he'))

theorem generatorOrientation_last (s : O7Actual.StageAt O N M hN m) {D : ℤ}
    (H : SupportBridge s D) (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
    let r := LocalDivision.red (divisionGenerator s H z x)
    generatorOrientation s H z x (Fin.last _) = residueBit r (-r) := by
  simp only [generatorOrientation, Fin.lastCases_last, divisionGenerator]

/-- The actual division coordinate detects precisely the conjugacy class
of the local square root in the maximal division order. -/
theorem actual_division_bit_iff (s : O7Actual.StageAt O N M hN m) {D : ℤ}
    (H : SupportBridge s D) (hd : (disc s D : ZMod s.ell) ≠ 0)
    (z w : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (y : ActualSupport s D w) :
    UnitConj (divisionGenerator s H z x) (divisionGenerator s H w y) ↔
      generatorOrientation s H z x (Fin.last _) = generatorOrientation s H w y (Fin.last _) := by
  let _ : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  rw [generatorOrientation_last, generatorOrientation_last]
  have hx := divisionGenerator_square s H z x
  have hy := divisionGenerator_square s H w y
  exact division_bit_iff _ _ (hx.trans hy.symm) (division_red_ne_zero_of_sq hd hx)

/-- At any split prime away from the level, every actual local support
generator is conjugate to the same integral companion matrix. -/
theorem actual_maximal_split_normalForm (s : O7Actual.StageAt O N M hN m)
    {D c : ℤ} (H : SupportBridge s D) (hc : disc s D = 1 - 4 * c)
    (hd : Squarefree (disc s D)) (p : Adelic.Prime) (hp : p.val ≠ s.ell)
    (haway : ¬ p.val ∣ N) (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    ∃ C : eichler p.val (N.factorization p.val),
      C.val = (!![0, -(c : ℤ_[p.val]); 1, 1] : Mat ℤ_[p.val]) ∧
      UnitConj C (splitOrderChart s p hp (localGenerator s H z x p)) := by
  let Y := splitOrderChart s p hp (localGenerator s H z x p)
  obtain ⟨ht, he⟩ := split_generator_trace_det s H hc hd.ne_zero p hp z x
  have hdisc : ¬ (p.val : ℤ_[p.val]) ^ 2 ∣ (1 - 4 * (c : ℤ_[p.val])) := by
    have hh := padic_prime_sq_not_dvd (p := p.val) hd
    rw [hc, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat] at hh
    exact hh
  let A : Mat ℤ_[p.val] := !![0, -(c : ℤ_[p.val]); 1, 1]
  obtain ⟨u, hu⟩ : UnitConj A Y.val := maximal_split_normalForm _ ht he hdisc
  have hE : eichler p.val (N.factorization p.val) = ⊤ := by
    rw [Nat.factorization_eq_zero_of_not_dvd haway, eichler_zero]
  let e := (Subalgebra.equivOfEq _ _ hE).trans Subalgebra.topEquiv
  refine ⟨e.symm A, rfl, Units.map e.symm.toMonoidHom u, ?_⟩
  apply Subtype.ext
  exact hu

end ZInQ.Manuscript.RC.O7Orbits
