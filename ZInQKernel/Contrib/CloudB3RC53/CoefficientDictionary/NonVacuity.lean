import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-!
# The coefficient dictionary: the hypotheses are jointly satisfiable

A concrete `TypeData` (the alphabet `ZMod 2` of sign coordinates, conductor `4`) and, for every
type data, the zero reading satisfy every hypothesis of `coefficientRules_symb`: the fixed-`U`
factorization and primary isolation trivially, and the (O.12) reading because fresh good
representatives with the product labels exist (CRT and Dirichlet, `realizeNat`). So the
hypotheses of the dictionary are not contradictory. (PROVED.)
-/

namespace ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd Finset

/-- The sign type data: `L = ZMod 2`, `typ p = (p − 1)/2 mod 2`, conductor `4`. -/
noncomputable def signTypeData : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2)) where
  m := 4
  m_pos := by norm_num
  two_dvd := by norm_num
  typ p := ((p / 2 : ℕ) : ZMod 2)
  classes ℓ := by
    have hℓ : ℓ = 0 ∨ ℓ = 1 := by revert ℓ; decide
    rcases hℓ with rfl | rfl
    · refine ⟨1, isUnit_one, fun p _ hp => ?_⟩
      rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by simp, ZMod.natCast_eq_natCast_iff'] at hp
      rw [ZMod.natCast_eq_zero_iff_even]
      exact ⟨p / 4, by omega⟩
    · refine ⟨3, by decide, fun p _ hp => ?_⟩
      rw [show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) by simp, ZMod.natCast_eq_natCast_iff'] at hp
      rw [ZMod.natCast_eq_one_iff_odd]
      exact ⟨p / 4, by omega⟩
  sign _ _ _ := rfl

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- The zero reading satisfies the (O.12) reading, for every type data. -/
theorem o12Reading_zero (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ) :
    O12Reading T (fun _ => 0) ap B := by
  intro U p _ hUgood _ ℓ bq
  let ty : ℕ → L := fun i => if i < 2 then ℓ else T.typ p + ℓ
  let bitOld : ℕ → ℕ → ZMod 2 := fun i s =>
    if i = 0 then bq s
    else if i = 1 then (if s = p then bq s + 1 else bq s)
    else if i = 2 then (if s = p then 0 else legBit p s + bq s)
    else (if s = p then 1 else legBit p s + bq s)
  obtain ⟨x, -, hx, hold, -⟩ := realizeNat T U ∅ hUgood ty bitOld (fun _ _ => 0) 4
  refine ⟨x 0, x 1, x 2, x 3, 1, (hx 0 (by norm_num)).1, (hx 1 (by norm_num)).1,
    (hx 2 (by norm_num)).1, (hx 3 (by norm_num)).1, (hx 0 (by norm_num)).2.1,
    (hx 1 (by norm_num)).2.1, (hx 2 (by norm_num)).2.1, (hx 3 (by norm_num)).2.1,
    (hx 0 (by norm_num)).2.2.2, (hx 1 (by norm_num)).2.2.2, fun s hs => ?_, fun s hs hsp => ?_,
    ?_, (hx 2 (by norm_num)).2.2.2, (hx 3 (by norm_num)).2.2.2, fun s hs hsp => ⟨?_, ?_⟩, ?_,
    Or.inl rfl, by simp⟩
  · rw [hold 0 (by norm_num) s hs]; simp [bitOld]
  · rw [hold 1 (by norm_num) s hs]; simp [bitOld, hsp]
  · rw [hold 1 (by norm_num) p ‹p ∈ U›]; simp [bitOld]
  · rw [hold 2 (by norm_num) s hs]; simp [bitOld, hsp]
  · rw [hold 3 (by norm_num) s hs]; simp [bitOld, hsp]
  · rw [hold 3 (by norm_num) p ‹p ∈ U›, hold 2 (by norm_num) p ‹p ∈ U›]; simp [bitOld]

/-- **Non-vacuity** (PROVED): for the sign type data and the zero reading (with `a_p = 0`), every
hypothesis of `coefficientRules_symb` holds, so it applies. -/
theorem coefficientRules_symb_nonvacuous :
    CoefficientRules (AddMonoidHom.id (ZMod 2)) (symb signTypeData (fun _ => 0)) :=
  coefficientRules_symb signTypeData (fun _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl) (o12Reading_zero signTypeData _)
    (fun _ _ => ⟨0, rfl⟩) (fun _ _ _ _ _ _ _ _ _ => rfl)

end ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
