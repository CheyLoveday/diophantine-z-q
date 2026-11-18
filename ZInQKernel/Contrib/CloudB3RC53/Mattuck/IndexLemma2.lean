import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Odd

/-!
# Mattuck at `p = 2`, part 1: the index lemma with torsion, and the lattice reduction

Manuscript `diophantine_zq.tex`, tex 4551–4556 (the old Kummer row: "`E^{(h)}(K_w)^∧_2 ≅
ℤ₂^{d_w} ⊕` (finite `2`-primary torsion with two generators)", residual dimensions `(2, 2 + d_w)`).

* **`card_modN_mul_card_torsion`** (the Herbrand-quotient identity for doubling): for an
  abelian group `A` and a subgroup `B` of finite index,
  `|A/2A| · |B[2]| = |B/2B| · |A[2]|` (as `Nat.card`; no finiteness of the torsion needed).
  Proof by indices: `[A : 2B] = [A : 2A][2A : 2B] = [A : B][B : 2B]`, `[2A : 2B] = [A : B + A[2]]`
  (doubling is onto `2A`), and `[B + A[2] : B] = [A[2] : B[2]]`.
* **`card_modN_two_of_lattice`** (the lattice reduction): if `U ≤ A` has finite index, no
  `2`-torsion, and `|U/2U| = 2^d`, then `|A/2A| = |A[2]| · 2^d`; with `|A[2]| = 4`,
  `dim_{𝔽₂} A/2A = 2 + d` (`finrank_modN_two_of_lattice`).
* Specialized to `E(K_u)` (`kummerResidualDim_of_lattice`): with full rational `2`-torsion and a
  torsion-free finite-index subgroup `U` with `|U/2U| = 2^d`, `kummerResidualDim = 4 + d`, the
  table value `LocalCondition.dim .oldKummer d`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open IsDedekindDomain WeierstrassCurve

variable {A : Type*} [AddCommGroup A] (B : AddSubgroup A)

/-- `2B` as a subgroup of `A`. -/
abbrev twoSub : AddSubgroup A := B.map (dbl A)

theorem comap_dbl_twoSub : (twoSub B).comap (dbl A) = (dbl A).ker ⊔ B := by
  ext a
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hab⟩
    have hk : a - b ∈ (dbl A).ker := by
      rw [mem_ker_dbl, nsmul_sub]
      rw [show (2 • b : A) = dbl A b from rfl, hab]
      exact sub_self _
    have : a = (a - b) + b := by abel
    rw [this]
    exact AddSubgroup.add_mem_sup hk hb
  · intro h
    obtain ⟨t, ht, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp h
    refine ⟨b, hb, ?_⟩
    change 2 • b = 2 • (t + b)
    rw [nsmul_add, (mem_ker_dbl t).mp ht, zero_add]

theorem addSubgroupOf_twoSub : (twoSub B).addSubgroupOf B = (dbl B).range := by
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, mem_range_dbl]
  constructor
  · rintro ⟨b, hb, hbx⟩
    exact ⟨⟨b, hb⟩, Subtype.ext hbx⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩

theorem relIndex_twoSub : (twoSub B).relIndex B = Nat.card (ModN B 2) := by
  rw [natCard_modN_two, AddSubgroup.relIndex, addSubgroupOf_twoSub]

theorem natCard_inf_ker : Nat.card ↥(B ⊓ (dbl A).ker) = Nat.card (dbl B).ker := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (AddSubgroup.mem_inf.mp x.2).1⟩,
        (mem_ker_dbl _).mpr (Subtype.ext ((mem_ker_dbl _).mp (AddSubgroup.mem_inf.mp x.2).2))⟩
      invFun := fun y => ⟨y.1.1, AddSubgroup.mem_inf.mpr ⟨y.1.2,
        (mem_ker_dbl _).mpr (congrArg Subtype.val ((mem_ker_dbl _).mp y.2))⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {B}

/-- **The index lemma with torsion** (Herbrand quotient of doubling): for `B ≤ A` of finite index,
`|A/2A| · |B[2]| = |B/2B| · |A[2]|`. PROVED. -/
theorem card_modN_mul_card_torsion [hB : B.FiniteIndex] :
    Nat.card (ModN A 2) * Nat.card (Submodule.torsionBy ℤ B 2) =
      Nat.card (ModN B 2) * Nat.card (Submodule.torsionBy ℤ A 2) := by
  set T := (dbl A).ker
  -- the indices
  have h1 := AddSubgroup.relIndex_mul_index (H := twoSub B) (K := B)
    (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.mp hx
      exact nsmul_mem hb 2)
  have h2 := AddSubgroup.relIndex_mul_index (H := twoSub B) (K := (dbl A).range)
    (AddSubgroup.map_le_range _ _)
  have h3 : (twoSub B).relIndex (dbl A).range = (T ⊔ B).index := by
    rw [← AddSubgroup.index_comap, comap_dbl_twoSub]
  have h4 := AddSubgroup.relIndex_mul_index (H := B) (K := T ⊔ B) le_sup_right
  have h5 : B.relIndex (T ⊔ B) = B.relIndex T := AddSubgroup.relIndex_sup_right T B
  have h6 := AddSubgroup.relIndex_mul_relIndex (⊥ : AddSubgroup A) (B ⊓ T) T bot_le inf_le_right
  rw [AddSubgroup.relIndex_bot_left, AddSubgroup.relIndex_bot_left,
    AddSubgroup.inf_relIndex_right] at h6
  rw [relIndex_twoSub] at h1
  rw [h3] at h2
  rw [h5] at h4
  rw [natCard_modN_two (A := A), natCard_torsionBy_two (A := A), natCard_torsionBy_two (A := B),
    ← natCard_inf_ker, ← h6]
  -- `b · i = j · a`, `r · j = i`, `i ≠ 0`
  have hi : B.index ≠ 0 := hB.index_ne_zero
  have hj : (T ⊔ B).index ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h4; exact hi h4.symm
  have key : Nat.card (ModN B 2) * B.relIndex T = (dbl A).range.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hj)
    rw [mul_assoc, h4, h1, ← h2, mul_comm]
  rw [← key]
  ring

/-- **The lattice reduction**: if `U ≤ A` has finite index, no `2`-torsion and `|U/2U| = 2^d`, then
`|A/2A| = |A[2]| · 2^d`. PROVED. -/
theorem card_modN_two_of_lattice (U : AddSubgroup A) [U.FiniteIndex]
    (hU : ∀ u ∈ U, 2 • u = 0 → u = 0) {d : ℕ} (hd : Nat.card (ModN U 2) = 2 ^ d) :
    Nat.card (ModN A 2) = Nat.card (Submodule.torsionBy ℤ A 2) * 2 ^ d := by
  have h := card_modN_mul_card_torsion (A := A) (B := U)
  have h1 : Nat.card (Submodule.torsionBy ℤ U 2) = 1 := by
    rw [natCard_torsionBy_two, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨0⟩⟩
    have hx : x = 0 := Subtype.ext (Subtype.ext (hU _ x.1.2 (congrArg Subtype.val
      ((mem_ker_dbl _).mp x.2))))
    have hy : y = 0 := Subtype.ext (Subtype.ext (hU _ y.1.2 (congrArg Subtype.val
      ((mem_ker_dbl _).mp y.2))))
    rw [hx, hy]
  rw [h1, mul_one, hd] at h
  rw [h, mul_comm]

theorem finrank_eq_of_card_pow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}
    (h : Nat.card V = 2 ^ n) : Module.finrank (ZMod 2) V = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have hH := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [h, Nat.card_zmod] at hH
  exact (Nat.pow_right_injective le_rfl hH).symm

/-- **`dim A/2A = 2 + d`** for `|A[2]| = 4` and a torsion-free finite-index `U` with
`|U/2U| = 2^d`. PROVED. -/
theorem finrank_modN_two_of_lattice (U : AddSubgroup A) [U.FiniteIndex]
    (hU : ∀ u ∈ U, 2 • u = 0 → u = 0) {d : ℕ} (hd : Nat.card (ModN U 2) = 2 ^ d)
    (h4 : Nat.card (Submodule.torsionBy ℤ A 2) = 4) :
    Module.finrank (ZMod 2) (ModN A 2) = 2 + d := by
  apply finrank_eq_of_card_pow
  rw [card_modN_two_of_lattice U hU hd, h4, pow_add]
  norm_num

/-- **The lattice reduction, as a node** (tex 4551–4556): for every abelian group `A` with
`|A[2]| = 4` and every finite-index subgroup `U` without `2`-torsion with `|U/2U| = 2^d`,
`dim_{𝔽₂} A/2A = 2 + d`. Kind: PROVED. -/
def LatticeReduction : Prop :=
  ∀ (A : Type) [AddCommGroup A] (U : AddSubgroup A), U.FiniteIndex →
    (∀ u ∈ U, 2 • u = 0 → u = 0) → ∀ d : ℕ, Nat.card (ModN U 2) = 2 ^ d →
      Nat.card (Submodule.torsionBy ℤ A 2) = 4 → Module.finrank (ZMod 2) (ModN A 2) = 2 + d

theorem latticeReduction_proof : LatticeReduction := fun _ _ U _ hU _ hd h4 =>
  finrank_modN_two_of_lattice U hU hd h4

/-! ### On `E(K_u)` -/

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] (u : HeightOneSpectrum R)
  (C : WeierstrassCurve (u.adicCompletionIntegers F))

open scoped Classical in
/-- **The old Kummer row from a lattice** (tex 4551–4556): with full rational `2`-torsion and a
finite-index subgroup `U ≤ E(K_u)` without `2`-torsion with `|U/2U| = 2^d`,
`kummerResidualDim = 4 + d = LocalCondition.dim .oldKummer d`. PROVED. -/
theorem kummerResidualDim_of_lattice
    (U : AddSubgroup (C.baseChange (u.adicCompletion F)).toAffine.Point) [U.FiniteIndex]
    (hU : ∀ P ∈ U, 2 • P = 0 → P = 0) {d : ℕ} (hd : Nat.card (ModN U 2) = 2 ^ d)
    (h4 : Nat.card (Submodule.torsionBy ℤ (C.baseChange (u.adicCompletion F)).toAffine.Point 2) =
      4) :
    kummerResidualDim u C = ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer d := by
  rw [kummerResidualDim, finrankTwoTorsion_eq_two h4, finrank_modN_two_of_lattice U hU hd h4]
  change 2 + (2 + d) = 4 + d
  omega

end ZInQ.Contrib.CloudB3RC53.Mattuck
