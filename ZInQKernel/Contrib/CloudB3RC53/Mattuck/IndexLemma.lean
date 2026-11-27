import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finiteness

/-!
# Mattuck, odd residue characteristic, part 1: the index lemma

Manuscript `diophantine_zq.tex`, tex 4551–4556 (the old Kummer row of the table of tex 4561–4573:
"`E^{(h)}(K_w)^∧_2 ≅ ℤ₂^{d_w} ⊕ (finite 2-primary torsion with two generators)`").

Let `A` be an abelian group and `B ≤ A` a subgroup of finite index on which doubling is bijective
(`B` uniquely `2`-divisible). Then `|A / 2A| = |A[2]|`:

* `card_torsion_eq`: `a ↦ a + B` is a bijection `A[2] ≃ (A/B)[2]`;
* `index_range_eq`: `2A` is the preimage of `2(A/B)`, so `[A : 2A] = [A/B : 2(A/B)]`;
* in the finite group `A/B`, `[A/B : 2(A/B)] = |(A/B)[2]|` (Mathlib's `AddSubgroup.index_range`);
* **`card_modN_two_eq_card_torsionBy`**: `|ModN A 2| = |A[2]|`, and
  `finrank_modN_two_eq_of_card_torsionBy`: if `|A[2]| = 4` then `dim_{𝔽₂} A/2A = 2`.

This is the group theory behind Mattuck's theorem at an odd place `w`: `A = E(K_w)`, `B = E₁(K_w)`
the kernel of reduction (the formal group), uniquely `2`-divisible since `2` is a unit of `𝒪_w`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

variable {A : Type*} [AddCommGroup A] (B : AddSubgroup A)

/-- Doubling as an endomorphism. -/
abbrev dbl (G : Type*) [AddCommGroup G] : G →+ G := nsmulAddMonoidHom 2

theorem mem_ker_dbl {G : Type*} [AddCommGroup G] (g : G) : g ∈ (dbl G).ker ↔ 2 • g = 0 :=
  Iff.rfl

theorem mem_range_dbl {G : Type*} [AddCommGroup G] (g : G) :
    g ∈ (dbl G).range ↔ ∃ h : G, 2 • h = g :=
  Iff.rfl

variable {B}

/-- If doubling is surjective on `B`, every element of `B` is twice an element of `B`. -/
theorem exists_two_nsmul_of_mem (hB : Function.Bijective fun b : B => 2 • b) {a : A}
    (ha : a ∈ B) : ∃ b ∈ B, 2 • b = a := by
  obtain ⟨b, hb⟩ := hB.2 ⟨a, ha⟩
  exact ⟨b, b.2, congrArg Subtype.val hb⟩

/-- If doubling is injective on `B`, `B` has no `2`-torsion. -/
theorem eq_zero_of_mem_of_two_nsmul (hB : Function.Bijective fun b : B => 2 • b) {a : A}
    (ha : a ∈ B) (h2 : 2 • a = 0) : a = 0 := by
  have : (2 • (⟨a, ha⟩ : B)) = 2 • (0 : B) := Subtype.ext (by simpa using h2)
  exact congrArg Subtype.val (hB.1 this)

/-- **`2A` is the preimage of `2(A/B)`** when `B` is `2`-divisible. -/
theorem range_dbl_eq_comap (hB : Function.Bijective fun b : B => 2 • b) :
    (dbl A).range = (dbl (A ⧸ B)).range.comap (QuotientAddGroup.mk' B) := by
  ext a
  simp only [AddSubgroup.mem_comap, mem_range_dbl]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨QuotientAddGroup.mk' B h, by simp⟩
  · rintro ⟨q, hq⟩
    obtain ⟨h, rfl⟩ := QuotientAddGroup.mk'_surjective B q
    have hmem : a - 2 • h ∈ B := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub]
      change QuotientAddGroup.mk' B a - QuotientAddGroup.mk' B (2 • h) = 0
      rw [← hq, map_nsmul, sub_self]
    obtain ⟨b, -, hb⟩ := exists_two_nsmul_of_mem hB hmem
    exact ⟨h + b, by rw [nsmul_add, hb]; abel⟩

/-- **`[A : 2A] = [A/B : 2(A/B)]`.** -/
theorem index_range_eq (hB : Function.Bijective fun b : B => 2 • b) :
    (dbl A).range.index = (dbl (A ⧸ B)).range.index := by
  rw [range_dbl_eq_comap hB]
  exact AddSubgroup.index_comap_of_surjective _ (QuotientAddGroup.mk'_surjective B)

/-- **`A[2] ≃ (A/B)[2]`**, `a ↦ a + B`, when doubling is bijective on `B`. -/
theorem card_torsion_eq (hB : Function.Bijective fun b : B => 2 • b) :
    Nat.card (dbl A).ker = Nat.card (dbl (A ⧸ B)).ker := by
  let f : (dbl A).ker → (dbl (A ⧸ B)).ker := fun a =>
    ⟨QuotientAddGroup.mk' B a, by
      rw [mem_ker_dbl, ← map_nsmul, (mem_ker_dbl _).mp a.2, map_zero]⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun a a' h => ?_, fun q => ?_⟩)
  · have h' : QuotientAddGroup.mk' B (a : A) = QuotientAddGroup.mk' B a' :=
      congrArg Subtype.val h
    have hmem : (a : A) - a' ∈ B := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub]
      exact sub_eq_zero.mpr h'
    have h2 : 2 • ((a : A) - a') = 0 := by
      rw [nsmul_sub, (mem_ker_dbl _).mp a.2, (mem_ker_dbl _).mp a'.2, sub_zero]
    exact Subtype.ext (sub_eq_zero.mp (eq_zero_of_mem_of_two_nsmul hB hmem h2))
  · obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective B (q : A ⧸ B)
    have hmem : 2 • a ∈ B := by
      rw [← QuotientAddGroup.eq_zero_iff]
      have := (mem_ker_dbl _).mp q.2
      rw [← ha] at this
      simpa using this
    obtain ⟨b, hbB, hb⟩ := exists_two_nsmul_of_mem hB hmem
    refine ⟨⟨a - b, (mem_ker_dbl _).mpr (by rw [nsmul_sub, hb, sub_self])⟩, Subtype.ext ?_⟩
    change QuotientAddGroup.mk' B (a - b) = (q : A ⧸ B)
    have h0 : QuotientAddGroup.mk' B b = 0 := (QuotientAddGroup.eq_zero_iff b).mpr hbB
    rw [map_sub, ha, h0, sub_zero]

/-- **The index lemma** (tex 4551–4556): if `B ≤ A` has finite index and doubling is bijective on
`B`, then `[A : 2A] = |A[2]|`. PROVED. -/
theorem index_range_dbl_eq_card_ker [B.FiniteIndex] (hB : Function.Bijective fun b : B => 2 • b) :
    (dbl A).range.index = Nat.card (dbl A).ker := by
  have : Finite (A ⧸ B) := AddSubgroup.finite_quotient_of_finiteIndex
  rw [index_range_eq hB, card_torsion_eq hB]
  exact AddSubgroup.index_range

/-- The subgroup of `2`-multiples underlying `ModN A 2`. -/
theorem toAddSubgroup_range_lsmul :
    (LinearMap.range (LinearMap.lsmul ℤ A 2)).toAddSubgroup = (dbl A).range := by
  ext a
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.lsmul_apply,
    mem_range_dbl]
  exact ⟨fun ⟨h, hh⟩ => ⟨h, by rw [← hh, two_zsmul, two_nsmul]⟩,
    fun ⟨h, hh⟩ => ⟨h, by rw [← hh, two_zsmul, two_nsmul]⟩⟩

theorem natCard_modN_two : Nat.card (ModN A 2) = (dbl A).range.index := by
  rw [← toAddSubgroup_range_lsmul]
  rfl

/-- The `2`-torsion submodule `A[2]` is the kernel of doubling. -/
theorem natCard_torsionBy_two :
    Nat.card (Submodule.torsionBy ℤ A 2) = Nat.card (dbl A).ker := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  rw [Submodule.mem_torsionBy_iff, mem_ker_dbl, two_zsmul, two_nsmul]

/-- **`|A/2A| = |A[2]|`** for an abelian group with a finite-index uniquely `2`-divisible subgroup.
PROVED. -/
theorem card_modN_two_eq_card_torsionBy [B.FiniteIndex]
    (hB : Function.Bijective fun b : B => 2 • b) :
    Nat.card (ModN A 2) = Nat.card (Submodule.torsionBy ℤ A 2) := by
  rw [natCard_modN_two, natCard_torsionBy_two, index_range_dbl_eq_card_ker hB]

/-- **`dim_{𝔽₂} A/2A = 2` when `|A[2]| = 4`**, for an abelian group with a finite-index uniquely
`2`-divisible subgroup. PROVED. -/
theorem finrank_modN_two_eq_of_card_torsionBy [B.FiniteIndex]
    (hB : Function.Bijective fun b : B => 2 • b)
    (h4 : Nat.card (Submodule.torsionBy ℤ A 2) = 4) :
    Module.finrank (ZMod 2) (ModN A 2) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (ModN A 2) = 4 := (card_modN_two_eq_card_torsionBy hB).trans h4
  have : Finite (ModN A 2) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hH := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ModN A 2)
  rw [hc, Nat.card_zmod] at hH
  exact (Nat.pow_right_injective le_rfl (hH.symm.trans (by norm_num : (4 : ℕ) = 2 ^ 2)))

/-- **The index lemma, as a node** (tex 4551–4556). For every abelian group `A` and every subgroup
`B` of finite index on which doubling is bijective, `|A/2A| = |A[2]|`. Kind: PROVED. -/
def IndexLemmaTwo : Prop :=
  ∀ (A : Type) [AddCommGroup A] (B : AddSubgroup A), B.FiniteIndex →
    Function.Bijective (fun b : B => 2 • b) →
      Nat.card (ModN A 2) = Nat.card (Submodule.torsionBy ℤ A 2)

theorem indexLemmaTwo_proof : IndexLemmaTwo := fun _ _ _ _ hB =>
  card_modN_two_eq_card_torsionBy hB

end ZInQ.Contrib.CloudB3RC53.Mattuck
