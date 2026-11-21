module

public import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.Grading
public import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.IntegralPoints
public import Mathlib.Tactic.Ring

/-! # Geometric points in the presence of a homogeneous unit -/

@[expose] public section

namespace RC.ModelInvariants

open DirectSum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (grading : ℤ → Submodule R S) [GradedAlgebra grading]

private theorem homogeneousUnit_inv_mem {d : ℤ} {δ : Sˣ} (hδ : (δ : S) ∈ grading d) :
    (↑δ⁻¹ : S) ∈ grading (-d) := by
  have h := coe_decompose_mul_add_of_left_mem grading (j := -d) (b := (↑δ⁻¹ : S)) hδ
  rw [add_neg_cancel, δ.mul_inv, decompose_of_mem_same grading (SetLike.one_mem_graded grading)] at h
  have he := congrArg ((↑δ⁻¹ : S) * ·) h
  rw [mul_one, ← mul_assoc, δ.inv_mul, one_mul] at he
  exact he.symm ▸ (decompose grading (↑δ⁻¹ : S) (-d)).property

private theorem homogeneousUnit_zpow_mem {d : ℤ} {δ : Sˣ} (hδ : (δ : S) ∈ grading d) (n : ℤ) :
    (↑(δ ^ n) : S) ∈ grading (n * d) := by
  cases n with
  | ofNat n =>
      exact SetLike.pow_mem_graded n hδ
  | negSucc n =>
      rw [zpow_negSucc, ← inv_pow]
      have h : Int.negSucc n * d = (n + 1) • -d := by
        rw [Int.negSucc_eq, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
      rw [h]
      exact SetLike.pow_mem_graded (n + 1) (homogeneousUnit_inv_mem grading hδ)

private theorem positive_homogeneousUnit {d : ℤ} {δ : Sˣ} (hd : d ≠ 0)
    (hδ : (δ : S) ∈ grading d) :
    ∃ (m : ℕ) (ε : Sˣ), 0 < m ∧ (ε : S) ∈ grading (m : ℤ) := by
  obtain h | h := lt_or_gt_of_ne hd
  · exact ⟨d.natAbs, δ⁻¹, by omega, by
      rw [show (d.natAbs : ℤ) = -d by omega]
      exact homogeneousUnit_inv_mem grading hδ⟩
  · exact ⟨d.natAbs, δ, by omega, by
      rw [show (d.natAbs : ℤ) = d by omega]
      exact hδ⟩

/-- Multiplication by `δ - 1` cannot give a nonzero element of degree zero.
For a nonzero multiplier the lowest degree stays put and the highest degree increases. -/
private theorem degreeZero_not_in_span {d : ℤ} (hd : 0 < d) {δ : Sˣ}
    (hδ : (δ : S) ∈ grading d) {c : S} (hc : c ∈ grading 0)
    (h : c ∈ Ideal.span ({(δ : S) - 1} : Set S)) : c = 0 := by
  classical
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp h
  by_cases hx0 : x = 0
  · simpa [hx0] using hx.symm
  let support := (decompose grading x).support
  have hs : support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hx0
    apply (decompose grading).injective
    rw [decompose_zero, ← DFinsupp.support_eq_empty]
    exact he
  let low := support.min' hs
  let high := support.max' hs
  have hlo : low ∈ support := Finset.min'_mem _ _
  have hhi : high ∈ support := Finset.max'_mem _ _
  have component (i : ℤ) :
      (decompose grading c i : S) =
        (δ : S) * (decompose grading x (i - d) : S) - (decompose grading x i : S) := by
    rw [← hx, mul_comm, sub_mul, one_mul, decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub]
    have he := coe_decompose_mul_add_of_left_mem grading (j := i - d) (b := x) hδ
    rw [show d + (i - d) = i by omega] at he
    rw [he]
  have off_support (i : ℤ) (hi : i ∉ support) : (decompose grading x i : S) = 0 := by
    have he : decompose grading x i = 0 := DFinsupp.notMem_support_iff.mp hi
    exact congrArg (fun v : grading i => (v : S)) he
  have on_support (i : ℤ) (hi : i ∈ support) : (decompose grading x i : S) ≠ 0 := by
    have he : decompose grading x i ≠ 0 := DFinsupp.mem_support_iff.mp hi
    exact fun hz => he (Subtype.ext hz)
  have hlow : low = 0 := by
    have hz : (decompose grading x (low - d) : S) = 0 :=
      off_support _ fun hm => by have := Finset.min'_le support (low - d) hm; omega
    by_contra hne
    have he := component low
    rw [decompose_of_mem_ne grading hc (Ne.symm hne), hz, mul_zero, zero_sub,
      eq_comm, neg_eq_zero] at he
    exact on_support _ hlo he
  have hhigh : high + d = 0 := by
    have hz : (decompose grading x (high + d) : S) = 0 :=
      off_support _ fun hm => by have := Finset.le_max' support (high + d) hm; omega
    by_contra hne
    have he := component (high + d)
    rw [decompose_of_mem_ne grading hc (Ne.symm hne), hz, sub_zero, add_sub_cancel_right] at he
    have hcancel := congrArg ((↑δ⁻¹ : S) * ·) he.symm
    rw [mul_zero, ← mul_assoc, δ.inv_mul, one_mul] at hcancel
    exact on_support _ hhi hcancel
  have := Finset.le_max' support low hlo
  omega

section Points

variable {k : Type*} [Field k] [Algebra R k] [IsAlgClosed k]

/-- A point of the degree-zero algebra lifts whenever a homogeneous unit of nonzero degree
exists. The lift can be constructed through the integral quotient obtained by setting a
positive-degree unit equal to one. -/
theorem degreeZero_restrict_surjective {d : ℤ} {δ : Sˣ} (hd : d ≠ 0)
    (hδ : (δ : S) ∈ grading d) :
    Function.Surjective (fun f : S →ₐ[R] k => f.comp (degreeZero grading).val) := by
  obtain ⟨m, ε, hm, hε⟩ := positive_homogeneousUnit grading hd hδ
  let I := Ideal.span ({(ε : S) - 1} : Set S)
  let A := degreeZero grading
  let q := Ideal.Quotient.mkₐ R I
  have hq : q (ε : S) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hpow (i : ℤ) : q (↑(ε ^ i) : S) = 1 := by
    change (Units.map q.toMonoidHom (ε ^ i) : (S ⧸ I)ˣ).val = 1
    rw [map_zpow, show Units.map q.toMonoidHom ε = 1 from Units.ext hq, one_zpow]
    rfl
  let : Algebra.IsIntegral A (S ⧸ I) := by
    constructor
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I z
    refine Decomposition.inductionOn (ℳ := grading) ?_ ?_ ?_ x
    · simpa using (isIntegral_zero : IsIntegral A (0 : S ⧸ I))
    · intro i x
      change IsIntegral A (q (x : S))
      apply IsIntegral.of_pow hm
      have hg : (x : S) ^ m * (↑(ε ^ (-i)) : S) ∈ grading 0 := by
        have he : m • i + (-i) * (m : ℤ) = 0 := by
          rw [nsmul_eq_mul]
          ring
        exact he ▸ SetLike.mul_mem_graded (SetLike.pow_mem_graded m x.property)
          (homogeneousUnit_zpow_mem grading hε (-i))
      let y : A := ⟨_, hg⟩
      have hy : algebraMap A (S ⧸ I) y = q x ^ m := by
        change q ((x : S) ^ m * (↑(ε ^ (-i)) : S)) = _
        rw [map_mul, map_pow, hpow, mul_one]
      rw [← hy]
      exact isIntegral_algebraMap
    · intro x y hx hy
      rw [map_add]
      exact hx.add hy
  have hinj : Function.Injective (algebraMap A (S ⧸ I)) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    intro x hx
    rw [RingHom.mem_ker] at hx
    change x = 0
    apply Subtype.ext
    exact degreeZero_not_in_span grading (by exact_mod_cast hm) hε x.property
      (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  intro f
  obtain ⟨F, hF⟩ := liftIntegralPoint hinj f
  exact ⟨F.comp q, hF⟩

end Points

#print axioms homogeneousUnit_inv_mem
#print axioms homogeneousUnit_zpow_mem
#print axioms positive_homogeneousUnit
#print axioms degreeZero_not_in_span
#print axioms degreeZero_restrict_surjective

end RC.ModelInvariants
