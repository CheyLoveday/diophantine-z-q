module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Finset.Powerset

/-!
# Finite coefficient allocation for products of multilinear polynomials

For `p q : MvPolynomial (Fin n) (ZMod 2)` whose support exponents are all at most `1`, and
disjoint `s₁ s₂ : Finset (Fin n)`, the coefficient of `z_{s₁} z_{s₂}^2` in the *ordinary*
product `p * q` equals the allocation sum over `t ⊆ s₁` of
`[z_{s₂} z_t] p * [z_{s₂} z_{s₁ \ t}] q`.

Source: `graphs-frozen-4eaee875.tex`, lines 559–570 and 608–625 (proof of `gr:address`).

Proof: expand the coefficient of the product by the antidiagonal convolution
(`MvPolynomial.coeff_mul`) and reindex the nonzero summands by `t ↦ (𝟙_{s₂} + 𝟙_t,
𝟙_{s₂} + 𝟙_{s₁ \ t})` using `Finset.sum_bij_ne_zero`.  A nonzero convolution term `(x, y)`
has `x, y` pointwise `≤ 1` by `hp`, `hq`, so it is the image of `t = {i ∈ s₁ | x i = 1}`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ZInQ.CoefficientAllocation

def squarefreeExponent (n : Nat) (s : Finset (Fin n)) : (Fin n →₀ Nat) :=
  ∑ i ∈ s, Finsupp.single i 1

/-- Pointwise value of `squarefreeExponent`: it is the indicator of `s`. -/
theorem squarefreeExponent_apply (n : Nat) (s : Finset (Fin n)) (i : Fin n) :
    squarefreeExponent n s i = if i ∈ s then 1 else 0 := by
  unfold squarefreeExponent
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  first
    | exact Finset.sum_ite_eq' s i (fun _ => 1)
    | simp

theorem squarefreeExponent_apply_of_mem {n : Nat} {s : Finset (Fin n)} {i : Fin n}
    (h : i ∈ s) : squarefreeExponent n s i = 1 := by
  rw [squarefreeExponent_apply, if_pos h]

theorem squarefreeExponent_apply_of_notMem {n : Nat} {s : Finset (Fin n)} {i : Fin n}
    (h : i ∉ s) : squarefreeExponent n s i = 0 := by
  rw [squarefreeExponent_apply, if_neg h]

theorem squarefreeExponent_apply_le_one (n : Nat) (s : Finset (Fin n)) (i : Fin n) :
    squarefreeExponent n s i ≤ 1 := by
  by_cases h : i ∈ s
  · have a := squarefreeExponent_apply_of_mem h
    omega
  · have a := squarefreeExponent_apply_of_notMem h
    omega

/-- Disjoint sets have pointwise indicator sum at most `1`. -/
theorem squarefreeExponent_disjoint_apply {n : Nat} {s₁ s₂ : Finset (Fin n)}
    (hdisj : Disjoint s₁ s₂) (i : Fin n) :
    squarefreeExponent n s₁ i + squarefreeExponent n s₂ i ≤ 1 := by
  by_cases h1 : i ∈ s₁
  · have h2 : i ∉ s₂ := Finset.disjoint_left.mp hdisj h1
    have a1 := squarefreeExponent_apply_of_mem h1
    have a2 := squarefreeExponent_apply_of_notMem h2
    omega
  · have a1 := squarefreeExponent_apply_of_notMem h1
    have a2 := squarefreeExponent_apply_le_one n s₂ i
    omega

/-- For `t ⊆ s`, the indicators of `t` and `s \ t` add up to the indicator of `s`. -/
theorem squarefreeExponent_sdiff_apply {n : Nat} {s t : Finset (Fin n)}
    (ht : t ⊆ s) (i : Fin n) :
    squarefreeExponent n t i + squarefreeExponent n (s \ t) i =
      squarefreeExponent n s i := by
  by_cases hs : i ∈ s
  · have a1 := squarefreeExponent_apply_of_mem hs
    by_cases hti : i ∈ t
    · have hd : i ∉ s \ t := fun h => (Finset.mem_sdiff.mp h).2 hti
      have a2 := squarefreeExponent_apply_of_mem hti
      have a3 := squarefreeExponent_apply_of_notMem hd
      omega
    · have hd : i ∈ s \ t := Finset.mem_sdiff.mpr ⟨hs, hti⟩
      have a2 := squarefreeExponent_apply_of_notMem hti
      have a3 := squarefreeExponent_apply_of_mem hd
      omega
  · have hti : i ∉ t := fun h => hs (ht h)
    have hd : i ∉ s \ t := fun h => hs (Finset.mem_sdiff.mp h).1
    have a1 := squarefreeExponent_apply_of_notMem hs
    have a2 := squarefreeExponent_apply_of_notMem hti
    have a3 := squarefreeExponent_apply_of_notMem hd
    omega

theorem squarefreeExponent_injective (n : Nat) :
    Function.Injective (squarefreeExponent n) := by
  intro s t h
  ext i
  have hi := DFunLike.congr_fun h i
  constructor
  · intro hs
    by_cases ht : i ∈ t
    · exact ht
    · have a1 := squarefreeExponent_apply_of_mem hs
      have a2 := squarefreeExponent_apply_of_notMem ht
      exact absurd hi (by omega)
  · intro ht
    by_cases hs : i ∈ s
    · exact hs
    · have a1 := squarefreeExponent_apply_of_notMem hs
      have a2 := squarefreeExponent_apply_of_mem ht
      exact absurd hi (by omega)

/-- Pointwise value of the chosen exponent `𝟙_{s₁} + 2 • 𝟙_{s₂}`. -/
theorem oneTwoExponent_apply (n : Nat) (s₁ s₂ : Finset (Fin n)) (i : Fin n) :
    (squarefreeExponent n s₁ + 2 • squarefreeExponent n s₂) i =
      squarefreeExponent n s₁ i + 2 * squarefreeExponent n s₂ i := by
  first
    | (rw [Finsupp.add_apply, Finsupp.nsmul_apply, smul_eq_mul]; done)
    | rfl
    | (simp only [Finsupp.coe_add, Finsupp.coe_nsmul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]; done)
    | (simp; done)

theorem coeff_mul_at_one_two_exponent (n : Nat)
    (p q : MvPolynomial (Fin n) (ZMod 2))
    (hp : ∀ d ∈ p.support, ∀ i : Fin n, d i <= 1)
    (hq : ∀ d ∈ q.support, ∀ i : Fin n, d i <= 1)
    (s₁ s₂ : Finset (Fin n))
    (hdisj : Disjoint s₁ s₂) :
    (p * q).coeff
      (squarefreeExponent n s₁ + 2 • squarefreeExponent n s₂) =
      ∑ t ∈ s₁.powerset,
        p.coeff
          (squarefreeExponent n s₂ + squarefreeExponent n t) *
        q.coeff
          (squarefreeExponent n s₂ + squarefreeExponent n (s₁ \ t)) := by
  rw [MvPolynomial.coeff_mul]
  symm
  refine Finset.sum_bij_ne_zero
    (fun t _ _ => (squarefreeExponent n s₂ + squarefreeExponent n t,
      squarefreeExponent n s₂ + squarefreeExponent n (s₁ \ t))) ?_ ?_ ?_ ?_
  · -- every allocation lies on the antidiagonal of the target exponent
    intro t ht _
    have ht' : t ⊆ s₁ := Finset.mem_powerset.mp ht
    refine Finset.mem_antidiagonal.mpr ?_
    show squarefreeExponent n s₂ + squarefreeExponent n t +
        (squarefreeExponent n s₂ + squarefreeExponent n (s₁ \ t)) =
      squarefreeExponent n s₁ + 2 • squarefreeExponent n s₂
    ext i
    rw [oneTwoExponent_apply]
    simp only [Finsupp.add_apply]
    have hpart := squarefreeExponent_sdiff_apply ht' i
    omega
  · -- the allocation map is injective
    intro t₁ _ _ t₂ _ _ h
    have h1 : squarefreeExponent n s₂ + squarefreeExponent n t₁ =
        squarefreeExponent n s₂ + squarefreeExponent n t₂ := congrArg Prod.fst h
    exact squarefreeExponent_injective n (add_left_cancel h1)
  · -- every nonzero convolution term comes from an allocation
    rintro ⟨x, y⟩ hxy hne
    have hsum : x + y = squarefreeExponent n s₁ + 2 • squarefreeExponent n s₂ :=
      Finset.mem_antidiagonal.mp hxy
    have hne' : p.coeff x * q.coeff y ≠ 0 := hne
    have hx : ∀ i, x i ≤ 1 :=
      hp x (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne'))
    have hy : ∀ i, y i ≤ 1 :=
      hq y (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne'))
    have hpt : ∀ i, x i + y i =
        squarefreeExponent n s₁ i + 2 * squarefreeExponent n s₂ i := by
      intro i
      have h := DFunLike.congr_fun hsum i
      rw [oneTwoExponent_apply, Finsupp.add_apply] at h
      exact h
    obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n), t = s₁.filter (fun i => x i = 1) := ⟨_, rfl⟩
    have hmem : ∀ i, i ∈ t ↔ i ∈ s₁ ∧ x i = 1 := by
      intro i
      rw [ht]
      exact Finset.mem_filter
    have htsub : t ⊆ s₁ := by
      intro i hi
      exact ((hmem i).mp hi).1
    have hfst : squarefreeExponent n s₂ + squarefreeExponent n t = x := by
      ext i
      rw [Finsupp.add_apply]
      have hxi := hx i
      have hyi := hy i
      have hpi := hpt i
      have hdi := squarefreeExponent_disjoint_apply hdisj i
      have h2le := squarefreeExponent_apply_le_one n s₂ i
      by_cases h1 : i ∈ s₁
      · have a1 := squarefreeExponent_apply_of_mem h1
        by_cases hxi1 : x i = 1
        · have hti : i ∈ t := (hmem i).mpr ⟨h1, hxi1⟩
          have a3 := squarefreeExponent_apply_of_mem hti
          omega
        · have hti : i ∉ t := fun h => hxi1 ((hmem i).mp h).2
          have a3 := squarefreeExponent_apply_of_notMem hti
          omega
      · have hti : i ∉ t := fun h => h1 ((hmem i).mp h).1
        have a1 := squarefreeExponent_apply_of_notMem h1
        have a3 := squarefreeExponent_apply_of_notMem hti
        omega
    have hsnd : squarefreeExponent n s₂ + squarefreeExponent n (s₁ \ t) = y := by
      ext i
      rw [Finsupp.add_apply]
      have hpi := hpt i
      have hfi := DFunLike.congr_fun hfst i
      rw [Finsupp.add_apply] at hfi
      have hpart := squarefreeExponent_sdiff_apply htsub i
      omega
    refine ⟨t, Finset.mem_powerset.mpr htsub, ?_, ?_⟩
    · show p.coeff (squarefreeExponent n s₂ + squarefreeExponent n t) *
          q.coeff (squarefreeExponent n s₂ + squarefreeExponent n (s₁ \ t)) ≠ 0
      rw [hfst, hsnd]
      exact hne'
    · show (squarefreeExponent n s₂ + squarefreeExponent n t,
          squarefreeExponent n s₂ + squarefreeExponent n (s₁ \ t)) = (x, y)
      rw [hfst, hsnd]
  · -- the summands agree
    intro t _ _
    rfl

end ZInQ.CoefficientAllocation
