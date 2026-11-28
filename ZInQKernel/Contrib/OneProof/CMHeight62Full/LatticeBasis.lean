import ZInQKernel.Contrib.OneProof.CMHeight62Full.Lattice

/-!
# Lattice reduction along a valuation: existence of a residually independent basis

Let `w` be a valuation on a field `Ω`, `F → Ω` a field extension, and `ϖ ∈ F` a uniformizer of
`w`: `w(ϖ) < 1` and every nonzero value of `w` is an integer power of `w(ϖ)` (so `w` is discrete,
its restriction to `F` is discrete, and `ϖ` is a uniformizer of both). Let `R` be the ring of
`w`-integral elements of `F` and `V` a finite-dimensional `F`-subspace of `Ω`, with lattice
`M = V ∩ 𝒪_w`.

* `exists_residuallyIndependent_basis`: if `M` lies in the `R`-span of finitely many elements of
  `Ω`, then `V` has an `F`-basis `b₁, …, bₙ` (`n = dim_F V`) that is residually independent, so its
  residues are linearly independent over the residue field of `F`;
* `exists_lattice_basis`: for that basis, `M` is the free `R`-module on `b`, and an element
  `Σ cᵢ bᵢ` of `M` has `w`-value `< 1` exactly when every `cᵢ` is divisible by `ϖ` in `R`. So
  `M` is `R`-free of rank `n` and the reduction map `M / ϖM → κ_w` is injective.

The finiteness hypothesis cannot be dropped: if `F = ℚ` with the `p`-adic valuation and `Ω = ℚ(x)`
with `w(f) = |f(α)|_p` for a transcendental `α ∈ ℤ_p`, then `w` is discrete with uniformizer `p`
and residue field `𝔽_p`, so `V = ℚ + ℚx` has no residually independent basis. It is also necessary,
since a residually independent basis is such a finite family.

The proof extends a residually independent family `f` one element at a time. For `g ∈ V` outside
the span of `f`, a linear form vanishing on that span and the finiteness hypothesis bound the
values `w(g − Σ aᵢ fᵢ)` from below; by discreteness one of them is least, and rescaling that best
approximation by a power of `ϖ` gives the new element. Only Mathlib and `Lattice.lean` are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open Module

section Zpow

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {π : Γ₀}

/-- Integer powers of an element `0 < π < 1` are antitone. -/
theorem zpow_le_zpow_of_lt_one_of_le_aux (h0 : π ≠ 0) (h1 : π < 1) {m m' : ℤ} (h : m ≤ m') :
    π ^ m' ≤ π ^ m := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le h
  rw [zpow_add₀ h0, zpow_natCast]
  exact mul_le_of_le_one_right' (Right.pow_le_one_of_le h1.le)

/-- Integer powers of an element `0 < π < 1` are strictly antitone. -/
theorem le_of_zpow_le_zpow_of_lt_one_aux (h0 : π ≠ 0) (h1 : π < 1) {m m' : ℤ}
    (h : π ^ m ≤ π ^ m') : m' ≤ m := by
  by_contra hlt
  have h2 : π ^ m' ≤ π ^ (m + 1) := zpow_le_zpow_of_lt_one_of_le_aux h0 h1 (by omega)
  have h3 : π ^ (m + 1) < π ^ m := by
    rw [zpow_add_one₀ h0]
    exact mul_lt_of_lt_one_right (zero_lt_iff.mpr (zpow_ne_zero m h0)) h1
  exact absurd (h.trans h2) (not_le.mpr h3)

end Zpow

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable (w : Valuation Ω Γ₀)

/-- `ϖ ∈ F` is a uniformizer of the valuation `w` on `Ω`: `ϖ ≠ 0`, `w(ϖ) < 1`, and every nonzero
value of `w` is an integer power of `w(ϖ)`. -/
def IsUniformizer (ϖ : F) : Prop :=
  ϖ ≠ 0 ∧ w (algebraMap F Ω ϖ) < 1 ∧
    ∀ x : Ω, x ≠ 0 → ∃ m : ℤ, w x = w (algebraMap F Ω ϖ) ^ m

variable {w}

namespace IsUniformizer

variable {ϖ : F} (hϖ : IsUniformizer w ϖ)
include hϖ

theorem valuation_ne_zero : w (algebraMap F Ω ϖ) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hϖ.1)

/-- Every value `< 1` is at most `w(ϖ)` (the discreteness hypothesis of `Lattice.lean`). -/
theorem le_of_lt_one (x : Ω) (hx : w x < 1) : w x ≤ w (algebraMap F Ω ϖ) := by
  by_cases h0 : x = 0
  · rw [h0, map_zero]
    exact zero_le
  obtain ⟨m, hm⟩ := hϖ.2.2 x h0
  have hm1 : 1 ≤ m := by
    by_contra hlt
    have h := zpow_le_zpow_of_lt_one_of_le_aux hϖ.valuation_ne_zero hϖ.2.1
      (show m ≤ 0 by omega)
    rw [zpow_zero, ← hm] at h
    exact absurd hx (not_lt.mpr h)
  have h := zpow_le_zpow_of_lt_one_of_le_aux hϖ.valuation_ne_zero hϖ.2.1 hm1
  rwa [zpow_one, ← hm] at h

/-- For `c ∈ F`, `w(c) < 1` iff `c / ϖ` is `w`-integral, i.e. `c ∈ ϖR`. -/
theorem lt_one_iff_div (c : F) :
    w (algebraMap F Ω c) < 1 ↔ w (algebraMap F Ω (c / ϖ)) ≤ 1 := by
  have hpos : 0 < w (algebraMap F Ω ϖ) := zero_lt_iff.mpr hϖ.valuation_ne_zero
  rw [map_div₀, map_div₀, div_le_one₀ hpos]
  exact ⟨hϖ.le_of_lt_one _, fun h => lt_of_le_of_lt h hϖ.2.1⟩

end IsUniformizer

/-- A linear form on `Ω` vanishing on a subspace `p` and equal to `1` at a point outside it. -/
theorem exists_linearForm_of_notMem {p : Submodule F Ω} {g : Ω} (hg : g ∉ p) :
    ∃ φ : Ω →ₗ[F] F, φ g = 1 ∧ ∀ x ∈ p, φ x = 0 := by
  obtain ⟨φ, hφg, hp⟩ := Submodule.exists_le_ker_of_notMem hg
  refine ⟨(φ g)⁻¹ • φ, ?_, fun x hx => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφg]
  · rw [LinearMap.smul_apply, LinearMap.mem_ker.mp (hp hx), smul_zero]

/-- If the `w`-integral part of `V` lies in the span of `t` over the `w`-integers of `F`, every
linear form is bounded on it by an integer power of `w(ϖ)`. -/
theorem exists_zpow_bound {ϖ : F} (hϖ : IsUniformizer w ϖ) (V : Submodule F Ω)
    {κ : Type*} [Fintype κ] (t : κ → Ω)
    (ht : ∀ x ∈ V, w x ≤ 1 → ∃ c : κ → F, (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧
      x = ∑ j, algebraMap F Ω (c j) * t j)
    (φ : Ω →ₗ[F] F) :
    ∃ N : ℤ, ∀ x ∈ V, w x ≤ 1 → w (algebraMap F Ω (φ x)) ≤ w (algebraMap F Ω ϖ) ^ N := by
  have hk : ∀ j, ∃ k : ℤ, w (algebraMap F Ω (φ (t j))) ≤ w (algebraMap F Ω ϖ) ^ k := by
    intro j
    by_cases h0 : algebraMap F Ω (φ (t j)) = 0
    · exact ⟨0, by rw [h0, map_zero]; exact zero_le⟩
    · obtain ⟨k, hk⟩ := hϖ.2.2 _ h0
      exact ⟨k, hk.le⟩
  choose k hk using hk
  refine ⟨-∑ j, |k j|, fun x hx hwx => ?_⟩
  obtain ⟨c, hc, rfl⟩ := ht x hx hwx
  have hφ : φ (∑ j, algebraMap F Ω (c j) * t j) = ∑ j, c j * φ (t j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hφ, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, map_mul]
  have hN : -∑ j, |k j| ≤ k j := by
    have h1 : |k j| ≤ ∑ j, |k j| :=
      Finset.single_le_sum (f := fun j => |k j|) (fun j _ => abs_nonneg (k j))
        (Finset.mem_univ j)
    have h2 := neg_abs_le (k j)
    omega
  calc w (algebraMap F Ω (c j)) * w (algebraMap F Ω (φ (t j)))
      ≤ 1 * w (algebraMap F Ω ϖ) ^ k j := mul_le_mul' (hc j) (hk j)
    _ = w (algebraMap F Ω ϖ) ^ k j := one_mul _
    _ ≤ w (algebraMap F Ω ϖ) ^ (-∑ j, |k j|) :=
      zpow_le_zpow_of_lt_one_of_le_aux hϖ.valuation_ne_zero hϖ.2.1 hN

/-- **Best approximation.** If no `g − Σ aᵢ fᵢ` vanishes and the exponents of their values are
bounded above, one of these values is least. -/
theorem exists_best_approximation {ϖ : F} (hϖ : IsUniformizer w ϖ) {ι : Type*} [Fintype ι]
    (f : ι → Ω) (g : Ω) (hg : ∀ a : ι → F, g - ∑ i, algebraMap F Ω (a i) * f i ≠ 0)
    (hbd : ∃ N : ℤ, ∀ (a : ι → F) (m : ℤ),
      w (g - ∑ i, algebraMap F Ω (a i) * f i) = w (algebraMap F Ω ϖ) ^ m → m ≤ N) :
    ∃ a₀ : ι → F, ∀ a : ι → F,
      w (g - ∑ i, algebraMap F Ω (a₀ i) * f i) ≤ w (g - ∑ i, algebraMap F Ω (a i) * f i) := by
  obtain ⟨m₀, ⟨a₀, ha₀⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ a : ι → F,
      w (g - ∑ i, algebraMap F Ω (a i) * f i) = w (algebraMap F Ω ϖ) ^ m)
    (by
      obtain ⟨N, hN⟩ := hbd
      exact ⟨N, fun m ⟨a, ha⟩ => hN a m ha⟩)
    (by
      obtain ⟨m, hm⟩ := hϖ.2.2 _ (hg 0)
      exact ⟨m, 0, hm⟩)
  refine ⟨a₀, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hϖ.2.2 _ (hg a)
  rw [ha₀, hm]
  exact zpow_le_zpow_of_lt_one_of_le_aux hϖ.valuation_ne_zero hϖ.2.1 (hmax m ⟨a, hm⟩)

/-- Adjoining to a residually independent family `f` an element `h` with `w(h) = 1` and
`w(h + Σ cᵢ fᵢ) ≥ 1` for all `c` keeps it residually independent. -/
theorem residuallyIndependent_cons {r : ℕ} {f : Fin r → Ω}
    (hf : ResiduallyIndependent (F := F) w f) {h : Ω} (hh : w h = 1)
    (hkey : ∀ c : Fin r → F, 1 ≤ w (h + ∑ i, algebraMap F Ω (c i) * f i)) :
    ResiduallyIndependent (F := F) w (Fin.cons h f : Fin (r + 1) → Ω) := by
  refine ⟨fun i => ?_, fun c hc hone => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero, hh]
    · rw [Fin.cons_succ]
      exact hf.1 j
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases hd : w (algebraMap F Ω (c 0)) = 1
  · have hd0 : c 0 ≠ 0 := by
      rintro h0
      rw [h0, map_zero, map_zero] at hd
      exact zero_ne_one hd
    have hd0' : algebraMap F Ω (c 0) ≠ 0 := (map_ne_zero _).mpr hd0
    refine le_antisymm ?_ ?_
    · refine Valuation.map_add_le _ ?_ ?_
      · rw [map_mul, hd, hh, one_mul]
      · refine Valuation.map_sum_le _ fun j _ => ?_
        rw [map_mul]
        exact mul_le_one' (hc j.succ) (hf.1 j)
    · have hsum : algebraMap F Ω (c 0) * h + ∑ j, algebraMap F Ω (c j.succ) * f j =
          algebraMap F Ω (c 0) * (h + ∑ j, algebraMap F Ω (c j.succ / c 0) * f j) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_div₀, ← mul_assoc, mul_div_cancel₀ _ hd0']
      rw [hsum, map_mul, hd, one_mul]
      exact hkey _
  · have hlt : w (algebraMap F Ω (c 0)) < 1 := lt_of_le_of_ne (hc 0) hd
    obtain ⟨i, hi⟩ := hone
    obtain ⟨j, hj⟩ : ∃ j : Fin r, w (algebraMap F Ω (c j.succ)) = 1 := by
      revert hi
      refine Fin.cases (fun hi => absurd hi hd) (fun j hj => ⟨j, hj⟩) i
    have hrest : w (∑ j, algebraMap F Ω (c j.succ) * f j) = 1 :=
      hf.2 (fun j => c j.succ) (fun j => hc j.succ) ⟨j, hj⟩
    have hfirst : w (algebraMap F Ω (c 0) * h) < w (∑ j, algebraMap F Ω (c j.succ) * f j) := by
      rw [map_mul, hh, mul_one, hrest]
      exact hlt
    rw [Valuation.map_add_eq_of_lt_right _ hfirst, hrest]

/-- **Extension step.** A residually independent family in `V` with fewer than `dim_F V` members
extends by one element of `V`. -/
theorem exists_residuallyIndependent_cons {ϖ : F} (hϖ : IsUniformizer w ϖ) (V : Submodule F Ω)
    [FiniteDimensional F V] {κ : Type*} [Fintype κ] (t : κ → Ω)
    (ht : ∀ x ∈ V, w x ≤ 1 → ∃ c : κ → F, (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧
      x = ∑ j, algebraMap F Ω (c j) * t j)
    {r : ℕ} (f : Fin r → Ω) (hf : ResiduallyIndependent (F := F) w f) (hfV : ∀ i, f i ∈ V)
    (hr : r < finrank F V) :
    ∃ h ∈ V, ResiduallyIndependent (F := F) w (Fin.cons h f : Fin (r + 1) → Ω) := by
  have hli : LinearIndependent F f := by
    rcases isEmpty_or_nonempty (Fin r) with hι | hι
    · exact linearIndependent_empty_type
    · exact linearIndependent_of_residuallyIndependent w hf
  have hWV : Submodule.span F (Set.range f) ≤ V :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hfV)
  have hne : Submodule.span F (Set.range f) ≠ V := by
    intro hEq
    have h1 := finrank_span_eq_card hli
    rw [hEq, Fintype.card_fin] at h1
    omega
  obtain ⟨g, hgV, hgW⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hWV hne)
  obtain ⟨φ, hφg, hφW⟩ := exists_linearForm_of_notMem hgW
  obtain ⟨N, hN⟩ := exists_zpow_bound hϖ V t ht φ
  have hu0 : w (algebraMap F Ω ϖ) ≠ 0 := hϖ.valuation_ne_zero
  have hmemW : ∀ a : Fin r → F,
      ∑ i, algebraMap F Ω (a i) * f i ∈ Submodule.span F (Set.range f) := fun a =>
    Submodule.sum_mem _ fun i _ => by
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmemV : ∀ a : Fin r → F, g - ∑ i, algebraMap F Ω (a i) * f i ∈ V := fun a =>
    Submodule.sub_mem _ hgV (hWV (hmemW a))
  have hφy : ∀ a : Fin r → F, φ (g - ∑ i, algebraMap F Ω (a i) * f i) = 1 := fun a => by
    rw [map_sub, hφg, hφW _ (hmemW a), sub_zero]
  have hne0 : ∀ a : Fin r → F, g - ∑ i, algebraMap F Ω (a i) * f i ≠ 0 := fun a h0 => by
    have h1 := hφy a
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  -- the value of `x / ϖ^m` for `w(x) = w(ϖ)^m`
  have hscale : ∀ (x : Ω) (m : ℤ), w x = w (algebraMap F Ω ϖ) ^ m →
      w (algebraMap F Ω (ϖ ^ m)⁻¹ * x) = 1 := fun x m hm => by
    rw [map_mul, map_inv₀, map_zpow₀, map_inv₀, map_zpow₀, hm,
      inv_mul_cancel₀ (zpow_ne_zero _ hu0)]
  have hbd : ∃ N' : ℤ, ∀ (a : Fin r → F) (m : ℤ),
      w (g - ∑ i, algebraMap F Ω (a i) * f i) = w (algebraMap F Ω ϖ) ^ m → m ≤ N' := by
    refine ⟨-N, fun a m hm => ?_⟩
    have hxV : algebraMap F Ω (ϖ ^ m)⁻¹ * (g - ∑ i, algebraMap F Ω (a i) * f i) ∈ V := by
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hmemV a)
    have hφx : φ (algebraMap F Ω (ϖ ^ m)⁻¹ * (g - ∑ i, algebraMap F Ω (a i) * f i)) =
        (ϖ ^ m)⁻¹ := by
      rw [← Algebra.smul_def, map_smul, hφy a, smul_eq_mul, mul_one]
    have h := hN _ hxV (hscale _ m hm).le
    rw [hφx, map_inv₀, map_zpow₀, map_inv₀, map_zpow₀, ← zpow_neg] at h
    have h2 := le_of_zpow_le_zpow_of_lt_one_aux hu0 hϖ.2.1 h
    omega
  obtain ⟨a₀, ha₀⟩ := exists_best_approximation hϖ f g hne0 hbd
  obtain ⟨m₀, hm₀⟩ := hϖ.2.2 _ (hne0 a₀)
  refine ⟨algebraMap F Ω (ϖ ^ m₀)⁻¹ * (g - ∑ i, algebraMap F Ω (a₀ i) * f i), ?_, ?_⟩
  · rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hmemV a₀)
  refine residuallyIndependent_cons hf (hscale _ m₀ hm₀) fun c => ?_
  have hu : algebraMap F Ω (ϖ ^ m₀) ≠ 0 := (map_ne_zero _).mpr (zpow_ne_zero _ hϖ.1)
  have hs : ∑ i, algebraMap F Ω (a₀ i - ϖ ^ m₀ * c i) * f i =
      ∑ i, algebraMap F Ω (a₀ i) * f i -
        algebraMap F Ω (ϖ ^ m₀) * ∑ i, algebraMap F Ω (c i) * f i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, map_mul]
    ring
  have heq : algebraMap F Ω (ϖ ^ m₀)⁻¹ * (g - ∑ i, algebraMap F Ω (a₀ i) * f i) +
      ∑ i, algebraMap F Ω (c i) * f i =
      algebraMap F Ω (ϖ ^ m₀)⁻¹ *
        (g - ∑ i, algebraMap F Ω (a₀ i - ϖ ^ m₀ * c i) * f i) := by
    rw [hs, map_inv₀]
    field_simp
    ring
  rw [heq, map_mul]
  calc (1 : Γ₀) = w (algebraMap F Ω (ϖ ^ m₀)⁻¹) * w (g - ∑ i, algebraMap F Ω (a₀ i) * f i) := by
        rw [← map_mul, hscale _ m₀ hm₀]
    _ ≤ w (algebraMap F Ω (ϖ ^ m₀)⁻¹) *
        w (g - ∑ i, algebraMap F Ω (a₀ i - ϖ ^ m₀ * c i) * f i) :=
      mul_le_mul' le_rfl (ha₀ _)

/-- Residually independent families in `V` of every size `r ≤ dim_F V`. -/
theorem exists_residuallyIndependent_fin {ϖ : F} (hϖ : IsUniformizer w ϖ) (V : Submodule F Ω)
    [FiniteDimensional F V] {κ : Type*} [Fintype κ] (t : κ → Ω)
    (ht : ∀ x ∈ V, w x ≤ 1 → ∃ c : κ → F, (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧
      x = ∑ j, algebraMap F Ω (c j) * t j)
    (r : ℕ) (hr : r ≤ finrank F V) :
    ∃ f : Fin r → Ω, ResiduallyIndependent (F := F) w f ∧ ∀ i, f i ∈ V := by
  induction r with
  | zero => exact ⟨Fin.elim0, ⟨fun i => i.elim0, fun _ _ ⟨i, _⟩ => i.elim0⟩, fun i => i.elim0⟩
  | succ r ih =>
    obtain ⟨f, hf, hfV⟩ := ih (by omega)
    obtain ⟨h, hV, hcons⟩ := exists_residuallyIndependent_cons hϖ V t ht f hf hfV (by omega)
    refine ⟨Fin.cons h f, hcons, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
      exact hV
    · rw [Fin.cons_succ]
      exact hfV j

/-- **Existence of a residually independent basis.** Let `ϖ ∈ F` be a uniformizer of `w` and `V`
a finite-dimensional `F`-subspace of `Ω` whose `w`-integral part lies in the span of a finite
family `t` over the `w`-integers of `F`. Then `V` has a residually independent `F`-basis. -/
theorem exists_residuallyIndependent_basis {ϖ : F} (hϖ : IsUniformizer w ϖ)
    (V : Submodule F Ω) [FiniteDimensional F V] {κ : Type*} [Fintype κ] (t : κ → Ω)
    (ht : ∀ x ∈ V, w x ≤ 1 → ∃ c : κ → F, (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧
      x = ∑ j, algebraMap F Ω (c j) * t j) :
    ∃ b : Fin (finrank F V) → Ω, ResiduallyIndependent (F := F) w b ∧ (∀ i, b i ∈ V) ∧
      LinearIndependent F b ∧ Submodule.span F (Set.range b) = V := by
  obtain ⟨b, hb, hbV⟩ := exists_residuallyIndependent_fin hϖ V t ht _ le_rfl
  have hli : LinearIndependent F b := by
    rcases isEmpty_or_nonempty (Fin (finrank F V)) with hι | hι
    · exact linearIndependent_empty_type
    · exact linearIndependent_of_residuallyIndependent w hb
  refine ⟨b, hb, hbV, hli, Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr hbV)) ?_⟩
  rw [finrank_span_eq_card hli, Fintype.card_fin]

/-- **Lattice basis and injective reduction.** Under the hypotheses of
`exists_residuallyIndependent_basis`, there is an `F`-basis `b` of `V` such that
* `M = V ∩ 𝒪_w` is the set of `Σ cᵢ bᵢ` with `w`-integral `cᵢ ∈ F` (uniquely, by linear
  independence): `M` is free of rank `dim_F V` over the `w`-integers `R` of `F`;
* `w(Σ cᵢ bᵢ) < 1` iff every `cᵢ / ϖ` is `w`-integral: the kernel of the reduction `M → κ_w` is
  `ϖM`, so `M / ϖM → κ_w` is injective. -/
theorem exists_lattice_basis {ϖ : F} (hϖ : IsUniformizer w ϖ)
    (V : Submodule F Ω) [FiniteDimensional F V] {κ : Type*} [Fintype κ] (t : κ → Ω)
    (ht : ∀ x ∈ V, w x ≤ 1 → ∃ c : κ → F, (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧
      x = ∑ j, algebraMap F Ω (c j) * t j) :
    ∃ b : Fin (finrank F V) → Ω, ResiduallyIndependent (F := F) w b ∧ (∀ i, b i ∈ V) ∧
      LinearIndependent F b ∧ Submodule.span F (Set.range b) = V ∧
      (∀ x : Ω, x ∈ V ∧ w x ≤ 1 ↔ ∃ c : Fin (finrank F V) → F,
        (∀ i, w (algebraMap F Ω (c i)) ≤ 1) ∧ x = ∑ i, algebraMap F Ω (c i) * b i) ∧
      ∀ c : Fin (finrank F V) → F, w (∑ i, algebraMap F Ω (c i) * b i) < 1 ↔
        ∀ i, w (algebraMap F Ω (c i / ϖ)) ≤ 1 := by
  obtain ⟨b, hb, hbV, hli, hspan⟩ := exists_residuallyIndependent_basis hϖ V t ht
  refine ⟨b, hb, hbV, hli, hspan, fun x => ⟨fun ⟨hxV, hwx⟩ => ?_, fun ⟨c, hc, hx⟩ => ?_⟩,
    fun c => ?_⟩
  · rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hxV
    obtain ⟨c, rfl⟩ := hxV
    simp_rw [Algebra.smul_def] at hwx ⊢
    refine ⟨c, ?_, rfl⟩
    rcases isEmpty_or_nonempty (Fin (finrank F V)) with hι | hι
    · exact fun i => (IsEmpty.false i).elim
    · exact (sum_integral_iff w hb c).mp hwx
  · subst hx
    refine ⟨Submodule.sum_mem _ fun i _ => ?_, Valuation.map_sum_le _ fun i _ => ?_⟩
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hbV i)
    · rw [map_mul]
      exact mul_le_one' (hc i) (hb.1 i)
  · simp_rw [← hϖ.lt_one_iff_div]
    rcases isEmpty_or_nonempty (Fin (finrank F V)) with hι | hι
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero]
      exact ⟨fun _ i => (IsEmpty.false i).elim, fun _ => zero_lt_one⟩
    · obtain ⟨i₀, hmax, hval⟩ := exists_valuation_sum_eq w hb c
      rw [hval]
      exact ⟨fun h i => (hmax i).trans_lt h, fun h => h i₀⟩

end ZInQ.Contrib.CMHeight62Full
