import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeBasis
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR

/-!
# The pole-space ladder at a degree-one place (node N9-alg)

Function-field formulation, as in `GroupCurveNotP1.lean`: places of `K/k` are valuation subrings
of `K` containing the constants. For a place `P`, an element `π` and `n : ℕ`, the pole space
`polePart k P π n` is the `k`-subspace of those `h` that lie in every place other than `P` and
satisfy `h π ^ n ∈ P`. When `P` is a place and `π` a uniformizer at `P`, this is
`L(n·P)` (`mem_polePart_iff`).

* `exists_polePart_succ_le`: at a degree-one place, `L((n+1)·P) ⊆ L(n·P) + k·g` for one `g`
  (the leading coefficient `h π^(n+1) mod 𝔪_P` lies in `k`);
* `finrank_polePart_le`: if `L(1·P)` consists of constants (the gap at `1`, the output of N9a),
  then `L(n·P)` is finite-dimensional with `dim L(n·P) ≤ n` for `n ≥ 1`;
* `span_eq_polePart_of_linearIndependent`: `n` linearly independent elements of `L(n·P)` span it;
* `exists_not_mem_polePart_of_linearIndependent`, `exists_exactPoleOrder_two_three`: so among
  `n + 2` independent elements of `L((n+2)·P)` one has exact pole order `n + 2`; in particular
  there are functions of exact pole orders `2` and `3`;
* `polePart_gap_of_baseChange`: the gap hypothesis from N9a's hypotheses;
* `linearIndependent_reduce`, `exists_reduce_not_mem_polePart`: the lower bound from lattice
  reduction (node N8). The reductions of a residually independent family are linearly independent
  over the residue field of `R`; so if they land in `L((n+2)·P)` on the special fibre, they span it
  and one of them has exact pole order `n + 2`.

Only Mathlib and the files of nodes N8, N9a and N10a are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open Module

section Ladder

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K]

/-- The pole space `L(n·P)`: elements lying in every place other than `P`, with `h π ^ n ∈ P`.
The condition at `P` is stated for places equal to `P`, so that this is a `k`-subspace for every
`P`; for a place `P` it is the expected set (`mem_polePart_iff`). -/
def polePart (P : ValuationSubring K) (π : K) (n : ℕ) : Submodule k K where
  carrier := {h | ∀ O : ValuationSubring K, IsConstPlace k O →
    (O ≠ P → h ∈ O) ∧ (O = P → h * π ^ n ∈ O)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    intro O hO
    refine ⟨fun hne => add_mem ((ha O hO).1 hne) ((hb O hO).1 hne), fun heq => ?_⟩
    rw [add_mul]
    exact add_mem ((ha O hO).2 heq) ((hb O hO).2 heq)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro O _
    exact ⟨fun _ => O.zero_mem, fun _ => by rw [zero_mul]; exact O.zero_mem⟩
  smul_mem' := by
    intro c h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    intro O hO
    refine ⟨fun hne => ?_, fun heq => ?_⟩
    · rw [Algebra.smul_def]
      exact mul_mem (hO c) ((hh O hO).1 hne)
    · rw [Algebra.smul_def, mul_assoc]
      exact mul_mem (hO c) ((hh O hO).2 heq)

variable {k}

theorem mem_polePart {P : ValuationSubring K} {π h : K} {n : ℕ} :
    h ∈ polePart k P π n ↔ ∀ O : ValuationSubring K, IsConstPlace k O →
      (O ≠ P → h ∈ O) ∧ (O = P → h * π ^ n ∈ O) :=
  Iff.rfl

/-- For a place `P`, `polePart k P π n` is the blueprint's set
`{h | (∀ O, IsConstPlace k O → O ≠ P → h ∈ O) ∧ h * π ^ n ∈ P}`. -/
theorem mem_polePart_iff {P : ValuationSubring K} (hP : IsConstPlace k P) {π h : K} {n : ℕ} :
    h ∈ polePart k P π n ↔
      (∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P → h ∈ O) ∧ h * π ^ n ∈ P := by
  rw [mem_polePart]
  constructor
  · intro hh
    exact ⟨fun O hO hne => (hh O hO).1 hne, (hh P hP).2 rfl⟩
  · rintro ⟨h1, h2⟩ O hO
    exact ⟨h1 O hO, fun heq => by subst heq; exact h2⟩

/-- The pole spaces increase with `n` when `π ∈ P`. -/
theorem polePart_mono {P : ValuationSubring K} {π : K} (hπ : π ∈ P) {m n : ℕ} (hmn : m ≤ n) :
    polePart k P π m ≤ polePart k P π n := by
  intro h hh
  rw [mem_polePart] at hh ⊢
  intro O hO
  refine ⟨(hh O hO).1, fun heq => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h1 := (hh O hO).2 heq
  subst heq
  rw [pow_add, ← mul_assoc]
  exact mul_mem h1 (pow_mem hπ d)

/-- If `h ∈ L((n+1)·P)` and `h π^(n+1)` vanishes at `P`, then `h ∈ L(n·P)`. -/
theorem mem_polePart_of_mul_pow_mem_nonunits {P : ValuationSubring K} {π : K}
    (hπ : IsUniformizerAt P π) {n : ℕ} {h : K} (hh : h ∈ polePart k P π (n + 1))
    (hn : h * π ^ (n + 1) ∈ P.nonunits) : h ∈ polePart k P π n := by
  rw [mem_polePart] at hh ⊢
  intro O hO
  refine ⟨(hh O hO).1, fun heq => ?_⟩
  subst heq
  have : h * π ^ n = h * π ^ (n + 1) * π⁻¹ := by
    rw [pow_succ, ← mul_assoc, mul_assoc _ π, mul_inv_cancel₀ hπ.1, mul_one]
  rw [this]
  exact hπ.2.2 _ hn

/-- For `h ∈ L((n+1)·P)`: `h ∈ L(n·P)` iff `h π^(n+1)` vanishes at `P`. -/
theorem mul_pow_mem_nonunits_iff {P : ValuationSubring K} (hP : IsConstPlace k P) {π : K}
    (hπ : IsUniformizerAt P π) {n : ℕ} {h : K} (hh : h ∈ polePart k P π (n + 1)) :
    h * π ^ (n + 1) ∈ P.nonunits ↔ h ∈ polePart k P π n := by
  refine ⟨mem_polePart_of_mul_pow_mem_nonunits hπ hh, fun h' => ?_⟩
  have h2 := ((mem_polePart_iff hP).1 h').2
  have : h * π ^ (n + 1) = π * (h * π ^ n) := by ring
  rw [this]
  exact GroupCurveNotP1.mul_mem_nonunits hπ.2.1 h2

/-- **One step of the ladder.** At a degree-one place, `L((n+1)·P) ⊆ L(n·P) + k·g` for some `g`:
`dim L((n+1)·P)/L(n·P) ≤ 1`. -/
theorem exists_polePart_succ_le {P : ValuationSubring K} (hP : IsDegreeOnePlace k P) {π : K}
    (hπ : IsUniformizerAt P π) (n : ℕ) :
    ∃ g : K, polePart k P π (n + 1) ≤ polePart k P π n ⊔ Submodule.span k {g} := by
  by_cases hall : ∀ h ∈ polePart k P π (n + 1), h * π ^ (n + 1) ∈ P.nonunits
  · exact ⟨0, fun h hh =>
      Submodule.mem_sup_left (mem_polePart_of_mul_pow_mem_nonunits hπ hh (hall h hh))⟩
  · push Not at hall
    obtain ⟨g, hg, hgn⟩ := hall
    obtain ⟨cg, hcg⟩ := hP.2.2 _ ((mem_polePart_iff hP.1).1 hg).2
    have hcg0 : cg ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hcg
      exact hgn hcg
    refine ⟨g, fun h hh => ?_⟩
    obtain ⟨ch, hch⟩ := hP.2.2 _ ((mem_polePart_iff hP.1).1 hh).2
    set a : k := ch / cg with ha_def
    have ha : algebraMap k K a * algebraMap k K cg = algebraMap k K ch := by
      rw [← map_mul, ha_def, div_mul_cancel₀ _ hcg0]
    have hd : h - a • g ∈ polePart k P π (n + 1) := sub_mem hh (Submodule.smul_mem _ _ hg)
    have hdn : (h - a • g) * π ^ (n + 1) ∈ P.nonunits := by
      have : (h - a • g) * π ^ (n + 1) = (h * π ^ (n + 1) - algebraMap k K ch) -
          (g * π ^ (n + 1) - algebraMap k K cg) * algebraMap k K a := by
        rw [Algebra.smul_def]
        linear_combination (-1 : K) * ha
      rw [this]
      exact sub_mem hch (GroupCurveNotP1.mul_mem_nonunits hcg (hP.1 a))
    have hmem := mem_polePart_of_mul_pow_mem_nonunits hπ hd hdn
    rw [← sub_add_cancel h (a • g)]
    exact Submodule.add_mem_sup hmem
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))

/-- The gap at `1` bounds `L((n+1)·P)` by the span of at most `n + 1` elements. -/
theorem exists_finset_polePart_le_span {P : ValuationSubring K} (hP : IsDegreeOnePlace k P)
    {π : K} (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c) :
    ∀ n : ℕ, ∃ s : Finset K, s.card ≤ n + 1 ∧
      polePart k P π (n + 1) ≤ Submodule.span k (s : Set K)
  | 0 => by
    refine ⟨{1}, by simp, fun h hh => ?_⟩
    obtain ⟨c, rfl⟩ := hgap h hh
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | n + 1 => by
    classical
    obtain ⟨s, hs, hle⟩ := exists_finset_polePart_le_span hP hπ hgap n
    obtain ⟨g, hg⟩ := exists_polePart_succ_le hP hπ (n + 1)
    refine ⟨insert g s, (Finset.card_insert_le g s).trans (by omega), hg.trans
      (sup_le (hle.trans (Submodule.span_mono ?_)) (Submodule.span_mono ?_))⟩
    · exact Finset.coe_subset.2 (Finset.subset_insert g s)
    · exact Set.singleton_subset_iff.2 (Finset.mem_coe.2 (Finset.mem_insert_self g s))

/-- Under the gap at `1`, every pole space is finite-dimensional. -/
theorem finiteDimensional_polePart {P : ValuationSubring K} (hP : IsDegreeOnePlace k P)
    {π : K} (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c) (n : ℕ) :
    FiniteDimensional k (polePart k P π n) := by
  obtain ⟨s, -, hle⟩ := exists_finset_polePart_le_span hP hπ hgap n
  have hle' : polePart k P π n ≤ Submodule.span k (s : Set K) :=
    (polePart_mono (GroupCurveNotP1.mem_of_mem_nonunits hπ.2.1) (Nat.le_succ n)).trans hle
  exact Submodule.finiteDimensional_of_le hle'

/-- **The ladder bound.** If `L(1·P)` consists of constants, then `dim L(n·P) ≤ n` for `n ≥ 1`. -/
theorem finrank_polePart_le {P : ValuationSubring K} (hP : IsDegreeOnePlace k P) {π : K}
    (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c) {n : ℕ} (hn : 1 ≤ n) :
    finrank k (polePart k P π n) ≤ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨s, hs, hle⟩ := exists_finset_polePart_le_span hP hπ hgap m
  exact (Submodule.finrank_mono hle).trans ((finrank_span_finset_le_card s).trans hs)

/-- `n` linearly independent elements of `L(n·P)` span it (`n ≥ 1`), and then
`dim L(n·P) = n`. -/
theorem span_eq_polePart_of_linearIndependent {P : ValuationSubring K}
    (hP : IsDegreeOnePlace k P) {π : K} (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c) {n : ℕ} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] {b : ι → K} (hb : LinearIndependent k b)
    (hcard : Fintype.card ι = n) (hbP : ∀ i, b i ∈ polePart k P π n) :
    Submodule.span k (Set.range b) = polePart k P π n ∧ finrank k (polePart k P π n) = n := by
  have := finiteDimensional_polePart hP hπ hgap n
  have hle : Submodule.span k (Set.range b) ≤ polePart k P π n :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hbP)
  have hrank : finrank k (Submodule.span k (Set.range b)) = n := by
    rw [finrank_span_eq_card hb, hcard]
  have hup := finrank_polePart_le hP hπ hgap hn
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [hrank]; exact hup)
  refine ⟨heq, ?_⟩
  rw [← heq, hrank]

/-- Among `n + 2` linearly independent elements, one is not in `L((n+1)·P)`; if they lie in
`L((n+2)·P)`, it has exact pole order `n + 2`. -/
theorem exists_not_mem_polePart_of_linearIndependent {P : ValuationSubring K}
    (hP : IsDegreeOnePlace k P) {π : K} (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c) {n : ℕ}
    {ι : Type*} [Fintype ι] {b : ι → K} (hb : LinearIndependent k b)
    (hcard : Fintype.card ι = n + 2) : ∃ i, b i ∉ polePart k P π (n + 1) := by
  by_contra hall
  push Not at hall
  have := finiteDimensional_polePart hP hπ hgap (n + 1)
  have hle : Submodule.span k (Set.range b) ≤ polePart k P π (n + 1) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hall)
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hb, hcard] at h1
  have h2 := finrank_polePart_le hP hπ hgap (Nat.le_add_left 1 n)
  omega

/-- Exact pole order `n + 1` in valuation form: for `h ∈ L((n+1)·P)`, `h ∉ L(n·P)` iff
`h π^(n+1)` is a unit at `P`. -/
theorem not_mem_polePart_iff_valuation_eq_one {P : ValuationSubring K} (hP : IsConstPlace k P)
    {π : K} (hπ : IsUniformizerAt P π) {n : ℕ} {h : K} (hh : h ∈ polePart k P π (n + 1)) :
    h ∉ polePart k P π n ↔ P.valuation (h * π ^ (n + 1)) = 1 := by
  rw [← mul_pow_mem_nonunits_iff hP hπ hh, ValuationSubring.mem_nonunits_iff, not_lt]
  have h1 := (P.valuation_le_one_iff _).2 ((mem_polePart_iff hP).1 hh).2
  exact ⟨fun h2 => le_antisymm h1 h2, fun h2 => h2.ge⟩

/-- **Exact pole orders `2` and `3`.** If `L(2·P)` and `L(3·P)` contain `2` and `3` linearly
independent elements (the lower bound from lattice reduction), then they have elements `x`, `y`
of exact pole orders `2` and `3` (chosen among the given ones). -/
theorem exists_exactPoleOrder_two_three {P : ValuationSubring K} (hP : IsDegreeOnePlace k P)
    {π : K} (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c)
    {b₂ : Fin 2 → K} (hb₂ : LinearIndependent k b₂) (hb₂P : ∀ i, b₂ i ∈ polePart k P π 2)
    {b₃ : Fin 3 → K} (hb₃ : LinearIndependent k b₃) (hb₃P : ∀ i, b₃ i ∈ polePart k P π 3) :
    ∃ x y : K, x ∈ Set.range b₂ ∧ y ∈ Set.range b₃ ∧
      x ∈ polePart k P π 2 ∧ x ∉ polePart k P π 1 ∧
      y ∈ polePart k P π 3 ∧ y ∉ polePart k P π 2 ∧
      P.valuation (x * π ^ 2) = 1 ∧ P.valuation (y * π ^ 3) = 1 := by
  obtain ⟨i, hi⟩ := exists_not_mem_polePart_of_linearIndependent (n := 0) hP hπ hgap hb₂
    (Fintype.card_fin 2)
  obtain ⟨j, hj⟩ := exists_not_mem_polePart_of_linearIndependent (n := 1) hP hπ hgap hb₃
    (Fintype.card_fin 3)
  exact ⟨b₂ i, b₃ j, ⟨i, rfl⟩, ⟨j, rfl⟩, hb₂P i, hi, hb₃P j, hj,
    (not_mem_polePart_iff_valuation_eq_one (n := 1) hP.1 hπ (hb₂P i)).1 hi,
    (not_mem_polePart_iff_valuation_eq_one (n := 2) hP.1 hπ (hb₃P j)).1 hj⟩

/-- The gap hypothesis from N9a's hypotheses (base-change form): `L(1·P) = k`. -/
theorem polePart_gap_of_baseChange {kb Kb : Type*} [Field kb] [Field Kb] [IsAlgClosed kb]
    [Algebra k kb] [Algebra.IsAlgebraic k kb] [Algebra kb Kb] [Algebra K Kb] [Algebra k Kb]
    [IsScalarTower k kb Kb] [IsScalarTower k K Kb]
    (hgen : IntermediateField.adjoin kb (Set.range (algebraMap K Kb)) = ⊤)
    (htr : TrdegLeOne k K) {P : ValuationSubring K} (hP : IsDegreeOnePlace k P)
    (σ : Kb ≃ₐ[kb] Kb)
    (hσ : ∀ Q : ValuationSubring Kb, IsDegreeOnePlace kb Q → Q.comap (σ : Kb →+* Kb) ≠ Q)
    {π : K} (hπ : IsUniformizerAt P π) :
    ∀ h ∈ polePart k P π 1, ∃ c : k, h = algebraMap k K c := by
  intro h hh
  obtain ⟨h1, h2⟩ := (mem_polePart_iff hP.1).1 hh
  rw [pow_one] at h2
  exact eq_algebraMap_of_mul_uniformizer_mem_of_baseChange hgen htr hP σ hσ hπ h1 h2

end Ladder

section Reduction

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {F Ω : Type*} [Field F] [Field Ω]
  [Algebra R F] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)

omit [IsLocalRing R] [IsScalarTower R F Ω] in
/-- A unit of `R` has `w`-value `1` when `w ≤ 1` on `R`. -/
theorem valuation_algebraMap_eq_one_of_isUnit (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    {r : R} (hr : IsUnit r) : w (algebraMap R Ω r) = 1 := by
  obtain ⟨u, rfl⟩ := hr
  have h1 : w (algebraMap R Ω ↑u) * w (algebraMap R Ω ↑u⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm (hR _) ?_
  calc (1 : Γ₀) = w (algebraMap R Ω ↑u) * w (algebraMap R Ω ↑u⁻¹) := h1.symm
    _ ≤ w (algebraMap R Ω ↑u) * 1 := mul_le_mul_of_nonneg_left (hR _) zero_le
    _ = w (algebraMap R Ω ↑u) := mul_one _

omit [Algebra R Ω] in
/-- An element of `𝒪_w` with `w`-value `1` is a unit of `𝒪_w`. -/
theorem isUnit_of_valuation_eq_one' {x : w.valuationSubring} (hx : w (x : Ω) = 1) :
    IsUnit x := by
  have hx0 : (x : Ω) ≠ 0 := fun h => by
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hinv : (x : Ω)⁻¹ ∈ w.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hx, inv_one]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change (x : Ω) * (x : Ω)⁻¹ = 1
  exact mul_inv_cancel₀ hx0

/-- **Reduction of a residually independent family.** If `Σ āᵢ b̄ᵢ = 0` in `κ_w` with
`āᵢ` in the residue field of `R` (acting through `residueHom`), then every `āᵢ` is `0`. -/
theorem eq_zero_of_sum_residueHom_mul_reduce (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) {ι : Type*} [Fintype ι]
    {b : ι → Ω} (hb : ResiduallyIndependent (F := F) w b) (a : ι → ResidueField R)
    (ha : ∑ i, residueHom w hR hm (a i) * reduce w (b i) (hb.1 i) = 0) : ∀ i, a i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  choose r hr using fun i => residue_surjective (a i)
  set c : ι → F := fun i => algebraMap R F (r i) with hc_def
  have hc : ∀ i, algebraMap F Ω (c i) = algebraMap R Ω (r i) := fun i =>
    (IsScalarTower.algebraMap_apply R F Ω (r i)).symm
  have hsum1 : w (∑ i, algebraMap F Ω (c i) * b i) = 1 := by
    refine hb.2 c (fun i => by rw [hc]; exact hR _) ⟨i₀, ?_⟩
    rw [hc]
    refine valuation_algebraMap_eq_one_of_isUnit w hR ?_
    by_contra hnu
    apply hi₀
    rw [← hr i₀, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  let s : w.valuationSubring := ∑ i, ⟨algebraMap R Ω (r i) * b i,
    (w.mem_valuationSubring_iff _).2 (valuation_algebraMap_mul_le w hR (r i) (hb.1 i))⟩
  have hs : (s : Ω) = ∑ i, algebraMap F Ω (c i) * b i := by
    simp only [s]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
  have hres : residue w.valuationSubring s = 0 := by
    simp only [s]
    rw [map_sum, ← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hr i]
    exact reduce_algebraMap_mul w hR hm (r i) (hb.1 i)
  have hu : IsUnit s := isUnit_of_valuation_eq_one' w (by rw [hs]; exact hsum1)
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at hres
  exact hres hu

/-- The reductions of a residually independent family are linearly independent over the residue
field of `R`, for any algebra structure on `κ_w` given by `residueHom`. -/
theorem linearIndependent_reduce (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1)
    [Algebra (ResidueField R) (ResidueField w.valuationSubring)]
    (halg : algebraMap (ResidueField R) (ResidueField w.valuationSubring) = residueHom w hR hm)
    {ι : Type*} [Fintype ι] {b : ι → Ω} (hb : ResiduallyIndependent (F := F) w b) :
    LinearIndependent (ResidueField R) fun i => reduce w (b i) (hb.1 i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine eq_zero_of_sum_residueHom_mul_reduce w hR hm hb g ?_
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, halg]

/-- **Ladder on the special fibre, with the lattice lower bound.** Let `b` be a residually
independent family of `n + 2` elements of `Ω` (a lattice basis of `L((n+2)·P_L)` from N8) whose
reductions lie in `L((n+2)·ē)` on `κ_w`. If `L(1·ē)` consists of constants, the reductions span
`L((n+2)·ē)`, which has dimension `n + 2`, and one of them has exact pole order `n + 2`. -/
theorem exists_reduce_not_mem_polePart (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1)
    [Algebra (ResidueField R) (ResidueField w.valuationSubring)]
    (halg : algebraMap (ResidueField R) (ResidueField w.valuationSubring) = residueHom w hR hm)
    {P : ValuationSubring (ResidueField w.valuationSubring)}
    (hP : IsDegreeOnePlace (ResidueField R) P) {π : ResidueField w.valuationSubring}
    (hπ : IsUniformizerAt P π)
    (hgap : ∀ h ∈ polePart (ResidueField R) P π 1,
      ∃ c : ResidueField R, h = algebraMap (ResidueField R) (ResidueField w.valuationSubring) c)
    {ι : Type*} [Fintype ι] {b : ι → Ω} (hb : ResiduallyIndependent (F := F) w b) {n : ℕ}
    (hcard : Fintype.card ι = n + 2)
    (hland : ∀ i, reduce w (b i) (hb.1 i) ∈ polePart (ResidueField R) P π (n + 2)) :
    (∃ i, reduce w (b i) (hb.1 i) ∉ polePart (ResidueField R) P π (n + 1)) ∧
      Submodule.span (ResidueField R) (Set.range fun i => reduce w (b i) (hb.1 i)) =
        polePart (ResidueField R) P π (n + 2) ∧
      finrank (ResidueField R) (polePart (ResidueField R) P π (n + 2)) = n + 2 := by
  have hli := linearIndependent_reduce w hR hm halg hb
  have hspan := span_eq_polePart_of_linearIndependent hP hπ hgap (Nat.le_add_left 1 (n + 1))
    hli hcard hland
  exact ⟨exists_not_mem_polePart_of_linearIndependent hP hπ hgap hli hcard, hspan⟩

end Reduction

end ZInQ.Contrib.CMHeight62Full
