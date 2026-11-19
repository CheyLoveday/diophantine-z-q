import Mathlib

/-!
# Restriction from `Gal(\bar K / K)` to `G_ℚ` along an embedding, and its image

Let `K` be a complete nontrivially normed nonarchimedean field of characteristic zero in which `ℚ`
is dense, `\bar K` an algebraic closure carrying the spectral norm, and `ι : \bar ℚ → \bar K` a
`ℚ`-embedding.

* `restrictionHom ι : Gal(\bar K / K) →* G_ℚ` is the restriction along `ι`, characterised by
  `ι (r σ x) = σ (ι x)` (`restrictionHom_apply`); it is well defined because `ι (\bar ℚ)` is
  normal over `ℚ` (Mathlib `AlgEquiv.restrictNormalHom`).
* `exists_spectralNorm_sub_lt`: `ι (\bar ℚ)` is dense in `\bar K`. This is the approximation of
  the minimal polynomial of `y ∈ \bar K` by a polynomial over `ℚ` together with the continuity of
  roots (Mathlib `Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`), the classical input
  behind Krasner's lemma in the form of Lang, *Algebraic Number Theory*, Ch. II, §2, Prop. 4 and
  its Corollary, p. 44 (Milne, *Algebraic Number Theory*, v3.08, Cor. 7.62, p. 132).
* `exists_galois_lift`: if `g ∈ G_ℚ` stabilises the place `ι⁻¹(\bar K°)` (the elements of
  spectral norm at most one), then `g = r σ` for some `σ ∈ Gal(\bar K / K)`. At finite level this
  is Milne, Prop. 8.10, p. 139 (the decomposition group is the local Galois group); here it is
  proved directly: `g` is continuous for the induced place, so `ι (g γ)` is a root of the minimal
  polynomial of `ι γ` over `K` (`aeval_minpoly_eq_zero`), and the finite-level lifts are glued by
  compactness of `Gal(\bar K / K)`.

## Classification

Definitions and PROVED statements only; no hypotheses are assumed.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DecompositionGlue

open Polynomial
open scoped NNReal Pointwise

/-- **PROVED**, an evaluation estimate: coefficientwise close polynomials of bounded degree
have close values on a bounded element. Locator: Mathlib `Polynomial.aeval_eq_sum_range'`,
`norm_sum_le`. -/
theorem norm_aeval_sub_le {F E : Type*} [NormedField F] [NormedField E] [NormedAlgebra F E]
    (f₁ f₂ : F[X]) {d : ℕ} (h₁ : f₁.natDegree ≤ d) (h₂ : f₂.natDegree ≤ d) {ε M : ℝ}
    (hM : 1 ≤ M) (hε : ∀ i, ‖f₁.coeff i - f₂.coeff i‖ ≤ ε) (a : E) (ha : ‖a‖ ≤ M) :
    ‖aeval a f₁ - aeval a f₂‖ ≤ (d + 1) * (ε * M ^ d) := by
  have hdeg : (f₁ - f₂).natDegree < d + 1 :=
    Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans (max_le h₁ h₂))
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0)
  rw [← map_sub, aeval_eq_sum_range' hdeg]
  calc ‖∑ i ∈ Finset.range (d + 1), (f₁ - f₂).coeff i • a ^ i‖
      ≤ ∑ i ∈ Finset.range (d + 1), ‖(f₁ - f₂).coeff i • a ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (d + 1), ε * M ^ d := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_smul, norm_pow, coeff_sub]
        calc ‖f₁.coeff i - f₂.coeff i‖ * ‖a‖ ^ i ≤ ε * M ^ i :=
              mul_le_mul (hε i) (pow_le_pow_left₀ (norm_nonneg a) ha i) (by positivity) hε0
          _ ≤ ε * M ^ d := mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hM (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) hε0
    _ = (d + 1) * (ε * M ^ d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **PROVED**, in a Galois extension the set of automorphisms sending a given element to a
given element is closed for the Krull topology. Locator: Mathlib
`stabilizer_isOpen_of_isIntegral`. -/
theorem isClosed_setOf_apply_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsIntegral F E] (y c : E) : IsClosed {σ : E ≃ₐ[F] E | σ y = c} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • (MulAction.stabilizer (E ≃ₐ[F] E) y : Set (E ≃ₐ[F] E)), ?_,
    (stabilizer_isOpen_of_isIntegral y).leftCoset σ, ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩ h
  apply hσ
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hτ
  change (σ * τ) y = c at h
  rwa [AlgEquiv.mul_apply, hτ] at h

section Restriction

variable {K : Type*} [Field K] [CharZero K]

/-- **DEFINITION**, restriction of scalars from `K` to `ℚ` on automorphisms of `\bar K`.
Locator: Mathlib `AlgEquiv.restrictScalars`. -/
def restrictScalarsGal :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      (AlgebraicClosure K ≃ₐ[ℚ] AlgebraicClosure K) :=
  MonoidHom.mk' (fun σ => σ.restrictScalars ℚ) fun _ _ => rfl

/-- **DEFINITION**, the restriction homomorphism `Gal(\bar K / K) → G_ℚ` along an embedding
`ι : \bar ℚ → \bar K`: `\bar ℚ` is made a subfield of `\bar K` through `ι`, and an automorphism is
restricted to this normal subfield. Locator: Mathlib `AlgEquiv.restrictNormalHom`. -/
def restrictionHom (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun q => (ι.commutes q).symm
  (AlgEquiv.restrictNormalHom (AlgebraicClosure ℚ)).comp restrictScalarsGal

/-- **PROVED**, the defining property `ι ∘ r(σ) = σ ∘ ι` of the restriction. Locator: Mathlib
`AlgEquiv.restrictNormal_commutes`. -/
theorem restrictionHom_apply (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    ι (restrictionHom ι σ x) = σ (ι x) := by
  let _ : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  have _ : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun q => (ι.commutes q).symm
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- **PROVED**, the restriction is determined by the defining property. Locator:
`restrictionHom_apply`. -/
theorem restrictionHom_eq_of_apply (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : ∀ x, σ (ι x) = ι (g x)) :
    restrictionHom ι σ = g :=
  AlgEquiv.ext fun x => ι.injective ((restrictionHom_apply ι σ x).trans (h x))

end Restriction

section Approximation

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [CharZero K]

/-- **PROVED**, `ι (\bar ℚ)` is dense in `\bar K` for the spectral norm, when `ℚ` is dense in
`K`. Locator: Mathlib
`Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` (approximation
of the minimal polynomial over `ℚ`) and `Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`
(continuity of roots); Lang, Ch. II, §2, Prop. 4 and Corollary, p. 44. -/
theorem exists_spectralNorm_sub_lt (hd : DenseRange ((↑) : ℚ → K))
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) (y : AlgebraicClosure K) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : AlgebraicClosure ℚ, spectralNorm K (AlgebraicClosure K) (y - ι x) < ε := by
  let _ : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  let _ : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  have hd' : DenseRange (algebraMap ℚ K) := by
    have e : ⇑(algebraMap ℚ K) = ((↑) : ℚ → K) := funext fun q => eq_ratCast _ q
    rw [e]
    exact hd
  have hyi : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hfm : (minpoly K y).Monic := minpoly.monic hyi
  have hfd : (minpoly K y).natDegree ≠ 0 := (minpoly.natDegree_pos hyi).ne'
  set d := (minpoly K y).natDegree with hd_def
  set M := max ‖y‖ 1 with hM_def
  have hM : 0 < M := lt_max_of_lt_right one_pos
  set t := ε / M with ht_def
  have ht : 0 < t := div_pos hε hM
  set ε' := t ^ d / (2 * ((d : ℝ) + 1)) with hε'_def
  have hε' : 0 < ε' := by positivity
  obtain ⟨g, hgm, hgd, hgc⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd' hfm hε'
  obtain ⟨b, hb, hyb⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε'
    (minpoly.aeval K y) hfm (hgm.map _) (by rw [natDegree_map, ← hgd]) hgc (IsAlgClosed.splits _)
  have hbroot : ((g.map (algebraMap ℚ (AlgebraicClosure ℚ))).map
      (ι : AlgebraicClosure ℚ →+* AlgebraicClosure K)).IsRoot b := by
    rw [mem_aroots] at hb
    rw [Polynomial.map_map, AlgHom.comp_algebraMap, IsRoot, eval_map_algebraMap]
    rw [aeval_map_algebraMap] at hb
    exact hb.2
  obtain ⟨x, rfl⟩ := Splits.mem_range_of_isRoot (IsAlgClosed.splits _)
    (map_ne_zero hgm.ne_zero) hbroot
  refine ⟨x, ?_⟩
  have hroot : ((d + 1 : ℝ) * ε') ^ (d : ℝ)⁻¹ ≤ t := by
    have h1 : (d + 1 : ℝ) * ε' ≤ t ^ d := by
      rw [hε'_def]
      have : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [pow_pos ht d]
    calc ((d + 1 : ℝ) * ε') ^ (d : ℝ)⁻¹ ≤ (t ^ d) ^ (d : ℝ)⁻¹ :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = t := Real.pow_rpow_inv_natCast ht.le hfd
  calc spectralNorm K (AlgebraicClosure K) (y - ι x) = ‖y - ι x‖ := rfl
    _ < ((d + 1 : ℝ) * ε') ^ (d : ℝ)⁻¹ * M := hyb
    _ ≤ t * M := mul_le_mul_of_nonneg_right hroot hM.le
    _ = ε := div_mul_cancel₀ ε hM.ne'

/-- **PROVED**, continuity of a place-preserving `g ∈ G_ℚ` forces `ι (g γ)` to be a root of the
minimal polynomial of `ι γ` over `K`. Hypotheses: `ℚ` is dense in `K`, `q ∈ ℚ` has
`0 < ‖q‖ < 1`, and `g` preserves `{z : spectralNorm (ι z) ≤ 1}`. Proof: approximate the minimal
polynomial by one over `ℚ`; its value at `γ` is small, `g` preserves smallness measured against
powers of `q`, and the values at `ι (g γ)` of the two polynomials stay close. -/
theorem aeval_minpoly_eq_zero (hd : DenseRange ((↑) : ℚ → K))
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {q : ℚ} (hq0 : 0 < ‖(q : K)‖)
    (hq1 : ‖(q : K)‖ < 1)
    (hO : ∀ z, spectralNorm K (AlgebraicClosure K) (ι z) ≤ 1 →
      spectralNorm K (AlgebraicClosure K) (ι (g z)) ≤ 1)
    (γ : AlgebraicClosure ℚ) : aeval (ι (g γ)) (minpoly K (ι γ)) = 0 := by
  let _ : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  let _ : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  have hd' : DenseRange (algebraMap ℚ K) := by
    have e : ⇑(algebraMap ℚ K) = ((↑) : ℚ → K) := funext fun q => eq_ratCast _ q
    rw [e]
    exact hd
  set c := ‖(q : K)‖ with hc_def
  have hqL : ∀ n : ℕ, ‖ι ((q : AlgebraicClosure ℚ) ^ n)‖ = c ^ n := by
    intro n
    rw [map_pow, map_ratCast, norm_pow, ← map_ratCast (algebraMap K (AlgebraicClosure K)) q,
      norm_algebraMap']
  have hq : (q : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h' : (q : ℚ) = 0 := by exact_mod_cast h
    rw [hc_def, h', Rat.cast_zero, norm_zero] at hq0
    exact lt_irrefl 0 hq0
  have hsmall : ∀ (z : AlgebraicClosure ℚ) (n : ℕ), ‖ι z‖ ≤ c ^ n → ‖ι (g z)‖ ≤ c ^ n := by
    intro z n hz
    have hcn : 0 < c ^ n := pow_pos hq0 n
    have h1 : ‖ι (z * ((q : AlgebraicClosure ℚ) ^ n)⁻¹)‖ ≤ 1 := by
      rw [map_mul, norm_mul, map_inv₀, norm_inv, hqL, mul_inv_le_iff₀ hcn, one_mul]
      exact hz
    have h2 := hO _ h1
    change ‖ι (g (z * ((q : AlgebraicClosure ℚ) ^ n)⁻¹))‖ ≤ 1 at h2
    rw [map_mul g, map_inv₀ g, map_pow g, map_ratCast g, map_mul, norm_mul, map_inv₀, norm_inv,
      hqL, mul_inv_le_iff₀ hcn, one_mul] at h2
    exact h2
  set a := ι γ with ha_def
  set b := ι (g γ) with hb_def
  have hai : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  have hfm : (minpoly K a).Monic := minpoly.monic hai
  set d := (minpoly K a).natDegree with hd_def
  set M := max (max ‖a‖ ‖b‖) 1 with hM_def
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : 0 < M := lt_of_lt_of_le one_pos hM1
  by_contra hne
  have hη : 0 < ‖aeval b (minpoly K a)‖ := norm_pos_iff.2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℕ, c ^ n < ‖aeval b (minpoly K a)‖ / 2 :=
    exists_pow_lt_of_lt_one (by positivity) hq1
  set ε' := c ^ n / ((d + 1) * M ^ d) with hε'_def
  have hε' : 0 < ε' := by positivity
  obtain ⟨h, -, hhd, hhc⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd' hfm hε'
  have hh'd : (h.map (algebraMap ℚ K)).natDegree ≤ d := by rw [natDegree_map, ← hhd]
  have hbound : ∀ x : AlgebraicClosure K, ‖x‖ ≤ M →
      ‖aeval x (h.map (algebraMap ℚ K)) - aeval x (minpoly K a)‖ ≤ c ^ n := by
    intro x hx
    calc _ ≤ (d + 1) * (ε' * M ^ d) :=
          norm_aeval_sub_le _ _ hh'd le_rfl hM1 (fun i => (hhc i).le) x hx
      _ = c ^ n := by
          rw [hε'_def]
          field_simp
  have e1 : aeval a (h.map (algebraMap ℚ K)) = ι (aeval γ h) := by
    rw [aeval_map_algebraMap, ha_def, aeval_algHom_apply]
  have e2 : aeval b (h.map (algebraMap ℚ K)) = ι (g (aeval γ h)) := by
    rw [aeval_map_algebraMap, hb_def, aeval_algHom_apply, aeval_algHom_apply]
  have ha' : ‖ι (aeval γ h)‖ ≤ c ^ n := by
    have := hbound a (le_max_of_le_left (le_max_left _ _))
    rwa [minpoly.aeval, sub_zero, e1] at this
  have hb1 : ‖aeval b (h.map (algebraMap ℚ K))‖ ≤ c ^ n := by
    rw [e2]
    exact hsmall _ n ha'
  have hb2 : ‖aeval b (minpoly K a) - aeval b (h.map (algebraMap ℚ K))‖ ≤ c ^ n := by
    rw [norm_sub_rev]
    exact hbound b (le_max_of_le_left (le_max_right _ _))
  have hle : ‖aeval b (minpoly K a)‖ ≤ c ^ n + c ^ n := by
    calc ‖aeval b (minpoly K a)‖
        = ‖(aeval b (minpoly K a) - aeval b (h.map (algebraMap ℚ K))) +
            aeval b (h.map (algebraMap ℚ K))‖ := by rw [sub_add_cancel]
      _ ≤ c ^ n + c ^ n := norm_add_le_of_le hb2 hb1
  linarith

/-- **PROVED**, every place-preserving `g ∈ G_ℚ` is the restriction of some
`σ ∈ Gal(\bar K / K)`: `σ ∘ ι = ι ∘ g`. The finite-level lifts given by
`aeval_minpoly_eq_zero` (through Mathlib `isConjRoot_iff_exists_algEquiv`) are glued by
compactness of `Gal(\bar K / K)` along primitive elements (Mathlib
`Field.primitive_element_inf_aux`). At finite level this is Milne, Prop. 8.10, p. 139. -/
theorem exists_galois_lift (hd : DenseRange ((↑) : ℚ → K))
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {q : ℚ} (hq0 : 0 < ‖(q : K)‖)
    (hq1 : ‖(q : K)‖ < 1)
    (hO : ∀ z, spectralNorm K (AlgebraicClosure K) (ι z) ≤ 1 →
      spectralNorm K (AlgebraicClosure K) (ι (g z)) ≤ 1) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, σ (ι x) = ι (g x) := by
  let C : AlgebraicClosure ℚ → Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := fun γ =>
    {σ | ∀ x ∈ IntermediateField.adjoin ℚ {γ}, σ (ι x) = ι (g x)}
  have hCne : ∀ γ, (C γ).Nonempty := by
    intro γ
    have hai : IsIntegral K (ι γ) := Algebra.IsIntegral.isIntegral _
    have hmin : minpoly K (ι γ) = minpoly K (ι (g γ)) :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hai)
        (aeval_minpoly_eq_zero hd ι g hq0 hq1 hO γ) (minpoly.monic hai)
    obtain ⟨σ, hσ⟩ := (isConjRoot_iff_exists_algEquiv (K := K)).mp
      (show IsConjRoot K (ι (g γ)) (ι γ) from hmin.symm)
    refine ⟨σ, fun x hx => ?_⟩
    let φ₁ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
      ((σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K).restrictScalars ℚ).comp ι
    let φ₂ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
      ι.comp (g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
    have hle : Algebra.adjoin ℚ {γ} ≤ AlgHom.equalizer φ₁ φ₂ :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hσ)
    have hx' : x ∈ Algebra.adjoin ℚ {γ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic γ)]
      exact hx
    exact hle hx'
  have hCdir : Directed (· ⊇ ·) C := by
    intro γ₁ γ₂
    obtain ⟨γ, hγ⟩ := Field.primitive_element_inf_aux ℚ γ₁ γ₂
    have h₁ : IntermediateField.adjoin ℚ {γ₁} ≤ IntermediateField.adjoin ℚ {γ} := by
      rw [← hγ]
      exact IntermediateField.adjoin.mono ℚ _ _ (by simp)
    have h₂ : IntermediateField.adjoin ℚ {γ₂} ≤ IntermediateField.adjoin ℚ {γ} := by
      rw [← hγ]
      exact IntermediateField.adjoin.mono ℚ _ _ (by simp)
    exact ⟨γ, fun σ hσ x hx => hσ x (h₁ hx), fun σ hσ x hx => hσ x (h₂ hx)⟩
  have hCcl : ∀ γ, IsClosed (C γ) := by
    intro γ
    have e : C γ = ⋂ x ∈ IntermediateField.adjoin ℚ {γ},
        {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K | σ (ι x) = ι (g x)} := by
      ext σ
      simp [C]
    rw [e]
    exact isClosed_biInter fun x _ => isClosed_setOf_apply_eq _ _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hCdir
    hCne (fun γ => (hCcl γ).isCompact) hCcl
  exact ⟨σ, fun x => Set.mem_iInter.mp hσ x x (IntermediateField.mem_adjoin_simple_self ℚ x)⟩

end Approximation

end ZInQ.Contrib.RC53Assist.DecompositionGlue
