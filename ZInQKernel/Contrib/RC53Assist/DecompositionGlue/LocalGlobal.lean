import ZInQKernel.Contrib.RC53Assist.DecompositionGlue.PlaceConjugacy
import ZInQKernel.Contrib.RC53Assist.DecompositionGlue.SpectralPlace
import ZInQKernel.Contrib.RC53Assist.DecompositionGlue.GaloisLift

/-!
# Local and global decomposition groups: the assembly over a complete field

Let `K` be a complete nontrivially normed nonarchimedean field of characteristic zero in which `ℚ`
is dense, `p` a rational prime with `0 < ‖p‖ < 1` in `K`, `w` the spectral valuation on `\bar K`,
and `O` a valuation subring of `\bar ℚ` lying over `p`. For an embedding `ι : \bar ℚ → \bar K`
inducing `O` (that is, `x ∈ O ↔ w (ι x) ≤ 1`, provided by `exists_algHom_comap_eq`) and the
restriction `r : Gal(\bar K / K) → G_ℚ` along `ι`:

* `restrictionHom_mem_decomposition`: `r` takes values in the decomposition group of `O`;
* `map_restrictionHom_localInertia`: `r` carries the inertia group of `w` onto the inertia group
  of `O`;
* `exists_frobenius_lift`: every arithmetic Frobenius at `O` is `r σ` for a local arithmetic
  Frobenius `σ` (the `p`-power map on the residue field of `w`).

The residue identification is the one induced by `ι`; its surjectivity comes from the density of
`ι (\bar ℚ)` in `\bar K` (`exists_spectralNorm_sub_lt`). This is the infinite-level form of Milne,
*Algebraic Number Theory*, v3.08, Prop. 8.10, p. 139 and the discussion of inertia and Frobenius
elements on pp. 139–141, with Lang, *Algebraic Number Theory*, Ch. II, §2, Prop. 3–4, pp. 43–44
for the approximation input.

## Classification

Definitions and PROVED statements only; no hypotheses are assumed.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DecompositionGlue

open scoped NNReal Pointwise
open GlueC10 (Qbar GQ)
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic (LiesOver IsArithFrob)

/-- **PROVED**, an element of a decomposition group maps the valuation subring into itself.
Locator: Mathlib `ValuationSubring.smul_mem_pointwise_smul`. -/
theorem apply_mem_of_mem_decompositionSubgroup {F E : Type*} [Field F] [Field E] [Algebra F E]
    {A : ValuationSubring E} {g : E ≃ₐ[F] E} (hg : g ∈ A.decompositionSubgroup F) {x : E}
    (hx : x ∈ A) : g x ∈ A := by
  have h1 : g • x ∈ g • A := ValuationSubring.smul_mem_pointwise_smul g x A hx
  rw [MulAction.mem_stabilizer_iff.1 hg] at h1
  exact h1

/-- **PROVED**, the elementwise description of the image of an inertia subgroup in the full
group. Locator: `mem_inertiaSubgroup_iff`. -/
theorem mem_map_inertiaSubgroup_iff {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (g : E ≃ₐ[F] E) :
    g ∈ (A.inertiaSubgroup F).map (A.decompositionSubgroup F).subtype ↔
      g ∈ A.decompositionSubgroup F ∧ ∀ x ∈ A, g x - x ∈ A.nonunits := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, (mem_inertiaSubgroup_iff A s).1 hs⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, (mem_inertiaSubgroup_iff A ⟨g, hg⟩).2 h, rfl⟩

/-- **PROVED**, ultrametric closure of the open unit ball under `a + b - c`. Locator: Mathlib
`Valuation.map_add_lt`. -/
theorem valuation_add_sub_lt_one {E Γ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation E Γ) {a b c : E} (ha : v a < 1) (hb : v b < 1) (hc : v c < 1) :
    v (a + b - c) < 1 := by
  rw [sub_eq_add_neg]
  exact v.map_add_lt (v.map_add_lt ha hb) (by rwa [Valuation.map_neg])

section Spectral

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **PROVED**, comparison of the spectral valuation with one. Locator:
`coe_spectralValuation`. -/
theorem spectralValuation_le_one_iff (x : AlgebraicClosure K) :
    spectralValuation K x ≤ 1 ↔ spectralNorm K (AlgebraicClosure K) x ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_spectralValuation, NNReal.coe_one]

/-- **PROVED**, comparison of the spectral valuation with one, strictly. Locator:
`coe_spectralValuation`. -/
theorem spectralValuation_lt_one_iff (x : AlgebraicClosure K) :
    spectralValuation K x < 1 ↔ spectralNorm K (AlgebraicClosure K) x < 1 := by
  rw [← NNReal.coe_lt_coe, coe_spectralValuation, NNReal.coe_one]

/-- **PROVED**, the local inertia group of the spectral place, elementwise. Locator:
`mem_inertiaSubgroup_iff`, `mem_decompositionSubgroup_spectral`. -/
theorem mem_spectral_inertia_iff (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    σ ∈ ((spectralValuation K).valuationSubring.inertiaSubgroup K).map
        ((spectralValuation K).valuationSubring.decompositionSubgroup K).subtype ↔
      ∀ y, spectralValuation K y ≤ 1 → spectralValuation K (σ y - y) < 1 := by
  rw [mem_map_inertiaSubgroup_iff]
  constructor
  · rintro ⟨-, h⟩ y hy
    exact (mem_valuationSubring_nonunits_iff _).1 (h y hy)
  · intro h
    exact ⟨mem_decompositionSubgroup_spectral K σ, fun y hy =>
      (mem_valuationSubring_nonunits_iff _).2 (h y hy)⟩

end Spectral

section Assembly

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [CharZero K]

/-- **PROVED**, the non-units of an induced place. Locator:
`mem_valuationSubring_nonunits_iff`. -/
theorem mem_nonunits_of_induced {O : ValuationSubring Qbar}
    {ι : Qbar →ₐ[ℚ] AlgebraicClosure K} (hι : ∀ x, x ∈ O ↔ spectralValuation K (ι x) ≤ 1)
    (x : Qbar) : x ∈ O.nonunits ↔ spectralValuation K (ι x) < 1 := by
  have hO : O = ((spectralValuation K).comap (ι : Qbar →+* AlgebraicClosure K)).valuationSubring :=
    by
      ext y
      rw [hι, Valuation.mem_valuationSubring_iff, Valuation.comap_apply]
      rfl
  rw [hO, mem_valuationSubring_nonunits_iff, Valuation.comap_apply]
  rfl

/-- **PROVED**, the restriction along an embedding inducing `O` lands in the decomposition group
of `O`. Locator: `restrictionHom_apply`, `spectralValuation_galois`. -/
theorem restrictionHom_mem_decomposition {O : ValuationSubring Qbar}
    {ι : Qbar →ₐ[ℚ] AlgebraicClosure K} (hι : ∀ x, x ∈ O ↔ spectralValuation K (ι x) ≤ 1)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    restrictionHom ι σ ∈ O.decompositionSubgroup ℚ := by
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hι, hι,
    ← map_inv, restrictionHom_apply, spectralValuation_galois]

/-- **PROVED**, a decomposition-group element is a restriction, for an embedding inducing `O`.
Locator: `exists_galois_lift`. -/
theorem exists_lift_of_mem_decomposition (hd : DenseRange ((↑) : ℚ → K)) {q : ℚ}
    (hq0 : 0 < ‖(q : K)‖) (hq1 : ‖(q : K)‖ < 1) {O : ValuationSubring Qbar}
    {ι : Qbar →ₐ[ℚ] AlgebraicClosure K} (hι : ∀ x, x ∈ O ↔ spectralValuation K (ι x) ≤ 1)
    {g : GQ} (hg : g ∈ O.decompositionSubgroup ℚ) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, σ (ι x) = ι (g x) := by
  refine exists_galois_lift hd ι g hq0 hq1 fun z hz => ?_
  rw [← spectralValuation_le_one_iff, ← hι] at hz ⊢
  exact apply_mem_of_mem_decompositionSubgroup hg hz

/-- **PROVED**, the residue map induced by `ι` is onto: every element of the closed unit ball of
`\bar K` is congruent, modulo the open unit ball, to the image of an element of `O`. Locator:
`exists_spectralNorm_sub_lt`. -/
theorem exists_residue_lift (hd : DenseRange ((↑) : ℚ → K)) {O : ValuationSubring Qbar}
    {ι : Qbar →ₐ[ℚ] AlgebraicClosure K} (hι : ∀ x, x ∈ O ↔ spectralValuation K (ι x) ≤ 1)
    {y : AlgebraicClosure K} (hy : spectralValuation K y ≤ 1) :
    ∃ x ∈ O, spectralValuation K (y - ι x) < 1 := by
  obtain ⟨x, hx⟩ := exists_spectralNorm_sub_lt hd ι y one_pos
  have hx' : spectralValuation K (y - ι x) < 1 := (spectralValuation_lt_one_iff _).2 hx
  refine ⟨x, ?_, hx'⟩
  rw [hι]
  have e : ι x = y - (y - ι x) := by ring
  rw [e]
  exact (Valuation.map_sub _ _ _).trans (max_le hy hx'.le)

/-- **PROVED**, the restriction carries the inertia group of the spectral place onto the inertia
group of `O`. Locator: `restrictionHom_apply`, `exists_lift_of_mem_decomposition`,
`exists_residue_lift`; Milne, Prop. 8.10, p. 139 and p. 139 (inertia groups). -/
theorem map_restrictionHom_localInertia (hd : DenseRange ((↑) : ℚ → K)) {q : ℚ}
    (hq0 : 0 < ‖(q : K)‖) (hq1 : ‖(q : K)‖ < 1) {O : ValuationSubring Qbar}
    {ι : Qbar →ₐ[ℚ] AlgebraicClosure K} (hι : ∀ x, x ∈ O ↔ spectralValuation K (ι x) ≤ 1) :
    (((spectralValuation K).valuationSubring.inertiaSubgroup K).map
        ((spectralValuation K).valuationSubring.decompositionSubgroup K).subtype).map
          (restrictionHom ι) =
      (O.inertiaSubgroup ℚ).map (O.decompositionSubgroup ℚ).subtype := by
  ext g
  rw [Subgroup.mem_map, mem_map_inertiaSubgroup_iff]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [mem_spectral_inertia_iff] at hσ
    refine ⟨restrictionHom_mem_decomposition hι σ, fun x hx => ?_⟩
    rw [mem_nonunits_of_induced hι, map_sub, restrictionHom_apply]
    exact hσ (ι x) ((hι x).1 hx)
  · rintro ⟨hgD, hgI⟩
    obtain ⟨σ, hσ⟩ := exists_lift_of_mem_decomposition hd hq0 hq1 hι hgD
    refine ⟨σ, ?_, restrictionHom_eq_of_apply ι σ g hσ⟩
    rw [mem_spectral_inertia_iff]
    intro y hy
    obtain ⟨x, hxO, hx⟩ := exists_residue_lift hd hι hy
    have h1 : spectralValuation K (σ (y - ι x)) < 1 := by
      rw [spectralValuation_galois]
      exact hx
    have h2 : spectralValuation K (ι (g x - x)) < 1 := (mem_nonunits_of_induced hι _).1 (hgI x hxO)
    have e : σ y - y = σ (y - ι x) + ι (g x - x) - (y - ι x) := by
      rw [map_sub σ, map_sub ι, hσ]
      ring
    rw [e]
    exact valuation_add_sub_lt_one _ h1 h2 hx

/-- **PROVED**, an arithmetic Frobenius at `O` is the restriction of a local arithmetic Frobenius,
read through the residue identification induced by `ι`. Locator: `exists_lift_of_mem_decomposition`,
`exists_residue_lift`; the arithmetic (`p`-power) convention of Milne, p. 141. -/
theorem exists_frobenius_lift (hd : DenseRange ((↑) : ℚ → K)) {q : ℚ}
    (hq0 : 0 < ‖(q : K)‖) (hq1 : ‖(q : K)‖ < 1) {O : ValuationSubring Qbar}
    {ι : Qbar →ₐ[ℚ] AlgebraicClosure K} (hι : ∀ x, x ∈ O ↔ spectralValuation K (ι x) ≤ 1)
    {p : ℕ} {g : GQ} (hg : IsArithFrob g O p) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ y, spectralValuation K y ≤ 1 → spectralValuation K (σ y - y ^ p) < 1) ∧
        restrictionHom ι σ = g := by
  obtain ⟨σ, hσ⟩ := exists_lift_of_mem_decomposition hd hq0 hq1 hι hg.1
  refine ⟨σ, fun y hy => ?_, restrictionHom_eq_of_apply ι σ g hσ⟩
  obtain ⟨x, hxO, hx⟩ := exists_residue_lift hd hι hy
  have hιx : spectralValuation K (ι x) ≤ 1 := (hι x).1 hxO
  have h1 : spectralValuation K (σ (y - ι x)) < 1 := by
    rw [spectralValuation_galois]
    exact hx
  have h2 : spectralValuation K (ι (g x - x ^ p)) < 1 :=
    (mem_nonunits_of_induced hι _).1 (hg.2 x hxO)
  have h3 : spectralValuation K (y ^ p - (ι x) ^ p) < 1 := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow
      (⟨y, hy⟩ : (spectralValuation K).valuationSubring) ⟨ι x, hιx⟩ p
    have hc' : y ^ p - (ι x) ^ p = (y - ι x) * (c : AlgebraicClosure K) := by
      have := congrArg Subtype.val hc
      push_cast at this
      exact this
    rw [hc', map_mul]
    have hcle : spectralValuation K (c : AlgebraicClosure K) ≤ 1 := c.2
    calc spectralValuation K (y - ι x) * spectralValuation K (c : AlgebraicClosure K)
        ≤ spectralValuation K (y - ι x) := mul_le_of_le_one_right' hcle
      _ < 1 := hx
  have e : σ y - y ^ p = σ (y - ι x) + ι (g x - x ^ p) - (y ^ p - (ι x) ^ p) := by
    rw [map_sub σ, map_sub ι, map_pow ι, hσ]
    ring
  rw [e]
  exact valuation_add_sub_lt_one _ h1 h2 h3

end Assembly

end ZInQ.Contrib.RC53Assist.DecompositionGlue
