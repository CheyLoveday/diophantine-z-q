# faltings5-lower results log

Base: 9a100aa72 (leaf-fold22b). Started 2026-11-15 05:16 PST.

## Statement analysis (VERIFIED, read)
- `GroupModel.height 𝒢 = ⨅ g (M : MetrizedModel A L g) (_ : M.model = 𝒢), M.hodge.modelHeight` (EReal),
  ZInQKernel/HDecomp/Faltings/Height.lean:235.
- Direction: FaltingsLemma5Lower ⟺ h(𝒩B) ≤ h(𝒩A) + ½ log deg φ. Upper bound of an infimum by an infimum:
  for each metrization M of 𝒩A, build a metrization M' of 𝒩B with modelHeight M' ≤ modelHeight M + ½ log deg φ.
  No product formula / uniformization uniqueness needed (no `AnalyticUniformizationUnique`).
- `modelHeight_eq`: for η ∈ lattice, η ≠ 0: h = (log secIndex Λ η − ½ Σ_σ log (‖coeff σ η‖² covol(periods σ)))/[K:ℚ].
- Bundle-field help: `AvSplit.MilneIsogenyQuasiInverse` (TailQ.lean:1207; field `OpenAddedLeaves17.milneIsogenyQuasiInverse`,
  available at TailZ23 L814 as `l.milneIsogenyQuasiInverse`, l : OpenAddedLeaves12). Plan: use it for the étaleness
  of φ at the origin (dφ injective on tangent vectors via Tangent.lean `eq_one_of_comp_intCast`).

## Plan (05:55)
Reduction `faltingsLemma5Lower_of` from three glue statements, then prove them:
- P1 `cotMap 𝒩A 𝒩B φ_N` bijective (étale at origin; Milne + Tangent.lean + dims).
- P2 surjectivity of `p ↦ p ≫ φ_N` on `Pts τ` (lifting ℂ-points along finite surjective).
- P3 `{p : 𝒩A.Pts τ // p ≫ φ_N = 1}` finite with card ≤ isogDeg φ.
Archimedean: Λ_B := Φ_A⁻¹(ker φ_N(ℂ)) ⊇ Λ_A, index = #ker φ_N(ℂ)_τ ≤ deg φ; covol Λ_A = index · covol Λ_B
(Mathlib `ZLattice.covolume_div_covolume_eq_relIndex` is for ι → ℝ only; transfer needed).
