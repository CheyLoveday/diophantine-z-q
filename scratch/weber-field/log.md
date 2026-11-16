# weber-field results log

Target: `X1Igusa.Weber.WeberFieldComparison` (scratch/x1-igusa/WeberComparison.lean, base 62d9b7c5).

## Setup
- 11-16 02:55 build dirs copied (reflink) from ~/dzq-wt/x1-igusa (same commit 62d9b7c5).

## Inventory (VERIFIED by reading the tree)
- `T5Glue.pp τ = ⟨1, τ⟩`, `jL = 1728 g₂³/discL`, `weber = g₂g₃/Δ · ℘` when `g₂g₃ ≠ 0` (RingClassLattice.lean:65-78).
- `T5Glue.G_eq_E`: `(ppD τ).G k = 2ζ(k) E_k(τ)` (k ≥ 3); `disc_ppD_ne_zero`: `Δ(⟨1,τ⟩) ≠ 0`.
- Vendored uniformization `PeriodPair.isUniformization_toPoint` (AnthropicFLT): `toPoint` additive, surjective,
  kernel = lattice, on `L.weierstrassCurve = ⟨0,0,0,-g₂/4,-g₃/4⟩`, `x(toPoint z) = ℘(z)`.
- Tau Ceti `WeierstrassCurve.eval_ΨSq_eq_zero_iff_zsmul_eq_zero` (any field), `eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero`
  (alg. closed), `zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero`, `ΨSq_ne_zero_of_Δ_ne_zero`.
- Mathlib `WeierstrassCurve.map_ΨSq`, `Polynomial.isLocalization`, `IsLocalization.under_map_of_isPrime_disjoint`,
  `differentiableOn_tsum_of_summable_norm`, `EisensteinSeries.r_mul_max_le`, `auxbound1/2`, `summable_one_div_norm_rpow`.

## Plan
Ideal `I = {F ∈ ℚ[J][T] : F(j(τ), f₁(τ)) = 0 on ℍ}` with `f₁ = g₂g₃℘(1/N)/Δ` (holomorphic on ℍ); prime by the
identity theorem; `I ∩ ℚ[J] = 0` since `j(i) = 1728`, `j(ρ) = 0`; contains the cleared universal division polynomial
`Φ_N`; algebraic lemma (localization at `ℚ[J]∖0`, PID `ℚ(j)[T]`) gives `θ` with `I = ker(T ↦ θ)`; `θ = w(P)`, `P` of
exact order `N` by the division-polynomial criterion on both sides.
- 11-16 ~03:00 PartA.lean (algebraic lemma exists_root_of_isPrime, clearing exists_clears, ev2_ΨSq, evK_clears) compiles, no sorry.
- 11-16 ~03:03 PartA.lean + points: exists_point_of_root (Kbar side), curveC_smul, eval_ΨSq_weber_eq_zero_iff (ℂ side, via vendored uniformization) compile.
- 11-16 ~03:10 WeberField.lean: X1Igusa.Weber.weberFieldComparison : WeberFieldComparison COMPILES; #print axioms: [propext, Classical.choice, Quot.sound]. VERIFIED.
- 11-16 03:13 `ZInQKernel/Contrib/OneProof/WeberField.lean` (new module; verbatim copies of `wOf`, `evAn`, `evAlg`,
  `WeberFieldComparison`, `adjoin_wOf` from scratch/x1-igusa/WeberComparison.lean, checked by string match):
  `lake build ZInQKernel.Contrib.OneProof.WeberField` OK (11356 jobs, all replayed but the new one, 7.3 s). VERIFIED.
- 11-16 03:14 #discharges (scratch/weber-field/Discharges.lean -> Discharges-output.txt): 61 open, 2609 theorems checked, 16 discharge one; r16CoreY by X1Igusa.r16CoreY_of_picZero_igusaDS (imported); weberFieldComparison and its main lemmas: standard axioms. VERIFIED.
- 11-16 03:15 autofold.json (x1-igusa's spec, afTateCharPolyPicZero flag updated, imports WeberField); dry run: strict count 45/10 on 55 -> 47/9 on 56; strictest 43/12 -> 45/11 (identical to x1-igusa: kinds/flag prefixes unchanged); FoldDryRun.lean compiles, sixContactMin_of_open31 standard axioms. VERIFIED.
