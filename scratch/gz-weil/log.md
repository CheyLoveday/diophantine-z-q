# gz-weil results log

Task: make gz-hl3's split of `hL3` net negative by turning `StrongWeilCurve` and `IsogenyLattice`
(Eichler–Shimura + Faltings, analytic form) into printed form or theorems, restricted to what the proof uses.

## Setup (2026-11-15 04:40 PST)
- base c118e9d2 (wip/gz-hl3). Build tree copied (reflink) from ~/dzq-wt/gz-hl3 (same ZInQKernel tree, built 11-15 04:12).

## Uses (VERIFIED, read)
- `StrongWeilCurve`, `IsogenyLattice` are used only in `eichlerShimuraParamAt_of_leaves`
  (GrossZagierHeegner.lean §5), which feeds `grossZagierHeegner_of_leaves` (all E) and
  `shimuraCMParamCd_of_leaves` (Cd.lean).
- The only consumer of hL3 in the chain is `GZDecomp.grossZagierCd_of_leaves`, at `E = C_d`,
  `d ≡ 5 mod 8` squarefree, `f` from `modular_cd`. GZStatements.Weak shows the Cd form
  `GrossZagierHeegnerCd` closes the chain (`frozenTarget_of_..._fhNonvanishingCd_grossZagierHeegnerCd`).
- So the parametrization leaf needed is exactly `ShimuraCMParamCd` (Cd.lean):
  `∀ d ≡ 5 (8) squarefree, EichlerShimuraParamAt C_d`.
- In it, `N = 32 d²` is forced (`GZStatements.level_eq_of_coeff_cd`, proved) and
  `eichler f` depends only on `coeff f n = aₙ(C_d) = heckeCoeff d n`
  (`GZStatements.LFunction_cd_eq_heckeCoeff`, proved).

## Step 1: the twist reduction (VERIFIED, compiled, `scratch/gz-weil/Twist.lean`, 04:55 PST)
- `eichlerCd d z = Σ heckeCoeff d (n+1)/(n+1) e((n+1)z)`; summable for Im z > 0 (bound |heckeCoeff d m| ≤ (2m+1)³).
- `twist_formula`: d Φ_d(z) = Σ_{a mod d} 𝓕χ_d(a) Φ₁(z + a/d)  (χ_d = (·/d), Fourier inversion on ZMod d).
- `period_identity`: γ ∈ Γ₀(32d²) ⇒ d(Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ(a)(Φ₁(γ'_a τ'_a) − Φ₁(τ'_a)), γ'_a ∈ Γ₀(32)
  (Tau Ceti intertwining lemma + reindexing a ↦ aD²).
- `jacobiChar_isPrimitive` (d odd squarefree), `dft_jacobiChar`: 𝓕χ = g·χ, `gaussD_sq`: g² = d (d ≡ 1 mod 4).
- `scalePP`, `g₂_scalePP`, `g₃_scalePP`; `isPeriodLattice_cd_iff`: IsPeriodLattice C_d L ↔ g₂ = 4d², g₃ = 0.
- `periods_cd`, `eichlerShimuraParamAt_cd`, `shimuraCMParamCd_of_modularParamC1 : ModularParamC1 → GZHL3.ShimuraCMParamCd`.
- `modularParamC1_of_leaves : WU → StrongWeilCurve → IsogenyLattice → ModularParamC1` (new leaf no stronger).
- `grossZagierHeegnerCd_of_leaves hU hP hHP hGZ hGC : GrossZagierHeegnerCd`.
- axioms: [propext, Classical.choice, Quot.sound] for all three.
