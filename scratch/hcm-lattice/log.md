# hcm-lattice results log

Base: wip/leaf-fold33b d879bb73. Build tree seeded from ~/dzq-check2 (same HEAD) by reflink copy.

## Plan (statements)
- (3) `locLat_sInvLat`: for every lattice 𝔞 ⊂ K (κ𝔞 = period lattice), every idele s and every p:
  `(s⁻¹𝔞)_p = s_p⁻¹ 𝔞_p` in `K_p = ∏_{v|p} K_v`, where `𝔞_p` = closure of 𝔞 in `K_p`.
- (1) `IsAnalyticIso` over ℙ²-coordinates (holomorphic lift to ℂ³∖0, nonvanishing differential, bijection ℂ/Λ ≅ E(ℂ));
  Weierstrass map satisfies it.
- (2) a holomorphic bijection ℂ/Λ → E_{L₀}(ℂ) with 0 ↦ O is z ↦ ξ_{L₀}(αz) (Liouville argument).

## Compile log
- T0.lean (#check probes): OK, 2m14 (mostly import).
- Lattice.lean: COMPILED (no errors, 7 s). VERIFIED:
  - `isOpen_latHat` : 𝔞̂ open in 𝔸_{K,f} for every lattice 𝔞 (κ𝔞 a period lattice), via `N·𝓞_K ⊆ 𝔞`
    (`exists_nat_mul_integers_mem`, from `two_coords`).
  - `locLat_sInvLat` : `(sInvLat s 𝔞)_p = s_p⁻¹ • 𝔞_p` for every lattice 𝔞, idele s, p (K_p = ∏_{v∣p} K_v,
    𝔞_p = closure of 𝔞 in K_p, s_p = p-component of s). Proof: U = s_f⁻¹𝔞̂ open, K dense in 𝔸_{K,f}.
  - `rep_local_of_global` : `s_f v − u ∈ 𝔞̂ → ∀ p, v − s_p⁻¹u ∈ (s⁻¹𝔞)_p`.
- Analytic.lean: COMPILED. VERIFIED: defs `IsProjCoord`, `IsHoloLift`, `IsHolomorphicMap`, `wedge`, `IsImmersion`,
  `InducesBij`, `IsAnalyticIso`; `deriv_derivWeierstrassP_ne` (℘'(z₀)=0 ⇒ ℘''(z₀)≠0, via disc ≠ 0 and isolated zeros);
  `toPoint_isImmersion`, `toPoint_isAnalyticIso` (Weierstrass map z ↦ [℘ : ℘'/2 : 1] is an analytic isomorphism
  ℂ/L → E_L(ℂ); at lattice points the lift [w + w³h : (−2 + w³k)/2 : w³] from Mathlib's ℘[L - l₀]).
- HCMLattice.lean (Analytic + §C): COMPILED, no sorry. VERIFIED:
  - projective-coordinate lemmas `IsProjCoord.{ne_zero_iff,coords,of_zero,homog,cross_eq_zero,eq_of_cross}`;
  - `exists_local_ext`: x'/(2y) has local holomorphic extensions everywhere (y'/(3x²−g₂/4) near y=0 using disc≠0;
    −u'+uq'/(2q) near O with u=X/Y, w=Z/Y, q=1−a₄uw−a₆w², wq=u³);
  - `exists_entire_of_local` (gluing across a dense set), `eq_const_of_periodic` (Liouville);
  - `exists_local_lift'` (hcm-dict's lift, for surjective holomorphic ξ);
  - `eq_toPoint_of_holo`: holomorphic ξ : ℂ → E_{L₀}(ℂ) inducing a bijection ℂ/L ≅ E_{L₀}(ℂ) with ξ(0)=O is
    z ↦ ξ_{L₀}(αz) with IsScale L₀ L α. (The Weierstrass-map step: proved, no Silverman leaf needed.)
