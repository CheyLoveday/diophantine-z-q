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
