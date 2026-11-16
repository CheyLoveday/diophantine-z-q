# bfh-gamma0 results log

## Setup
- Merged origin/main (2880fef1e) into wip/bfh-gamma0 (merge e4b8cc397). VERIFIED.
- Build tree copied from ~/dzq-check2 (at origin/main 2880fef1e); `lake build ZInQKernel.Contrib.OneProof.BFHKronecker` OK (10121 jobs). VERIFIED.

## Gamma0New.lean (scratch; compiles, one unused-variable lint only) VERIFIED
- `IsGamma0New F`: F ∈ S_k(Γ₀(N)) Petersson-orthogonal to `V_d g` for all g ∈ S_k(Γ₀(M)), dM | N, M ≠ N.
- `restrict_levelRaise_gamma0`: restriction Γ₀(N)→Γ₁(N) commutes with V_d.
- `relIndex_gamma1_gamma0_ne_zero`.
- `isGamma0New_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) : IsGamma0New (f.toCuspFormGamma0 hχ)`
  (mem_cuspFormsNew_iff + peterssonInnerCosets_restrict_restrict + restrict_toCuspFormGamma0).
- `heckeGamma0 N k`: ℤ-linear extension of Tau Ceti's `heckeSlashGamma0CuspFormEnd` (untwisted Γ₀(N)
  double-coset operators) to the Hecke ring 𝕋(Δ₀(N), Γ₀(N)).
- `coe_heckeGamma0`: on functions, `heckeGamma0 T F` = Tau Ceti's nebentypus action
  `heckeRingHomCuspCharSpace k 1 T` on the restriction of F (via `twistedHeckeSlashSum_eq_heckeSlashSum`).
