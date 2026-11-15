# pb-sanity results log

Task: validate the definitions of pb-bypass (ZInQKernel/Contrib/OneProof/PanBerger.lean, merged from
origin/wip/pb-bypass c1636db9 into this branch at 73447464).

## Setup
- Build: copied (reflink) ~/dzq-wt/pb-bypass/.lake/build and lean/.lake/build; `lake build
  ZInQKernel.Contrib.OneProof.PanBerger ZInQKernel.Contrib.G9.KerTheta ZInQKernel.Contrib.G9.BdREmb`
  completed (VERIFIED, 2026-11-15 06:30).

## Plan (cheapest first)
1. B_cris^+ ≠ 0, B_cris ≠ 0, B_st ≠ 0: 0 ∉ tMonoid, via p^m·∏ log[ε_i] ≠ 0 in A_cris
   (argument in A_inf only: ker θ = (ξ) from Contrib/G9/KerTheta, ξ-adic separatedness of
   [ε]-1, lattice (N-1)!·A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p], θ[1/p], ∩ p^n O = 0).
2. bcrisAct is a group action by ring automorphisms; stAct σ bijective; stAct group law ⇔ cocycle.
3. Potentially trivial representations are pst.
4. Statement check of PanPrinted / BergerPrinted vs prints.

## Step 1: non-degeneracy of B_cris^+, B_cris, B_st (scratch/pb-sanity/Sanity1.lean) — COMPILES
`lake env lean scratch/pb-sanity/Sanity1.lean`: no error, no warning (VERIFIED 2026-11-15 ~08:00).
Proved (namespace HDec.PkgI4.PanBergerSplit):
- `exists_not_mem_xi_pow`, `eq_xi_pow_mul`: every x ≠ 0 in A_inf is ξ^s·w with θ(w) ≠ 0
  (ξ = p − [p♭] of Contrib/G9/KerTheta; via WittVector.exists_eq_pow_p_mul, p-regularity mod ξ^n,
  and "c ∈ O♭ divisible by all (p♭)^n ⇒ c = 0").
- `latG_bound`, `acris0_le_latSub`: N!·A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p].
- `pow_mul_prod_logOf_ne_zero`: p^m · ∏ log[ε_i] ≠ 0 in A_cris for every finite list of ε_i with
  ε_i^♯ = 1, ε_i ≠ 1 (leading coefficient argument with θ[1/p] and ∩ p^n O = 0).
- `zero_notMem_tMonoid`; instances `nontrivial_bcrisPlus`, `nontrivial_bcris`, `nontrivial_bst`;
  `algebraMap_qp_bst_injective`; `logOf_not_isNilpotent`, `logOf_ne_zero`, `isUnit_logOf_bcris`.
- `nonempty_tEps` (ε = (1, ζ_p, ζ_{p²}, …) has ε^♯ = 1, ε ≠ 1), `exists_t`.

## Step 2: Galois action (Sanity1.lean, section Action) — COMPILES (VERIFIED ~09:00)
- `bcrisAct_mul`, `bcrisAct_one`, `bcrisAut : GQp p →* (Bcris p ≃+* Bcris p)`: G_Qp acts on
  B_cris by ring automorphisms (group homomorphism), via functoriality of oAct, flatAct, W(·),
  locAct, adicMap (`adicMap_comp'`, `adicMap_id'`), bcrisPlusAct.
- `stEquiv σ : Bst p ≃+* Bst p` (each stAct σ is a ring automorphism; unconditional),
  `stAct_one` (logU 1 = 0; via uSigma 1 = 1, log[1] = 0).
- `uSigma_spec` (existence of u_σ via KerTheta.dvd_of_coeff_zero), `untilt_uSigma` (u_σ^♯ = 1, so
  the `else 0` branch of logU never occurs: `logU_eq`), `uSigma_mul` (u_{στ} = σ♭(u_τ)·u_σ).
- `stAct_mul_iff`: group law on B_st ⇔ cocycle logU(στ) = logU σ + σ(logU τ).
- `LogAdditive` (Prop: log[xy] = log[x] + log[y] in A_cris for x^♯ = y^♯ = 1) — NOT proved;
  `stAct_mul (hL : LogAdditive p)`: group law given it.

## Step 3: potentially trivial representations (Sanity1.lean, section Pst) — COMPILES (VERIFIED ~09:30)
- `isSemistableOver_of_trivial`: ρ trivial on G_K ⇒ IsSemistableOver K ρ (any K; D_st,K ≅ Hom(V, B_st^{G_K}),
  finrank of Hom computed through ranks, so no finite-dimensionality of B_st^{G_K} is needed).
- `isPst_of_trivial_on`, `localIsPst_one` (trivial n-dim ℚ̄_p-rep satisfies LocalIsPst).
- `quadChar` (σ ↦ σ(α)/α for α² ∈ ℚ_p, α ≠ 0; includes the unramified quadratic character),
  `isPst_quadChar`.
