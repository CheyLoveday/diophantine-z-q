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

## Step 4: K_0 ⊆ B_st^{G_K} (Sanity1.lean, section K0) — COMPILES (VERIFIED ~11:40)
- `pow_mul_prod_logOf_mul_ne_zero`: main lemma with an extra factor y ≠ 0 of A_inf.
- `embW_injective`: A_inf → B_st is injective. `stAct_embW`: equivariant (σ acts by W(σ♭)).
- `muFlat` (μ♭ = (μ, μ^q, μ^{q²}, …) for μ^m = 1, p ∤ m, pq ≡ 1 mod m), `untilt_muFlat`,
  `flatAct_muFlat`; `teichB_pow_mem_bstInv`: [μ♭]^i ∈ B_st^{G_K} when μ ∈ K.
- `coe_theta_zpToW`: θ ∘ (ℤ_p → A_inf) is the inclusion ℤ_p ⊆ ℂ_p.
- `linearIndependent_teichB`: 1, [μ♭], …, [μ♭]^{d−1} (d = deg minpoly_{ℚ_p} μ) are ℚ_p-linearly
  independent in B_st; `natDegree_minpoly_le_finrank_bstInv`: if B_st^{G_K} is finite-dimensional
  then dim ≥ [ℚ_p(μ):ℚ_p]. (K_0 = ℚ_p(μ) for μ of order p^f − 1: Serre, Local Fields IV §4,
  UNVERIFIED locator; standard.)

## Step 5: deliverables (VERIFIED ~12:10)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` OK; `scratch/pb-sanity/Discharges.lean`
  output in discharges-output.txt: no new discharge from PanBergerSanity (expected: sanity file);
  r11r12 by panBerger_of_printed; "63 open hypotheses, 2048 theorems checked, 8 discharge one".
- autofold.json (pb-bypass spec, flags updated): dry run "strict count: 46/10 on 56 -> 48/9 on 57;
  strictest 45/11 -> 47/10"; the dry-run module (FoldDryRun.lean) compiles with no error.
- docs/research/pb-sanity.md drafted: verdict printed form for both leaves.
