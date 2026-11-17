# bdr-inv: `B_dR^{G_F} = F` proved in Lean (−1 field, −1 strict GLUE)

Task bdr-inv, 2026-11-17. Base `wip/leaf-fold33b` at fe2f0d4a5. Log: `scratch/bdr-inv/log.md`.

## Verdict

The research field `bdRInvariantsPrinted : DeRhamPrint.BdRInvariantsPrinted`
(`ZInQKernel/Contrib/OneProof/DeRhamPrint.lean:70`; Fontaine's `B_dR^{G_K} = K` in the Lean form
`finrank ℚ_[p] (bdrFix p F) = finrank ℚ_[p] F` for every `F` finite over `ℚ_p`, `G_F` acting through `gfToGqp`;
kinds row "pending review", GLUE/GLUE) is **proved outright, statement unchanged, no new leaf, no new hypothesis**:

```
theorem BdRInv.bdRInvariantsPrinted_proof : DeRhamPrint.BdRInvariantsPrinted
```

`ZInQKernel/Contrib/OneProof/BdRInvariants.lean` (new contributor-kit file, same content as
`scratch/bdr-inv/BdRInv.lean`, about 490 lines); axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED).
The statement is imported from `DeRhamPrint`, not restated, so it is verbatim by construction. The statement is
true as written (so not false, and not vacuous: `[F : ℚ_p] ≥ 1`, and the proof gives an explicit isomorphism
`F ≅ B_dR^{G_F}`).

Inputs used, all theorems already in the tree (no open field is used):

* Tate's theorem `ℂ_p(i)^{G_K} = 0` (`i ≠ 0`): `ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof`;
* Ax–Sen–Tate `ℂ_p^{G_K} = K`: `ZInQ.Contrib.CloudB3W11.axSenTate_proof`;
* bdr-kertheta: `B_dR^+` is a DVR (`isDiscreteValuationRing_BDeRhamPlus`), `B_dR = Frac(B_dR^+)`
  (`isFractionRing_BDeRham`), `ker θ = (ξ)` in `W(O♭)` (`ker_fontaineTheta_Cp`), maximal ideal `(ξ)`;
* derham-print's TDict: `ε`, `[ε] − 1 ∉ (ξ²)` (`xe_not_mem_sq`), `mkSeq`, `plus`;
* g9-derham (OneProof chain copies): `θ⁺` equivariant (`thetaPlusCp_bdrPlusMap`), the Hensel lift and its
  naturality (`exists_hensel_lift`, `hensel_lift_natural`), `range_gfToGqp_eq`, `phiF`, `fieldF`;
* Mathlib's `cyclotomicCharacter.spec`.

## 1. Checks (all VERIFIED)

| check | outcome |
| --- | --- |
| `lake env lean scratch/bdr-inv/BdRInv.lean` | no errors, no warnings; `#print axioms` standard |
| `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.BdRInvariants` | success (16039 jobs, the new module 54 s); `frozenTarget` axioms standard |
| `#discharges` (`scratch/bdr-inv/Discharges.lean`, output `discharges-output.txt`) | `DISCHARGES [OpenResearchLeaves39.bdRInvariantsPrinted] by BdRInv.bdRInvariantsPrinted_proof`, `still assumes: []`, axioms standard |
| `autofold.py scratch/bdr-inv/autofold.json --dry-run` (`FoldDryRun.lean.txt`) | **strict 16/15 on 31 → 16/14 on 30; strictest 16/15 → 16/14**; generates `sixContactMin_of_open58` |
| dry-run module (line 1, the count line, stripped), `lake env lean` | compiles; `HDec.HSyn.sixContactMin_of_open58` axioms standard |

For the lead: `python3 scripts/one_proof/autofold.py scratch/bdr-inv/autofold.json` (no `--allow-rise`), then the
usual post-fold checks. `kinds.tsv` loses the row `research bdRInvariantsPrinted`. With it, derham-print's
`deRhamH1AbVarT_of_leaves` needs only `deRhamVpAbVarPrinted` (Fontaine: `V_p(A)` is de Rham) and the textbook
field `mumfordTorsionAlgClosed`.

## 2. The proof

Notation: `O = 𝓞_ℂ_p`, `B⁺ = BDeRhamPlus O p` (Mathlib), `B = BdR p` (pkg-I4, `= Frac B⁺`), `θ⁺ : B⁺ → ℂ_p`,
`σ⁺ = DR.bdrPlusMap p (oAct p σ)` (so `bdrAct σ` is the localization of `σ⁺`), `K = fieldF p F ⊆ ℚ̄_p` with
`G_K = K.fixingSubgroup = gfToGqp(G_F)` (`range_gfToGqp_eq`).

**Step 1 (cyclotomic cocycle of `T = [ε] − 1`), `bdrPlus_T`.** For every `σ ∈ G_{ℚ_p}` there is `w ∈ B⁺` with
`σ⁺(T) = T·w` and `θ⁺(w) = χ(σ)` (Mathlib's `cyclotomicCharacter`, through `cyc`).

* Roots of unity: `zq n ∈ ℚ̄_p` with `zq 0 = 1`, `zq 1` a primitive `p`-th root, `zq (n+1)^p = zq n`; their images
  form a TDict `RootSystem` `Zq`, `ε = eps Zq`. Building them in `ℚ̄_p` (not in `ℂ_p`) gives
  `σ(ζ_m) = ζ_m^{a_m}` with `a_m = (χ(σ) mod p^m).val` from `cyclotomicCharacter.spec` (`cpAct_zq`).
* In the tilt, `σ(ε) = ε^{a_m} · ρ_m^{p^m}` (`preTiltMap_eps`) with `ρ_m = (σ(ζ_{n+m}) ζ_{n+m}^{-a_m})_n`
  and `ρ_m^♯ = 1` (`untilt_rho`); checked componentwise in `ℂ_p`.
* `[ρ] − 1 ∈ ker θ = ξ·W(O♭)`, so `[ρ] − 1 = T·r` with `‖θ⁺ r‖ ≤ C := ‖θ⁺(v)‖⁻¹`, `T = ξ·v` (`teich_sub_one`;
  `v` a unit since `T ∉ (ξ²)`). Geometric sums give `σ⁺T = [ε]^a [ρ]^{p^m} − 1 = T·w_m` with
  `θ⁺(w_m) = a_m + p^m θ⁺(r)` (`bdrPlus_T_approx`); `w_m` does not depend on `m` (`T ≠ 0`, domain), and
  `‖a_m − χ(σ)‖ ≤ ‖p‖^m` (`PadicInt.ker_toZModPow`), so `θ⁺(w) = χ(σ)`.

**Step 2 (invariants are units of `B⁺`), `key`.** `T` is a uniformizer of the DVR `B⁺` (`irreducible_T`). For
`x ∈ B^{G_K}`, `x ≠ 0`: `x = a/b`, `a = u_a T^j`, `b = u_b T^k`, so `x·T^k = u·T^j` with `u` a unit. Applying
`σ ∈ G_K` and Step 1: `u·w^k = σ⁺(u)·w^j`, so `θ⁺(u)·χ(σ)^k = σ(θ⁺u)·χ(σ)^j`, i.e. `θ⁺u ∈ ℂ_p(j−k)^{G_K}`. As
`θ⁺u ≠ 0`, Tate's theorem forces `j = k` (`tate_step`), so `x = u ∈ (B⁺)^×`.

**Step 3 (`F ≅ B^{G_F}`).** The Hensel lift `ι₀ : F → B⁺` of `F ≅ K ⊆ ℚ̄_p ⊆ ℂ_p` through `θ⁺`
(`exists_hensel_lift`) is `G_K`-invariant (`hensel_lift_natural`: `θ⁺(σ⁺ ι₀ y) = σ(y) = y`). So
`Φ : F → B^{G_F}`, `y ↦ ι₀ y`, is `ℚ_p`-linear and injective. Surjective: for `x ≠ 0` invariant, `x = u` (Step 2),
`θ⁺u ∈ ℂ_p^{G_K} = K` (Ax–Sen–Tate), say `θ⁺u = y`; then `x − Φ(y)` is invariant with `θ⁺ = 0`, hence not a unit,
hence `0` by Step 2. `finrank` is preserved by `LinearEquiv.ofBijective Φ`.

This is the classical argument (Brinon–Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §4.3,
the computation `B_dR^{G_K} = K`; Fontaine, Astérisque 223 (1994), Exp. II; locators UNVERIFIED). The only
deviation: instead of `t = log[ε]` with `σ(t) = χ(σ)t` (which needs `[ε]^{χ(σ)}` for `p`-adic exponents and the
logarithm's functional equation), it uses `T = [ε] − 1`, for which only `θ(σ(T)/T) = χ(σ)` is needed, obtained by
`p`-adic approximation through `A_inf = W(O♭)`.

## 3. By-products usable elsewhere (all in `BdRInv`, compiled)

* `bdrPlus_T`: `σ([ε] − 1) = ([ε] − 1)·w`, `θ(w) = χ(σ)` — the Galois action on `gr¹ B_dR = ℂ_p(1)`.
* `key`: every nonzero `G_K`-invariant of `B_dR` is a unit of `B_dR^+` (`K` any finite subextension of `ℚ̄_p`).
* `preTiltMap_eps`, `untilt_rho`, `teich_sub_one`, `irreducible_T` (`[ε] − 1` is a uniformizer of `B_dR^+`).

## 4. Files

* `scratch/bdr-inv/BdRInv.lean` — the proof (imports `DeRhamPrint`, `AxSenTate`, `TateTwistInvariants`).
* `ZInQKernel/Contrib/OneProof/BdRInvariants.lean` — the same, as a new contribution module (no existing file
  under `ZInQKernel/` edited).
* `scratch/bdr-inv/autofold.json`, `FoldDryRun.lean.txt`, `Discharges.lean`, `discharges-output.txt`, `Probe.lean`.
