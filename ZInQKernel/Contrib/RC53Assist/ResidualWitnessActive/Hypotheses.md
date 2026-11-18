# Active residual witness: hypothesis inventory

The two targets are the constructors `ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine`
and `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual` (manuscript Lemma
`ex:limits-residual-bound`, tex 4453–4648). Both are applied in `Witness.lean` to the instance below
(`activeGenuineCounts`, `activeActualCounts`). This file marks every input of the two constructors
as GENUINE (the hypothesis carries content at this instance: its premises are realized, or its
data are nonzero genuine objects) or VACUOUS/TRIVIAL (it holds for a degenerate reason), with the
theorem of `Witness.lean` that shows it.

## The instance

* Field `K = ℚ(i)`, radicand `k = −1` with `α = i`, `A = 0`, one complex place.
* Curve `E₁₁ : y² = x(x − 11)(x + 33)`; at every finite place the integral equation
  `y² = x³ + 22x² − 363x` (discriminant `2304 · 11⁶`), whose generic fibre is the base change of
  `E₁₁`; all four points killed by `2` are rational over every completion.
* `N = 66`, moving prime `r = 5`, derivative primes `D = {7}`, active prime `13`.
  The charged primes are `{2, 3, 5, 7, 11}` (`actCharged_eq`).
* Supports: `S₀ = Sloc = S` = places above `{2, 3, 5, 7, 11}`; `S'` = places above
  `{2, 3, 5, 7, 11, 13}`; `S' − S` is nonempty (`newPlaces_nonempty`).
* Coefficients: the actual residual module `𝔽₂ ⊗ M₁` of `E₁₁` over `S`, coefficient index `j = 0`,
  trivial character (at `j = 0` the coefficient ring `A₁ = 𝔽₂` has only the trivial unit).
* Labels (`actCond`): relaxed derivative above `7`; old Kummer above `2, 3, 11`; full above `5`.
* Local conditions (`actΔ`), genuine complexes with cochain maps into `C^•(G_{K_v}, M)`:
  the Kummer complex above `2, 3, 11` (`actΔ_U_oldKummer`), `τ≤1 C^•(G_{K_v}, M)` above `7`
  (`actΔ_U_derivRelaxed`), the full local complex above `5` (`actΔ_U_full`); at the active places the
  unramified condition `C^•(G_q/I_q, M)` of the support change.
* Residual model `Dsel = actSel`: the cohomology of the global complex, of each condition and of
  each local complex, with the induced maps (`formalData`); degrees `s = {0, 1, 2}`; bounds
  `a = 0`, `b = 3`.
* Original-support data `Dfull = actFull`: the old conditions, and at the active places the
  unramified condition thickened by the cone of its identity; quotient `W = actW`.
* Minimal model `L = actL`: the cohomology of the residual cone, with zero differential.

## The inputs of `residualRankCounts_genuine`

| Input | Value at the instance | Status | Evidence |
|---|---|---|---|
| `K`, `Ew`, `hEw` | `ℚ(i)`, integral equation of `E₁₁` at every place | GENUINE | `smallLocal_elliptic`, `local_models_are_baseChanges` |
| `h410`, `h51`, `h28`, `h23`, `h788` | printed inputs (Milne I.4.10, I.5.1, I.2.8, I.2.3; Nekovář 7.8.8(ii)) | explicit hypotheses, unchanged | — |
| `k`, `α`, `hα`, `hK` | `−1`, `i` | GENUINE | `smallAlpha_radicand`, `smallK_complex` |
| `N`, `hN` | `66` (support parameter) | GENUINE | — |
| `A`, `hA` | `0`; `ω(1) = 0 ≤ 0` | TRIVIAL (`k = −1` has no prime factor) | `by simp` |
| `r`, `hr` | `5` | GENUINE | — |
| `D`, `hD`, `hDodd` | `{7}`, prime and odd | GENUINE (nonempty) | `actD_prime`, `actD_odd` |
| `cond` | `actCond` | GENUINE | `exists_derivative_place`, `exists_oldKummer_place` |
| `hcondD` | relaxed derivative only above `7` | GENUINE: the premise is realized at the place above `7` | `actCond_derivative`, `exists_derivative_place` |
| `hfull` | four rational `2`-torsion points at old-Kummer places | GENUINE: the premise is realized at the places above `2, 3, 11` | `actCond_full_torsion`, `exists_oldKummer_place` |
| `w`, `hw` | a complex place | GENUINE | `smallInfinitePlace_complex` |
| `Sloc` | `S` | GENUINE | — |
| `Dsel` | residual model of the genuine Selmer data with Kummer, derivative and full conditions; nonzero `U`, `L` | GENUINE | `formalData`, `act_U_positive`, `act_L_positive` |
| finiteness of `Dsel.G`, `Dsel.U`, `Dsel.L` | from the printed global and local finiteness | GENUINE | `actSel_G_finite`, `actSel_U_finite`, `actSel_L_finite` |
| `s`, `hs` | `{0, 1, 2}` | GENUINE | — |
| `eG` | `Gⁿ ≅ Hⁿ(G_{K,S₀}, 𝔽₂²)`, `n = 0, 1, 2` | GENUINE | `actEG` |
| `hUm` | condition part vs. genuine condition dimensions | GENUINE: left side `≥ 2`; holds **with equality**, the old Kummer rows by Mattuck's exact dimension | `act_hUm`, `act_hUm_eq`, `act_U_positive`, `oldKummer_places_exact` |
| `hLm` | local part vs. genuine local dimensions | GENUINE: left side `≥ 2`, `Σ (h⁰ + h¹) ≤ Σ (h⁰ + h¹ + h²)` | `act_hLm`, `act_L_positive` |
| `S`, `S'`, `hSS'`, `hS'` | `S ⊊ S'`, both finite | GENUINE: nonempty active support | `smallS_sub`, `smallS'_finite`, `newPlaces_nonempty` |
| `pr`, `hset` | `2`, the finite Nekovář setting | GENUINE | `smallSetting` |
| `M` and its instances | the actual residual module | GENUINE | `smallM_facts` |
| `ψ`, `hψ` | the factorizations of the localizations at the new places through `G_q/I_q` | GENUINE (index set nonempty; factorization proved in the repository) | `urFactor`, `urFactor_spec`, `newPlaces_nonempty` |
| `Δ` | Kummer / relaxed derivative / full conditions | GENUINE | `actΔ_U_oldKummer`, `actΔ_U_derivRelaxed`, `actΔ_U_full` |
| `Dfull`, `W`, `f`, `g` | thickened active conditions; `W = Cone(id)` of the active unramified conditions | GENUINE as data: `f` is not the identity and `W ≠ 0`; the thickening is formal (see below) | `actFull`, `actW_nontrivial` |
| `hDp` | restriction of `Dfull` along `f` is the Nekovář data | GENUINE | `act_hDp` |
| `hfg`, `hinj`, `hsurj`, `hex` | `0 → U_ur → U_ur ⊕ Cone(id) → Cone(id) → 0` exact | GENUINE | `act_fg`, `act_inj`, `act_surj`, `act_ex` |
| `hW` | `Cone(id)` acyclic | holds, but NOT the text's case (see below) | `act_hW`, `active_full_change_not_acyclic` |
| `a`, `b` and the bounds of the residual cone | `[0, 3]` | GENUINE | `actP_ge`, `actP_le` |
| `pP`, `QuasiIso pP` | actual quasi-isomorphism onto the genuine smaller-support Selmer complex with Kummer, derivative and full conditions | GENUINE (the old-Kummer case) | `actPP`, `actPP_quasiIso`, `formalMap_quasiIso` |
| `L`, bounds, finiteness, `hLmin` | cohomology of the residual cone, zero differential | GENUINE | `actL_ge`, `actL_le`, `actL_finite`, `actL_minimal` |
| `pL`, `QuasiIso pL` | through the genuine support change (new places) and the change of condition | GENUINE: the transfer is exercised, `2 ≤ genericRank < rankTot` | `actPL_quasiIso`, `activeGenuineCounts_strict`, `two_le_genericRank` |

## The extra inputs of `residualRankCounts_actual`

| Input | Value | Status | Evidence |
|---|---|---|---|
| `E`, `j`, `χ₀` | `E₁₁`, `0`, trivial (forced at `j = 0`) | GENUINE | — |
| `hT₀`, `hM₀`, `h2₀`, `htriv₀` | full rational `2`-torsion, trivial action on it | GENUINE | `smallTorsion` |
| `eGact` | `Gⁿ ≅ Hⁿ(G_{K,S₀}, 𝔽₂ ⊗ M₁)` | GENUINE | `actEGact` |
| `χ` and the two instances | trivial character over `S` | GENUINE | — |

All other inputs are those of the table above; `activeActualCounts_strict` and
`two_le_genericRank` give `2 ≤ genericRank < rankTot` for this constructor as well.

## What remains vacuous, trivial or formal, and why

1. **The text's active change of condition is not available over `𝔽₂`.** The text replaces the
   unramified condition by the full condition at the active primes and obtains acyclicity of the
   quotient only after inverting `t` (tex 4619–4631). Both constructors have coefficients `𝔽₂`,
   where `t = 0` cannot be inverted, and there the quotient is not acyclic: at a place above `13`
   the unramified condition has `h¹ = 2` and the full local complex `h¹ = 4`, so no injection with
   acyclic cokernel exists (`active_unramified_not_full`, `active_full_change_not_acyclic`). The
   witness therefore uses the only kind of change with acyclic quotient: the active unramified
   conditions thickened by the contractible cone of their identity. `hW` holds genuinely for it, but
   it is not the text's "after inverting `t`" case, which needs an interface over `𝔽₂((t))`.
2. **`hA` is trivial**: `k = −1` has no prime factor, so `ω(k) = 0 ≤ A = 0`. This is forced by
   `K = ℚ(i)`, which the manuscript excludes from its final companion choices; the target types
   accept it.
3. **The Kummer coefficient map** `ι_v : E₁₁(K̄_v)[2] ≅ M` is an `𝔽₂`-linear isomorphism between two
   modules with trivial Galois action (`Tv_trivial`, `smallM_facts`), chosen abstractly; it is not
   the comparison along a decomposition embedding `K_S → K̄_v`. The Kummer complex built from it has
   exactly Mattuck's dimensions (`oldKummer_places_exact`).
4. **The moving prime** `5` carries the full condition; its finite character is invisible at the
   residue field (tex 4600: "reduction modulo `t` kills that character").
5. `N = 66` is a support parameter; no equality with the conductor of `E₁₁` is asserted.

No other input of either constructor is vacuous at this instance.

## Printed inputs, unchanged

Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Ch. I: Theorem 4.10(c) (pp. 56–57),
Theorem 5.1 (p. 67), Theorem 2.8 (p. 31), Corollary 2.3 (p. 28); Nekovář, *Selmer complexes*,
Astérisque 310 (2006), Proposition 7.8.8(ii) (pp. 186–187). They are explicit hypotheses of the
statements; the locators are those of the repository's statements of these propositions.
