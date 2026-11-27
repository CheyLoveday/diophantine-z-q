# `ColmezTiltIso`: B_dR as printed by Colmez

Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992), 629-644, §2, p. 632
(GDZ scan PPN235181684_0292, LOG_0042, SHA-256
`f64fbacd511b3458f2be96485686b75181e9e6e12395e06526d57ba5782fb978`, PDF page 5, read at 150 dpi),
recalls Fontaine's construction on the ring `R` of sequences `(x^{(n)})` in `O_{C_p}` with
`(x^{(n+1)})^p = x^{(n)}`. The tree builds `B_dR` on Mathlib's `PreTilt 𝓞_ℂ_[p] p` with Mathlib's
`fontaineTheta`, `BDeRhamPlus` and `BDeRham`. The files here prove that the two constructions agree,
as named Lean theorems.

## Files

| File | Imports | Content |
|---|---|---|
| `Ring.lean` | Mathlib | `ColmezR O p`, the printed addition (a limit) and multiplication, `colmezEquiv` |
| `Theta.lean` | `Ring` | Witt expansion, `wittEquiv`, the printed `θ` is `fontaineTheta` |
| `Cp.lean` | `Theta`, `G9.KerTheta` | `O = 𝓞_ℂ_[p]`: limits in `ℂ_p`, `thetaPlusCp`, Galois action |
| `BdR.lean` | `Cp` | Colmez's `B_dR^+`, `B_dR` as printed, isomorphic to the tree's |
| `TpShape.lean` | `G9.I4Layer` | the period pairing on `T_p` versus on `V_p = ℚ_p ⊗ T_p` |
| `RowTp.lean` | `TpShape`, `ColmezTorsionIso.Row` | the Colmez row stated on `T_p` |

`Ring.lean` and `Theta.lean` work for any commutative ring `O` that is `p`-adically complete with
`p` not a unit (Mathlib's standing hypotheses for `PreTilt.untilt` and `fontaineTheta`).

## Main statements

Ring (`Ring.lean`):

* `ColmezR O p`: structure with `seq : ℕ → O` and `pow_seq_succ : ∀ n, seq (n + 1) ^ p = seq n`.
* `IsPAdicLim p a L`: `∀ k, ∀ᶠ m in atTop, a m - L ∈ span {(p : O)} ^ k`; `IsPAdicLim.unique`.
* `exists_isPAdicLim_addApprox`: the printed limit `lim_m (x^{(n+m)} + y^{(n+m)})^{p^m}` exists.
* `ColmezR.add_seq_isPAdicLim`: `IsPAdicLim p (fun m => (x.seq (n+m) + y.seq (n+m)) ^ p ^ m)
  ((x + y).seq n)`: addition on `ColmezR` is the printed limit (it is defined as that limit).
* `ColmezR.mul_seq`: `(x * y).seq n = x.seq n * y.seq n`.
* `colmezEquiv : ColmezR O p ≃+* PreTilt O p`, with `coeff_colmezEquiv`
  (`PreTilt.coeff n (colmezEquiv x) = mk (x.seq n)`) and `colmezEquiv_symm_seq`
  (`(colmezEquiv.symm y).seq n = untilt ((frobeniusEquiv _ p).symm^[n] y)`).

`θ` (`Theta.lean`, `Cp.lean`):

* `witt_expansion`: `w = Σ_{n<N} p^n [Frob⁻ⁿ (w.coeff n)] + p^N u` in `W(A)`, `A` perfect of
  characteristic `p` (the printed `(x_0, x_1, …) = Σ p^n [x_n^{p^{-n}}]`, modulo `p^N`).
* `wittEquiv : W(ColmezR O p) ≃+* W(PreTilt O p)` (`WittVector.map colmezEquiv`).
* `colmezTheta O p = (fontaineTheta O p).comp wittEquiv`;
  `colmezTheta_sub_printedThetaSum_mem`: `θ(w) - Σ_{n<N} p^n (w.coeff n).seq n ∈ (p)^N`;
  `isPAdicLim_colmezTheta`; `eq_colmezTheta_of_printed` (any map given by the printed series is
  `colmezTheta`); `colmezTheta_teichmuller`: `θ([x]) = x.seq 0`.
* `tendsto_printedThetaSum`: the printed series converges in `ℂ_p` to
  `fontaineTheta 𝓞_ℂ_[p] p (wittEquiv w)`.
* `thetaPlusCp_ofPlus_wittEquiv`: the tree's `thetaPlusCp` on the image of `w ∈ W(R)` in `B_dR^+`
  is `colmezTheta w`; `thetaPlusCp_teichmuller`: it sends `[x]` to `x^{(0)}`.

Galois (`Cp.lean`):

* `galAct p σ : ColmezR 𝓞_ℂ_[p] p →+* ColmezR 𝓞_ℂ_[p] p` for `σ ∈ GQp p`, componentwise:
  `galAct_seq : ((galAct p σ x).seq n : ℂ_[p]) = cpAct p σ (x.seq n)`.
* `colmezEquiv_galAct`: `colmezEquiv (galAct p σ x) = DR.preTiltMap p (oAct p σ) (colmezEquiv x)`.
* `wittEquiv_map_galAct`, `bdrPlusMap_ofLoc_wittEquiv`, `bdrAct_wittEquiv`: the same on `W`, on
  `B_dR^+` (the tree's `DR.bdrPlusMap p (oAct p σ)`) and on `B_dR` (the tree's `bdrAct p σ`), on
  the image of `W(R)`.

`B_dR^+` and `B_dR` (`BdR.lean`):

* `colmezThetaInvertP O p : W(R)[1/p] →+* O[1/p]` and
  `ColmezBdRPlus O p = AdicCompletion (ker colmezThetaInvertP) W(R)[1/p]`, the printed
  `B⁺_dR = lim← W(R)[p^{-1}]/(Ker θ)^n`.
* `colmezBdRPlusEquiv : ColmezBdRPlus O p ≃+* BDeRhamPlus O p`, with `colmezBdRPlusEquiv_of`.
* For `O = 𝓞_ℂ_[p]`: `isDiscreteValuationRing_colmezBdRPlus`; `colmezThetaPlus` with
  `colmezThetaPlus_of` (it extends `colmezTheta`), `colmezThetaPlus_surjective` and
  `ker_colmezThetaPlus` (its kernel is the maximal ideal), as printed: "B⁺_dR est un anneau de
  valuation discrète, d'idéal maximal Ker θ et de corps résiduel C_p".
* `colmezBdREquiv : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃+* BdrKer.BdR 𝓞_ℂ_[p] p`
  (`colmezBdREquiv_algebraMap`): the printed `B_dR`, "le corps des fractions de B⁺_dR", is the
  tree's `B_dR` (Mathlib's `BDeRham 𝓞_ℂ_[p] p`, the same type as `PkgI4.BdR p`).

Row on `T_p` (`TpShape.lean`, `RowTp.lean`):

* `Tp.shapeT_iff_shapeV`: for a `ℤ_p`-module `T` with `G_F`-action `τ`, the pairing
  `P : H → (T →ₗ[ℤ_p] B_dR)` (values in a `ℚ_p`-submodule `S`, equivariant, non-degenerate on
  `B_dR ⊗_{ℤ_p} T`) exists iff the same holds on `ℚ_p ⊗_{ℤ_p} T` with `B_dR ⊗_{ℚ_p} (ℚ_p ⊗ T)`.
  `B_dR` is a `ℤ_p`-algebra through `ℤ_p ⊂ ℚ_p` (`Tp.algZp`, a scoped instance).
* `Colmez1992DeRhamAbVarTp`: the row with `P ω : T_p(X) →ₗ[ℤ_p] B_dR`, `T_p(X)` built from
  `X(ℂ_p)` (`TCp`), as in the print; `colmez1992DeRhamAbVarTp_iff_cp` and
  `colmez1992DeRhamAbVar_iff_tp` (equivalent to the row as stated).

All declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Consequence for the `B_dR` rows

The tree's `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p` and `B_dR = BDeRham 𝓞_ℂ_[p] p` are Colmez's (and so
Fontaine's) up to the named isomorphisms `colmezEquiv`, `wittEquiv`, `colmezBdRPlusEquiv` and
`colmezBdREquiv`, compatibly with `θ` and with the action of `G_{ℚ_p}` on the image of `W(R)`. The
existing tree theorems that complete the identification are used directly:
`isDiscreteValuationRing_BDeRhamPlus`, `ker_thetaPlusCp`, `thetaPlusCp_surjective`,
`maximalIdeal_BDeRhamPlus` and `isFractionRing_BDeRham` (all in `G9/KerTheta.lean`), with the
functoriality lemmas `bdrPlusMap_ofLoc`, `locMap_algebraMap` and the definition of `bdrAct`
(`G9/I4Layer.lean`).

## Not covered

* The operations Colmez does not print on `R` (negation, subtraction, integer multiples, casts) are
  carried over from `PreTilt`; addition, multiplication, powers, `0` and `1` are the printed ones.
* The valuation `v_R(x) = v̂(x^{(0)})` and the topology on `B⁺_dR` described on p. 632 are not
  formalized.
* Galois compatibility on `B_dR^+` and `B_dR` is stated on the image of `W(R)`. A transported
  action on all of `ColmezBdRPlus` (through `colmezBdRPlusEquiv`) and a proof that it is the
  continuous extension of the componentwise action are not included.
