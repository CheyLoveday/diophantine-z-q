# A single Fontaine period for the kernel's `B_dR`

**VERIFIED (Lean):** Fork main at `be73b91c5` already constructed
`t = log[ε]` as a nonzero uniformizer (`DeRhamPrint.TDict.tt`,
`tt_ne_zero`, `tt_eq_varpi_mul_unit`), identified `B_dR` with
`B_dR^+[1/t]` (`bdREquivAwayT`), and proved the cyclotomic law using
`HDec.PkgI4.BergerBst.logTeich` (`DeRhamScholze.TT.fontaineTwistT`).
`ZInQKernel/Contrib/OneProof/BdRT.lean` now proves that the two
constructions give the same `t` for every compatible primitive root system
and that `bdREquivAwayT` identifies the localization action with the
kernel's `bdrAct`.

Count effect: none. This is proof glue; no bundle field, statement, rating, or
generated file changes. The strict count remains 5 published / 24 glue.

## Lean statements

All names below are in `DeRhamPrint.BdRT`, with `p` prime and
`Z : DeRhamPrint.TDict.RootSystem p`. Write `t := TDict.tt p Z`,
`ε := TDict.eps Z`, `𝔪 := maximalIdeal B_dR^+`, and `χ(σ) := cycPow p σ 1`.
Write `ι` for the kernel's map from `B_dR^+` to `B_dR`, `ι_t` for the
localization map to `B_dR^+[1/t]`, and `e := TDict.bdREquivAwayT Z`.

| Declaration | Statement |
| --- | --- |
| `tt_eq_logTeich` | `t = BergerBst.logTeich p (TDict.untilt_eps Z)`. |
| `isGenEps_eps` | `IsGenEps p ε`: the untilt is 1 and the first inverse Frobenius coordinate has untilt different from 1. |
| `bdrPlusMap_tt` | `DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (χ(σ)) * t` for each `σ : GQp p`. |
| `bdrAct_tt` | `bdrAct p σ (ι t) = qpToBdR p (χ(σ)) * ι t` for each `σ`. |
| `awayTAct` | The ring endomorphism of `B_dR^+[1/t]` induced by `ι_t ∘ DR.bdrPlusMap p (oAct p σ)`. |
| `awayTAct_comp` | `awayTAct p Z σ ∘ ι_t = ι_t ∘ DR.bdrPlusMap p (oAct p σ)` as ring homomorphisms. |
| `bdREquivAwayT_intertwines` | `e (bdrAct p σ x) = awayTAct p Z σ (e x)` for every `σ` and `x : B_dR`. |
| `awayTAction` | The maps `awayTAct p Z σ` form a monoid homomorphism from `GQp p` to the ring endomorphisms under composition. |
| `awayTEquivAwayXi` | A `B_dR^+`-algebra equivalence `B_dR^+[1/t] ≃ B_dR^+[1/xi]`. |
| `fontaineT_reading` | `t ≠ 0`, `t ∈ 𝔪`, `t ∉ 𝔪²`, `𝔪 = (t)`, both cyclotomic laws, existence of an equivariant `B_dR^+`-algebra equivalence `B_dR ≃ B_dR^+[1/t]`, and existence of a `B_dR^+`-algebra equivalence `B_dR^+[1/t] ≃ B_dR^+[1/xi]`. |

The new arguments are on-the-spot glue (provenance (c)). The first proof
evaluates the truncation of `logSeries` through degree `n` using
`psEval_C` and `psEval_X`. Each positive natural number is a unit in
`ℚ_p`, so its reciprocal maps to `Ring.inverse`. The tail lies in
`(xi)^(n+1)`; `logPlus_unique` then identifies the sums. The action
extends because both the image of `t) and the cyclotomic factor are units
in the localization. The transport proof gives the kernel map the exact
KerTheta localization type before applying `transport_extends` and
`ext_of_extends`, so it does not ask typeclass search to unfold
`DR.genMonoid`. The comparison at `xi` composes the existing algebra
equivalences.

## Checks

**VERIFIED:** The import `DeRhamScholzeT` and its three missing prerequisites
were compiled with `lake env lean -o`, one at a time, using existing local
artifacts for the other dependencies. All 79 checks in
`scratch/bdr-t/CheckBase.lean` passed. The full Lake target build was
interrupted: its initial invocation launched parallel compiler jobs by
default, and serial retries scheduled lengthy dependency rebuilds. The
direct compilation checked the actual source of each of the four missing
modules. See `scratch/bdr-t/log.md` for the build outcomes.

`lake env lean ZInQKernel/Contrib/OneProof/BdRT.lean` passed with no
`sorry`. It imports neither `ZInQKernel.OneProof.Main` nor
`ZInQKernel.OneProof.H.TailC` through its dependency closure. Its
`#print axioms` output was:

```text
'DeRhamPrint.BdRT.tt_eq_logTeich' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.isGenEps_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.bdrPlusMap_tt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.bdrAct_tt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.awayTAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.awayTAct_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.bdREquivAwayT_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.awayTAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.awayTEquivAwayXi' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamPrint.BdRT.fontaineT_reading' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Replacement text for the kernel-wide bullet

**VERIFIED (locator checked by the reading desk):** Brinon–Conrad, *CMI
summer school notes on p-adic Hodge theory*, preliminary version of June
24, 2009. The manuscript cites the notes at L10975 and L10994; its
bibliography entry is at L11019–L11023. The replacement uses the checked
definition of `B_dR` and the presentation by inverting `t`.

* **B_dR.** The manuscript uses `B_dR` in its invariant spaces (L10984–L10992)
  without defining the ring. Use Brinon–Conrad (provenance (b), the
  manuscript's `brinon-conrad`), Def. 4.4.7, p. 60 and the discussion at
  Def. 9.1.4, p. 131, for `B_dR` and the `B_dR^+[1/t]` presentation. The
  kernel's ring is Mathlib's `BDeRham 𝓞_ℂ_[p] p`: the
  `ZInQ.Contrib.G9.PkgI4.BdR`, `ZInQ.Contrib.G9.BdrKer.BdR`,
  `HDec.PkgI4.BdR`, and `ZInQKernel/OneProof/H/TailC.lean` copies are each definitionally
  equal to it. The positive ring is Mathlib's `BDeRhamPlus`, the completion of
  `W(PreTilt 𝓞_ℂ_[p])[1/p]` at `ker θ`. In
  `ZInQ.Contrib.G9.BdrKer.Cp`, `ker_fontaineTheta_Cp` and `ker_fontaineThetaInvertP_Cp` supply the generator
  `xi = p - [p-flat]` before and after inverting `p`; `isAdicComplete_BDeRhamPlus`,
  `isDiscreteValuationRing_BDeRhamPlus`, and `maximalIdeal_BDeRhamPlus` give
  the complete DVR and its maximal ideal. `isFractionRing_BDeRham` and
  `bdREquivAway` match the fraction field and the presentation inverting
  `xi`. The period `t = log[ε]` is `DeRhamPrint.TDict.tt`;
  `DeRhamPrint.BdRT.tt_eq_logTeich` identifies it with
  `HDec.PkgI4.BergerBst.logTeich` for the same `ε`, and
  `DeRhamPrint.BdRT.fontaineT_reading` gives `t ≠ 0`, the uniformizer
  properties, and `σ(t) = χ(σ)t`. The `[1/t]` presentation is matched by
  `DeRhamPrint.TDict.bdREquivAwayT`. Its Galois action is
  `DeRhamPrint.BdRT.awayTAction`, extending the action on the positive ring
  by `DeRhamPrint.BdRT.awayTAct_comp` and matching the kernel's
  `bdrAct` by `DeRhamPrint.BdRT.bdREquivAwayT_intertwines`. The row that
  reaches `B_dR` is `deRhamVpAbVarDirect` (LEAF;
  `DeRhamPrint.Direct.DeRhamVpAbVarDirect` over `DeRhamPrint.Direct.ddrF`);
  its rating is unchanged. Fontaine, *Astérisque* 223, Exp. II is outside the
  manuscript's bibliography and unread. Berger 2002 §1.2 is UNVERIFIED as
  a locator for this definition.

## Known issues

- **VERIFIED:** The generated `B_dR` bullet in `docs/one-proof/OPEN.md` predates
  the construction of `t`. Its open nonvanishing claim is obsolete
  (`DeRhamPrint.TDict.tt_ne_zero`), and the active row is
  `deRhamVpAbVarDirect`, replacing `deRhamH1AbVarT`.
- **VERIFIED:** The docstring at
  `ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean:234` cites L10995 for the
  consequence; it is at L10997. The docstring on `FontaineTwistT` in
  `ZInQKernel/Contrib/OneProof/DeRhamScholzeHT.lean` still labels it GLUE and
  does not record the proof now in `DeRhamScholze.TT.fontaineTwistT` or the
  transformation law for `TDict.tt` in `DeRhamPrint.BdRT.bdrPlusMap_tt`.
- **VERIFIED:** Brinon–Conrad Def. 9.1.4 names `B_cris` (as recorded in the
  reading desk's locator); cite the surrounding discussion on p. 131 for
  `B_dR^+[1/t] = B_dR`, and Def. 4.4.7, p. 60 for the definition of
  `B_dR`. Fontaine, *Astérisque* 223, Exp. II is outside the manuscript
  bibliography and the pages are unread (UNVERIFIED). Berger 2002 §1.2 as a
  locator for the period and period ring is UNVERIFIED; the manuscript cites
  Berger 2002 for monodromy at L739–L741.

## Manuscript check

- L735–L738 — **OK.** De Rhamness comes from proper smooth comparison and finite descent; the two weights are `0, −1` for the Tate module convention. This work checks the period ring used in that argument.
- L755–L756 — **OK.** The cyclotomic character has weight `−1` in the stated convention: `t⁻¹` cancels the cyclotomic action on the Tate line and has filtration index `−1`.
- L10948–L10950 — **OK.** The Tate module is dual to étale cohomology in degree one. With `ℚ_ℓ(1)` of weight `−1`, the two possible weights are `0, −1`; the two identical summands halve their multiplicities.
- L10984–L10992 — **gap filled.** The manuscript uses `B_dR` without defining it. The period ring comparison supplies the dictionary for the Galois action in the diagonal tensor actions defining `D_F′` and `D_K`. Finite descent itself is along `F′/K`: `Gal(F′/K)` acts semilinearly on the first space and each filtration step, with invariants the corresponding spaces over `K`.
- L10996–L10997 — **OK.** In dimension two, the degree-one de Rham Hodge numbers are `2, 2`. The `gr¹ B_dR` twist is `ℂ_p(1)` (used on the Hom side in `DeRhamScholze.HT.gr1_mem`); the duality gives Tate module weights `0, 0, −1, −1`.
