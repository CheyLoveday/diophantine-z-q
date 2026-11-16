# h33-dict log

Base origin/main 2880fef1. Build tree copied from ~/dzq-check2 (same commit). TYZ source ~/tyz-src/Period7.tex is
NOT on this host (directory missing on 11-16): all readings of TYZ below are taken from the repository's notes
(tyz-split.md §2.1, h33-sign.md, rv-tyz-inputs.md), which were read in Period7.tex by earlier tasks.

## Statements

* Target: `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (ZInQKernel/OneProof/TYZSplit.lean L157-176), plain argument
  `h33` of `ZInQ.OneProof.frozenTarget` (not a bundle field).
* New leaf `H33Dict.TYZThm33Printed`: ∀ (X, Y) with `IsX0Identification X Y` (TYZ's `i₀ : (X₀(32),∞) ≅ (A,O)`
  over ℚ, via its pullbacks in ℚ(X₀(32))), ∀ algebraic lifts `w n` of `i₀(P_n)`, TYZ Thm 3.3 for
  `z_n = (1-[i])w n` (n≡5), `w n` (n≡7), with `ε` chosen after `Φ, χ` (`TYZThm33EpsAfter`).
* Glue (proved): `TYZProp324Used` (TYZ Prop 3.2(4) used form) from hCM; `tyzThm33_of_epsAfter`;
  `isX0Identification_eta`; `tyzThm33_of_printed (hCM) (h : TYZThm33Printed) : TYZThm33`.

## Compile log

* PartA.lean v1: kernel deterministic timeout in `picToMax_eq_one` (rewrite by `restrict_ringClassArtinEquiv`
  at K = QNeg n, the known pitfall). Fixed: general-K lemma `picToMax_eq_one_of_fix`, specialize.
* H33Dict.lean v2 (A + B, `etaCuspBounds` sorry): 0 errors; axioms of `tyzProp324Used_of`,
  `tyzThm33_of_epsAfter` standard; `tyzThm33_of_printed` has sorryAx only through `etaCuspBounds`. VERIFIED (37 s).
