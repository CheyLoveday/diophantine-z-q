# gt-valence results log

Target: `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` (ZInQKernel/OneProof/H/TailZ2.lean L76).
Verbatim copy with dependencies: scratch/gt-valence/statement.lean.

## Findings
- VERIFIED (read): `MeasureTheory.volume` on `UpperHalfPlane` is Mathlib's `dx dy / y^2` measure
  (Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean, `volume_def`), with
  `SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume`. So `vol(s)` in the statement is the hyperbolic area and
  the statement is the genuine valence formula (no vacuity, no mismatch).
- VERIFIED (grep): consumers of the field are only TailZ2 `val_le`, `val_eq`, `val_ex` (for `Γ*`, exact
  automorphy via `abs_auto`), TailZ3 `valenceFormulaGammaStar_of_leaves`, `qmHauptmodulBase3_of_leaves`, and
  GammaStarArea `valenceFormulaGammaStar_noShimizu`, `qmHauptmodulBase3_noShimizu`; all at `Γ = Γ*`.
- Plan: prove the general statement (no reroute needed) by a boundary-free argument: automorphic partition of
  unity `χ` (Σ_γ χ∘γ = 1, compact support), the Riesz identity `∫ log|F| Δχ = 2π Σ ord_ρ χ(ρ)`, conformal
  invariance of `y²Δ`, and `∫_ℍ χ dμ = vol(s)` from the fundamental domain.
