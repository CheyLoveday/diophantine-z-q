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

## Compiled (lean -o, module VC.*, scratch/gt-valence/mk.sh)
- VC/A1: `integral_mul_laplacian` (Green: ∫ f Δχ = ∫ Δf χ, f C² on open V ⊇ tsupport χ). COMPILED.
- VC/A2: `laplacian_ureg` (Δ ½log(|x|²+ε²) = 2ε²/(|x|²+ε²)²), `laplacian_log_im` (Δ log Im = −1/Im²). COMPILED.
- VC/A3: `locallyIntegrable_log_norm`, `integral_radial` (∫_ℂ 2/(|z|²+1)² = 2π). COMPILED.
- VC/A4: `integral_log_norm_sub_laplacian` (∫ log|x−u| Δχ = 2π χ(u), regularization + dominated convergence). COMPILED.
- VC/A5: `integral_log_norm_analytic` (∫ log|F| Δχ = 2π Σᶠ ord_z(F) χ(z), via Mathlib's extract_zeros_poles_log). COMPILED.
