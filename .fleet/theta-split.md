# theta-split (2026-11-14)

**Verdict.** The bundle field `thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic` is used only
through `thetaPointOfFibre_of_qm_ratios`, which applies it once: at `Ω(τ)` on the explicit QM curve, where
`j_θ(Ω(τ)) = J(u) ∈ ℚ \ {0}`. These are infinitely many points, and they are non-CM (by the project's NoCM
step), so they are not finitely many CM points. The field can be replaced by statements about the
explicit functions `τ ↦ θ_m(Ω(τ))`. They need no abelian variety and no polarization (answering qm-glue's
"missing definition"), and they do not need qm-split's `ThetaNullNonvanishing`.

**Compiles** (`scratch/theta-split/ThetaUse.lean`, imports `ZInQKernel.OneProof.H.TailA`; no sorry; all 12
`#print axioms` are standard):
* `thetaPointOfFibre_of_qm_atQM : FibreQMPeriod → ThetaRatiosAtQM → ThetaPointOfFibre` (drop-in).
* Route 1: `thetaPointOfFibre_of_qm_curve : FibreQMPeriod → ThetaEightSquare → QMThetaSymmetricCurve →
  ThetaPointOfFibre`.
  * `QMThetaSymmetricCurve` says that along the curve `e_k(θ_m⁸) = R_k(j_θ)(Σθ⁸)^k` for `3 ≤ k ≤ 9`, with
    explicit `R_k ∈ ℚ[X]`.
  * `ThetaEightSquare` is the global identity `Σθ¹⁶ = (Σθ⁸)²/4`.
  * Both are numerically VERIFIED at 80 digits (30 points, residual ≤ 1e-76). `R_3` matches Lin–Yang's
    printed Igusa vector, and every `R_k(0)` matches the product point `diag(i,i)`.
* Route 2: `thetaPointOfFibre_of_qm_cm' : FibreQMPeriod → QMThetaShape → QMCMNodesNumeric →
  ShimuraCMThetaAlgebraic → ThetaPointOfFibre`.
  * LEAF: Shimura's CM theorem in its own form, restricted to scalar CM.
  * Analytic shape glue, implied by Route 1.
  * Numeric facts at four explicit CM nodes (D = −4, −19, −40, −43; `j_θ = 0, 81/64, 1296/125, 194481/10⁶`
    numerically).
  * Proved in Lean: the CM property of the nodes, Lagrange interpolation, and Vieta.

**Remains (not proved):**
* Route 1: the seven curve identities (glue). They follow from Igusa's theta expressions and structure
  theorem plus Lin–Yang Example 29, given F1's identification of `Ω(τ)` with the QM locus. Also the global
  `k = 2` identity (from `dim M₈ = 1`).
* Route 2: the shape (analytic: Γ*-invariance, Hauptmodul, pole orders); certified evaluation at four
  points for `QMCMNodesNumeric`; and the leaf itself (cited, locators UNVERIFIED).

Report: `docs/research/theta-split.md`; log `scratch/theta-split/log.md`; numerics `scratch/theta-split/py/`.
