# theta-split results log

## 2026-11-14

- Setup: `lake build ZInQKernel.OneProof.H.TailA` (6 s; only the 2 upstream `lean/` helper modules
  were missing), then scratch files `import ZInQKernel.OneProof.H.TailA` and are checked with
  `lake env lean scratch/theta-split/<file>.lean`. VERIFIED (T0.lean).
- Consumers of `G0Split.ThetaPt.ThetaRatiosAlgebraic` (VERIFIED, read): every consumer (TailA:5010,
  TailD:588, TailE:6663, TailI:257, TailK:322, TailO, TailZ4) passes the field to
  `ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`, which uses it once, at `Ω = Ω(τ)` (pkg-I1 /
  bp-analytic `Omega`) for the `τ` supplied by `FibreQMPeriod`, i.e. `Im τ > 0` and
  `jNum(Ω(τ))/jDen(Ω(τ)) = J(u)` with `u ∈ ℚ \ 𝒞`. `J(u) ≠ 0` (kernel `J_ne_zero`, PRArith l.131).
- Finding (VERIFIED by the above): the use is at infinitely many period matrices `Ω(τ)`, all on the
  explicit QM curve `τ ↦ Ω(τ)`, with rational nonzero `j_θ`; not at finitely many CM points. The
  fibres are NoCM (`FibreComTrivial`), so a theorem about CM points (Shimura's CM theory) does not
  cover the use.
- Numerics (double precision, `py/dnum.py`, `py/fit.py`; 30 random τ): with `E_k = e_k(θ_m⁸(Ω(τ)))`
  (elementary symmetric functions of the ten even θ⁸) and `j = j_θ(Ω(τ))`:
  `E_2/E_1² = 3/8` (a global Siegel identity), and `E_k/E_1^k` is a polynomial in `j` of degree 1 for
  k = 3, 4, 5 and degree 2 for k = 6, 7 (fit residual ≤ 5e-9); k ≥ 8 needs higher precision.
  E.g. `E_3/E_1³ ≈ 0.0727881 + 0.0010288 j` (`1/972 = 0.00102880…`).
- High-precision numerics (`py/hp.py`: decimal, 80 digits; `py/fit_hp.py`, 14 points, fit with
  d+1 points, check on the rest): `E_k/E_1^k = R_k(j)` with `deg R_k = ⌊k/3⌋` and **rational**
  coefficients, residual ≤ 5e-75 (VERIFIED, computed):
  R_1 = 1, R_2 = 3/8, R_3 = 283/3888 + j/972, R_4 = 1529/186624 − j/1458,
  R_5 = 13/23328 + 17j/314928, R_6 = 521/22674816 + 95j/5668704 + j²/2834352,
  R_7 = 19/34012224 + 313j/272097792 − j²/2834352,
  R_8 = 1/136048896 + 107j/3673320192 + 49j²/1836660096,
  R_9 = (1 + 9j/8 + j²/4 + j³)/24794911296, R_10 = j²/3779136² (trivial identity).
  Check: `j_θ(Ω(i√(9+6√2))) = −16/27` to 78 digits with this code.
- Cross-check against Lin–Yang (`py/lycheck.py`, VERIFIED computed): on diagonal period matrices
  `e_3(θ⁸) = (116/27)ψ₄³ − (8/27)ψ₆² + 1081344·χ₁₂` (ψ₄=E₄⊗E₄, ψ₆=E₆⊗E₆, χ₁₂=Δ⊗Δ; residual 1e-77);
  with Lin–Yang's QM vector `ψ₆²/ψ₄³ = j`, `2¹²3⁶χ₁₂/ψ₄³ = j+1` (as restated in
  scratch/h-v14/igusa_check.py) this predicts `R_3 = 283/3888 + j/972`: MATCH.
- `ThetaUse.lean` (imports `ZInQKernel.OneProof.H.TailA`) COMPILES, no sorry, all four
  `#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED, `lake env lean`, ~20 s):
  verbatim copy `ThetaRatiosAlgebraicCopy ↔ ThetaRatiosAlgebraic := Iff.rfl`;
  `thetaPointOfFibre_of_qm_atQM : FibreQMPeriod → ThetaRatiosAtQM → ThetaPointOfFibre`;
  `thetaRatiosAtQM_of_symmetric : QMThetaSymmetric → ThetaRatiosAtQM`;
  `qmThetaSymmetric_of_core : QMThetaSymmetricCore → QMThetaSymmetric` (k = 0, 1, 10 proved:
  `esymm_one`, `esymm_ten`); `thetaPointOfFibre_of_qm_core`.
