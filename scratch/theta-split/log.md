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
