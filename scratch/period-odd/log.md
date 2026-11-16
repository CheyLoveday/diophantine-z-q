# period-odd results log

Task: prove `ZInQ.CdOpt.CdTwistedPeriodOdd` (ZInQKernel/Contrib/OneProof/CdOptimal.lean), or reduce it;
target: hL3 replaced by `GrossZagierModuliOptCd` + `EtaW32Character` only.

## 2026-11-16

- Build: copied `.lake/build` and `lean/.lake/build` from ~/dzq-wt/cd-optimal (same commit 04d7251c).
  Probe import of `ZInQKernel.Contrib.OneProof.CdOptimal` compiles (1.5 min). VERIFIED.
- Plan (bypass of CdTwistedPeriodOdd): GZHL3.GrossZagierFormulaCd from GrossZagierModuliOptCd + EtaW32Character,
  by a case split on `Λ_d ⊄ (1+i)L`:
  * yes: cd-optimal's route A (lattice_eq_of_periods + core_selfOptimal);
  * no: `Λ_d = k(1+i)L`, so `L' = ((1+i)/2)L = Λ_d/(2k)` is the period lattice of the 2-isogenous
    `E' : y² = x³ + 4d²x`, `E'` is optimal; apply the GZ leaf at `E'` (it covers every short model in the class)
    and transfer to `C_d` along the explicit 2-isogeny `(x,y) ↦ (y²/x², y(x²+d²)/x²)` (analytic form: z ↦ z,
    ℂ/L → ℂ/L').
  Needs in Lean: (A) `E'.LFunction = C_d.LFunction`; (C) the analytic isogeny identity; (D) the bad-case lattice.
- Numerical check (scratch/period-odd/isog_check.gp, d = 5, PARI): with L = ℤ[i]ω the lattice of C_d,
  h = (1+i)ω/2, L' = ((1+i)/2)L: ℘_L(h) = 0; ℘_{L'}(z) = x − d²/x; ℘'_{L'}(z)/2 = y(x²+d²)/x²;
  ℘_L(z+h) = −d²/x; ℘'_L(z+h)/2 = d²y/x²; (℘_{L'}, ℘'_{L'}/2) on y² = x³ + 4d²x. All residuals < 1e-12. VERIFIED.
- Character-sum identity used for (A) (derivation, to be compiled): for a ≠ 0, char ≠ 2,
  Σ_x χ(x³+ax) = Σ_{x≠0} χ(x + a/x) = Σ_X χ(X)(1 + χ(X²−4a)) = Σ_X χ(X³ − 4aX).
- (A) DONE: `ZInQKernel/Contrib/OneProof/PeriodOdd/LFunction.lean` compiles (`lake env lean`, 7 s);
  `ZInQ.PeriodOdd.LFunction_ePrime_eq (hd : Odd d) (hsq : Squarefree d) : (ePrime d).LFunction =
  (shortCurve (-(d : ℚ) ^ 2)).LFunction`, `ePrime d := shortCurve (4 * d^2)`; axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED. Ingredients: `charSum_isog` (Σχ(x³+ax) = Σχ(X³−4aX), a ≠ 0),
  minimality of y² = x³+4d²x at 2 from c₄ (v₂(c₄) = 6), additive at p | 2d, good at p ∤ 2d.
- (C) DONE: `ZInQKernel/Contrib/OneProof/PeriodOdd/Isogeny.lean` builds (`lake build`, 7 s).
  `weierPt_ePrime_eq (hd : d ≠ 0) (hL : IsPeriodLattice C_d L) (z) : isogPt hd (weierPt C_d L z) =
  weierPt (ePrime d) (latP L) z` with `latP L = scalePP L ((1+i)/2)`, `isogPt (x,y) = (x − d²/x, y(x²+d²)/x²)`,
  `(0,0), O ↦ O`; `map_isogPt` (commutes with ℚ-algebra maps); `isPeriodLattice_ePrime`;
  `weierstrassP_split`/`derivWeierstrassP_split` (℘ over L' = L ⊔ (h+L)); `weierstrassP_I_mul` (℘(iz) = −℘(z)).
  Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
