# gz-hl3 log

## 2026-11-15 03:45 setup
- Base 24f97774. Build trees reflink-copied from ~/dzq-check2 (same HEAD). `lake build` of Decomp, Hensel,
  TYZGenus.CM, TauCeti CanonicalHeight: up to date (10119 jobs, no rebuild).
- ~/tyz-src/Period7.tex is ABSENT on this host (TYZ source not readable this run).
- Target (VERIFIED, read): `ZInQ.GZDecomp.GrossZagierHeegner`, ZInQKernel/Contrib/GZDecomp/Decomp.lean:131.

## Objects available (VERIFIED, read)
- Mathlib `PeriodPair`, `weierstrassP`, `derivWeierstrassP`, `g₂`, `g₃`, `derivWeierstrassP_sq`
  (℘'² = 4℘³ − g₂℘ − g₃), Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:1075.
- Tau Ceti `Affine.Point.canonicalHeight` (needs AdmissibleAbsValues: Mathlib instance for NumberField),
  `canonicalHeight_eq_zero_of_isOfFinAddOrder` (no Northcott needed).
- Kernel `TYZGenus.CM.HeegnerForm N D` (general N), `tauH`.
- sympy (VERIFIED): with x = X − b₂/12, y = (Y − a₁x − a₃)/2, the Weierstrass equation of E equals
  (Y² − (4X³ − (c₄/12)X − c₆/216))/4. So g₂ = c₄/12, g₃ = c₆/216 is the period lattice of dx/(2y+a₁x+a₃).

## 03:50 HL3.lean statements compile (lake env lean, no errors)

## 04:30 reduction compiles
- `ZInQ.GZHL3.grossZagierHeegner_of_leaves (hU : WeierstrassUniformization) (hES : EichlerShimuraParam)
  (hHP : HeegnerPointRational) (hGZ : GrossZagierFormula) (hGC : GrossConjugation) : GrossZagierHeegner`
  #print axioms: [propext, Classical.choice, Quot.sound] (VERIFIED, compiled).
- Glue proved (VERIFIED, compiled): `heegnerRepsExist` (finite complete set of Γ₀(N)-reps of Heegner forms with
  B ≡ β mod 2N: SL₂(ℤ) reduction to 𝒟 via Mathlib `exists_smul_mem_fd`, explicit transform of forms
  [A,B,C]·γ with root γ•τ_Q, primitivity/disc/positivity/residue preserved, Γ₀(N) finite index),
  `weierPt_some` (the analytic point lies on E when g₂ = c₄/12, g₃ = c₆/216: weierPt is not junk),
  `exists_embedding`, `algEquiv_eq_one_of_fix`, `deriv_mul_ne_zero` (L'(E/K,1) = F'(1)G(1) ≠ 0).
- sympy (VERIFIED): transform identities A' = Ad²−Bdc+Cc², B' = −2Abd+B(ad+bc)−2Cac, C' = Ab²−Bab+Ca²:
  A(dz−b)²+B(dz−b)(−cz+a)+C(−cz+a)² = A'z²+B'z+C', disc' = det²·disc, inverse transform returns det²·(A,B,C).
