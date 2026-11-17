# y3-p1j log

## 2026-11-17

- Read (VERIFIED): docs/research/y3-route-a.md, .fleet/y3-route-a.md, scratch/y3-route-a/log.md; diophantine_zq.tex L400-640.
- Manuscript L410-441 (VERIFIED by reading): B=(2,-3), O=Z[i,(1+j)/2], mu=2j+ij (L411-412); Riemann form, Rosati (L412-420);
  "normalizer quotient is P^1_j, branch values 0, oo, -16/27, indices 4,6,2 [babagranath, linyang]" (L420-422);
  K_0, K_3 (L423-424); N normalizes K_3, local normalizers, |N/(A_f^* K_0)| = 4 (L425-429); central ideles act
  trivially (L430-434); Y_3 with all determinant components admits N/(A_f^* K_3) with quotient P^1_j,
  deg(Y_3 -> P^1_j) <= 4|(O/3O)^*| <= 4*81 = 324 (L434-440).
- Computed (VERIFIED, scratch/y3-p1j/units_mod3.py, exact arithmetic on the basis (1,i,(1+j)/2,(i+ij)/2)):
  |O/3O| = 81, |(O/3O)^*| = 72 (36 of norm 1 mod 3, 36 of norm -1). So 4|(O/3O)^*| = 288 <= 324 (manuscript's
  bound holds), and |N/(A_f^* K_3)| = 4*72/2 = 144 (the central (Z/3)^* = {+-1} is in A_f^* K_3).
- Kernel facts (VERIFIED, read): R2fpProps (HDecomp/QM/Leaves.lean:94) is R2 on Y_3 (pi : Y -> P^1, fibres = Aut(O)-twist
  classes of underlying pairs, CM values). R1heckeProps (twist alpha, rightMul u realised by automorphisms of Y) is
  proved from any fine witness: heckeOfFine_proof (TailU:2220). FactorThroughSurj proved (factorThroughSurj_proof,
  TailZ20:1076) for targets that are proper smooth curves (Over objects), not for ToP1 charts.
- Row r1r2 = LeafAdopt.R1R2fpRepW (LPrefix:5248), built by x6Rows_of_leavesW (TailZ21:1603) from BabaGranathRational
  (R2X6PropsIff + surjectivity of pi_6), GonzalezRotgerX6 (X6 witness + R5ptProps), RayClassCM, T5; producers in the
  current chain: babaGranathRationalAb := babaGranathRationalAb_of_printed (elkiesX6StarPrinted_of_functionField
  n.elkiesX6StarFunctionField) ... (EichlerBoundCopy etc.), elkiesX6StarFunctionField from elkiesX6StarEvery and
  x6CoarseModuli (TailZ59:83, EichlerBoundCopy:3703), gonzalezRotgerX6Ab from x6CoarseModuli (TailZ59:78).
