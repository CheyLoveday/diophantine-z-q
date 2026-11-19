- Base: a4d99ff24beea5543e7f12b1791feddb9871a97c.
- Reciprocity / Local / Product: finite factors explicit in valuation and
  unit residue, invariant under squares; finite support and product one
  including the real factor; the existing WeilIndexProductFormula for every
  list of rational units with the explicit family.
- Gauss: exact negative Fourier quotient phase; normalized odd Gauss sum
  square and unit twist; signed normalized dyadic sums at moduli four and
  eight.
- Integral / ResidueHaar: normalized cutoff at zero shift stabilizes on the
  polar dual. Residue fibers have translated Haar mass and the corresponding
  quotient index. Stabilized value G_(p^(e+2δ))(u)/p^((e+3δ)/2). The
  shifted integral gives gaussGamma times the stationary phase at every
  finite place. At two the value is exactly the explicit eighth root.
- Actual: finite support for gaussGamma on all rational diagonal lists;
  actual odd unit defect is the Legendre sign at odd coefficient valuation
  and one otherwise; actual dyadic unit defect is the mod-four sign.
- Real: positive-character damped Gaussian integral with polar Haar tends to
  the existing real index.
- Determinant / Character: determinant factor even; supplied-conductor
  character evaluates to the root-character product times Jacobi(m,d)
  on positive representatives; exact canonical residue test for the
  fixed-pool pullback.
- Remaining finite product: signed value of oddGauss p 1; its square and
  twist leave only this sign to identify gaussGamma with finiteGamma.
- Remaining stage character: actual old-level conductor divisibilities and
  the fixed-pool canonical residue test.
- Verification: ten files passed sequential lake env lean. Resource checks
  preceded each run. All 125 printed theorem audits use only propext,
  Classical.choice and Quot.sound. No new prints, axioms or placeholders.
