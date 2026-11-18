# Scope and sizing

- **VERIFIED (source, before build).** The target at base 06e5d5d8 is
  `HDec.CMBranch.CMjBridges.CMPeriodShortWeierstrassComparison` in
  `ZInQKernel/Contrib/OneProof/JDescent.lean`. It asks for sections on the
  actual abelian variety over its number field and evaluations along a witness
  of the specified period.
- **VERIFIED (source).** The vendored
  `AlgebraicGeometry.SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed`
  returns a curve model of an algebraically closed fibre and a divisor formula
  with an unspecified genus. Tau Ceti has Riemann–Roch for abstract function
  fields, and its `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Genus.lean`
  computes the spaces at infinity and genus for a given nonsingular Weierstrass
  equation over the ground field. Neither result supplies the pole spaces at
  the identity of the given dimension-one `PkgI3.AbVar L`. No such bridge was
  found in the vendored curve or Jacobian development.
- **VERIFIED (source).** The projective coherent GAGA interface
  `ComplexAnalytic.gaga₁` compares cohomology of a supplied coherent sheaf on
  a supplied projective complex scheme. The uniformization supplies
  holomorphy of pulled-back regular sections on their domains; the stronger
  uniformization supplies local coordinates and openness. No declaration was
  found that supplies the two sections over L or takes a divisor supported on
  the identity to analytic pole bounds along `IsPeriodAt`.
- **VERIFIED (source).** Mathlib supplies the normalized Laurent principal part
  of ℘, holomorphy off the lattice, periodicity, its short cubic identity, and
  bounded entire rigidity. The vendored complex Weierstrass point
  parametrization gives surjectivity on affine points. These apply to the
  specified period pair, independently of any choice of equation over L.
- **SPECULATIVE (scope).** Constructing the required algebraic sections over L
  is a separate curve development: construct the low pole filtration on the
  actual scheme, prove its genus and the dimension formula over L (or prove
  base change and descend), and relate the identity parameter to evaluation.
  The useful local interface is a short nonsingular cubic over L on an open
  containing all the nonidentity points of the period map, with an even
  x-coordinate having an exact double pole there. Matching y may be deduced
  from nonsingularity and the cubic, without a separate pole bound for y.
- **VERIFIED (manuscript).** At L579 and L583–587 the input is a CM elliptic
  curve over L, and the degree of its j is used to bound the class number.
  The supplied reading of Fowler §2·1 is for the modular j of the period.
  The standard comparison is implicit; no manuscript error was identified.
