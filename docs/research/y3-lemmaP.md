# Relative Lemma P for full level three

**Scoped stop:** the tree has a normalized Picard family attached to a chosen line bundle, but no construction of the dual abelian scheme and its normalized Poincaré bundle over the bases of `Y3RouteA.Y3FullThreeRepZ30`. The lattice result does not supply a relative polarization. The exact remaining geometry is `Y3LemmaP.RelativeLemmaP`, the existence of the canonical principal polarization on every test object and its rigidity under pullback. Lean proves the polarized/unpolarized representability comparison conditional on this proposition.

## Known issues

- **VERIFIED (manuscript):** L467 uses a polarized automorphism, and L474–475 descends a canonical principal polarization. L411–421 fixes the type but does not supply the relative existence and uniqueness needed to pass from the polarization-free problem to the polarized one. This is a gap in the comparison, not evidence that the conclusion is false.
- **UNVERIFIED (source):** Buzzard's moduli problem is recalled as polarization-free. If that reading is correct, the invocation at L444 cannot by itself supply the polarization used at L467 and L474–475. The cited result at the auxiliary level and the precise polarization content were not re-read. The manuscript does not invoke Buzzard directly at level three.
- **VERIFIED (prior source audit):** L421–422 attaches $4,6,2$ to the normalizer quotient without naming the covering map. These are elliptic orders of the normalizer orbifold; the coarse level-one map $V → V/W$ has index two at each of these branch values, as distinguished in `docs/research/locators.md` (R2). The orders give the indices for a torsion-free cover of that orbifold. The sentence should specify that interpretation; an index $4$ or $6$ for the degree-four coarse map would be an error.
- **VERIFIED (scope of existing results):** `RvQMPolar.lemmaP_lattice` and `Y3Hodge.lemmaP_H1` give Riemann forms under the stated lattice or Hodge hypotheses. They are not theorems about algebraic principal polarizations over fields or over general schemes. The existing field argument in the research record is for characteristic zero. The integral base also includes positive characteristics.

## Polarized objects and their comparison

`ZInQKernel/Contrib/OneProof/Y3LemmaP.lean` uses the actual `Scheme.Pic` and
`CloudR2Poincare.L1.normalizedPolarizationFamily`. It does not assume
`KleimanPicZeroProper954`, another Picard representability proposition, or
the unpolarized representability statement as an input to Lemma P.

- A `QMAbSchemePPol S` is a `QMAbSchemeP S` with one class `P` in
  `Pic(A ×ₛ A)`. Biadditivity is tested on pairs of generalized points, over
  all test schemes. It forces $P$ to restrict to the trivial class along both
  zero axes. The class is also required to be symmetric under swapping the factors.
- On every geometric fibre $A_s$, $P_s$ is the normalized Mumford class of
  some ample $L$. In classical notation its class is
  $m^*L \otimes p_1^*L^{-1} \otimes p_2^*L^{-1} \otimes \pi^*e^*L$,
  with $e$ the zero section and $\pi$ the projection to the base.
  The associated class of $t_x^*L \otimes L^{-1}$,
  rigidified along the unit, must have trivial kernel on **all** test schemes
  over $s$. Checking only geometric points could miss a nontrivial
  infinitesimal kernel. The inducing $L$ is an existential witness, so
  different line bundles inducing the same polarization do not become distinct
  moduli data.
- In the classical duality dictionary, a biadditive class normalized on both
  axes gives a map to the relative Picard functor, pointed at zero. On each
  geometric fibre the parameter abelian variety is connected, so the map
  lands in the identity component. Conversely the normalized Poincaré bundle
  pulled back along $(1,\lambda)$ gives the class for a polarization
  $\lambda:A\to A^\vee$. For an ample $L$ over a field the associated map to
  $A_s^\vee$ is an isogeny; trivial scheme theoretic kernel makes it an
  isomorphism. This explains the formulation using classical duality. The
  relative duality dictionary itself is outside the formalization.
- The Rosati condition is the global equality of the pullbacks of $P$ along
  $(\iota(a),1)$ and $(1,\iota(a^\dagger))$. The first coordinate is the
  line bundle variable and the second the parameter. Thus the equality is
  $\iota(a)^\vee\circ\lambda=\lambda\circ\iota(a^\dagger)$, for the fixed
  $a^\dagger=\mu^{-1}\overline a\mu$, $\mu=2j+ij$.
  The positive sign of $E_0(x,y)=\operatorname{Trd}(\mu^{-1}x\overline y)$ on
  a complex fibre is selected by ampleness. No choice of a complex
  identification is required over an arithmetic base. At the lattice level
  `RvQMPolar.eq_pm_E0_of_principal` and the positivity check distinguish the
  chosen sign, while `RvQMPolar.Enu_not_rosati_mu` explains why simply asking
  that Rosati preserve the order does not give this uniqueness.
- A polarized pullback is the same cartesian identification as in the tree's
  `QMFamFibre`, carrying the action, the level sections and the class $P$.
  Over the identity of the base this is the polarized isomorphism relation:
  the square is an isomorphism carrying the zero section, and zero-preserving
  maps of abelian schemes are group homomorphisms by rigidity. The Lean
  comparison uses the original cartesian predicate directly.
  The level marking is unchanged: the manuscript's Isom sheaf at L451–453
  does not choose a fixed scalar-valued Weil pairing on the marking.

The missing glue is stated as `Y3LemmaP.RelativeLemmaP`. Its two conjuncts
are `CanonicalPolarizationExists` (every test object has a polarization) and
`CanonicalPolarizationPullback` (for any cartesian identification preserving
the action and level, pullback takes the target class to the source class).
The latter applied to the identity square gives uniqueness, and includes
invariance under all isomorphisms. The pair of statements is the exact
relative assertion in the Picard class model; neither is registered as a leaf.
Given it, the same underlying curve and classifying morphisms work in both
directions of `y3FullThreeRepZ30Pol_iff`. In the unpolarized-to-polarized
direction the universal curve is locally noetherian because it is smooth over
`Spec ℤ[1/30]`.

The new theorems (in namespace `Y3LemmaP`) are:

| Theorem | Statement |
| --- | --- |
| `canonicalAdjoint_involutive` | For every $a$ in the maximal order, $(a^\dagger)^\dagger=a$. |
| `canonicalAdjoint_mul` | For $a,b$ in the order, $(ab)^\dagger=b^\dagger a^\dagger$. |
| `canonicalAdjoint_riemann` | For $a$ in the order and $x,y$ in the algebra, $E_0(ax,y)=E_0(x,a^\dagger y)$. |
| `pairMap_id` | The pair map for the identity square is the identity on $A\times_S A$. |
| `IsBilinear.eval_one_left`, `IsBilinear.eval_one_right` | A biadditive class evaluates to the trivial bundle class at $(0,y)$ and $(x,0)$, on every test scheme. |
| `CanonicalPrincipalPolarization.ext` | Two canonical polarizations with equal underlying classes are equal. |
| `canonicalPolarization_eq` | Given `CanonicalPolarizationPullback`, any two canonical polarizations on a test object coincide. |
| `existsUnique_canonicalPolarization` | Given `RelativeLemmaP`, each such object has exactly one canonical polarization. |
| `qmFamFibrePol_iff` | Given `CanonicalPolarizationPullback`, the polarized and unpolarized pullback predicates are equivalent for any polarized pair. |
| `y3FullThreeRepZ30Pol_iff` | `RelativeLemmaP → (Y3FullThreeRepZ30Pol ↔ Y3FullThreeRepZ30)`. |

**VERIFIED (Lean 4.35.0):** The module compiled with `lake env lean` and the
separate import check `lake env lean scratch/y3-lemmaP/Audit.lean` passed.
Each of the eleven `#print axioms` commands reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The hypotheses of the
conditional theorems are explicit arguments, not axioms.

## Remaining geometry

A fieldwise proof must address all characteristics away from 30. One can
separate the relative comparison into construction of the geometric
polarizations, local lifting or construction over the base, and rigidity and
descent for the relative polarization. Fibrewise uniqueness alone only
compares already existing objects on geometric fibres. It gives neither
local existence nor detection of equality over nonreduced bases. With a
relative dual, rigidity of homomorphisms of abelian schemes would compare
global morphisms after checking the geometric fibres; the local fixed-type
condition can then be checked as equality of the two relative homomorphisms
in the Rosati identity. If polarizations are constructed locally in the fppf
topology, uniqueness would identify their overlap restrictions and permit
descent. The available normalized Picard family needs an input line bundle
and does not construct those local classes. This is a missing piece of
abelian scheme theory, rather than a sign or lattice computation.

**Flag:** keep the row ELLIOT and retain ON THE SPOT. The suggested gloss is
“relative Lemma P stated as `Y3LemmaP.RelativeLemmaP`; comparison proved
conditional on it.” Replace ON THE SPOT by “proved in Lean: relative Lemma P”
only after the geometry is proved. The row, claim and score files are unchanged.

## Manuscript check

- **L410–421 — OK.** The chosen `μ`, trace form, determinant and adjoint law agree with `RvQMPolar.E0_gram`, `gram_det` and `E0_rosati`. The printed locator in Lin–Yang is **UNVERIFIED** here.
- **L421–422 — unverified.** The prior source audit verifies the normalizer orbifold orders $4,6,2$; reading them as coarse level-one ramification indices would be an error.
- **L443–446 — unverified.** The application of Buzzard at the auxiliary level and the precise polarization carried by the moduli problem were not checked against the print.
- **L449–453 — OK.** The written marking is the `𝒪`-linear Isom marking; the polarized formulation uses the same marking.
- **L464–472 — unverified.** The torsion-free congruence argument does not construct the polarization that the text uses to make the stabilizer automorphism polarized.
- **L472–477 — unverified.** The relative polarization and its preservation must be supplied before descending it and identifying the polarized and polarization-free universal properties. The conditional Lean comparison does not construct the quotient or identify its generic fibre with the canonical model.
