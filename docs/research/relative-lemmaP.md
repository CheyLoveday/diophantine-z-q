# Relative Lemma P for full level three

**Scoped stop:** the comparison still needs the fixed-type polarization in families. Lean proves that its pullback half follows from two separate statements: fixed-type comparison on geometric fibres, and fibre detection for normalized Picard classes. Lean proves the fibre detection step globally over a field and locally over the second projection over an arbitrary reduced locally noetherian base. Neither construction in families nor the all-base pullback half is closed, so the representability equivalence remains conditional.

## Statement check

**VERIFIED:** the frozen biadditivity condition normalizes the class on both zero axes. Twisting the pairing by a bundle pulled back from the base cannot produce another biadditive pairing: pulling back along the double zero section recovers the base twist. The fibre kernel in the frozen definition is tested on all schemes, so triviality on geometric points alone is insufficient to pass that test. No counterexample or need to change the statement was found. Normalization by itself does not show that geometric fibres determine a global class.

## Known issues

- **VERIFIED (manuscript):** L467 and L474–475 use the fixed-type polarization and its preservation, while L410–421 specifies its type on a lattice. The relative construction and rigidity are not supplied in these lines. The polarization content of the auxiliary-level Buzzard citation is **UNVERIFIED**.
- **VERIFIED (prior source audit, `docs/research/locators.md`, R2):** L421–422 needs to say which map supplies the indices. The numbers 4, 6 and 2 are normalizer orbifold orders. They would be incorrect as the ramification indices of the degree-four coarse level-one quotient, whose indices at these three values are all two.

## What Lean proves

In `ZInQKernel/Contrib/OneProof/Y3RelLemmaP.lean` and `ZInQKernel/Contrib/OneProof/Y3RelLemmaPSeesaw.lean`, all declarations below are in namespace `Y3LemmaP`.

| Theorem | Statement |
| --- | --- |
| `pairMap_fst`, `pairMap_snd`, `pairMap_comp` | The pair map commutes with the two projections and with composition over a change of base. |
| `tensor_fst_left`, `tensor_snd_left` (private) | Each projection of a product morphism is the corresponding projection followed by that factor's morphism. |
| `lift_fst_left`, `lift_snd_left` (private) | The two projections of a lifted pair of points are the original points, on underlying schemes. |
| `lift_comp_pairMap` (private) | The image of a lifted pair of points is the lift of both points mapped along the base change. |
| `baseTwist_eq_one_of_isBilinear` | If a class and its twist by a class from the base are both biadditive, the base class is trivial. |
| `IsBilinear.div`, `IsZeroAxisNormalized.div` | Taking a quotient preserves biadditivity, respectively triviality on both zero axes. |
| `HasCanonicalRosati.map_pairMap` | An order-equivariant map pulls the fixed Rosati identity back to the source family. |
| `evalClass_map_pairMap` | Evaluating a pulled back class is evaluating the original class on the two mapped generalized points. |
| `IsBilinear.map_pairMap` | A multiplication-compatible map pulls back biadditivity on all tests. |
| `IsBilinear.isZeroAxisNormalized`, `IsZeroAxisNormalized.map_pairMap` | A biadditive class is trivial on the axes; a pointed map preserves both axis identities. |
| `eq_of_geometricPairClass_eq` | Under `NormalizedPairFibreRigidity`, two normalized classes with equal geometric restrictions are equal, by taking their quotient. |
| `canonicalPolarizationPullback_of_normalizedSeesaw`, `canonicalPolarizationPullback_iff_fibreComparison` | Under `NormalizedPairFibreRigidity`, preservation in the frozen cartesian predicate is equivalent to `CanonicalPolarizationFibreComparison`. The equality at the zero value of the marking supplies pointedness. |
| `y3FullThreeRepZ30Pol_iff_of_relativePieces` | The above two Props and `CanonicalPolarizationExists` imply the frozen representability equivalence. |
| `geometricallyIntegral_of_smooth_geometricallyConnected` | A smooth geometrically connected morphism is geometrically integral, by the tree's field criterion. |
| `pic_eq_one_of_algClosure` | On a pointed proper geometrically integral scheme over a field, a Picard class trivial over the algebraic closure is trivial. |
| `residueFibre_eq_one_of_geometricPairClass` | Triviality on the geometric base fibres of the pair implies triviality on the actual residue fibres of the second projection. |
| `exists_open_pairClass_eq_of_geometricPairClass_eq` | Over a reduced locally noetherian base, if two classes agree on the geometric base fibres, they agree on the preimage under the second projection of an open neighborhood of each point of the second factor. |
| `pairClass_eq_over_field_of_geometricPairClass_eq` | Over a field, two normalized classes with equal geometric base restrictions are equal globally. This does not assert that two fixed-type principal classes agree on the geometric fibre. |

The geometric-to-residue bridge extends the residue field of a point of the second factor to its algebraic closure, then factors the resulting test through the twofold fibre product over that algebraic closure. Triviality descends along this actual fpqc field extension. The native reduced local seesaw now applies. Over a field the existing normalized global seesaw uses the normalized Picard sheaf to turn local triviality into equality of actual classes. The native theorem of the square was checked but is for an abelian variety over a characteristic-zero field; arbitrary test schemes in that theorem do not change its hypothesis on the abelian variety.

**VERIFIED (Lean 4.35.0):** both new production modules compile with `lake env lean`.
The independent import check `lake env lean scratch/relative-lemmaP/Audit.lean`
also exits successfully. Each of the 24 new theorem checks, including the
five private helpers, reports exactly `propext`, `Classical.choice` and
`Quot.sound`. The outstanding Props are ordinary explicit arguments of the
conditional theorems.

## Exact outstanding geometry

- `NormalizedPairFibreRigidity` is a kernel statement for `Pic(A ×ₛ A)` on the frozen QM families: a class trivial on both zero axes and on all geometric base fibres is trivial. There is no principality, Rosati, choice of ample line bundle, comparison between moduli problems, or Picard representability in its statement. The native seesaw route still needs the relative gluing step on reduced bases, and detection across nilpotent thickenings. The proved field case and reduced local case are suppliers for this task.
- `CanonicalPolarizationFibreComparison` asks for equality only after geometric fibre restriction of the two classes in the frozen pullback predicate. Its proof needs the field-level algebraic fixed-type uniqueness and its application to the marked cartesian identification. It makes no inference from pointwise equality to equality over the base.
- The independent existence obligation is the frozen `CanonicalPolarizationExists`: construct the actual pairing in families, including in positive characteristic. Neither of the two preceding Props constructs it. Together the three give `RelativeLemmaP` and hence the comparison.

Keep the row **ELLIOT** and **ON THE SPOT**. Replace ON THE SPOT by “proved in Lean: relative Lemma P” only when both frozen halves are proved. No row was changed and no leaf was added.

## Mathematical boundary

The frozen definition of a principal pairing is the Picard-class version of a principal polarization: with a relative dual and the normalized Poincaré bundle, a pairing biadditive in its two coordinates corresponds to a homomorphism $A\to A^\vee$, and its ample, kernel-free geometric restrictions characterize a principal polarization. This interpretation does not require a choice of a global inducing ample line bundle. It does require the relative duality dictionary, which is outside the Lean argument here. The fixed adjoint is essential: requiring merely that Rosati preserve the order does not single out a polarization (see `RvQMPolar.Enu_not_rosati_mu`).

For the remaining all-base seesaw, two distinct issues occur. Over a general
base the available relative normalized Picard descent theorem
`isSheaf_zariski_picardFunctorNormalized` asks for the universal
structure-sheaf pushforward unit to be an isomorphism; the field-base
supplier does not fill this argument over an arbitrary base. Over a reduced base the native cohomology proof gives local triviality over the second projection. A global argument must use the zero-axis trivialization and compatibility of the local isomorphisms. Over a square-zero thickening the obstruction to triviality lies in the image of $H^1(A\times_S A, I\mathcal O)$, from the exact sequence of units. A proof without the relative dual could use a relative $H^1$ product decomposition, with coefficients in the ideal of the thickening, to show that the two zero axes detect this image. Residue fields do not handle this step. With the relative dual, one would instead apply rigidity of homomorphisms of abelian schemes to the difference of the corresponding homomorphisms. These are possible proof routes (**SPECULATIVE** as a formalization plan); neither all-base argument is implemented here.

Fibre comparison is a separate geometry problem, even when the total space is reduced. A **SPECULATIVE** formalization route compares the two Weil pairings on a rational Tate module at a split prime different from the residue characteristic. The involution is orthogonal on the two-dimensional simple module; the compatible alternating forms then come from the one-dimensional space of alternating forms on the two-dimensional multiplicity space. To deduce equality of polarizations, one still needs the algebraic Weil pairing dictionary, injectivity of the rational endomorphism representation after extension to `ℚ_ℓ`, integrality and the positive sign. This is an unchecked route, not a Lean supplier. The compiled complex lattice and Hodge arguments do not provide a principal class from an algebraic ample line bundle in positive characteristic.

For existence it is not enough to choose independent polarizations on all geometric fibres. One needs a relative construction or a coherent local lift with descent, including over nonreduced test schemes. For example, a strategy using deformation of the maximal-order action at a good prime and extension of isomorphisms of abelian schemes would still need a proof of the special-fibre polarization condition and a construction over arbitrary locally noetherian bases. This route is **SPECULATIVE** here. No relative Picard representability hypothesis or other unpublished glue is assumed by an unconditional theorem in this work.

## Manuscript check

| Lines | Verdict | Check |
| --- | --- | --- |
| L410–421 | OK | The fixed type, Gram matrix, determinant and adjoint identity are verified by `RvQMPolar`. The Lin–Yang numbering is **UNVERIFIED** here. |
| L421–422 | unverified | The interpretation as normalizer orbifold orders is consistent with the prior audit. The sentence does not identify the covering map for the indices; see Known issues. |
| L443–446 | unverified | The polarization content of Buzzard's auxiliary-level theorem, and the numbered locator, were not re-read. |
| L449–453 | OK | The marking used here is the manuscript's order-linear marking; its zero value is the section used in the pullback argument. |
| L464–472 | unverified | The argument starts with a polarized stabilizer; the passage from the polarization-free object to that fixed-type polarization remains unproved here. The torsion calculation was not used as a supplier. |
| L472–477 | unverified | No global class, preservation across the quotient, or comparison of the generic fibre is supplied by the local seesaw calculation. |
