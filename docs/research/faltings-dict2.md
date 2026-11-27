# The print-form and scheme-kernel bridges for Faltings’ Lemma 1

**VERIFIED in Lean.** Both bridges are proved. Every morphism extending the
generic homomorphism is a homomorphism, and the affine points in
`HasTorusExtension` identify the actual scheme kernel, after base change to
the algebraic closure, with a split torus **as a group scheme**. The
scheme-level fibre dictionary now proves the specialization of the printed
morphism extension theorem. The proposed replacement is **LEAF / LEAF**,
provenance **(b)**, on the recorded reading, subject to the third skeptic
pass. The comparisons are proved here (provenance (c)) and add no rows.
No new hypothesis or fold was added to the live assembly.

## What the print says

The reading desk records “läßt sich eindeutig auf ganz S fortsetzen”
(Faltings, Invent. Math. 73 (1983), p. 350, Lemma 1). As specialized here,
`S = Spec O` is normal and `U = Spec K` is the dense open generic point.
The input `f` is still a homomorphism. The printed conclusion is
`∃! g : G.G ⟶ H.G, F.map g = f`, with `F = Over.pullback (jO O)`.
Every other hypothesis in `FaltingsLemma1DVR` is unchanged.
`isMonHom_of_generic` compares the unit and multiplication equations after
restriction. The tensor unit and the model square are smooth, hence flat;
the target is separated. Generic restriction is injective on both Hom
sets by `NeronC.pullback_map_injective`. Thus any extending morphism
preserves the group law. This gives uniqueness among homomorphisms from
uniqueness among morphisms, and conversely.

## The scheme kernel and the torus

For the quotient `π : G ⟶ B.X` supplied by `HasTorusExtension G`, take
`T = G ×_{B.X} Spec k` along the unit of `B.X`. The existing group kernel in
`MilneQuasiInverse/Kernel.lean` gives the fibre product its group structure
and identifies its points on every test scheme with the group kernel of
postcomposition by `π`. The unit section is closed over the field, so
`T ⟶ G` is a closed group immersion.

The coordinate ring of the split torus is the polynomial algebra on
`Fin r` with the product of the variables inverted. Over a commutative
ring this makes each variable invertible, so this is the Laurent
polynomial ring. The relative Spec–global-sections adjunction makes its
spectrum represent tuples of units in global sections. Multiplication
of tuples defines its group law. In particular its `R`-points are
multiplicatively and naturally equivalent to `Fin r → Rˣ`.

Base change preserves the kernel square. The existing `Φ` identifies
points on the base-changed source and quotient with points over the
original field through `k → k̄`. Evaluate the natural family `e` at
the universal tuple (the coordinates of the identity of the split torus)
and lift the result to the base-changed kernel. Naturality computes the
induced map on every affine test algebra. It is injective by injectivity
of `e` and surjective by its kernel-image property. The affine
isomorphism test in `SemiAbelianDescendsPerfect.lean` lifts affine
charts of the target and glues the lifts using pointwise injectivity on
overlaps. The unit and multiplication equations of the comparison
map are also checked on affine tests, since `e` is a monoid homomorphism.
The resulting isomorphism is in the category of group schemes over
`k̄`.

`HasTorusExtensionScheme G` packages the same abelian quotient and
faithfully flat homomorphism (flat and surjective), its closed
scheme kernel, and a group isomorphism `Gₘ^r ≅ T_{k̄}`. This is an
extension of the whole fibre and imposes no splitting over `k`. Both
residue-field fibres meet the new condition, including rank zero for
the abelian generic fibre.

## Lean statements

All names are in `ZInQ.FaltingsRestate`. Private helpers are marked with
an asterisk.

| Theorem | Statement |
|---|---|
| `isMonHom_of_generic` | A map of the DVR models whose generic restriction equals a homomorphism is a homomorphism. |
| `faltingsLemma1DVR_iff_print` | `FaltingsLemma1DVR ↔ FaltingsLemma1DVRPrint`. |
| `faltingsLemma1DVRPrint_of_printed_points` | The printed extension premise with the pointwise fibre dictionary and the morphism conclusion implies both DVR forms. |
| `torusEval_natural`* | Evaluation of Laurent variables as units commutes with algebra maps. |
| `splitTorusPoints_natural` | The multiplicative equivalence from the split torus's affine points to tuples of units commutes with algebra maps. |
| `torusKernel_isPullback` | The kernel square in schemes over `k` is the pullback of the quotient and the unit. |
| `torusKernel_isClosedImmersion` | The kernel inclusion is a closed immersion. |
| `hom_ext_of_algPt`* | Maps of schemes over a field agreeing on all affine algebra points are equal. |
| `torusIso_of_points`* | A natural injective monoid map from tuples of units with image the represented kernel gives an isomorphism from the split torus to that kernel in group objects. |
| `hasTorusExtensionScheme_of_hasTorusExtension` | `HasTorusExtension G → HasTorusExtensionScheme G`. |
| `isSemiabelianModelO_imp_faltingsDefScheme` | `IsSemiabelianModelO G → FaltingsSemiabelianDefScheme G` (both residue-field fibres with scheme tori). |
| `faltingsLemma1DVRPrint_of_printed` | Unique extension as a morphism on the normal base, for models satisfying the scheme-level definition and a dense open immersion, implies `FaltingsLemma1DVRPrint ∧ FaltingsLemma1DVR`. |
| `faltingsSemistableHeightBC_of_faltingsLemma1Print` | `FaltingsLemma1DVRPrint → SilverbergZarhinThm35 → NeronSchemeExtensionDedekind → FaltingsSemistableHeightBC`. |

The constructions `splitTorusPoints` and `torusKernel_points` are
multiplicative equivalences, respectively
`(Spec R ⟶ Gₘ^r) ≃* (Fin r → Rˣ)` over the base field and
`(X ⟶ T) ≃* ker((X ⟶ G) →* (X ⟶ B.X))` for every test scheme over that
field. The latter is the pullback's actual inclusion on points.

## Proposed leaf docstring

> Faltings 1983, p. 350, Lemma 1 (page read by the reading desk). A
> generic-fibre homomorphism of semiabelian schemes with abelian generic
> fibres extends uniquely as a morphism. The normal base is the spectrum
> of a DVR and the dense open is its generic point. Both residue-field
> fibres are extensions by torus group schemes by
> `isSemiabelianModelO_imp_faltingsDefScheme`. The specialization is
> `faltingsLemma1DVRPrint_of_printed`;
> `faltingsLemma1DVR_iff_print` proves equivalence to the homomorphism form.

## Known issues

- **VERIFIED (manuscript):** L621 and L733 cite the paper for other theorems;
  neither cites Lemma 1. This is a reroute through the paper in the
  bibliography. No new source or manuscript error was found in this check.
- **VERIFIED (recorded reading):** Height invariance is asserted in §3,
  p. 354 without a proof or citation there. The older locator “§1” and
  attribution of an SGA 7 citation to Faltings for that assertion are wrong.
- **UNVERIFIED beyond the recorded reading:** The print was not reread in
  this task. The torus comparison uses Lean proofs in this tree; it does
  not rely on the unverified external locators in the older pointwise
  predicate's docstring.

## Manuscript check

| Tex lines | Verdict |
|---|---|
| L596–597 | **unverified**: the good reduction step from integral `j` is separate from these bridges. |
| L597–598 | **gap filled** for the formal route to base change invariance of the stable Faltings height: the existing Néron comparison now uses the literal extension conclusion and checks the scheme-level fibre hypotheses. |
| L620–621 | **gap filled** for using the semistable-model inequality on stable heights over a common semistable field; the separate isogeny inequality and additivity were not reread here. |
| L732–733 | **OK** as a citation to the paper for the stated semisimplicity and endomorphism results. This is not a citation to Lemma 1. |
| L814–817 | **OK** on the previous audit: the Raynaud criterion used by the height consumer has the cited Silverberg–Zarhin input. |
| L875–876 | **OK** on the previous audit: the stable Jacobian height is the height in this route. |
| L896 | **gap filled** for the same formal passage to stable heights as L620–621. |
| L11084–11086 | **OK**: the bibitem lists the 1983 paper and its erratum. |

## Verification and dry run

- **VERIFIED:** All new modules compile with `lake env lean`, and none
  imports `ZInQKernel.OneProof.Main` transitively. The
  [axiom audit](../../scratch/faltings-dict2/axioms-out.txt) covers all 13 new
  theorems, including the private helpers, and four definitions. Each
  declaration uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- **VERIFIED:** The [live discharge check](../../scratch/faltings-dict2/discharges-out.txt)
  finds `faltingsSemistableHeightBC_of_faltingsLemma1Print` with the print-form
  leaf and the two existing inputs, with the same three axioms. It checks
  12,396 theorems; 27 match one of the 30 open hypotheses. The 30 include
  the separate pole completeness hypothesis.
- **VERIFIED:** The [autofold spec](../../scratch/faltings-dict2/autofold.json)
  was run with `--dry-run` only. Both strict and strictest move from
  **5 LEAF / 24 GLUE** to **6 LEAF / 23 GLUE** on 29 H fields, as recorded in
  the [dry-run output](../../scratch/faltings-dict2/autofold-dryrun.txt).
