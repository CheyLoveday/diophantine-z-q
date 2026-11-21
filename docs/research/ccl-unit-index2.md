# Cai–Chen–Liu unit index on the staged Heegner chain

The staged application now carries the unit factor in both point norm relations.
With the manuscript's `c = d, m = 1`, the factor is the index of the image of
`ℤˣ` in `(𝓞 K)ˣ`. The staged constructor supplies the companion condition that
makes this index one. The resulting global cochain identity keeps its original
statement, including the boundary term.

The base import closures of `hRC` and `ZInQ.OneProof.frozenTarget` contain no
older CCL transport module. The former is the genuine restricted converse
defined in `SelmerTwoPower.lean:217`. The latter takes it as a hypothesis and
passes it to the pole-completeness proof at
`ZInQKernel/OneProof/Main.lean:249–260`. The separate RC proof candidate
`Wiring.Leaves` imports `Heegner.lean` through the arithmetic bundle, which
only mentions the CCL interface in a comment. The older transport statements
remain available to the older wiring pending retirement at fold.
[Closure results](../../scratch/ccl-unit-index2/closure.txt) ·
[Base consumer list](../../scratch/ccl-unit-index2/consumers.md)

## Statement and discharge

Cai–Chen–Liu, Trans. Amer. Math. Soc. 370 (2018), Thm 2.15, p. 3730
(read: AI reading of the journal page). In the recorded reading,
`uₘ Σσ Pₘₗ^σ` equals `Tₗ Pₘ` at an inert prime and
`(Tₗ − Σw Frob_w) Pₘ` at a split prime. The factor is one for `m ≠ 1`.
`cclUnitFactor` encodes those two cases. `HeegnerPointData.NormRelationsWithUnits`
gives the two equations after applying the elliptic quotient and taking
`c = d, m = 1`. `CCLThm2_15AppliedWithUnits` replaces the staged input for
the same literature theorem. It packages these point identities and the
existing anchor. The anchor and its six dictionary steps remain GLUE.
[Applied statement](../../ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean)

The unit calculation proves surjectivity of the map on units when
`[K : ℚ] = 2` and `disc K < -4`. A nonrational integral unit would
have quadratic minimal-polynomial discriminant `t² − 4n = disc K · i²`
with `n = ±1` and `i ≠ 0`. The left side is at least −4 and the right
side is at most `disc K`. A rational integral unit is integral over
`ℤ` and its norm is the square of that integer, which makes the integer
a unit. The alternative level calculation reduces the Heegner form modulo
16 when `4 ∣ N` and rules out both exceptional fields. The staged proof
uses the companion data supplied by its constructor.
[Unit proofs](../../ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean)

- `E2ChainInputsS` takes the weighted CCL application. It stores
  `D.kfin ≠ -3` from the existing companion output. Together with
  `D.kfin < 0`, `D.kfin % 4 = 1`, and `discr_of_sqrt`, this gives
  `disc K < -4`. The new named proofs are `unitFactor_eq_one` and
  `normRelations`. The definitions and proofs that apply the normalized
  witness are `E2ChainInputsS.datum`, `E2ChainInputsS.anchor`, and
  `E2ChainInputsS.hG`. Their callers receive the same cochain identity
  via `e2ProviderS`. [Staged chain](../../ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean)
- `e2ChainInputsS_of_actual` fills the exclusion from `St.companion hodd`.
  Its existing `St` and `hodd` arguments suffice. The constructor and
  its two wrappers accept the corrected CCL application in place of the
  old one. The wrappers are `e2ChainInputsS_of_actual'` and
  `e2ChainInputsS_of_support`. [Actual constructor](../../ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean) ·
  [Good reduction wrapper](../../ZInQKernel/Contrib/CloudB3E2Norm/E2ChainGood.lean) ·
  [Support wrapper](../../ZInQKernel/Contrib/CloudB3E1RingClass/SupportReq.lean)
- The staged input bundle is used by `CommonCoordinate19Leaf`. Its
  `e2ProviderOnS`, `e2ProviderOnS_succ`,
  `CommonCoordinateInputsGenuineS`, `commonCoordinateInputsLimitE_of_S`,
  `commonCoordinateInputsNF_of_genuineS`, and
  `commonCoordinateTarget_of_genuineS` inherit the corrected type through
  that bundle. Every existing constructor fills the stored inequality from
  the companion output. The package still takes its assembled chain as
  an input. [Staged downstream package](../../ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Leaf.lean)

The two norm Props concern only points on the elliptic curve and the
relative trace. They supply the arithmetic step at tex 2914–2936. The
Kummer transfer, Frobenius comparison on the two places and retained
cochain boundary still require the existing arguments at tex 4157–4172.
The added companion field is only an inequality on a discriminant,
supplied by the already named companion construction at tex 2595–2603.
`H20DictFields.hnorm_of_full_anchor` and the subgroup transport use the
normalized equations. The standalone `CochainNorm` lemmas already take
the unweighted point equation as an explicit input and do not read the
CCL witness. None of these proofs takes a unit hypothesis.

## Verification

**VERIFIED.** Lake built the changed modules and all 60 terminal targets
in the reverse import graph of `Heegner.lean`, one target at a time. Their
import closures cover all 462 direct and transitive importers. The axiom
check covers 20 declarations, including the inert and
split specialization, the modulo-16 argument, the provider's global
identity, and both constructor wrappers. It finds only `propext`,
`Classical.choice` and `Quot.sound`.
[Build results](../../scratch/ccl-unit-index2/builds.txt) ·
[Axiom check](../../scratch/ccl-unit-index2/Check.lean) ·
[Axiom output](../../scratch/ccl-unit-index2/axioms.txt)

## Retirement at fold

Paths in this section are relative to `ZInQKernel/Contrib/`.

- Delete `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean`, including
  `e2ProviderOn`, `e2ProviderOn_succ`, `CommonCoordinateInputsGenuineE2`,
  `commonCoordinateInputsGenuineK_of_E2`,
  `commonCoordinateInputsNF_of_genuineE2` and
  `commonCoordinateTarget_of_genuineE2`.
- Move `chainCond` and `dvd_chainCond` out of
  `OneProof/RC/Wiring/CommonCoordinate18E2.lean` and point the staged
  import to their new location. Preserve the staged imports needed for
  the transport. Then delete that old file, including `classSupport`,
  `ActualPresentation.ps_getD_pos`, `ActualPresentation.ps_getD_prime`,
  `E2ChainInputs` and its entire namespace, and `e2Provider`.
- Delete `CloudB3E2Norm/H20HeegnerNorm.lean`, including
  `HeegnerTransportAt`, `hnorm_of_normRelations`, `hnorm_of_print`
  and `nonVacuity_transport`. In `H20Transport.lean`, import
  `PrintsArith.Heegner` directly and delete `hnorm_of_print_on`.
  In `H20Anchor.lean`, delete `CCLGenuine` and
  `hnorm_of_genuine_print`. Keep the subgroup and full-anchor dictionaries
  used by the staged proof.
- In `H20DictFields.hnorm_of_full_anchor`,
  `H20PresClass.gx_step_anchored`, `H20PresClassOf.gx_step_heegner`
  and `H20PresClassMatch.gx_step_heegner_at`, spell the premise as the
  existing existential anchored `NormRelations`. The staged bridge already
  supplies exactly that premise. Then delete the old applied witness
  `CCLThm2_15Applied` from `PrintsArith/Heegner.lean`. The relation
  `HeegnerPointData.NormRelations` itself remains the proved input to the
  additive transport.

## Known issues

- **VERIFIED, tree error.** The older application treated the unweighted
  equation as the printed result for arbitrary anchors. It permits
  `d = 1`, and the old generic premises can hold for `D_K = -4`.
  Both the counterexample to the premise check and the inability to erase
  a scalar by additive transport were verified in the previous run.
  [Earlier checks](../../scratch/ccl-unit-index/Check.lean)
- **VERIFIED, level calculation.** The congruence `2² ≡ −4 mod 8`
  defeats the mod-8 argument. Modulo 16 the residues 13 and 12 are both
  nonsquares. The connection between the explicit curve and
  `4 ∣ newformLevel` was not needed for the staged discharge.
- **UNVERIFIED, journal page.** The locator and the two formulas use the
  recorded reading. The page was not independently re-read. Using
  `m = d > 1` would require new conductor checks, since `3 ∈ S` in
  the recorded print and an admissible old conductor may contain 3.
- The applied interface remains conditional on the global compatible
  family and the algebraic parametrization dictionary. Individual
  Heegner forms in the anchor do not by themselves construct a global
  compatible family. With an arbitrary true anchor the zero point system
  still satisfies both norms. The staged application uses `FullAnchor`.
  No manuscript error was found in the cited use.

## Manuscript check

| Step in `diophantine_zq.tex` | Verdict |
| --- | --- |
| Tex 2349–2352 and 2595–2603. The final companion is chosen with negative fundamental discriminant outside the exceptional fields. | OK |
| Tex 2720–2722 and 2839–2844. The Heegner field is split at `2N` and outside the two exceptional fields. | OK |
| Tex 2729–2741, 2841–2855 and 3500–3506. The old conductor contains the moving prime and the finite character factors through the ring class group. | OK |
| Tex 2836–2838. The analytic parametrization realizes the algebraic map with the stated cusp normalization. | unverified (GLUE) |
| Tex 2915–2917. One compatible system of proper ideal lattices with fixed orientations gives the CM points. | unverified (the global compatibility remains GLUE) |
| Tex 2917–2921. At split level use the full old conductor and only enlarge by a prime outside `6dND_K`, as in the recorded journal reading. | OK |
| Tex 2921–2922. The index in the printed application is one, now proved in the staged Lean interface. | gap filled |
| Tex 2924–2929. Both unweighted relations follow by substituting the proven unit factor. | OK |
| Tex 2931–2932. The two Frobenius classes are inverse by the principal-ideal Artin symbol, used through the field dictionary. | OK |
| Tex 2933–2936. Hecke equivariance and the cusp degree give the norm after applying the quotient map. | unverified (the analytic-to-algebraic map comparison remains GLUE) |
| Tex 4142–4146 and 4157–4172. The split point factor goes through transfer and the retained cochain boundary. | OK |
