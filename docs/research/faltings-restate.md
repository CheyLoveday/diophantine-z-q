# Faltings’ height invariance and the Néron identification

**Result.** The printed height equality is already a Lean theorem. The separate
Néron identification follows from one direct instance of Faltings’ Lemma 1
over a discrete valuation ring, then gives the old field
`faltingsSemistableHeightBC` with the two existing fields for Raynaud’s
criterion and Néron model existence. The proposed fold replaces one GLUE row
by one read LEAF: on the 29 H fields at `be73b91c5`, both strict and strictest
go from **5 LEAF / 24 GLUE** to **6 LEAF / 23 GLUE**. The base bundles are unchanged.

## From the print to the route

Faltings defines a semiabelian scheme by smoothness and connected fibres
that are extensions of abelian varieties by tori over their residue fields.
In `IsSemiabelianModel` the abelian generic fibre and smoothness are part of
`GroupModel`; at each maximal ideal the predicate checks connectedness and
`HasSemiAbelianIdCompTorus` on `resFibre`. The connected open subgroup in
that predicate is the entire closed fibre. The torus need not be split
over the residue field.

The theorem `faltingsHeightBaseChange` is the instance of H4a
(`Contrib.HeightBC.modelHeightBaseChange`) for these models. It compares
the same semiabelian model and its base change. H4a works for all group
models, so the proof of the old field also applies it to arbitrary base
changes of Néron models.

For the Néron comparison, the local proof first takes the open subgroups
with fibrewise identity components as image. On the source, semistability
of the *group model* after base change is given by `isSemistable_bcDVR_iff`;
this does not assert that the base change is a Néron model. Geometric
semistability descends to the residue field by the existing perfect
field result. The number field residue fields are finite, and the
identity components commute with base change by the existing
geometric connectedness proof. At a DVR the two open subgroups thus
satisfy Lemma 1. The generic group isomorphism and its inverse extend;
uniqueness makes the extensions inverse. The Néron mapping property
identifies this isomorphism with the restriction of the map into the
target Néron model.

Globally, the generic comparison map is already an open immersion away
from finitely many primes by spreading out. At the remaining primes use
localization of both Néron models, their assumed semistability, and
the comparison just proved over the DVR. The common open subgroup
constructed this way is all that the height proof uses.

Given semistable `N` over `L` and an arbitrary Néron model `N'` over
`L'`, embed `L'` into the algebraic closure of the original field and
take its compositum with the Raynaud field. The new model `N''` there
is semistable. The two-model comparison, invariance of height on an
open subgroup, and H4a give `h(N'') = h(N)`. Base change and Néron
minimality give `h(N'') ≤ h(N') ≤ h(N)`. This does not use persistence
of Néron semistability. The old consumer then identifies the kernel’s
infimum with the height of a semistable Néron model.

## Lean statements

All names below are in `ZInQ.FaltingsRestate`. The first file is
[`FaltingsRestate.lean`](../../ZInQKernel/Contrib/OneProof/FaltingsRestate.lean);
the local proofs are in
[`FaltingsRestateDVR.lean`](../../ZInQKernel/Contrib/OneProof/FaltingsRestateDVR.lean).

| Theorem | Statement |
|---|---|
| `faltingsHeightBaseChange` | For a semiabelian model `G` over `𝓞_L` and a group model `G'` with `IsBaseChangeOf G' G` over `𝓞_{L'}`, `G'.height = G.height`. |
| `semistableNeronIdentification_of_ss2` | `SemistableNeronBaseChange → SemistableNeronIdentification`. The conclusion is SS2, with target semistability added: there exist `U,V` over the larger ring of integers with `V` a base change of `N` and `U` open in both `V` and `N'` as a group model. |
| `semistableNeronIdentification_of_cor33` | `GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34 → SemistableNeronIdentification`, via SS2 and the proved localization and strict henselization facts. |
| `height_eq_of_two_semistable` | Given `SemistableNeronIdentification`, two semistable Néron models over `L ⊆ L'` have equal height. |
| `faltingsSemistableHeightBC_of_identification` | `SemistableNeronIdentification → SemistableReductionThmIF → NeronModelExists → FaltingsSemistableHeightBC`. |
| `faltingsSemistableHeightBC_of_leaves` | `SemistableNeronIdentification → SilverbergZarhinThm35 → NeronSchemeExtensionDedekind → FaltingsSemistableHeightBC`. |
| `range_pullback` | The image of the base change of a map over schemes is the inverse image of the original image under the projection. |
| `generic_iso_of_range` | An open immersion into a DVR group model with image the fibrewise identity component induces an isomorphism on the generic fibre. |
| `closed_fibre_of_range` | Over a DVR with perfect residue field, an open subgroup model with image the fibrewise identity component of a semistable model has connected semiabelian closed fibre. |
| `exists_semiabelian_component` | A semistable group model over such a DVR admits an open subgroup model with this image which is semiabelian in the sense of `IsSemiabelianModelO`. |
| `identityComponent_of_faltingsLemma1` | Given Lemma 1 and two semistable group models over such a DVR, with the target Néron, a homomorphism that is a generic isomorphism restricts to an open immersion from the source identity component onto the target identity component. |
| `identityComponentBaseChangeDVRRange_of_faltingsLemma1` | Given Lemma 1, a finite extension of fraction fields and two semistable Néron models, the base change of an open subgroup representing the original identity component admits an open group immersion into the new Néron model. The larger residue field is perfect. |
| `semistableNeronIdentification_of_faltingsLemma1` | `FaltingsLemma1DVR → SemistableNeronIdentification`. |
| `faltingsSemistableHeightBC_of_faltingsLemma1` | `FaltingsLemma1DVR → SilverbergZarhinThm35 → NeronSchemeExtensionDedekind → FaltingsSemistableHeightBC`. |

## Rating and known issues

| Statement | Rating and provenance |
|---|---|
| `FaltingsHeightBaseChange` | **VERIFIED, proved**, so no row. (b) Faltings, Invent. Math. 73 (1983), §3 p. 354 and p. 351 Bem. b), both pages read by the reading desk. |
| `SemistableNeronIdentification` | **VERIFIED, proved from Lemma 1**, so no row. Consequence (**GLUE**) with the semiabelian dictionary. Also implied by SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (read by the reading desk; uncited in the manuscript). Keeping this comparison as the leaf would keep both counts at 5/24. |
| `faltingsLemma1DVR` | **LEAF**, published; **VERIFIED** page read by the reading desk. (b) Faltings, Invent. Math. 73 (1983), p. 350, Lemma 1, in the paper cited in the manuscript. For two semiabelian schemes over a normal base, a homomorphism on a dense open extends uniquely; specialize to the spectrum of a DVR with its generic point and to models with abelian generic fibres. Neither Néron models nor the height conclusion occurs in the leaf. |

- **VERIFIED (reading desk):** Faltings asserts invariance without proof or
  citation on p. 354. The locator “§1” and the attribution of an SGA 7 IX
  Cor. 3.3 citation to Faltings in `docs/research/ss-faltings.md` are wrong.
  That report removed the Corollary 3.3 declaration, but its comparison content
  was still needed to read the new statement for Néron models. The present
  proof supplies the required part of that comparison using Lemma 1.
- **UNVERIFIED locator:** BLR 7.4/3 was suggested as another source for the
  comparison; it is not used here. No proof of the comparison from the
  tree’s BLR-style facts alone was found. Those facts give localization and
  the smooth good-reduction comparison, whereas at the remaining primes a
  generic isomorphism must extend between connected semiabelian models.
  The smallest imported form used here is Lemma 1 over a DVR with abelian
  generic fibres. No other new leaf is needed.

## Manuscript check

| Tex lines | Verdict |
|---|---|
| L596–597, everywhere good reduction of the CM elliptic curve after a finite extension | **unverified** here: the integral-`j` potential good reduction step is separate. This proof treats the invariance that is used after that step. |
| L597–598, extension preserves the stable height | **gap filled**: the statement is uncited there. The height of the base changed semiabelian scheme is unchanged by H4a. The Néron comparison and the height argument over the Raynaud field justify the passage to the kernel’s stable height. |
| L599–600, original normalization | **OK**: the route uses the metrized Hodge line with the `(i/2)^g` metric and divides the degree by the field degree, as in `HodgeData.lean`. The displayed CM summand is outside this proof. |
| L620–621, height variation under isogeny | **gap filled** for using the semistable-model version on stable heights: the existing reader chooses a common semistable field, and the restored height field justifies the comparison. The isogeny inequality itself is unchanged and its print was not re-read here. |
| L814–817, Raynaud’s criterion (cited at L816–817) | **OK**: use the cited Silverberg–Zarhin Thm. 3.5 with 3 or 5 invertible. The global proof uses a field containing all 15-torsion to arrange this at every place. |
| L875–876, stable height of the Jacobian | **OK**: Javanpeykar §2.3 identifies the curve height with the stable Jacobian height (read in the locator audit). The new proof supplies the same stable-height identification to the existing reader. |
| L896, additivity and height variation | **gap filled** for the same passage to stable heights as L620–621. The separate isogeny and additivity proofs are unchanged. |
| L11084–11086, bibliography entry `faltings1983` | **OK**: the paper and erratum are listed; the new input is Lemma 1 of the 1983 paper, p. 350. |

## Verification

The reproducers and results are in [`scratch/faltings-restate/`](../../scratch/faltings-restate/).

- Both new Lean modules compiled with `lake env lean`; neither imports
  `ZInQKernel.OneProof.Main`, directly or transitively. No existing module changed.
- `Axioms.lean` printed only `propext`, `Classical.choice`, and `Quot.sound`
  for all 14 theorems, including the private helpers; see `axioms-out.txt`.
- The autofold spec discharges `faltingsSemistableHeightBC` using
  `faltingsLemma1DVR`, `silverbergZarhinThm35`, and
  `neronSchemeExtensionDedekind`. Running
  `python3 scripts/one_proof/autofold.py scratch/faltings-restate/autofold.json --dry-run`
  succeeded; `autofold-dryrun.txt` records the count and the changed lines.
  No fold was applied.
- The live `#discharges` check passed. It matched
  `faltingsSemistableHeightBC_of_faltingsLemma1` to
  `OpenResearchLeaves61.faltingsSemistableHeightBC` with exactly the three inputs
  listed above and the standard axioms. See `discharges-out.txt`. It scanned
  30 open hypotheses, of which 29 are H fields. The live `frozenTarget`
  also printed only the three standard axioms.
