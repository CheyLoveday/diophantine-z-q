# Faltings’ semiabelian definition over a DVR

**VERIFIED in Lean.** The source and target of `FaltingsLemma1DVR` satisfy the
fibre conditions recorded by the reading desk for Faltings, Invent. Math. 73
(1983), p. 350. Their whole closed fibres are extensions of abelian varieties
by tori, their fibres have a common finite dimension within each model, and the
models are commutative. The base is affine normal and `Spec K` is its dense
generic open. `faltingsLemma1DVR_of_printed` uses these proofs to specialize
the recorded extension theorem to the unchanged leaf. This clears the Lean
objections to **LEAF / LEAF**, provenance **(b)**, on the recorded reading.
The proposed fold moves from **5 LEAF / 24 GLUE** to **6 LEAF / 23 GLUE** in
both counts. No fold was applied.

## The definition and proof

[`FaltingsDict.lean`](../../ZInQKernel/Contrib/OneProof/FaltingsDict.lean)
uses `GroupModelO` for the group scheme over `Spec O`, and
`FaltingsSemiabelianDef` asks for smoothness, separatedness, finite type
(local finite type and quasi-compactness), and commutativity. It checks
connectedness and `HasTorusExtension` on both residue-field fibres, via
`jO O` for the fraction field and `closedFibreMap O` for the closed residue
field. It explicitly asks for a natural number `g` equal to both Krull
dimensions and to `A.dim`. This dimension clause occurs in the premise of the
specialization theorem; the existing leaf receives it as a theorem from its
existing hypotheses.

`HasTorusExtension` gives an abelian variety over the residue field and a
flat surjective group homomorphism from the **whole** fibre to it. Its kernel
is specified in the functor of points: on every algebra over the algebraic
closure, the injective map from `(Rˣ)^r` has image exactly the kernel and is
natural in `R`. This uses the functor-of-points option in the review. The
definition does not assert a separately packaged torus scheme or a Yoneda
comparison theorem. It allows non-split tori over the residue field. At the
generic point the quotient is the supplied abelian variety and the torus has
rank zero.

For the closed fibre, the existing group-scheme result identifies the image
of the open connected subgroup with the connected component of the unit.
Connectedness makes this image the whole fibre. The open immersion is then
an isomorphism, and the proof transports the quotient, kernel and naturality
along it. For dimension, a smooth chart at the closed identity meets both
fibres along the identity section, since opens containing the closed point
of a local spectrum contain every point. After base change the chart has the
same smooth relative dimension. The dimension is locally constant on each
smooth fibre and therefore constant on each connected fibre, giving the
common Krull dimension. For commutativity, the two multiplications on the
model square agree after pullback to the generic fibre. The square is flat and
the target separated, so schematic density gives equality over `O`.

For the base, `O` is integrally closed. Every nonzero element is a unit times
a power of a uniformizer, so `K` is `O[1/π]`. The image of `jO O` is `D(π)`;
it is exactly the generic point and is dense. In particular `jO O` is an open
immersion onto the required open subscheme. The generic and closed maps
account for all points, since a nonzero prime of a DVR is maximal.

## Lean statements

All names are in `ZInQ.FaltingsRestate`. Every row below is **VERIFIED**;
private helpers are marked with an asterisk.

| Theorem | Statement |
|---|---|
| `isIso_openSubgroup_of_connected`* | An open connected subgroup of a connected locally finite type group scheme over a field maps isomorphically onto it. |
| `hasTorusExtension_of_connected` | On such a connected group, `HasSemiAbelianIdCompTorus` implies `HasTorusExtension`. |
| `isLocalizationAway_uniformizer` | If `π` is irreducible in the DVR `O`, then `IsLocalization.Away π K`. |
| `jO_range_eq_basicOpen` | For such `π`, the image of `jO O` is `D(π)`. |
| `jO_genericOpen` | `jO O` is an open immersion with dense image the singleton generic point. |
| `specDVR_points` | Every base point is in the image of `jO O` or `closedFibreMap O`. |
| `closedFibre_hasTorusExtension` | `IsSemiabelianModelO G` implies `HasTorusExtension (closedFibre G)`. |
| `smoothRank_chart`* | Every point of a smooth morphism has an open neighbourhood on which the morphism is smooth of some relative dimension. |
| `smoothRank_mono`* | Restricting a chart to a smaller open keeps its smooth relative dimension. |
| `smoothRank_of_connected`* | For a smooth morphism from a connected scheme to a field spectrum, the smooth relative dimension on any nonempty chart holds on the whole source. |
| `dim_baseChange_eq_chart`* | A connected field base change meeting a smooth chart of relative dimension `n` has Krull dimension `n`. |
| `genericFibre_connected`* | The generic fibre is connected, by its isomorphism to `A`. |
| `genericFibre_dim_eq` | The generic fibre has Krull dimension `A.dim`. |
| `fibre_dims` | Given `IsSemiabelianModelO G`, there is a natural number equal to the Krull dimension of both fibres. |
| `closedFibre_dim_eq` | Given `IsSemiabelianModelO G`, the closed fibre has Krull dimension `A.dim`. |
| `isCommMonObj_groupModelO` | The group law on any `GroupModelO` is commutative. |
| `genericFibre_hasTorusExtension` | The generic fibre satisfies `HasTorusExtension` with torus rank zero. |
| `isSemiabelianModelO_imp_faltingsDef` | Over a DVR, `IsSemiabelianModelO G → FaltingsSemiabelianDef G`. |
| `faltingsLemma1DVR_models` | Under the two model hypotheses of the leaf, both models satisfy `FaltingsSemiabelianDef`. |
| `faltingsLemma1DVR_of_printed` | Extension and uniqueness on dense opens of the affine normal DVR base for models satisfying `FaltingsSemiabelianDef` imply the existing `FaltingsLemma1DVR`. |

## Proposed docstring for `FaltingsLemma1DVR`

> Faltings 1983, p. 350, Lemma 1. A homomorphism over the generic fibre of two
> semiabelian schemes with abelian generic fibres extends uniquely as a
> homomorphism. S = Spec O (normal), U = its generic point (dense open);
> semiabelian fibrewise over residue fields, torus geometric (not required
> split), as in the Def. on p. 350. The fibre conditions, including the common
> dimension within each model, are proved by `faltingsLemma1DVR_models`.
> The dense open and specialization are checked by `jO_genericOpen` and
> `faltingsLemma1DVR_of_printed`.

## Known issues

- **VERIFIED (manuscript):** The citations at L621 and L733 are to the paper,
  for height variation under isogeny and the semisimplicity and endomorphism
  theorems, respectively. The manuscript does not cite Lemma 1. Using it is
  an approved reroute through a source in the manuscript's bibliography.
- **VERIFIED (recorded reading):** The earlier attribution of an SGA 7
  citation to Faltings' height invariance and the locator “§1” were wrong.
  The reading desk located the invariance assertion in §3, p. 354, without a
  proof or citation there. The existing Lean comparison uses p. 350, Lemma 1.
- **UNVERIFIED beyond the recorded reading:** The exact printed wording and
  any extra qualifications of the definition and Lemma 1 were not checked
  anew here. Final source rating still needs the separate reading and skeptic
  pass. No new manuscript error was found in the lines checked here.

## Manuscript check

| Tex lines | Verdict |
|---|---|
| L596–597 | **unverified** here: potential good reduction from integral `j` is separate from this dictionary. |
| L597–598 | **gap filled** for the formal route: Lemma 1 supplies the Néron comparison used to justify passage from invariance for a base-changed semiabelian model to invariance of the stable height. The current proof checks the hypotheses of that comparison. |
| L620–621 | **gap filled** for the formal passage to stable height in the isogeny bound: the existing route compares over a common semistable field. The isogeny inequality and additivity are separate inputs and were not reread here. |
| L732–733 | **OK** as a citation to the paper for the stated semisimplicity and endomorphism results; those results are outside this proof. Neither this citation nor L621 cites Lemma 1. |
| L814–817 | **OK** for the recorded criterion: the existing discharge still uses the cited Silverberg–Zarhin Theorem 3.5; the formal global argument takes a field containing the 15-torsion so it can use 3 or 5 at each prime. |
| L875–876 | **OK** on the existing locator audit: Javanpeykar §2.3 identifies the curve height with the stable height of its Jacobian. This dictionary concerns the stable-height comparison used by the existing reader. |
| L896 | **gap filled** for the same formal passage to stable heights as L620–621. The separate isogeny and additivity arguments are unchanged. |
| L11084–11086 | **OK**: the bibliography lists the 1983 paper and erratum. Lemma 1 on p. 350 is a reroute through this paper. |

## Verification and proposed fold

- **VERIFIED:** The new module compiled with `lake env lean` using compiled
  dependencies from the matching base revision `ffe23c61e`. The proof module
  does not import `ZInQKernel.OneProof.Main`, directly or transitively.
  [`Axioms.lean`](../../scratch/faltings-dict/Axioms.lean) printed exactly
  `propext`, `Classical.choice`, and `Quot.sound` for each of the 20 theorems.
  The complete output is in [axioms-out.txt](../../scratch/faltings-dict/axioms-out.txt).
- **VERIFIED:** `python3 scripts/one_proof/autofold.py scratch/faltings-dict/autofold.json --dry-run`
  proposes replacing `faltingsSemistableHeightBC` by `faltingsLemma1DVR`.
  The [manifest](../../scratch/faltings-dict/autofold.json) records the
  specialization and the [output](../../scratch/faltings-dict/autofold-dryrun.txt)
  records `5/24 on 29 -> 6/23 on 29; strictest 5/24 -> 6/23`.
- **VERIFIED:** The live [discharge output](../../scratch/faltings-dict/discharges-out.txt)
  for the unchanged top theorem contains:

  ```text
  DISCHARGES [OpenResearchLeaves61.faltingsSemistableHeightBC] by ZInQ.FaltingsRestate.faltingsSemistableHeightBC_of_faltingsLemma1
    still assumes: [ZInQ.FaltingsRestate.FaltingsLemma1DVR,
   SZRaynaud.SilverbergZarhinThm35,
   ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 30 open hypotheses, 12359 theorems checked, 26 discharge one
  ```

  The count of 30 includes the separate pole-completeness hypothesis; the
  dry-run count of 29 is for H alone. The two other inputs above were already
  fields. No new bridge assumption was added.
