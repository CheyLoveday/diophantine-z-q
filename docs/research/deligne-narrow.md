# The Deligne input read by the frozen proof

**VERIFIED:** `Y3Hodge.DeligneCanonicalModelY3Narrow` follows from the current
`DeligneCanonicalModelY3EveryPrint` and proves the three outputs the frozen proof
reads: a holomorphic QM family, descent to ray class fields at the three
specified CM types, and connectedness of the fine witness over `ℚ`. It drops
the lower half-plane from the point map, the equality-to-double-coset
implication, and analyticity of regular function evaluations away from
`g = 1`. The separate body moduli and holomorphy hypotheses at `1` are
redundant; the corresponding facts are retained once. The forward fibre,
unit moduli and reciprocity clauses are restricted to their read cases.
No new open hypothesis is introduced.

**Reading risk:** neither a polarization nor level structure in the complex
moduli identification is read. The proof **does** use the sign-sensitive
integral `H₁` clause, both at `1` and at the unit representatives of the
three CM types. The published polarized PEL theorem over the reflex field
`ℚ` still needs to be compared with the kernel's unpolarized fine witness.
Dropping the unused clauses narrows that reading; it does not settle it.
The checked closure contains `IsHodgeH1Print` both before and after the
bypass and contains `lemmaP_H1` in neither case.

## Narrowed proposition

For each `(Y, Φ)` with `Y3Fix.R1fpPropsAbP Y Φ`, there is one
`Ψ : ℍ → (B ⊗ 𝔸_f)^× → Y(ℂ)` with the following properties.

| Clause | What remains |
|---|---|
| Onto | All complex points of `Y`, with upper representatives. The old full-domain fibre relation and `exists_upper` prove this restriction from the print. |
| Fibres | Only `DCRel → equality`, starting at `i`, moving to an integral unit representative, or moving at the same parameter from a unit representative. |
| Holomorphy | Zariski continuity for every `g`; full `IsHolFamily` at `g=1`. |
| Unit moduli | The original `IsHodgeH1Print` at `u=1` for every `τ`, and at `u∈𝒪̂^×` for a representative of the base change of a `ℚ̄`-point with one of the three indicated CM types. |
| Reciprocity | One pair of existential conventions as before. For connectedness: the fixed `(q4, tau0)` over `ℚ(i)`, the fixed idele `s4` or its inverse, and all `g`. For ray class descent: fields `K4, K3, K24`, integral `q`, upper CM `τ`, integral unit `g`, and ideles in the ray kernel modulo three. |

The universal fine-witness interface is retained: the existing fine-moduli
proof can supply any witness of this type. There is no new existence
assertion for `Y`. `narrow_of_print` uses the same witness and restricts its
point map; apart from the existing upper-representative dictionary for onto
and fibres, the proof specializes the old conjuncts. The restriction and
the replacement assembly are on-the-spot glue, provenance (c). The input is
still a consequence attributed to the print, pending review.

## Census

Base: `41892618b`. This is the Theorem 5.3 headline in
`ZInQKernel/OneProof/Main.lean:190`. The expanded [census table](../../scratch/deligne-narrow/census.md)
records the complete source trace with file:line and separates package
construction from terminal consumption; `Census.lean` traverses declaration
types and values from the actual headline. The
[census output](../../scratch/deligne-narrow/census-output.txt) lists 80
declarations that head or directly reference the relevant interfaces. The
[manifest](../../scratch/deligne-narrow/generated-declarations.tsv) lists
the carried bundle declarations and their callers, with source lines.

| Live reader | Base file:line | Data read |
|---|---|---|
| The research bundle and its three conversions | `ZInQKernel/OneProof/H/TailZ89.lean:18,79`; `ZInQKernel/OneProof/H/Y3Open.lean:332,366,413` | Carry the field until `Y3Open.lean:424`, which calls the constructor of the full intermediate. |
| `bodyH_of_PM`, `unitsH_of_PM`, `deligneH_of_print`; `Y3Fix.shimuraMainThmIDeligneY3AbU_of_print` | `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean:939,951,960`; `ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean:887` | Rebuild the old all-clauses package on `ℍ`; `Ψ(i,1)` supplies a point for the fine witness, with no moduli facts about that point. |
| `RayClassCFT.shimuraFamilyAb_of_U` | `ZInQKernel/Contrib/OneProof/RayClassShimura.lean:3049`; called at `ZInQKernel/OneProof/H/Y3Copy4.lean:1417` | Holomorphy and the `H₁` moduli clause at `Ψ(τ,1)`, for arbitrary upper `τ`, CM or otherwise. |
| `RayClassCFT.rayClassCMAb_of_leaves` | `ZInQKernel/Contrib/OneProof/RayClassShimura.lean:3042`; called at `ZInQKernel/OneProof/H/Y3Copy4.lean:1435` | Onto at a complex base change, two forward fibre equalities, unit moduli at the CM representative, and reciprocity for its integral embedding and the ray kernel. |
| `DCY3Used.y3ConnectedAb_of_U` | `ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean:681`; called at `ZInQKernel/OneProof/H/Y3Copy5.lean:2145` | Onto at arbitrary complex points in opposite clopens, forward fibres from `i`, Zariski continuity for each `g`, and the fixed CM action on all `g`. |

`Y3Hodge.shimuraMainThmIDeligneY3AbU_of_printPM`
(`Y3HodgePrint.lean:967`) is a convenience wrapper outside the live graph;
`Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print`
(`ShimuraY3Print.lean:102`) is also outside it and takes a different
lattice-form input. Neither needs replacement in this fold. The live
conversion's old exact conclusion would put all the removed clauses back
into the chain. The new constants preserve the three conclusions that are
actually consumed downstream.

## Replacement proofs

`ZInQKernel/Contrib/OneProof/DeligneNarrow.lean` proves
`bodyNarrow_of_PM` and `narrow_of_print`, then `witness_of_narrow` to pin the
same fine witness. `shimuraFamilyAb_of_narrow` uses the original
Hodge-to-lattice conversion at `1`. `embed_core_narrow` and `obj_at_narrow`
specialize the existing descent proof; `rayClassCMAb_of_narrow_leaves`
has the old reader's conclusion with the same textbook inputs.
`connected_of_narrow_body` reuses the existing connectedness argument;
`y3ConnectedAb_of_narrow` has the old connectedness reader's conclusion.
`ReadData` holds these three outputs, and `readData_of_narrow` fills it.

`scratch/deligne-narrow/Discharges.lean` has one example for each output
starting from the old print and passing through `narrow_of_print`.
All eleven new theorems report exactly `propext`, `Classical.choice`
and `Quot.sound`. The same file ran the standard `#discharges` command
against the original headline: 37 open hypotheses and 13,861 theorems
checked. No new theorem matches an old field. The reported match for the
old Deligne field is the pre-existing conditional
`print_of_deligneH`. See
[discharges-output.txt](../../scratch/deligne-narrow/discharges-output.txt).

## Bypass and counts

Ordinary autofold writes a conversion that fills the *old* field. Its proof
term would have to have type `DeligneCanonicalModelY3EveryPrint`; the
narrowed proposition has no such provider. The scratch bypass instead
threads `ReadData` through the old whole-package carriers until the three
reader sites, then calls the unchanged lower assembly.

Run `python3 -B scratch/deligne-narrow/generate.py` from the repository root
to regenerate `DryRun.lean` and `generated-declarations.tsv`. The dry run
includes the whole frozen headline and the H top, old/new closure checks,
and a bundle shape check. It compiled with no errors or warnings. Of the
30 research field types, only the Deligne field changed; all other headline
argument types and the conclusion matched. Both the H and headline checks
find the old proposition before and only the narrowed proposition after the
bypass. The closure search follows types and values; modules without a
transitive import of a checked declaration's defining module cannot
reference it and are omitted. The 32 copied theorems and the scratch
headline use only the standard axioms. See
[dry-run-output.txt](../../scratch/deligne-narrow/dry-run-output.txt).

For integration, `generate.py --tail-only` emits the H declarations with
imports restricted to `TailZ89` and `DeligneNarrow`. That module also
compiled with only the standard axioms
([tail-only-output.txt](../../scratch/deligne-narrow/tail-only-output.txt)).
The proposed new H
call is `sixContactMin_of_open83` with `OpenResearchLeaves64`; the rest of
the headline signature stays as before.

**VERIFIED** by the production scorer and row validator, both strict and
strictest: **5 LEAF / 28 GLUE on 33 H inputs → 5 / 28 on 33**. Including
the four separate headline inputs, **5 / 32 on 37 → 5 / 32 on 37**. The
proposed [kinds row](../../scratch/deligne-narrow/kinds-row.tsv) is
`research / deligneCanonicalModelY3Narrow / consequence / GLUE / GLUE`.
The flag starts with **pending review** and names the removed clauses.
The reviewer sets any new rating.

## Known issues

- The Shimura 1967 Main Theorem I, Deligne 1971 §§4–5 (Cor. 5.7 / Ex. 5.8),
  and Milne §§5–8, 12–14 locators are **UNVERIFIED**. They were inherited
  from the parent statement, with no new reading of the printed sources.
- The polarization issue identified in `docs/research/locators.md`, row
  R1, still applies to the comparison with the unpolarized moduli problem.
  `Y3Hodge.lemmaP_H1` is over the genuine complex homology; it does not
  prove the relative polarized comparison for algebraic families in
  `docs/research/y3-route-a.md`. The Hodge sign is fixed on the Lean side
  (`F0_iff`); its match to the print still needs reading. Neither issue
  adds a separate hypothesis here.
- The R1 audit also distinguishes the adelic action on the tower from
  actions on a fixed level. The narrowed statement asserts a point-map
  equality at the indicated CM data; it asserts no action by arbitrary
  adelic elements on the fixed-level scheme.
- The earlier Buzzard citation directly at level three was corrected by
  the integral-model route (see `docs/research/y3-route-a.md` §0).
  The manuscript instead uses the prime-to-six auxiliary level five,
  then adds level three and descends.
- The earlier checked source note in `docs/research/y3-x6.md` distinguishes
  the manuscript's local branch equation from the global square-root step
  on the Lean route. This fold leaves that open glue unchanged.

## Manuscript check

The following line references are to `diophantine_zq.tex` at the base.
No new manuscript or source error was found in this scope.

- **L411–422 — unverified:** the principal polarization and normalized quotient set the QM datum. The cited polarization and branch comparison was not re-read; this work retains the existing Lean data.
- **L423–440 — unverified:** the full `K₃` level and determinant components give the double-coset setting and the degree bound. The scratch proof reuses that setting; its full identification with the canonical model is not checked against the print here.
- **L443–477 — unverified:** the integral model with a universal family descends to the full-three moduli problem. The new reader uses the already supplied fine witness; the comparison of the polarized and unpolarized problems is not proved here.
- **L473–480 — unverified:** the identification of the generic fibre with `Y₃` and its complex moduli interpretation are used together. The manuscript does not spell out the `H₁` and complex structure identification at `[τ,u]`; this is the retained part of the Deligne input.
- **L480–484 — gap filled:** the description of geometric components is not a proof of connectedness over `ℚ`. Conditional on the retained reciprocity action, the Lean reader proves connectedness over `ℚ` without assuming geometric connectedness.
- **L519–528 — unverified:** the local argument uses an unramified extension at the contacts. The manuscript gives no explicit *Shimura reciprocity* formula for `Y₃` here or elsewhere. The Lean ray class step keeps the needed specializations from the attributed Shimura/Deligne consequence. The local reciprocity at L826 concerns a different argument.
- **L908–909 — OK:** these are the three normalized CM branch discriminants used by the existing Lean row. This narrowing retains the ray class descent proof for precisely those three cases.
