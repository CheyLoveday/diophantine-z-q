# Narrowing the Javanpeykar row

**VERIFIED (Lean):** `JavanpeykarThm111JacK` follows from `JavanpeykarThm111An`
alone, and the existing `JavanpeykarBound` reader needs only that narrower instance.
The proposed replacement is `JavanpeykarThm111JacKEx`: it uses one height witness,
with existence and uniqueness supplied from inputs already in the active chain.
The bypass leaves the open count unchanged. No existing module or board was edited.

For a number field `K`, take a smooth proper geometrically connected curve `X₀/K`
with integral projective `X = X₀ ×_K AlgebraicClosure K` and genus `g ≥ 1`.
For any tensor-compatible representative `V/K` of `Pic⁰(X₀/K)`, and given a
positive-degree Belyi map of `X`, the replacement asks for a real `x` with
`IsAnStableHeightSS (ofVendored V) x` and `x ≤ 13·10⁶ · g · deg_B(X)⁵`.
Here `deg_B` is the least Belyi degree. The universal version bounds every
witness `x` instead. Both present the manuscript's L870 citation (provenance (b)):
Javanpeykar's Theorem 1.1.1 on `X` with the identification in Section 2.3 at the
Jacobian of `X_K`. Bibliographic and display locators are from the reading desk's
audit (arXiv:1403.6404v1 pp. 1 and 9; `docs/research/locators.md`, R18).

The old row quantifies over an arbitrary algebraic closure of ℚ, a curve and
Jacobian `W` over that closure, and heights drawn from models of `W` over
arbitrary number fields `L`. The new row fixes the closure of `K`, the base-changed
curve, and its Jacobian over `K`. This removes the need to compare models over
unrelated number fields by descending a geometric isomorphism to a finite
extension (`docs/research/javanpeykar-direct.md`, §3 item 1). The one-way
specialization `javanpeykarThm111JacK_of_an` uses `exists_jacBar` to supply `W`
and introduces the old model witness with `L = K`. The reader itself uses no
such geometric Jacobian.

## Reader and bridges

**VERIFIED (Lean):** `javanpeykarBound_of_jacK` identifies the kernel's Jacobian
with `V` over `K`, transports its kernel height along that isomorphism, and uses
the existing printed and analytic height comparisons to supply
`IsAnStableHeightSS`. It identifies the Jacobian dimension with the geometric
genus, obtains the base-changed Belyi map using the finite constant-field
extension result, and supplies projectivity. The narrow bound then applies to
`V` directly. `belyiDegree_le` and `javanpeykarBound_mono` give the reader's
bound at the displayed map degree. The live chain supplies the
Stichtenoth comparison via `constantFieldExtensionUnramifiedFinite_proof`,
T35 via `uniformizationLeafAll_proof` and Mumford torsion, and the semistability
descent via `semiAbelianDescendsPerfect_proof`.

**VERIFIED (Lean):** `isAnStableHeightSS_iff_kernel` packages the existing
metric and semistability comparisons. `isAnStableHeightSS_unique` converts the
two witnesses to the kernel predicate and applies `isStableFaltingsHeight_uniqueF`.
The bypass supplies Néron model existence from `neronSchemeExtensionDedekind`
and the comparison from `faltingsSemistableHeightBC_of_faltingsLemma1Print`
(Faltings, Invent. Math. 73 (1983), Lemma 1, p. 350, as audited in the active fold). This handles different
semistable extension fields, Néron models, and sections in witnesses for a fixed
`V`. It is also the field-independence input for relating an arbitrary
number-field definition of this Jacobian to the semistable setting in §2.3.

**VERIFIED (Lean):** `exists_isAnStableHeightSS` obtains a real witness from
semistable reduction, Néron existence and metrization. With it,
`javanpeykarThm111JacKEx_of_jacK` passes to the existential bound.
`javanpeykarThm111JacKEx_of_an` makes the bridge from the old row explicit
using only the already present Néron and Raynaud inputs.
`javanpeykarThm111JacK_of_jacKEx` transports the inequality to any other witness by
uniqueness, and `javanpeykarBound_of_jacKEx` then reads the same kernel bound.
`isAnStableHeightSS_of_iso` transports the analytic predicate over a number
field, and `isAnStableHeightSS_of_picZero` applies this to any two
tensor-compatible representatives. These Lean comparisons are glue; the
on-the-spot steps are provenance (c) and add no leaf.

**Remaining:** The lead's ruling on the Theorem 1.1.1 / Section 2.3 composite
is still needed. The curve's Arakelov height is not defined in Lean here.
To split the composite, the smallest faithful bridge would identify the real
height of the curve as defined by the print's metrized determinant of
cohomology with an `IsAnStableHeightSS` witness for its `Pic⁰` over a
semistable field, then use the field and representative comparisons above to
read it over `K`. That would require formalizing the metrized curve invariant
and its comparison with the Jacobian, including the use of the semistability
of the Jacobian of a curve with semistable reduction inside §2.3. The task
does not attempt that Arakelov construction. Reading the remaining
dictionary hypotheses against the print (projectivity, least Belyi degree,
and the analytic normalization) remains part of statement review.

## Bypass and count

**VERIFIED:** The dry run composes the live conversions from
`OpenResearchLeaves67_jp` to `GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS`,
where the chain first consumes `javanpeykarBound`. The new
`ZInQ.OneProof.frozenTarget_jp` rejoins the unchanged downstream chain.
This is a bypass because the narrower row does not supply the old field
for an autofold. The old row occurs in the old top's dependency closure;
the new closure reaches the existential row and its reader instead, and both
closures reach the existing Faltings conversion. All new definitions,
theorems and both tops report only `propext`, `Classical.choice`
and `Quot.sound`. See [the replay instructions](../../scratch/jp-jack/REPLAY.md) for the
generator and [the closure output](../../scratch/jp-jack/ClosureCheck.txt) for
the two dependency checks.

Before and after: **29 H hypotheses plus 4 others, 33 total**. Both strict
columns count **5 LEAF / 24 GLUE** for H and **6 LEAF / 27 GLUE** overall.

Proposed kinds row:

| bundle | field | kind | strict | strictest | rating | flag |
| --- | --- | --- | --- | --- | --- | --- |
| research | `javanpeykarThm111JacKEx` | consequence | GLUE | GLUE | pending review | narrowed (jp-jack): Section 2.3's objects, a curve over a number field K and the Jacobian of X_K; the model/field-independence step is gone; remaining: the Section 2.3 composite (the lead's ruling) and the bridges listed in the report |

## Known issues

No mathematical error was found in the checked application. The row reads
semistability of the Jacobian's Néron model through `IsAnStableHeightSS`;
Javanpeykar's curve-model semistability has a different definition and
enters the reading through Section 2.3. The arXiv text was checked in the
existing locator audit; the journal pagination for §2.3 was not independently
page-checked here.

Resource check: the superseded cache rebuild survived the first stop attempt
and overlapped with early Lean checks, violating the one-process limit. It was
then terminated and the remaining verification used an exclusive process lock.

## Manuscript check

Each line refers to `diophantine_zq.tex`. These checks concern the scoped reader
and its inputs, not a new audit of the upstream modularity argument.

| TeX lines | Verdict | Check |
| --- | --- | --- |
| L383–396, L579 | OK | `M` is a product of primes, hence at least one, and `Q = R^(R E₀)` with `R ≥ 10¹²` is larger than the height-bound coefficient. |
| L595–598 | gap filled | The base-change invariance used here and implicit in stable height at L875–876 is supplied for the reader by the existing Faltings fold and witness uniqueness. The CM good-reduction argument itself is outside this check. |
| L710–716 | OK | Given the displayed kernel-field estimate, the constants absorb `4DR^R` into `Q`, as reused at L873. |
| L814–817 | OK | The prime-to-residue-characteristic choice in the local semistability application uses the same Raynaud input as the existing global semistable-witness construction. |
| L852–857 | unverified | The conductor-to-level step was not re-audited; the arithmetic of L872–873 uses its `N ≤ QM²` as supplied. |
| L860–864 | unverified | The common Tate constituent and Faltings Hom input belong to the preceding chain; this task did not recheck them. |
| L865–867 | OK | A nonzero map from the absolutely simple surface has finite kernel; reducibility gives the complement up to isogeny and forces `dim J ≥ 2`, as needed for the genus condition. |
| L868–870 | OK | The stated genus and map degree bounds give `g, deg_B ≤ N²` since the least degree is no larger than the given map degree. The task uses the chain's existing modular-curve data. |
| L870–872 | gap filled | The cited display gives the leading bound via the Jacobian over its field of definition; the Lean reader supplies the Pic⁰, genus, Belyi degree, and height bridges. |
| L872–874 | OK | `13·10⁶ N¹² ≤ Q¹³M²⁴` and `N² ≤ Q³M⁴` follow from the displayed bounds on `N,Q`; the field degree repeats L713. |
| L875–876 | gap filled | The same original stable normalization is transported between the kernel and analytic predicates. The remaining curve-height identification is the §2.3 part of the proposed row. |
