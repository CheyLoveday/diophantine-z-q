# Joining the adelic algebra to Appendix F

`PMAdelic.geometry` constructs `PM.Geometry` for the proved order
`Adelic.levelOrder ell h N hN`, where `ell` is prime, `ell % 4 = 3`,
`N > 0`, and `N` is prime to `ell`. It takes the named Jetchev–Kane
comparison on double cosets and ELLIOT's modular special-fibre statements.
The ramification, level, right operations and comparison on ideal classes
are supplied by the join. In the Hecke comparison, every line indexing
gives the same multiset of neighbour classes, including multiplicities.
The citation itself supplies no level-one case.

The Heegner specialization stops at the comparison of the actual enhanced
CM points and at the identification of the same evaluation map on the
entries used downstream. The existing torsor result and the same-place
elliptic point reduction account for different sides of this comparison;
the precise missing statements are below. No new printed input is
introduced for Heegner reduction.

## Statements and consumers

All new declarations are in `ZInQ.Manuscript.RC.PMAdelic`. Write
`R` for the constructed level order, `c = Adelic.classesEquiv R`,
`j` for the supplied double-coset equivalence to the supersingular
locus, `F` for prime-field arithmetic Frobenius, and `C = j ∘ c`.
By `nbAt` we mean the class of the actual neighbour at the specified line.

| Declaration | Statement and consumer |
| --- | --- |
| `adelic` | Assigns `algebraicGeometry`'s `ram`, `eichler`, `atkin`, `atkin_involutive` and `uniformizer` to the corresponding five `PMGeometry.Adelic` fields. |
| `atkinOnDoubleCosets`, `uniformizerOnDoubleCosets` | For the respective proved permutation `U` on ideal classes, the double-coset permutation is `c ∘ U ∘ c⁻¹`. This undoes the existing transport from the proved right adelic action; these are the operations the named comparison reads. |
| `neighbourMultiset_eq` | For any two `LineIndex R p hp` and any class `z`, mapping the multiset of all lines by `nbAt` at `z` yields equal multisets of classes. Both indices enumerate the same actual locally principal subideals. In particular, summing any function on classes over either index gives the same sum. Used for `GeometricInput.hecke_compare`. |
| `JetchevKane.idealClasses` | The equivalence `C` is `c` followed by `j`; supplies `GeometricInput.classes`. |
| `JetchevKane.hecke_compare` | At every prime `p ∤ Nℓ₀`, for every line indexing and class `z`, `T_p[C(z)] = ∑ᵢ [C(nbAt(z,i))]` as a divisor. It transports `Adelic.hecke_eq_neighbours` along `C` and uses the multiset equality above. Supplies `GeometricInput.hecke_compare`. |
| `JetchevKane.atkin_compare` | At `p^e ∥ N`, `W_{p^e}(C(z)) = C(atkin_{p^e}(z))`; supplies `GeometricInput.atkin_compare`. |
| `JetchevKane.frobenius_compare` | `F(C(z)) = C(uniformizer(z))`; supplies `GeometricInput.frobenius_compare`. |
| `JetchevKane.frobenius_ss` | If `x` is supersingular, so is `F(x)`, by surjectivity of `j` and its Frobenius comparison. Supplies `GeometricInput.frobenius_ss`. |
| `geometricInput` | Constructs the entire `PMGeometry.GeometricInput` over `adelic` from the comparison and special fibre. |
| `geometry` | Applies `GeometricInput.geometry` to obtain the entire `PM.Geometry`, including specialized Hecke, affine Atkin–Lehner, the uniformizer identity, and equivariant specialization. |

The reindexing and transport between equivalent types are on-the-spot (c).
The geometry constructor uses the existing divisor arguments, which account
for the base cusp and its Atkin–Lehner translation. The left-order unit
group comparison in tex 8467–8468 is `Adelic.classGEquiv`; it is not a
field of `PM.Geometry`.

## Inputs that remain

| Input | Kind and manuscript lines |
| --- | --- |
| `CoarseFibre.Point`, `ss`, `T`, `W`, `frobenius` | ELLIOT: the coarse quadratic-residue model of `X₀(N)`, the supersingular locus, and the geometric operators. Tex 8465–8474, 8476–8479, 8481–8490, 9331–9339, 9347–9355. |
| `JetchevKane.classes`, `hecke`, `atkin`, `frobenius` | Named print: the equivalence of `DoubleCosets R` with the coarse supersingular locus, Jetchev–Kane §§1.1–1.2 and 2.5 as cited (locators UNVERIFIED here), tex 8465–8474. The same input includes its operator comparisons as used by ELLIOT: the good Hecke divisor is the image of the adelic multiset, `W_{p^e}` is the right Atkin–Lehner permutation, and `F` is the right division uniformizer (tex 8481–8490, 9331–9339, 9347–9355). These are the manuscript's comparison requirements, with no separate print for the operators. |
| `SpecialFibre.frobenius_sq` | ELLIOT: `F² = 1` on the coarse point model over the quadratic residue field, tex 8470–8473, 9351–9355. Stability of the supersingular subset under `F` is derived. |
| `SpecialFibre.infinity`, `T_infinity`, `frobenius_infinity` | ELLIOT: the rational base cusp, its Hecke divisor `(p+1)[∞]`, and its Frobenius fixedness. Tex 8480–8487, 9347–9355. |
| `SpecialFibre.J`, `jacobianGroup`, `divisorClass`, `quotient` | ELLIOT: specialized Jacobian points, the degree-zero divisor class map, and the quotient to the good elliptic special fibre. Tex 8476–8481. |
| `SpecialFibre.hecke_quotient` | ELLIOT: intertwining on `T_p[x] − T_p[∞]` with eigenvalue `a_p(E)`. Tex 8481–8487. |
| `SpecialFibre.atkinSign`, `atkinSign_eq`, `atkin_quotient` | ELLIOT: the sign `w_{p^e} ∈ {±1}` and its quotient relation on `[W_{p^e}x] − [W_{p^e}∞]`. Tex 8487–8489, 9334–9339. |
| `SpecialFibre.frobenius_quotient` | ELLIOT: the rational quotient commutes with Frobenius on the indicated degree-zero classes. Tex 9347–9355. |

These inputs use only the coarse model and the quotient identities on
the divisor classes read by Appendix F. The named comparison contains no
assertion about CM conjugates, orientation torsors, or theta coefficients.

### Heegner scope

For each evaluated `(θ, D, dat)` with `selG D = some dat` on
the inert support, use the restricted ring-class place of the same
absolute place `v` as the detector. Fix the existing reference tuple
(including the sign at ℓ₀ and all level orientations) and Artin labels
`σ_c`. The minimal missing CM bridge consists of:

1. The reductions `r_c` in the *same* `CoarseFibre.Point` of the actual
   enhanced curves `x_D^{σ_c}`, and
   `r_c = C(z_{t₀,c})` on this reference tuple. This is the
   manuscript's geometric use of the **existing** Cornut–Jetchev
   comparison (tex 9265–9279, specially its §§4.9–4.10 as cited,
   locators UNVERIFIED here). The existing `CJSetting.Thm31` and its
   `κ = 1` consequence give a statement about abstract oriented
   adelic fibres. `CJReductionData.PrintRealization.red_eq` is a
   comparison of that abstract reduction with the print's abstract map;
   it does not identify (r_c) on the modular special fibre.
2. ELLIOT, tex 8476–8479 and 9283–9291: on these points the specialized
   parametrization satisfies
   `π_{ℓ₀}(r_c) = datumReduction_v(σ_c(y))`, where `y`
   is the datum's actual generic elliptic point. `HeegnerDatum.hy`
   identifies (y) using the complex parametrization; it does not give
   reduction of (x_D^{σ_c}) or commutation with the good local model.
   Only the indicated conjugates are needed. A full reduction theory
   would have to construct the modular model and identify its actual
   CM points; the two pointwise equalities are the interface needed
   here.

For the evaluation, ELLIOT (tex 8370–8393, 8452–8459, 9265, 9288–9291),
`datumReduction` and `evaluationAt` already construct the ring-class
reduction and detector at the same place once the compatible embedding is
fixed. `stageMap_eq_lam_comp` proves the formula for the untwisted local
map formed from that reduction. What the downstream comparison still
needs is that the actual shared `StageKummer` used by `lamOf` takes
`Lσ_c(y)` to `λ_M(datumReduction_v(Lσ_c(y)))` for the entries it uses.
Equality of homomorphisms at the selected entry is sufficient for
`PMGeometry.lamOf_reduction_at`; equality at unused entries is
unnecessary. `Wiring.actualRingClassRed` and the twisted
`Wiring.actualStageMapOn` already identify the map at the fixed witness;
`OddStagedInstance.hev` pins only that entry. The leaf documentation and
`exists_pinned_stageKummer` show the other entries are free. To obtain
the displayed equation for the shared map, align the split twist row
with the detector at the witness and use the actual reductions from
compatible embeddings for the other evaluated data. With that agreement
and the two CM equalities, the
existing Heegner lemma gives the reference-tuple congruence for
`Visibility.ComparisonCore.reduction` with the existing Artin character
match and lift; none of these pointwise inputs is a new print.

## Known issues

- Citation scope error at tex 8468–8474: the manuscript says the
  description allows every level prime to the ramified prime. The
  existing source audit A052 records Jetchev–Kane's hypothesis as
  `N > 1`, with general prime powers allowed. The citation does not
  cover level one; this is a gap in its application there. The Lean
  constructor is conditional on explicit comparison data at the level
  in question and does not assert the comparison exists at level one.
- The prime-field `F` used here acts on the quadratic model by an
  involution. Quadratic-field Frobenius in the Kummer calculation is
  `F²`; the manuscript uses `F` differently in tex 8379–8388 and
  8440–8446. No comparison with a different reduction place is used.

## Manuscript check

- 8462–8465 — OK: the explicit ramified algebra and level order supply the corresponding fields.
- 8465–8468 — OK: the adelic class and left-order identifications are supplied by `classesEquiv` and `classGEquiv`.
- 8468–8474 — error: the cited source's scope omits `N = 1`. The comparison is supplied as a named input, with no level-one application.
- 8470–8473 — unverified: the quadratic-field coarse model is used as stated; a construction by scalar Frobenius is not formalized here.
- 8476–8481 — unverified: the modular good model, specialized divisor class map and extended quotient are the ELLIOT inputs listed above.
- 8481–8487, 9040–9042, 9067–9071 — gap filled: the adelic multiset gives the actual neighbour sum for every line indexing, with multiplicity; the imported divisor calculation removes the cusp term.
- 8487–8489, 9331–9339 — gap filled: comparison with the proved right permutation supplies the geometric action on ideal classes, and the imported quotient calculation restores the cuspidal translation before scaling.
- 8489–8492, 9347–9355 — gap filled: transport of the right uniformizer gives the restricted Frobenius and hence the imported specialization identity used by the fixed detector.
- 9331–9358 — OK: the norm-character and orientation factors are separate from the geometric operator comparisons.
- 9195–9263 — unverified: the existing oriented torsor interfaces are used to locate the missing CM comparison, without reconstructing their geometric realization.
- 9265–9279 — unverified: the actual enhanced CM reductions at the chosen place are not identified by the current abstract torsor record.
- 9280–9291 — unverified: the finite sum calculation follows from the existing pointwise lemma, but its specialization and shared evaluation premises for the evaluated data are still missing.

## Validation

`Comparison.lean` and `Geometry.lean` each passed
`lake env lean --threads=1` in a serial queue. The 14
`#print axioms` checks report only `propext`, `Classical.choice`
and `Quot.sound`. The new files use no `sorry`, axiom declarations,
local notation or import of `ZInQKernel.OneProof.Main`.
