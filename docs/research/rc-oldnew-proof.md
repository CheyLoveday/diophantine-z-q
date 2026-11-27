# Old/new independence for the even inventory

`oldNewIndependenceWeightTwo_proved : OldNewIndependenceWeightTwo` supplies
the weight-two old/new input for the even inventory. Its statement is
`∀ (N : ℕ) [NeZero N], LinearIndependent ℂ (fun x : CuspDilation N => x.form)`.
Each index records a genuine normalized newform and a degree whose product
with its source level divides `N`. The placed consumers use this theorem
directly. Both Lean files compile, and the axiom audit found only
standard axioms.

The inherited manuscript error at tex 8162–8167 is the missing base factor
in the simplified expansion. Tex 8168–8182 records the exact expression.
The earlier inventory also misattributed independence to Li's strong
multiplicity-one theorem. See Known issues.

## Proof and provenance

For the constituent inventories in tex 9649–9654 and 9754–9764, the actual
dilations are simultaneous eigenvectors of the diamond operators and of
all `Tₚ` with `p ∤ N`. The vendored
`CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd` gives the inflated
diamond character.
`EigenformAwayFromLevel.heckeTCuspNat_levelRaise_eq_eigenvalue_smul` gives
the Hecke equation for every admissible degree.
`Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq` in the vendored
`Newforms/StrongMultiplicityOne/Across.lean` recovers the source level
and underlying form from these two sets of eigenvalues. Its proof uses
the old/new splitting and level descent. The joint eigenspaces are
supremum-independent by the vendored `iSupIndep_iInf_eigenspace`.

The grouping by joint eigenvalue function and the Fourier argument within
each group are on-the-spot (provenance (c)). With the source fixed, each
degree gives just one label. In a finite relation choose the least degree
with nonzero scalar and apply the Fourier coefficient linear functional
there. `CuspDilation.coeff_form` and `Odd.divCoeff` give zero for larger
degrees and the normalized coefficient one for the chosen degree.
Mathlib's `linearIndependent_iUnion_finite` combines the groups.
Injectivity of the label-to-form map follows from the resulting linear
independence.

## Statements and inputs supplied

The exact Lean statements are in
`ZInQKernel/Contrib/OneProof/RC/EvenJoin/OldNewProof.lean` and
`ZInQKernel/Contrib/OneProof/RC/EvenJoin/OldNewConsumers.lean`.
The first file supplies the leaf and its injectivity consequence. The
private lemmas supply the following steps.

| Theorem | Statement and use |
| --- | --- |
| `columnOperator_apply` | Each ambient diamond or good-prime Hecke endomorphism acts on `x.form` by the corresponding value of `columnEigenvalues x`. |
| `source_eq_of_eigenvalues_eq` | Equal joint eigenvalue functions imply `x.source = y.source`. |
| `column_degree_pos` | For nonzero ambient level, every `x.degree` is positive. |
| `column_coeff_degree` | `x.coeff x.degree = 1`. |
| `independent_eigenvalue_fiber` | For each joint eigenvalue function `a`, `x ↦ x.val.form` is complex-linearly independent on `{x : CuspDilation N // columnEigenvalues x = a}`. |
| `oldNewIndependenceWeightTwo_proved` | `OldNewIndependenceWeightTwo`, with no additional hypotheses. |
| `cuspDilation_form_injective` | `Function.Injective (fun x : CuspDilation N => x.form)` for nonzero `N`. |
| `cuspDilation_coeff_independent_proved` | `LinearIndependent ℂ (CuspDilation.coeff (N := N))` for nonzero `N`. Supplies the Fourier independence required by the finite inventory. |

In the statements below, a subscript “proved” on an inventory, basis,
seed, model, or Galois input denotes its specialization at
`oldNewIndependenceWeightTwo_proved`. The corresponding abbreviations
are `cuspInventory_proved`, `PlacedCuspLists.inventory_proved`,
`PlacedCuspLists.evenBasis_proved`, `PlacedCuspLists.seed_proved`,
`PlacedCuspLists.determinantData_proved`, `PlacedCuspLists.model_proved`
and `PlacedGaloisInput_proved`. The determinant abbreviation supplies the
original `DeterminantFourierData` on the specialized row and residue ideal.

| Theorem | Statement and input supplied |
| --- | --- |
| `cuspInventory_coeff_proved` | `κ (inventory.expansion x n) = x.val.coeff n` for every column and Fourier index. Supplies the exact inventory coefficient. |
| `cuspInventory_char_proved` | `κ (inventory.χ (cuspOrigin D x) u : K) = (x.val.char u : ℂ)` for every column and unit. Supplies the exact inventory character. |
| `PlacedCuspLists.block_span_proved` | `a b ∈ Submodule.span ℂ (blockColumns (P.inventory_proved T) P.κ (m b) (P.blockChar b))`. Supplies the intrinsic span of each block. |
| `PlacedCuspLists.seed_complex_proved` | `D.κ (basis.eval n seed) = (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n`. Supplies the complex seed coordinate. |
| `PlacedCuspLists.seed_integral_proved` | `basis.eval n seed = algebraMap _ _ (D.ringMap (timesTheta (fixedH C₀ i U hU) n))`. Supplies its integral representative. |
| `placed_diamond_eval_proved` | At each diamond unit `u` there are integral scalars `ψ` and `c j` with moving character value `ψ`, and every coefficient of the translated seed is the image of `ψ` times the divided seed coefficient plus the sum of `c j` times the undivided unary coefficients. Supplies the diamond correction. |
| `PlacedCuspLists.integral_diamonds_proved` | `basis.eval n (basis.diamond u seed) ∈ integralRange (O := FixedRing D.w)` for all `u, n`. Supplies the integral orbit input. |
| `PlacedCuspLists.fresh_coeff_mem_proved` | `oneCoeff basis seed Subtype.val_injective integral_diamonds (r * (q * n)) (oneLatSeed basis seed U) ∈ m` when `2 ∈ m`, `n ≠ 0`, and `q,r` are distinct good primes outside `U` with neither dividing `n`. Supplies the two-fresh trace input. |
| `PlacedCuspLists.model_coordinates_proved` | For `n ≠ 0`, `D.κ (algebraMap M.1.O M.1.K (M.2.coeff n (M.1.F U))) = (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n`. Supplies the scoped coordinate comparison. |
| `budgetRealization_of_placed_proved` | `BudgetRealizationScoped (hS := hS) C₀ i B` from `PlacedGaloisInput_proved` for every good `U` with `U.card + 1 ≤ B`. Supplies the row realizations at bound `B`. |
| `rules_and_seed_of_placed_joint_proved` | `CoefficientRules (evenSign W.S) (P.symbol hS) ∧ ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ` from the same input for every `B` and eligible `U`. Supplies the joint even conclusion. |

## Remaining hypotheses and owners

The old/new theorem has only the nonzero-level typeclass in its existing
statement. The inventory constructors and downstream theorems retain the
following named inputs.

- **Inventory caller.** Finite column lists and the source coefficient
  and character lifts `ha` and `hχ` along `κ` for the abstract
  constructor. The placed constructor gets these lifts from
  `PlacedCuspLists`. The row constructors use block lists `A`, their
  intrinsic level divisibility proofs, and character identities `hB`
  and `hJ`. These are the data quantified inside the existing
  `PlacedGaloisInput`.
- **Fixed-place and even source setup.** The original ambient data
  `W, L, τ, P, hS, i`, the conductor and moving-level nonzero
  instances, the number field and place `F, v`, `C₀`, and embeddings
  `j, hK, hC` (or their row comparison `hκ`). The row uses the
  goodness condition `hU`, parity `hodd`, two-power phase order
  `horder`, and prime over two `htwo`. The determinant and fresh
  coefficient consumers take the designated residue ideal and
  applicable `hm`, `h2`. The final premise ranges over the existing
  capacity bounds.
- **Modular Galois attachment.** `D.sourceAttachments` at every actual
  normalized cuspidal source. It requires continuity, good-prime
  unramifiedness in the ideal presentation, and arithmetic Frobenius
  trace and determinant on the common coefficient field.
- **Local cuspidal comparison.** `CuspidalLocalAt` for the row formed
  using those attachments. For every `q ∈ U` and `Q : LocalPair q`,
  it asks for `CuspidalData X Q`, support of the seed on its active
  coordinates, and the `WhittakerComparison` for its `up` operator at
  coefficient one.

## Known issues

- At tex 8162–8167 the simplified expansion omits a base factor. The
  supplied even consumers use the exact expression at 8168–8182.
- The prior inventory report identifies Li 1975, Theorem 5, p. 298
  (locator UNVERIFIED here) as strong multiplicity one. The source uses
  old/new independence elsewhere. The cited Diamond–Shurman GTM 228
  Theorem 5.8.3 and Atkin–Lehner 1970 Theorem 5, p. 151 (trivial
  character) remain UNVERIFIED. The Lean proof removes the need for an
  independence print or a reading-list locator for that leaf.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited missing base factor in the simplified expansion. |
| 8168–8182 | OK | The exact expansion includes that factor. |
| 9649–9654 | gap filled | The cuspidal inventory retains distinct old degrees in an independent characteristic-zero family. The attachment to Galois representations remains the named input above. |
| 9655–9659 | OK | The existing diamond comparison specializes to the independent seed and columns. |
| 9660–9668 | OK | The existing placed model uses the good Hecke coordinates and exact Fourier comparison. |
| 9754–9760 | gap filled | Independence preserves the intrinsic spans of the blocks and their old degrees. The local representation claim still uses the existing cuspidal input. |
| 9762–9764 | gap filled | The cuspidal coefficient inventory uses one normalized source per eigensystem and all its actual degrees. |
| 9764–9769 | unverified | The sourcewise trace and determinant require the existing attachment. |

## Verification

Built the direct imports with `lake build`. Checked both new Lean files
with `lake env lean` on Lean 4.35.0. The cache was seeded with
source-matched artifacts from an existing build and validated by Lake.
The checks ran serially under the 60 GB memory cap.

`lake env lean scratch/rc-oldnew-proof/Audit.lean` ran `#print axioms`
for all 29 declarations, including all 19 theorems. The raw results are
in `scratch/rc-oldnew-proof/axioms.txt`.

- `GoodPrime` uses `propext`.
- The following declarations each use `propext`, `Classical.choice`, and
  `Quot.sound`.

```text
columnOperator
columnEigenvalues
columnOperator_apply
source_eq_of_eigenvalues_eq
column_degree_pos
column_coeff_degree
independent_eigenvalue_fiber
oldNewIndependenceWeightTwo_proved
cuspDilation_form_injective
cuspDilation_coeff_independent_proved
cuspInventory_proved
cuspInventory_coeff_proved
cuspInventory_char_proved
PlacedCuspLists.inventory_proved
PlacedCuspLists.block_span_proved
PlacedCuspLists.evenBasis_proved
PlacedCuspLists.seed_proved
PlacedCuspLists.seed_complex_proved
PlacedCuspLists.seed_integral_proved
placed_diamond_eval_proved
PlacedCuspLists.integral_diamonds_proved
PlacedCuspLists.fresh_coeff_mem_proved
PlacedCuspLists.determinantData_proved
PlacedCuspLists.model_proved
PlacedCuspLists.model_coordinates_proved
PlacedGaloisInput_proved
budgetRealization_of_placed_proved
rules_and_seed_of_placed_joint_proved
```

The worktree was already on the requested branch at
`9a60a98cd9bcca63c7bc283c58be01eb9952578d`. The fetch attempt received
HTTP 403 from the network proxy.
