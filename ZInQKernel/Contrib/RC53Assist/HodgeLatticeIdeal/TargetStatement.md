# The Hodge lattice in invariant-differential coordinates

## Frozen targets

Fixed on November 19, 2026, before writing any proof body for this contribution.
All types attached to a group model are in universe zero.

Let `K L : Type`, with `[Field K] [Field L] [NumberField L] [Algebra K L]`, let
`E : PkgI3.AbVar K`, let `hdim : E.dim = 1`, and let
`G : ZInQ.DefFaltings.GroupModel E L`. Put `R := 𝓞 L` and `V := G.hodgeSpace 1`.
The model, its unit section, its generic-fibre identification, and its submodule `G.omega`
are the original objects, not replacements.

Take Weierstrass data `E'`, `e`, `i`, `hfield`, `hO` exactly as in
`HodgeLineBinding.hodgeEval_invariantDifferential`, including `[E'.IsElliptic]`.
That reviewed theorem produces

```
hreg : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine)
  ∈ regularAtOrigin (E.baseChange L)
η := hodgeEval G hdim ⟨_, hreg⟩
η = G.wedge ![originParameter G E' i hO]
η ≠ 0
```

The following targets are to hold for that actual `η`, not for a newly normalized section.
Generic coordinate lemmas for an arbitrary nonzero vector in an `L`-line are allowed as helpers;
the final specialization must derive nonvanishing from the reviewed binding.

### Definitions and the degree-one dictionary

`coordinateMap η : L →ₗ[R] V` is the restriction of scalars of
`LinearMap.toSpanSingleton L V η`, so its value at `a` is `a • η`.

```
coefficientSubmodule (M : Submodule R V) (η : V) : Submodule R L :=
  M.comap (coordinateMap η)
Iη := coefficientSubmodule (G.detLattice 1) η
```

Thus, definitionally, `a ∈ Iη ↔ a • η ∈ G.detLattice 1`.

The natural degree-one map is

```
oneHodgeMap G : G.cotangent →ₗ[R] G.hodgeSpace 1 :=
  (TensorProduct.mk R L (exteriorPower R 1 G.cotangent) 1) ∘ₗ
    (exteriorPower.oneEquiv R G.cotangent).symm.toLinearMap
```

Prove that this map is injective and that

```
G.detLattice 1 = G.omega.map (oneHodgeMap G)
```

Its value at `G.dCls f` is the original wedge `G.wedge ![f]`. In particular the parameter
appearing in the reviewed binding maps to the actual invariant differential in the Hodge line.

### A. Reconstruction and unique coefficients

With `Iη` and `coordinateMap` as above, prove

```
G.detLattice 1 = Iη.map (coordinateMap η)
Function.Injective (coordinateMap η)
∀ v ∈ G.detLattice 1, ∃! a : L, a ∈ Iη ∧ a • η = v
```

The surjectivity used here follows from
`finrank_hodgeSpace_one_of_dim_one G hdim` and `η ≠ 0`.
No assertion that `η` itself is integral is made.

### B. A genuine nonzero fractional ideal

Prove, without lattice-shaped assumptions,

```
Iη ≠ ⊥
Iη.FG
Submodule.span L (Iη : Set L) = ⊤
IsFractional (nonZeroDivisors R) Iη
```

Bundle the same submodule as

```
coefficientFractionalIdeal G hdim η hη : FractionalIdeal (nonZeroDivisors R) L
```

with its coercion equal to `Iη`, and prove that this fractional ideal is nonzero.
The nonzero coefficient map identifies `Iη` with `G.detLattice 1` as `R`-modules;
together with `oneHodgeMap` it gives the `G.omega` / `Iη` dictionary. This is not a claim of
principality, a global generator, or freeness over `R`.

#### Rank input and quantifier boundary

The required pointwise rank statement is

```
Module.rank L (L ⊗[R] G.cotangent) = 1
```

It follows from the reviewed `finrank_hodgeSpace_one_of_dim_one`, using the degree-one
exterior-power base-change equivalence and finite-dimensionality of the cotangent space;
alternatively it follows from the reviewed `finrank_cotangentSpace_genStalk` and
`rank_tensor_cotangent` after choosing the existing Weierstrass presentation.

`CotangentRank` in the original file quantifies over ALL dimensions and ALL abelian varieties.
The rank-one statement does not prove that global proposition. The original theorem
`hodgeLatticeTheorem_of_cotangentRank : CotangentRank → HodgeLatticeTheorem` must therefore
not be applied to a fabricated global hypothesis. For this dimension-one task, use its exact
pointwise proof: `hodgeLattice_of_lattice` with the derived rank, and the unconditional
`omegaFG_of_omegaLocal omegaLocal` and `omegaSpans_of_omegaLocal omegaLocal`.
This yields the original `HodgeLatticeTheorem` conclusion for this `G` and `g = 1`:

```
Module.finrank L (G.hodgeSpace 1) = 1 ∧
  ∃ s ∈ G.detLattice 1, s ≠ 0 ∧ secIndex (G.detLattice 1) s ≠ 0
```

Finiteness of the determinant lattice also follows from the original `detLat_fg` and
`detLattice_eq`. There is no rank-one barrier in the reviewed statements; the global
all-dimensions proposition is explicitly outside this target.

### C. Section index in the ORIGINAL orientation

The exact definition is `HodgeData.lean`, lines 68–70:

```
secIndex (M : Submodule R V) (s : V) : ℕ :=
  (Submodule.span R {s}).toAddSubgroup.relIndex M.toAddSubgroup
```

Prove for every `a : L`, without assuming membership,

```
secIndex (G.detLattice 1) (a • η) = secIndex Iη a
secIndex (G.detLattice 1) (a • η) =
  (Submodule.span R {a}).toAddSubgroup.relIndex Iη.toAddSubgroup
```

This is the index of `Iη ∩ R a` in `Iη` in general, not the reverse index.
For `a ∈ Iη`, it is the cardinality of `Iη / R a`, with value zero if infinite.
For `a ∈ Iη` and `a ≠ 0`, writing `Jη` for the bundled fractional ideal, prove

```
(secIndex (G.detLattice 1) (a • η) : ℚ) * FractionalIdeal.absNorm Jη =
  |Algebra.norm ℚ a|
(secIndex (G.detLattice 1) (a • η) : ℚ) =
  |Algebra.norm ℚ a| / FractionalIdeal.absNorm Jη
secIndex (G.detLattice 1) (a • η) ≠ 0
```

The membership and nonzero conditions are indispensable for this norm formula.
As an orientation check, integral rescaling by `r : R` multiplies the section index by
`(Algebra.norm ℤ r).natAbs` when starting from a nonzero section belonging to the lattice.

### Final specialization and checks

The main export must quantify over the original Weierstrass data and conclude the existence
of the reviewed `hreg`, with the equalities and nonvanishing above, and A–C for
`η = hodgeEval G hdim ⟨_, hreg⟩`. No extra lattice, rank, principality, norm, or evaluation
hypothesis is allowed in that export.

Include non-vacuity examples on an actual number field, checking a nontrivial scalar section
and the index orientation. Provide named theorems with kind labels and exact source locators,
module build evidence, first-failure custody, axiom reports, and source sizes and SHA-256 hashes.

## Definition locators read before freezing

* `Models.lean`: `GroupModel.omega`, lines 151–152; `detLattice`, lines 158–162;
  `wedge`, lines 164–167; `HodgeLatticeTheorem`, lines 262–269.
* `HodgeLattice.lean`: `detLat`, lines 109–113; `hodgeLattice_of_lattice`, lines 115–122;
  `OmegaFG`, lines 243–247; `CotangentRank`, lines 249–255; `OmegaSpans`, lines 257–263;
  `detLattice_eq`, lines 265–267; `omegaLocal`, lines 604–701;
  `hodgeLatticeTheorem_of_cotangentRank`, lines 707–709; `detLat_fg`, lines 857–866.
* `HodgeData.lean`: `secIndex`, lines 68–70; `secIndex_smul`, lines 72–103.
* `IdealLines.lean`: `secIndex_mul_absNorm`, lines 25–98.
* `HodgeLineBinding/HodgeLine.lean`: `finrank_cotangentSpace_genStalk`, lines 56–67;
  `finrank_hodgeSpace_one`, lines 72–81;
  `finrank_hodgeSpace_one_of_dim_one`, lines 133–139.
* `HodgeLineBinding/Binding.lean`: `hodgeEval_invariantDifferential`, lines 98–183.
* `HodgeLineBinding/Linearity.lean`: `ιMulti_single_eq`, lines 164–169.

No minimal-discriminant, delta, archimedean, period, height, or new-model claim is part of
this contribution.
