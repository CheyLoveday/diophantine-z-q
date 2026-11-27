# Algebraic binding of the invariant differential to the Hodge line of a group model

## Frozen target (fixed before any proof was written)

World (all types in universe `0`, as in `ZInQ.DefFaltings.GroupModel`):

* `K L : Type`, `[Field K] [Field L] [NumberField L] [Algebra K L]`;
* `E : PkgI3.AbVar K` with `hdim : E.dim = 1`; write `B := E.baseChange L`, `X := B.X.left`,
  `o := identityPoint B.X` (the image of the point of `Spec L` under the unit section of `B`);
* `G : ZInQ.DefFaltings.GroupModel E L`, with its own unit section, `ξ = G.genericUnit`,
  `G.genStalk`, `G.cotangent = 𝔪_ξ/𝔪_ξ²`, `G.dCls`, `G.wedge`, `G.hodgeSpace 1`
  (all unchanged; `G.gen` is used only through its stalk map at the identity of the generic
  fibre and the point equation it satisfies as a homomorphism of group objects);
* Weierstrass data over `L` of the shape produced by
  `abVar_projectiveWeierstrassModel_numberField L B (dimension of B = 1)`:
  `E' : WeierstrassCurve L` with `[E'.IsElliptic]`,
  `e : E'.toAffine.FunctionField ≃ₐ[L] X.functionField`,
  `i : X ≅ Proj E'.toProjective.grading`,
  `hfield : i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom`,
  `hO : i.hom o = pointO E'` (a point equation; no section equation is used).

Objects to construct (all from actual maps; no basis of an abstract line is chosen):

1. `originStalkEquiv G : G.genStalk ≃+* X.presheaf.stalk o`, the composite of the stalk map of
   the projection of the generic fibre `𝒢 ×_{𝓞_L} L → 𝒢` at the identity `ξ_L` of the generic
   fibre (an isomorphism of local rings) with the inverse of the stalk map of `G.gen` at `ξ_L`.
2. `originEval : Ω[𝒪_{X,o}/L] →ₗ[𝒪_{X,o}] 𝔪_o/𝔪_o²`, the evaluation of Kähler differentials
   at the rational point `o`: `D a ↦ class of a - a(o)`, where `a(o) ∈ L` is the value given by
   the unit section of `B`.
3. `regularAtOrigin : Submodule L Ω[L(X)/L]`, the image of `Ω[𝒪_{X,o}/L]`, and the value map
   `originValue : regularAtOrigin →ₗ[L] 𝔪_o/𝔪_o²` (well defined because
   `Ω[𝒪_{X,o}/L] → Ω[L(X)/L]` is injective for a smooth curve in characteristic zero).
4. `toModelCotangent G : 𝔪_o/𝔪_o² → G.cotangent`, the map induced by `originStalkEquiv G`, and
   `hodgeEval G : regularAtOrigin → G.hodgeSpace 1`, `η ↦ 1 ⊗ ι(toModelCotangent (originValue η))`.
5. `kaehlerTransport e : Ω[L(E')/L] →ₗ[L] Ω[L(X)/L]`, Kähler functoriality of the field
   isomorphism `e` (which is the function-field pull-back of `i`, by `hfield`).
6. `originParameter G E' i hO ∈ 𝔪_ξ`: the image under `originStalkEquiv G`⁻¹ of the image under
   the stalk map of `i` at `o` of the germ at `O` of the function `-x/y` (a local parameter).

Target statement:

```
theorem hodgeEval_invariantDifferential (hdim : E.dim = 1) (E' : WeierstrassCurve L)
    [E'.IsElliptic] (e) (i) (hfield) (hO) :
    ∃ hreg : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine)
        ∈ regularAtOrigin E,
      hodgeEval G hdim ⟨_, hreg⟩ = G.wedge ![originParameter G E' i hO] ∧
      G.wedge ![originParameter G E' i hO] ≠ 0
```

that is, `c = 1` in `G.wedge ![f] = c • image(ω)` for the local parameter `f` corresponding to
`-x/y`; and the existence form obtained by combining it with the number-field S2a theorem.
The explicit local formula behind it is `ω = u⁻¹ • d(-x/y)` with
`u = 1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²`, `z = -x/y`, `w = -1/y`, `u ≡ 1` at `O`
(Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., IV.1).

## First barrier analysis

* (i) Stalk of the model at `ξ` versus the stalk of the generic fibre at its identity: not a
  barrier. The projection `𝒢 ×_{𝓞_L} L → 𝒢` induces isomorphisms on all local rings
  (`ZInQ.DefFaltings.HodgeLattice.genericFibreStalkIso`), and the identity of the generic fibre
  maps to `ξ` and, under `G.gen`, to the origin (`fst_genericFibreUnit`,
  `gen_genericFibreUnit`), all proved in `HDecomp/Faltings/HodgeLattice.lean`.
* (ii) Unit section of `B` versus the `O`-section of the projective model: not needed. Only the
  point equation `i(o) = O` is used, through stalk maps at points. The value `a(o)` in the
  evaluation map comes from the unit section of `B` itself; on the projective side only the
  local ring at `O` and the valuation at infinity are used.
* (iii) A projective group law: not needed.

No genuine barrier was found for the algebraic evaluation; see the module documentation of
`Binding.lean` for what is proved and what is left to the owning lane.

## Outcome (appended after the proofs; the frozen part above is unchanged)

The frozen target is proved as stated: `hodgeEval_invariantDifferential` in `Binding.lean`, with
hypotheses exactly `hdim`, `[E'.IsElliptic]`, `e`, `i`, `hfield`, `hO` (the structure-morphism
equation of S2a is not needed), and its existence form `exists_weierstrassModel_hodgeEval`.
Shape details forced by elaboration: `regularAtOrigin` is an `abbrev`; `toModelCotangent` is an
additive map whose `𝓞_L`-linearity is the separate theorem `toModelCotangent_smul`; `hodgeEval`
is a function, packaged as the `L`-linear map `hodgeEvalLinear`.

Beyond the frozen target: compatibility of `originStalkEquiv` with the constants, `L`-linearity,
`finrank L (G.hodgeSpace 1) = 1`, the wedge of the local parameter spans the Hodge line, and the
comparison of the regular Kähler line with the Hodge line is an `L`-linear isomorphism
(`lineComparisonEquiv`, `LineComparison.lean`). See `README.md`.
