# Exact theorem statements and axiom dependencies

All names below lie in `ZInQ.Contrib.RC53Assist.AbelianCurve`. The signatures are copied from the checked contribution sources, retaining every hypothesis and every local algebra or local-ring instance. The proof bodies are not repeated. `Axioms.txt` contains the exact compiler output for all 84 declarations, including definitions and private helpers.

## `sections_functionField_tower`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 74–78.

```lean
theorem sections_functionField_tower {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] :
    letI := functionFieldAlgebra f
    letI := sectionsAlgebra f U
    IsScalarTower k Γ(X, U) X.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `finiteType_sections`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 95–98.

```lean
theorem finiteType_sections {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    Algebra.FiniteType k Γ(X, U)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `integral_dimension_eq`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 111–113.

```lean
private theorem integral_dimension_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `normalization_dimension`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 134–136.

```lean
private theorem normalization_dimension {k R : Type} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ n : ℕ, ringKrullDim R = n ∧ Algebra.trdeg k R = n
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `fractionField_trdeg`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 156–158.

```lean
private theorem fractionField_trdeg {k R F : Type} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Field F] [Algebra R F] [Algebra k F] [IsScalarTower k R F]
    [IsFractionRing R F] : Algebra.trdeg k F = Algebra.trdeg k R
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `affine_dimension_eq_trdeg`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 167–171.

```lean
theorem affine_dimension_eq_trdeg {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := functionFieldAlgebra f
    topologicalKrullDim U = ((Algebra.trdeg k X.functionField).toENat : WithBot ℕ∞)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `dimension_open_cover`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 186–189.

```lean
private theorem dimension_open_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `dimension_eq_trdeg`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 212–215.

```lean
theorem dimension_eq_trdeg {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    letI := functionFieldAlgebra f
    topologicalKrullDim X = ((Algebra.trdeg k X.functionField).toENat : WithBot ℕ∞)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `functionField_essFiniteType`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 238–241.

```lean
theorem functionField_essFiniteType {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    letI := functionFieldAlgebra f
    Algebra.EssFiniteType k X.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `isFunctionField_of_dimension_one`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 257–260.

```lean
theorem isFunctionField_of_dimension_one {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    TauCeti.IsFunctionField k X.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `tensor_domain_of_localization`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 272–275.

```lean
private theorem tensor_domain_of_localization {k A B L : Type} [Field k] [CommRing A]
    [Algebra k A] (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) [CommRing B] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [IsLocalization M B] [CommRing L] [Algebra k L]
    [IsDomain (A ⊗[k] L)] : IsDomain (B ⊗[k] L)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `functionField_tensor_domain`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 298–301.

```lean
theorem functionField_tensor_domain {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] (L : Type) [Field L] [Algebra k L] :
    letI := functionFieldAlgebra f
    IsDomain (X.functionField ⊗[k] L)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `exact_constants_of_tensor_domain`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 331–332.

```lean
private theorem exact_constants_of_tensor_domain {k K : Type} [Field k] [Field K] [Algebra k K]
    [IsDomain (K ⊗[k] AlgebraicClosure k)] : algebraicClosure k K = ⊥
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `functionField_exact_constants`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 353–356.

```lean
theorem functionField_exact_constants {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] :
    letI := functionFieldAlgebra f
    IsIntegrallyClosedIn k X.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_scheme_integral`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 364–365.

```lean
theorem abelian_scheme_integral {k : Type} [Field k] (G : Over (Spec (.of k)))
    [GeometricallyIntegral G.hom] : IsIntegral G.left
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_functionField`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/FunctionField.lean`, lines 372–377.

```lean
theorem abelian_functionField (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G]
    [IsProper G.hom] [Smooth G.hom] [GeometricallyIntegral G.hom]
    [IsIntegral G.left] (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsFunctionField ℚ G.left.functionField ∧
      IsIntegrallyClosedIn ℚ G.left.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `identitySection_comp`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 36–37.

```lean
theorem identitySection_comp (G : Over (Spec (.of ℚ))) [GrpObj G] :
    identitySection G ≫ G.hom = 𝟙 _
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `identityPoint_closed`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 48–49.

```lean
theorem identityPoint_closed (G : Over (Spec (.of ℚ))) [GrpObj G] :
    IsClosed ({identityPoint G} : Set G.left)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `rat_algebraMap_bijective_of_hom_to_rat`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 72–73.

```lean
theorem rat_algebraMap_bijective_of_hom_to_rat {F : Type} [Field F] [Algebra ℚ F]
    (φ : F →+* ℚ) : Function.Bijective (algebraMap ℚ F)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `finrank_eq_one_of_hom_to_rat`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 80–81.

```lean
theorem finrank_eq_one_of_hom_to_rat {F : Type} [Field F] [Algebra ℚ F] (φ : F →+* ℚ) :
    Module.finrank ℚ F = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `stalk_functionField_tower`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 97–101.

```lean
theorem stalk_functionField_tower {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := functionFieldAlgebra f
    letI := stalkAlgebra f x
    IsScalarTower k (X.presheaf.stalk x) X.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `identityPlace_degree`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 129–132.

```lean
theorem identityPlace_degree (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    (identityPlace G).degree = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `identityPlace_integers`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/IdentityPlace.lean`, lines 145–150.

```lean
theorem identityPlace_integers (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    (identityPlace G).integers.toSubring =
      (⊤ : Subring (G.left.presheaf.stalk (identityPoint G))).map
        (algebraMap (G.left.presheaf.stalk (identityPoint G)) G.left.functionField)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `regular_of_flat_local`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 46–50.

```lean
private theorem regular_of_flat_local {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsRegularLocalRing S
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `regular_localization_etale`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 66–68.

```lean
private theorem regular_localization_etale {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [IsRegularRing R] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `regular_stalk_of_etale_chart`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 88–91.

```lean
private theorem regular_stalk_of_etale_chart {X : Scheme.{0}} {R : Type} [CommRing R]
    [IsRegularRing R] {U : X.Opens} (hU : IsAffineOpen U)
    (φ : R →+* Γ(X, U)) (hφ : φ.Etale) (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `smooth_stalk_regular`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 104–105.

```lean
theorem smooth_stalk_regular {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ)) [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `functionField_kaehler_rank_one`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 118–121.

```lean
theorem functionField_kaehler_rank_one {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    Module.finrank X.functionField (KaehlerDifferential ℚ X.functionField) = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `smooth_relativeDimension_one`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 132–134.

```lean
theorem smooth_relativeDimension_one {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1) :
    SmoothOfRelativeDimension 1 f
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `locallyQuasiFinite_etale`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 175–176.

```lean
private theorem locallyQuasiFinite_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `coheight_flat_quasifinite`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 186–187.

```lean
private theorem coheight_flat_quasifinite {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f]
    [LocallyQuasiFinite f] (x : X) : coheight (f x) = coheight x
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `maximal_polynomial_height`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 208–210.

```lean
private theorem maximal_polynomial_height (k : Type) [Field k] :
    ∀ (ι : Type) [Finite ι] (m : Ideal (MvPolynomial ι k)) [m.IsMaximal],
      m.height = Nat.card ι
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `coheight_closed_etale_polynomial`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 239–241.

```lean
private theorem coheight_closed_etale_polynomial {k : Type} [Field k] {R : CommRingCat.{0}}
    {n : ℕ} (φ : MvPolynomial (Fin n) k →+* R) (hφ : φ.Etale) (x : Spec R)
    (hx : IsClosed {x}) : coheight x = n
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `closed_stalk_dimension_one`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 254–256.

```lean
theorem closed_stalk_dimension_one {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `closed_stalk_discreteValuationRing`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 282–284.

```lean
theorem closed_stalk_discreteValuationRing {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1)
    {x : X} (hx : IsClosed {x}) : IsDiscreteValuationRing (X.presheaf.stalk x)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `smooth_curve_valuation_stalk`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 296–298.

```lean
theorem smooth_curve_valuation_stalk {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1) (x : X) :
    ValuationRing (X.presheaf.stalk x)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `identity_stalk_discreteValuationRing`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 323–325.

```lean
theorem identity_stalk_discreteValuationRing (G : Over (Spec (.of ℚ))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1) :
    IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `smoothIdentityPlace_degree`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 340–343.

```lean
theorem smoothIdentityPlace_degree (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    (smoothIdentityPlace G hdim).degree = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `ellipticFunctionField_of_genus_one`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SmoothCurve.lean`, lines 351–356.

```lean
theorem ellipticFunctionField_of_genus_one (G : Over (Spec (.of ℚ))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (hg : letI := functionFieldAlgebra G.hom
      TauCeti.genus ℚ G.left.functionField = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField ℚ G.left.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `globalFunctions_bijective`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/DifferentialLine.lean`, lines 80–82.

```lean
theorem globalFunctions_bijective {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] [GeometricallyIntegral f] :
    Function.Bijective (globalFunctionsMap f)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `finrank_globalSections_trivial_line`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/DifferentialLine.lean`, lines 120–124.

```lean
theorem finrank_globalSections_trivial_line {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] [GeometricallyIntegral f]
    (M : X.Modules) (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    letI := globalSectionsModule f M
    Module.finrank k Γ(M, ⊤) = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_genus_one_of_differentials`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/DifferentialLine.lean`, lines 170–176.

```lean
theorem abelian_genus_one_of_differentials
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.genus ℚ G.left.functionField = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_isEllipticFunctionField`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/DifferentialLine.lean`, lines 190–196.

```lean
theorem abelian_isEllipticFunctionField
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField ℚ G.left.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_weierstrassModel`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/WeierstrassReduction.lean`, lines 28–35.

```lean
theorem abelian_weierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧
      Nonempty (W.FunctionField ≃ₐ[ℚ] G.left.functionField)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_weierstrassCoordinates`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/WeierstrassReduction.lean`, lines 45–56.

```lean
theorem abelian_weierstrassCoordinates
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    let P := smoothIdentityPlace G hdim
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧
      ∃ e : W.FunctionField ≃ₐ[ℚ] G.left.functionField,
        P.ord (e W.genericX) = -2 ∧ P.ord (e W.genericY) = -3 ∧
        (∀ Q : TauCeti.Place ℚ G.left.functionField, Q ≠ P → 0 ≤ Q.ord (e W.genericX)) ∧
        (∀ Q : TauCeti.Place ℚ G.left.functionField, Q ≠ P → 0 ≤ Q.ord (e W.genericY))
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `fromFunctionField_structure`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/BirationalComparison.lean`, lines 44–47.

```lean
theorem fromFunctionField_structure {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) :
    letI := functionFieldAlgebra f
    fromFunctionField X ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ X.functionField))
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `functionFieldMap_over`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/BirationalComparison.lean`, lines 62–65.

```lean
theorem functionFieldMap_over {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) (e : Y.functionField →+* X.functionField) :
    (Spec.map (CommRingCat.ofHom e) ≫ fromFunctionField Y) ≫ g =
      fromFunctionField X ≫ f
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `extend_from_valuation_stalks`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/BirationalComparison.lean`, lines 77–81.

```lean
theorem extend_from_valuation_stalks {X Y : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) [IsProper g]
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (a : Spec X.functionField ⟶ Y) (ha : a ≫ g = fromFunctionField X ≫ f) :
    ∃ b : X ⟶ Y, b ≫ g = f ∧ fromFunctionField X ≫ b = a
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `eq_of_generic_agreement`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/BirationalComparison.lean`, lines 143–146.

```lean
theorem eq_of_generic_agreement {X Y : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of ℚ)) (sY : Y ⟶ Spec (.of ℚ)) [IsSeparated sY]
    (f g : X ⟶ Y) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX)
    (h : fromFunctionField X ≫ f = fromFunctionField X ≫ g) : f = g
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `isomorphism_of_functionField_equiv`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/BirationalComparison.lean`, lines 161–168.

```lean
theorem isomorphism_of_functionField_equiv {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) [IsProper f] [IsProper g]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
    (e : Y.functionField ≃+* X.functionField) :
    ∃ i : X ≅ Y, i.hom ≫ g = f ∧
      fromFunctionField X ≫ i.hom =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fromFunctionField Y
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `isomorphism_functionFieldMap`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/BirationalComparison.lean`, lines 189–193.

```lean
theorem isomorphism_functionFieldMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (e : Y.functionField ≃+* X.functionField) (i : X ≅ Y)
    (h : fromFunctionField X ≫ i.hom =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fromFunctionField Y) :
    i.hom.functionFieldMap = CommRingCat.ofHom e.toRingHom
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `projectiveStructure_proper`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ProjectiveComparison.lean`, lines 45–45.

```lean
theorem projectiveStructure_proper (E : WeierstrassCurve ℚ) : IsProper (projectiveStructure E)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `projectivePoint_mem_zChart`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ProjectiveComparison.lean`, lines 52–53.

```lean
theorem projectivePoint_mem_zChart (E : WeierstrassCurve ℚ) (P : Proj E.toProjective.grading)
    (hP : P ≠ pointO E) : P ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `projective_valuation_stalk`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ProjectiveComparison.lean`, lines 63–65.

```lean
theorem projective_valuation_stalk (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : Proj E.toProjective.grading) :
    ValuationRing ((Proj E.toProjective.grading).presheaf.stalk P)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `identityPlace_transport_infinity`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ProjectiveComparison.lean`, lines 100–107.

```lean
theorem identityPlace_transport_infinity (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (E : WeierstrassCurve ℚ) (e : E.toAffine.FunctionField ≃+* G.left.functionField)
    (hx : letI := functionFieldAlgebra G.hom
      (smoothIdentityPlace G hdim).ord (e E.toAffine.genericX) = -2) :
    letI := functionFieldAlgebra G.hom
    ((smoothIdentityPlace G hdim).valuation.comap e.toRingHom).IsEquiv
      (WeierstrassCurve.Affine.infinityPlace E.toAffine)
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `comparison_sends_identity`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ProjectiveComparison.lean`, lines 132–139.

```lean
theorem comparison_sends_identity (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (E : WeierstrassCurve ℚ) (e : E.toAffine.FunctionField ≃+* G.left.functionField)
    (i : G.left ≅ Proj E.toProjective.grading)
    (he : i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom)
    (hx : letI := functionFieldAlgebra G.hom
      (smoothIdentityPlace G hdim).ord (e E.toAffine.genericX) = -2) :
    i.hom (identityPoint G) = pointO E
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelian_projectiveWeierstrassModel`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ProjectiveComparison.lean`, lines 166–178.

```lean
theorem abelian_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] G.left.functionField)
        (i : G.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = G.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint G) = pointO E
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abVar_functionField`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ObjectBridge.lean`, lines 35–39.

```lean
theorem abVar_functionField (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    TauCeti.IsFunctionField ℚ A.X.left.functionField ∧
      IsIntegrallyClosedIn ℚ A.X.left.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abVar_identityPlace_degree`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ObjectBridge.lean`, lines 47–50.

```lean
theorem abVar_identityPlace_degree (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    (smoothIdentityPlace A.X hdim).degree = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abVar_projectiveWeierstrassModel`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ObjectBridge.lean`, lines 60–71.

```lean
theorem abVar_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `groupAbVar_projectiveWeierstrassModel`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/ObjectBridge.lean`, lines 79–92.

```lean
theorem groupAbVar_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (A : Grp (Over (Spec (.of ℚ)))) [PkgI2.IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := (inferInstance : PkgI2.IsAbelianVariety A).geomIntegral
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelianScheme_geometricallyIntegral`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SchemeBridge.lean`, lines 30–32.

```lean
theorem abelianScheme_geometricallyIntegral
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A] :
    GeometricallyIntegral A.X.hom
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelianScheme_integral`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SchemeBridge.lean`, lines 40–41.

```lean
theorem abelianScheme_integral
    (A : Grp (Over (Spec (.of ℚ)))) [PkgI2.IsAbelianScheme A] : IsIntegral A.X.left
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelianScheme_functionField`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SchemeBridge.lean`, lines 49–55.

```lean
theorem abelianScheme_functionField
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := functionFieldAlgebra A.X.hom
    TauCeti.IsFunctionField ℚ A.X.left.functionField ∧
      IsIntegrallyClosedIn ℚ A.X.left.functionField
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelianScheme_identityPlace_degree`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SchemeBridge.lean`, lines 65–71.

```lean
theorem abelianScheme_identityPlace_degree
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := h.smooth
    letI := functionFieldAlgebra A.X.hom
    (smoothIdentityPlace A.X hdim).degree = 1
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

## `abelianScheme_projectiveWeierstrassModel`

Source: `ZInQKernel/Contrib/RC53Assist/AbelianCurve/SchemeBridge.lean`, lines 82–94.

```lean
theorem abelianScheme_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E
```

Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.

# Exact remaining proposition definitions

## `InvariantDifferentialTrivialization`

```lean
def InvariantDifferentialTrivialization : Prop :=
  ∀ (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left] [Smooth G.hom]
    [QuasiCompact G.hom], topologicalKrullDim G.left = 1 →
      Nonempty (differentialSheaf G.hom ≅ SheafOfModules.unit G.left.ringCatSheaf)
```

## `RegularDifferentialComparison`

```lean
def RegularDifferentialComparison : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f], topologicalKrullDim X = 1 →
      letI := functionFieldAlgebra f
      letI := globalSectionsModule f (differentialSheaf f)
      Nonempty (Γ(differentialSheaf f, ⊤) ≃ₗ[ℚ]
        ↥(TauCeti.weilDifferentialFiltration (0 : TauCeti.Divisor ℚ X.functionField)))
```

Locators, citation status, and precisely what remains are in `README.md`.
