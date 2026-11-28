import ZInQKernel.Contrib.OneProof.HeightModelM5.StalkOmega

/-!
# Differentials relative to the base ring and relative to the base stalks

For `f : X ⟶ Spec R`, the sheaf `Ω¹_{X/R} = relOmega f` is built relative to the base ring `R`,
while the textbook sheaf `Ω¹_{X/S}` is relative to `f⁻¹𝒪_S`. This file shows that the two agree on
stalks: the stalk of `Ω¹_{X/R}` at `x` is `Ω[𝒪_{X,x}⁄𝒪_{S,f(x)}]`.

* `kaehlerLocalizationEquiv`: for `R → R' → B` with `R'` a localization of `R`, the natural map
  `Ω[B⁄R] → Ω[B⁄R']` is an isomorphism. It is surjective, and its kernel is the image of
  `B ⊗ Ω[R'⁄R]`, which vanishes since a localization is formally unramified.
* `isLocalization_baseStalk`, `isScalarTower_baseStalk`: `𝒪_{S,f(x)}` is the localization of `R` at
  the prime `f(x)`, compatibly with `R → 𝒪_{X,x}` and `f^♯ : 𝒪_{S,f(x)} → 𝒪_{X,x}`.
* `stalkOmegaBaseEquiv`, `stalkOmegaBaseEquiv_germ_dSheaf`, `stalkOmegaBaseFormula`: the stalk of
  `Ω¹_{X/R}` at `x` is `Ω[𝒪_{X,x}⁄𝒪_{S,f(x)}]`, the germ of `d b` going to `d` of the germ of `b`.

Everything here uses Mathlib and the sheaf constructions of this directory only.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential
open scoped TensorProduct

set_option linter.style.haveILetI false

namespace ZInQ.HeightModelM5

namespace BS

section Localization

variable (R R' B : Type*) [CommRing R] [CommRing R'] [CommRing B] [Algebra R R'] [Algebra R' B]
  [Algebra R B] [IsScalarTower R R' B] (M : Submonoid R) [IsLocalization M R']

include M in
/-- **Differentials over a localization of the base**: `Ω[B⁄R] → Ω[B⁄R']` is bijective. -/
theorem kaehlerMap_bijective : Function.Bijective (KaehlerDifferential.map R R' B B) := by
  haveI := Algebra.FormallyUnramified.of_isLocalization (Rₘ := R') M
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, KaehlerDifferential.map_surjective R R' B⟩
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R' B x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

/-- `Ω[B⁄R] ≃ₗ[B] Ω[B⁄R']` for a localization `R'` of `R`. -/
noncomputable def kaehlerLocalizationEquiv : Ω[B⁄R] ≃ₗ[B] Ω[B⁄R'] :=
  LinearEquiv.ofBijective (KaehlerDifferential.map R R' B B) (kaehlerMap_bijective R R' B M)

theorem kaehlerLocalizationEquiv_D (b : B) :
    kaehlerLocalizationEquiv R R' B M (D R B b) = D R' B b :=
  KaehlerDifferential.map_D R R' B B b

end Localization

section Stalk

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X)

/-- The `R`-algebra structure on `𝒪_{S,f(x)}`, through `R ≅ Γ(S, 𝒪_S)`. -/
noncomputable abbrev algBase : Algebra R ((Spec R).presheaf.stalk (f x)) :=
  ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (f x) trivial).hom.toAlgebra

/-- The `𝒪_{S,f(x)}`-algebra structure on `𝒪_{X,x}`, through `f^♯`. -/
noncomputable abbrev algBaseStalk : Algebra ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- `𝒪_{S,f(x)}` is the localization of `R` at the prime `f(x)`. -/
theorem isLocalization_baseStalk :
    letI := algBase f x
    haveI : (f x).asIdeal.IsPrime := (f x).isPrime
    IsLocalization.AtPrime ((Spec R).presheaf.stalk (f x)) (f x).asIdeal := by
  letI := algBase f x
  haveI : (f x).asIdeal.IsPrime := (f x).isPrime
  exact StructureSheaf.IsLocalization.to_stalk R (f x)

/-- `R → 𝒪_{S,f(x)} → 𝒪_{X,x}` is the structure map `R → 𝒪_{X,x}`. -/
theorem isScalarTower_baseStalk :
    letI := stalkAlgebra f x
    letI := algBase f x
    letI := algBaseStalk f x
    IsScalarTower R ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  letI := stalkAlgebra f x
  letI := algBase f x
  letI := algBaseStalk f x
  exact IsScalarTower.of_algebraMap_eq fun r =>
    (Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial _).symm

/-- `Ω[𝒪_{X,x}⁄R] ≃ Ω[𝒪_{X,x}⁄𝒪_{S,f(x)}]`. -/
noncomputable def kaehlerBaseStalkEquiv :
    letI := stalkAlgebra f x
    letI := algBaseStalk f x
    Ω[X.presheaf.stalk x⁄R] ≃ₗ[X.presheaf.stalk x]
      Ω[X.presheaf.stalk x⁄(Spec R).presheaf.stalk (f x)] :=
  letI := stalkAlgebra f x
  letI := algBase f x
  letI := algBaseStalk f x
  haveI := isLocalization_baseStalk f x
  haveI := isScalarTower_baseStalk f x
  haveI : (f x).asIdeal.IsPrime := (f x).isPrime
  kaehlerLocalizationEquiv R ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x)
    (f x).asIdeal.primeCompl

theorem kaehlerBaseStalkEquiv_D (b : X.presheaf.stalk x) :
    letI := stalkAlgebra f x
    letI := algBaseStalk f x
    kaehlerBaseStalkEquiv f x (D R (X.presheaf.stalk x) b) =
      D ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) b := by
  letI := stalkAlgebra f x
  letI := algBase f x
  letI := algBaseStalk f x
  haveI := isLocalization_baseStalk f x
  haveI := isScalarTower_baseStalk f x
  haveI : (f x).asIdeal.IsPrime := (f x).isPrime
  exact kaehlerLocalizationEquiv_D R ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x)
    (f x).asIdeal.primeCompl b

/-- **The stalk of `Ω¹_{X/R}` relative to the base stalk**:
`(Ω¹_{X/R})_x ≃ Ω[𝒪_{X,x}⁄𝒪_{S,f(x)}]`. -/
noncomputable def stalkOmegaBaseEquiv :
    letI := algBaseStalk f x
    stalkOmega f x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄(Spec R).presheaf.stalk (f x)] :=
  letI := stalkAlgebra f x
  letI := algBaseStalk f x
  (stalkOmegaEquiv f x).trans (kaehlerBaseStalkEquiv f x)

/-- The germ of `d b` goes to `d` of the germ of `b`, over `𝒪_{S,f(x)}`. -/
theorem stalkOmegaBaseEquiv_germ_dSheaf (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)) :
    letI := algBaseStalk f x
    stalkOmegaBaseEquiv f x ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace)
        (relOmega f).val.presheaf U x hx).hom (dSheaf f U b)) =
      D ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom b) := by
  letI := stalkAlgebra f x
  letI := algBaseStalk f x
  exact (congrArg (kaehlerBaseStalkEquiv f x) (stalkOmegaEquiv_germ_dSheaf f x U hx b)).trans
    (kaehlerBaseStalkEquiv_D f x _)

/-- **The stalk formula relative to the base stalks**, in canonical form: for every `x`, an
`𝒪_{X,x}`-linear isomorphism `(Ω¹_{X/R})_x ≃ Ω[𝒪_{X,x}⁄𝒪_{S,f(x)}]`, for the algebra structure
`f^♯ : 𝒪_{S,f(x)} → 𝒪_{X,x}`, sending the germ of `d b` to `d` of the germ of `b`. -/
theorem stalkOmegaBaseFormula (x : X) :
    letI : Algebra ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    ∃ φ : stalkOmega f x ≃ₗ[X.presheaf.stalk x]
        Ω[X.presheaf.stalk x⁄(Spec R).presheaf.stalk (f x)],
      ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
        φ ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace)
            (relOmega f).val.presheaf U x hx).hom (dSheaf f U b)) =
          D ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom b) :=
  ⟨stalkOmegaBaseEquiv f x, stalkOmegaBaseEquiv_germ_dSheaf f x⟩

end Stalk

end BS

end ZInQ.HeightModelM5
