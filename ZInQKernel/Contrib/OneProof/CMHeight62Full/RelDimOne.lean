import Mathlib
import ZInQKernel.HDecomp.Faltings.Models
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructureScheme

/-!
# Relative dimension one everywhere (node L0)

Let `L` be a number field and `f : X ⟶ Spec 𝓞_L` a smooth morphism with a section `e`. Suppose
that the fibre of `f` over the generic point is irreducible and that the local ring of `X` at
`e(η)` (`η` the generic point) is a discrete valuation ring. Then `f` is smooth of relative
dimension one at every point (`smoothOfRelativeDimension_one_of_genericFibre`).

The proof compares the relative dimension `d` of a standard smooth chart around any point with an
invariant of a single local ring: the rank of the Kähler differentials `Ω[𝒪_{X,y}⁄ℤ]` at a point
`y` of the chart lying over `η`.

* `finrank_kaehlerInt_eq`: for a standard smooth `RU → A` of relative dimension `d` and a
  localization `T = A_p` in which every element of `RU` has zero differential over `ℤ`,
  `Ω[T⁄ℤ]` has rank `d` (the map `Ω[T⁄ℤ] → Ω[T⁄RU]` is then an isomorphism).
* Over `η`, the local rings are algebras over the field `L`; elements of `𝓞_L` have zero
  differential over `ℤ` (their minimal polynomials are separable), and so do quotients of them.
  This gives `finrank_kaehler_stalk_of_chart`.
* `X` is irreducible: `f` is flat, so every point generizes into the generic fibre, which is
  irreducible. Every chart contains the generic point of `X`, so all charts have the same
  dimension. At `e(η)` the dimension is one by the generic-section computation of
  `exists_localModel_of_smooth` and `eq_one_of_genericSection_equiv`.

For a group model `𝒢` over `𝓞_L` (`GroupModel.smoothOfRelativeDimension_one`) the generic fibre
is the abelian variety `E_L`, geometrically integral, and the stalk at `e(η)` is `𝒢.genStalk`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing AlgebraicGeometry CategoryTheory NumberField

section KaehlerInt

/-- An element that is a simple root of an integer polynomial, with a unit derivative, has zero
differential over `ℤ`. -/
theorem kaehlerD_eq_zero_of_aeval {T : Type*} [CommRing T] (t : T) (p : Polynomial ℤ)
    (hp : Polynomial.aeval t p = 0)
    (hu : IsUnit (Polynomial.aeval t (Polynomial.derivative p))) :
    KaehlerDifferential.D ℤ T t = 0 := by
  have h := (KaehlerDifferential.D ℤ T).map_aeval p t
  rw [hp, map_zero] at h
  exact hu.smul_eq_zero.1 h.symm

/-- Every algebraic integer of a number field is a root of an integer polynomial whose derivative
does not vanish at it. -/
theorem exists_intPoly_aeval_derivative_ne_zero {L : Type*} [Field L] [NumberField L]
    (a : 𝓞 L) : ∃ p : Polynomial ℤ, Polynomial.aeval a p = 0 ∧
      Polynomial.aeval a (Polynomial.derivative p) ≠ 0 := by
  have hint : IsIntegral ℤ (algebraMap (𝓞 L) L a) := a.2
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := RingOfIntegers.coe_injective
  refine ⟨minpoly ℤ (algebraMap (𝓞 L) L a), ?_, ?_⟩
  · apply hinj
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply]
    exact minpoly.aeval ℤ _
  · intro h0
    have hsep : (minpoly ℚ (algebraMap (𝓞 L) L a)).Separable :=
      Algebra.IsSeparable.isSeparable ℚ _
    have hq := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    apply hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ (algebraMap (𝓞 L) L a))
    rw [hq, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_algebraMap_apply, h0, map_zero]

variable {L : Type*} [Field L] [NumberField L] {T : Type*} [CommRing T]

/-- If every nonzero algebraic integer becomes a unit in `T`, the image of `𝓞_L` in `T` has zero
differential over `ℤ`. -/
theorem kaehlerD_ringHom_eq_zero (κ : 𝓞 L →+* T) (hκ : ∀ c : 𝓞 L, c ≠ 0 → IsUnit (κ c))
    (a : 𝓞 L) : KaehlerDifferential.D ℤ T (κ a) = 0 := by
  obtain ⟨p, hp, hp'⟩ := exists_intPoly_aeval_derivative_ne_zero a
  have hκp : ∀ q : Polynomial ℤ, Polynomial.aeval (κ a) q = κ (Polynomial.aeval a q) :=
    fun q => Polynomial.aeval_algHom_apply κ.toIntAlgHom a q
  refine kaehlerD_eq_zero_of_aeval (κ a) p ?_ ?_
  · rw [hκp, hp, map_zero]
  · rw [hκp]
    exact hκ _ hp'

/-- A quotient `a / b` of algebraic integers (with `κ b * t = κ a`) has zero differential. -/
theorem kaehlerD_eq_zero_of_mul_eq (κ : 𝓞 L →+* T) (hκ : ∀ c : 𝓞 L, c ≠ 0 → IsUnit (κ c))
    (t : T) {a b : 𝓞 L} (hb : b ≠ 0) (h : κ b * t = κ a) :
    KaehlerDifferential.D ℤ T t = 0 := by
  have h1 := (KaehlerDifferential.D ℤ T).leibniz (κ b) t
  rw [h, kaehlerD_ringHom_eq_zero κ hκ a, kaehlerD_ringHom_eq_zero κ hκ b, smul_zero,
    add_zero] at h1
  exact (hκ b hb).smul_eq_zero.1 h1.symm

end KaehlerInt

section ChartRank

variable {RU A T : Type*} [CommRing RU] [CommRing A] [CommRing T] [Algebra RU A] [Algebra A T]
  [Algebra RU T] [IsScalarTower RU A T]

/-- If every element of `RU` has zero differential in `T` over `ℤ`, the base change map
`T ⊗ Ω[RU⁄ℤ] → Ω[T⁄ℤ]` vanishes. -/
theorem mapBaseChange_eq_zero_of_kaehlerD
    (hD : ∀ u : RU, KaehlerDifferential.D ℤ T (algebraMap RU T u) = 0)
    (y : TensorProduct RU T Ω[RU⁄ℤ]) : KaehlerDifferential.mapBaseChange ℤ RU T y = 0 := by
  have hmap : ∀ ω : Ω[RU⁄ℤ], KaehlerDifferential.map ℤ ℤ RU T ω = 0 := by
    intro ω
    have hω : ω ∈ Submodule.span RU (Set.range (KaehlerDifferential.D ℤ RU)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [KaehlerDifferential.map_D]
      exact hD u
    | zero => exact map_zero _
    | add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]
    | smul r x _ hx => rw [map_smul, hx, smul_zero]
  induction y using TensorProduct.inductionOn with
  | tmul b ω => rw [KaehlerDifferential.mapBaseChange_tmul, hmap, smul_zero]
  | add y z hy hz => rw [map_add, hy, hz, add_zero]

/-- **Chart rank.** Let `RU → A` be standard smooth of relative dimension `d` and `T` the
localization of `A` at a prime. If every element of `RU` has zero differential in `T` over `ℤ`,
then `Ω[T⁄ℤ]` has rank `d` over `T`. -/
theorem finrank_kaehlerInt_eq (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d RU A]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime T p]
    (hD : ∀ u : RU, KaehlerDifferential.D ℤ T (algebraMap RU T u) = 0) :
    Module.finrank T Ω[T⁄ℤ] = d := by
  have : Algebra.IsStandardSmooth RU A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : Nontrivial A := ⟨⟨0, 1, fun h =>
    ‹p.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ p.zero_mem (h.symm ▸ isUnit_one))⟩⟩
  have : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p
  have hrk := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := RU) (S := A) d
  have : Module.Finite A Ω[A⁄RU] := Module.rank_lt_aleph0_iff.1 (by
    rw [hrk]
    exact Cardinal.natCast_lt_aleph0)
  let b := Module.finBasisOfFinrankEq A Ω[A⁄RU] (Module.finrank_eq_of_rank_eq hrk)
  have := KaehlerDifferential.isLocalizedModule_map RU A T p.primeCompl
  let b' := Module.Basis.ofIsLocalizedModule T p.primeCompl
    (KaehlerDifferential.map RU RU A T) b
  have h1 : Module.finrank T Ω[T⁄RU] = d := by
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
  have hinj : Function.Injective (KaehlerDifferential.map ℤ RU T T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map ℤ RU T x).1 hx
    exact mapBaseChange_eq_zero_of_kaehlerD hD y
  let e := LinearEquiv.ofBijective _ ⟨hinj, KaehlerDifferential.map_surjective ℤ RU T⟩
  rw [e.finrank_eq, h1]

end ChartRank

section Scheme

variable {L : Type} [Field L] [NumberField L]

/-- The rank of `Ω[𝒪_{X,y}⁄ℤ]` at a point `y` over the generic point of `Spec 𝓞_L` equals the
relative dimension of any standard smooth chart containing `y`. -/
theorem finrank_kaehler_stalk_of_chart {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (𝓞 L)))
    {U : (Spec (CommRingCat.of (𝓞 L))).Opens} {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (d : ℕ)
    (hd : RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE U V e).hom) (y : X)
    (hy : y ∈ V) (hgen : f y = genericPoint (Spec (CommRingCat.of (𝓞 L)))) :
    Module.finrank (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄ℤ] = d := by
  let RU := Γ(Spec (CommRingCat.of (𝓞 L)), U)
  let A := Γ(X, V)
  let _ : Algebra RU A := (f.appLE U V e).hom.toAlgebra
  have hd' : Algebra.IsStandardSmoothOfRelativeDimension d RU A := hd
  let _ : Algebra A (X.presheaf.stalk y) := (X.presheaf.germ V y hy).hom.toAlgebra
  let _ : Algebra RU (X.presheaf.stalk y) :=
    ((X.presheaf.germ V y hy).hom.comp (f.appLE U V e).hom).toAlgebra
  have : IsScalarTower RU A (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let p := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have : IsLocalization.AtPrime (X.presheaf.stalk y) p := hV.isLocalization_stalk ⟨y, hy⟩
  refine finrank_kaehlerInt_eq (RU := RU) (A := A) d p fun u => ?_
  have hfy : f y ∈ U := e hy
  have hbot : (f y).asIdeal = ⊥ := by
    rw [hgen, genericPoint_eq_bot_of_affine]
    rfl
  let Ls := Localization.AtPrime (f y).asIdeal
  let κ : 𝓞 L →+* X.presheaf.stalk y := (f.stalkMap y).hom.comp
    ((specStalkEquiv (f y) : Ls →+* _).comp (algebraMap (𝓞 L) Ls))
  have hκ : ∀ c : 𝓞 L, c ≠ 0 → IsUnit (κ c) := by
    intro c hc
    have hc' : c ∈ (f y).asIdeal.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hbot]
      exact hc
    exact ((IsLocalization.map_units Ls (⟨c, hc'⟩ : (f y).asIdeal.primeCompl)).map
      (specStalkEquiv (f y) : Ls →+* _)).map (f.stalkMap y).hom
  obtain ⟨⟨a, b⟩, hz⟩ := IsLocalization.mk'_surjective (f y).asIdeal.primeCompl
    ((specStalkEquiv (f y)).symm
      (((Spec (CommRingCat.of (𝓞 L))).presheaf.germ U (f y) hfy).hom u))
  dsimp only at hz
  have hb : (b : 𝓞 L) ≠ 0 := fun h0 => b.2 (h0 ▸ (f y).asIdeal.zero_mem)
  have hspec := IsLocalization.mk'_spec Ls a b
  rw [hz] at hspec
  have halg : algebraMap RU (X.presheaf.stalk y) u = (f.stalkMap y).hom
      (((Spec (CommRingCat.of (𝓞 L))).presheaf.germ U (f y) hfy).hom u) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    change (X.presheaf.germ V y hy).hom ((f.appLE U V e).hom u) = _
    rw [Scheme.Hom.appLE]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  refine kaehlerD_eq_zero_of_mul_eq κ hκ _ (a := a) hb ?_
  rw [halg]
  have h2 := congrArg (fun z => (f.stalkMap y).hom (specStalkEquiv (f y) z)) hspec
  simp only [map_mul, RingEquiv.apply_symm_apply] at h2
  rw [mul_comm] at h2
  exact h2

/-- The rank of `Ω[𝒪_{X,e(η)}⁄ℤ]` is one when the stalk at `e(η)` is a discrete valuation ring. -/
theorem finrank_kaehler_stalk_section {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (𝓞 L)))
    [Smooth f] (e : Spec (CommRingCat.of (𝓞 L)) ⟶ X) (he : e ≫ f = 𝟙 _)
    [IsDomain (X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of (𝓞 L))))))]
    [IsDiscreteValuationRing
      (X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of (𝓞 L))))))] :
    Module.finrank (X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of (𝓞 L))))))
      Ω[X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of (𝓞 L)))))⁄ℤ] = 1 := by
  obtain ⟨P, hP0, hP⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField L)
  let s : Spec (CommRingCat.of (𝓞 L)) := ⟨P, hP⟩
  let Rs := Localization.AtPrime s.asIdeal
  have : IsDiscreteValuationRing Rs :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP0 Rs
  obtain ⟨n, A₀, _, _, hn, σ, φ, φη, -, -⟩ := exists_localModel_of_smooth f e he s
  obtain rfl := eq_one_of_genericSection_equiv σ n φη
  let T := X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of (𝓞 L)))))
  let B := Localization.AtPrime (RingHom.ker σ)
  let _ : Algebra A₀ T := ((φη : B →+* T).comp (algebraMap A₀ B)).toAlgebra
  let _ : Algebra Rs T := (((φη : B →+* T).comp (algebraMap A₀ B)).comp
    (algebraMap Rs A₀)).toAlgebra
  have : IsScalarTower Rs A₀ T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization.AtPrime T (RingHom.ker σ) :=
    IsLocalization.isLocalization_of_algEquiv (RingHom.ker σ).primeCompl
      (AlgEquiv.ofRingEquiv (f := φη) fun _ => rfl)
  refine finrank_kaehlerInt_eq (RU := Rs) (A := A₀) 1 (RingHom.ker σ) fun u => ?_
  have hunitRs : ∀ x : Rs, x ≠ 0 → IsUnit (algebraMap Rs T x) := by
    intro x hx
    have hx' : algebraMap Rs A₀ x ∈ (RingHom.ker σ).primeCompl := by
      rw [Ideal.mem_primeCompl_iff, RingHom.mem_ker, AlgHom.commutes]
      exact hx
    exact (IsLocalization.map_units B (⟨_, hx'⟩ : (RingHom.ker σ).primeCompl)).map
      (φη : B →+* T)
  have hinj : Function.Injective (algebraMap (𝓞 L) Rs) :=
    IsLocalization.injective Rs (Ideal.primeCompl_le_nonZeroDivisors s.asIdeal)
  let κ : 𝓞 L →+* T := (algebraMap Rs T).comp (algebraMap (𝓞 L) Rs)
  have hκ : ∀ c : 𝓞 L, c ≠ 0 → IsUnit (κ c) := fun c hc =>
    hunitRs _ fun h0 => hc (hinj (h0.trans (map_zero _).symm))
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective s.asIdeal.primeCompl u
  dsimp only
  have hb : (b : 𝓞 L) ≠ 0 := fun h0 => b.2 (h0 ▸ s.asIdeal.zero_mem)
  refine kaehlerD_eq_zero_of_mul_eq κ hκ _ (a := a) hb ?_
  have h2 := congrArg (algebraMap Rs T) (IsLocalization.mk'_spec Rs a b)
  rw [map_mul, mul_comm] at h2
  exact h2

/-- A flat scheme over `Spec R` (`R` a domain) whose generic fibre is irreducible is
irreducible: every point generizes into the generic fibre. -/
theorem irreducibleSpace_of_isIrreducible_genericFibre {X : Scheme} {R : CommRingCat}
    [IsDomain R] (f : X ⟶ Spec R) [Flat f]
    (hirr : IsIrreducible (f ⁻¹' {genericPoint (Spec R)})) : IrreducibleSpace X := by
  rw [irreducibleSpace_def]
  have hcl : closure (f ⁻¹' {genericPoint (Spec R)}) = ⊤ := by
    rw [Set.top_eq_univ, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hyx, hy⟩ := Flat.generalizingMap f (genericPoint_specializes (f x))
    have hy' : y ∈ f ⁻¹' {genericPoint (Spec R)} := hy
    exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hyx)
  rw [← hcl]
  exact hirr.closure

/-- **Node L0, Mathlib form.** Let `f : X ⟶ Spec 𝓞_L` be smooth with a section `e`. If the fibre
over the generic point `η` is irreducible and the stalk of `X` at `e(η)` is a discrete
valuation ring, then `f` is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_genericFibre {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of (𝓞 L))) [Smooth f] (e : Spec (CommRingCat.of (𝓞 L)) ⟶ X)
    (he : e ≫ f = 𝟙 _)
    (hirr : IsIrreducible (f ⁻¹' {genericPoint (Spec (CommRingCat.of (𝓞 L)))}))
    (η : Spec (CommRingCat.of (𝓞 L))) (hη : genericPoint (Spec (CommRingCat.of (𝓞 L))) = η)
    [IsDomain (X.presheaf.stalk (e η))] [IsDiscreteValuationRing (X.presheaf.stalk (e η))] :
    SmoothOfRelativeDimension 1 f := by
  subst hη
  have := irreducibleSpace_of_isIrreducible_genericFibre f hirr
  set η := genericPoint (Spec (CommRingCat.of (𝓞 L))) with hηdef
  have hfe : ∀ s, f (e s) = s := fun s => by rw [← Scheme.Hom.comp_apply, he]; rfl
  let θ := genericPoint X
  have hθ : f θ = η := by
    have h1 : f θ ⤳ f (e η) := (genericPoint_specializes (e η)).map f.continuous
    rw [hfe] at h1
    exact (h1.antisymm (genericPoint_specializes (f θ))).eq
  -- the rank at `θ` is one, through a chart at `e(η)`
  have hθ1 : Module.finrank (X.presheaf.stalk θ) Ω[X.presheaf.stalk θ⁄ℤ] = 1 := by
    obtain ⟨U, hU, V, hV, hxV, hVU, hss⟩ := Smooth.exists_isStandardSmooth f (e η)
    let _ : Algebra Γ(Spec (CommRingCat.of (𝓞 L)), U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    have hstd : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of (𝓞 L)), U) Γ(X, V) :=
      hss.toAlgebra
    obtain ⟨ι, κ, _, _, ⟨P⟩⟩ := hstd.out
    have hn : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V hVU).hom :=
      ⟨⟨ι, κ, ‹_›, ‹_›, P, rfl⟩⟩
    have hθV : θ ∈ V := (genericPoint_specializes (e η)).mem_open V.isOpen hxV
    rw [finrank_kaehler_stalk_of_chart f hV hVU _ hn θ hθV hθ,
      ← finrank_kaehler_stalk_of_chart f hV hVU _ hn (e η) hxV (hfe η)]
    exact finrank_kaehler_stalk_section f e he
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, hVU, hss⟩ := Smooth.exists_isStandardSmooth f x
  let _ : Algebra Γ(Spec (CommRingCat.of (𝓞 L)), U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have hstd : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of (𝓞 L)), U) Γ(X, V) :=
    hss.toAlgebra
  obtain ⟨ι, κ, _, _, ⟨P⟩⟩ := hstd.out
  have hn : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V hVU).hom :=
    ⟨⟨ι, κ, ‹_›, ‹_›, P, rfl⟩⟩
  have hθV : θ ∈ V := (genericPoint_specializes x).mem_open V.isOpen hxV
  have hd := finrank_kaehler_stalk_of_chart f hV hVU _ hn θ hθV hθ
  rw [hθ1] at hd
  rw [← hd] at hn
  exact ⟨U, hU, V, hV, hxV, hVU, hn⟩

end Scheme

section GroupModel

open ZInQ.DefFaltings MonObj

/-- A scheme over `Spec K` (`K` a field) whose structure morphism is geometrically integral is
integral. -/
theorem isIntegral_of_geometricallyIntegral {K : Type} [Field K]
    (Y : Over (Spec (CommRingCat.of K))) [GeometricallyIntegral Y.hom] : IsIntegral Y.left :=
  GeometricallyIntegral.geometrically_isIntegral (𝟙 _) (𝟙 _) Y.hom (IsPullback.of_id_fst)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- The fibre of a group model over the generic point of `Spec 𝓞_L` is irreducible: it is the
image of the generic fibre `E_L`. -/
theorem GroupModel.isIrreducible_genericFibre (𝒢 : GroupModel E L) :
    IsIrreducible (𝒢.G.hom ⁻¹' {genericPoint (Spec (CommRingCat.of (𝓞 L)))}) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  have hg : Set.range g = {genericPoint (Spec (CommRingCat.of (𝓞 L)))} := by
    have hpt : ∀ y : Spec (CommRingCat.of L), g y = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
      fun y => by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap (𝓞 L) L) y.asIdeal = (⊥ : Ideal (𝓞 L))
        rw [Ideal.eq_bot_of_prime y.asIdeal]
        exact (RingHom.ker_eq_bot_iff_eq_zero _).2 fun x hx =>
          RingOfIntegers.coe_injective (hx.trans (map_zero _).symm)
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact hpt y
    · intro hz
      exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L), (hpt _).trans hz.symm⟩
  have := isIntegral_of_geometricallyIntegral (E.baseChange L).X
  rw [← hg, ← Scheme.Pullback.range_fst]
  have hsurj : Function.Surjective
      (𝒢.gen.inv.left : (E.baseChange L).X.left ⟶ Limits.pullback 𝒢.G.hom g) :=
    Scheme.Hom.surjective _
  have : IrreducibleSpace ↥(Limits.pullback 𝒢.G.hom g) := by
    rw [irreducibleSpace_def]
    have h := (IrreducibleSpace.isIrreducible_univ (E.baseChange L).X.left).image _
      (𝒢.gen.inv.left : (E.baseChange L).X.left ⟶ Limits.pullback 𝒢.G.hom g).continuous.continuousOn
    rw [Set.image_univ_of_surjective hsurj] at h
    exact h
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- **Node L0.** A group model whose local ring at the identity of the generic fibre is a
discrete valuation ring is smooth of relative dimension one over `𝓞_L`. -/
theorem GroupModel.smoothOfRelativeDimension_one (𝒢 : GroupModel E L)
    [IsDomain 𝒢.genStalk] [IsDiscreteValuationRing 𝒢.genStalk] :
    SmoothOfRelativeDimension 1 𝒢.G.hom := by
  have he : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := Over.w (η[𝒢.G])
  have : IsDomain (𝒢.G.left.presheaf.stalk (𝒢.unitSection (genericPt L))) :=
    ‹IsDomain 𝒢.genStalk›
  have : IsDiscreteValuationRing (𝒢.G.left.presheaf.stalk (𝒢.unitSection (genericPt L))) :=
    ‹IsDiscreteValuationRing 𝒢.genStalk›
  exact smoothOfRelativeDimension_one_of_genericFibre 𝒢.G.hom 𝒢.unitSection he
    (GroupModel.isIrreducible_genericFibre 𝒢) (genericPt L) (genericPoint_eq_bot_of_affine _)

end GroupModel

end ZInQ.Contrib.CMHeight62Full
