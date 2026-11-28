import Mathlib
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructure

/-!
# Local structure at the identity point: from schemes to algebra (node N5-bridge)

Let `R` be a domain, `f : X ⟶ Spec R` a smooth morphism and `e : Spec R ⟶ X` a section
(`e ≫ f = 𝟙`). Let `s` be a point of `Spec R` whose local ring `R_s` is a discrete valuation ring,
and let `η` be the generic point. We prove:

* `exists_localModel_of_smooth`: around `e(s)` there is an affine chart `Γ(U) → Γ(V)` that is
  standard smooth of some relative dimension `n`. Its base change `A₀ = R_s ⊗ Γ(V)` carries the
  section `σ : A₀ → R_s` induced by `e`. The localization of `A₀` at the section prime
  `σ⁻¹(𝔪)` is the stalk `𝒪_{X,e(s)}`, and the stalk map of `e` there is `localSection σ`. The
  localization of `A₀` at `ker σ` is the stalk at `e(η)`, compatibly with `stalkSpecializes`.
* `finrank_cotangentSpace_genericSection`: at `ker σ` the cotangent space has dimension `n`. The
  sequence `𝔪/𝔪² → κ ⊗ Ω → Ω[κ⁄R_s]` is exact and injective on the left, and the residue field
  `κ` is the fraction field of `R_s`.
* `exists_localModel`: if the stalk at `e(η)` (the local ring of the generic fibre at its
  identity) is a discrete valuation ring, then `n = 1`. This is the statement used by N5
  (`localStructure_of_standardSmooth`).

The statements use only Mathlib objects. A group model over `𝓞_L` (smooth, separated,
quasi-compact, with unit section `η[G].left` and `Over.w` for `e ≫ f = 𝟙`) instantiates them
directly, with `R = 𝓞_L` and the generic point `genericPoint_eq_bot_of_affine`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing

section ChartAlgebra

variable {RU : Type*} [CommRing RU] {A : Type*} [CommRing A] [Algebra RU A]
variable {Rs : Type*} [CommRing Rs] [Algebra RU Rs]

/-- The base change `Rs ⊗[RU] A` of a chart to the local ring. -/
abbrev chartBase (RU Rs A : Type*) [CommRing RU] [CommRing A] [Algebra RU A] [CommRing Rs]
    [Algebra RU Rs] : Type _ :=
  TensorProduct RU Rs A

/-- The `A`-algebra structure of `Rs ⊗[RU] A` (on the right factor). -/
abbrev chartBaseAlgebra : Algebra A (chartBase RU Rs A) :=
  Algebra.TensorProduct.rightAlgebra

/-- The section of the base-changed chart induced by `g : A → Rs`. -/
def chartSection (g : A →ₐ[RU] Rs) : chartBase RU Rs A →ₐ[Rs] Rs :=
  Algebra.TensorProduct.lift (AlgHom.id Rs Rs) g fun _ _ => Commute.all _ _

theorem chartSection_tmul (g : A →ₐ[RU] Rs) (x : Rs) (a : A) :
    chartSection g (x ⊗ₜ a) = x * g a := by
  simp [chartSection]

attribute [local instance] chartBaseAlgebra

theorem chartSection_algebraMap (g : A →ₐ[RU] Rs) (a : A) :
    chartSection g (algebraMap A (chartBase RU Rs A) a) = g a := by
  rw [Algebra.TensorProduct.right_algebraMap_apply, chartSection_tmul, one_mul]

theorem chartBase_isLocalization (q : Ideal RU) [q.IsPrime] [IsLocalization.AtPrime Rs q] :
    IsLocalization (Algebra.algebraMapSubmonoid A q.primeCompl) (chartBase RU Rs A) :=
  IsLocalization.tensorRight Rs q.primeCompl

/-- If a prime `P` of the base-changed chart lies over `p`, the localization of the chart at `P`
is the localization of `A` at `p`. -/
theorem exists_localizationEquiv_of_comap {T : Type*} [CommRing T] [Algebra A T]
    (q : Ideal RU) [q.IsPrime] [IsLocalization.AtPrime Rs q]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime T p]
    (P : Ideal (chartBase RU Rs A)) [P.IsPrime]
    (hP : P.comap (algebraMap A (chartBase RU Rs A)) = p) :
    ∃ φ : Localization.AtPrime P ≃+* T, ∀ a : A,
      φ (algebraMap (chartBase RU Rs A) (Localization.AtPrime P)
        (algebraMap A (chartBase RU Rs A) a)) = algebraMap A T a := by
  have := chartBase_isLocalization (A := A) (Rs := Rs) q
  have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A q.primeCompl) (Localization.AtPrime P) P
  subst hP
  let φ := IsLocalization.algEquiv (P.comap (algebraMap A (chartBase RU Rs A))).primeCompl
    (Localization.AtPrime P) T
  exact ⟨φ.toRingEquiv, fun a => φ.commutes a⟩

/-- The kernel of the section lies over the prime `p'` of a point whose local ring maps locally
to a field, compatibly with `g`. -/
theorem comap_ker_chartSection {T' : Type*} [CommRing T'] [IsLocalRing T'] [Algebra A T']
    (p' : Ideal A) [p'.IsPrime] [IsLocalization.AtPrime T' p'] {O' : Type*} [CommRing O']
    (hO : IsField O') (τ' : T' →+* O') [IsLocalHom τ'] (g : A →ₐ[RU] Rs)
    (hg : ∀ a, g a = 0 ↔ τ' (algebraMap A T' a) = 0) :
    (RingHom.ker (chartSection g)).comap (algebraMap A (chartBase RU Rs A)) = p' := by
  ext a
  have hp : a ∈ p' ↔ algebraMap A T' a ∈ maximalIdeal T' := by
    conv_lhs => rw [← IsLocalization.AtPrime.under_maximalIdeal T' p']
    rfl
  have hu : ∀ y : O', IsUnit y ↔ y ≠ 0 := fun y =>
    ⟨fun h => @IsUnit.ne_zero _ _ hO.nontrivial _ h, fun h =>
      let ⟨z, hz⟩ := hO.mul_inv_cancel h
      IsUnit.of_mul_eq_one z hz⟩
  rw [hp, Ideal.mem_comap, RingHom.mem_ker, chartSection_algebraMap, hg, mem_maximalIdeal,
    mem_nonunits_iff, ← isUnit_map_iff τ' (algebraMap A T' a), hu, not_not]

variable [IsDomain Rs] [IsDiscreteValuationRing Rs]
variable {T : Type*} [CommRing T] [IsLocalRing T] [Algebra A T]
variable {O : Type*} [CommRing O]
variable (τ : T →+* O) [IsLocalHom τ] (ψ : Rs →+* O) [IsLocalHom ψ]
variable (g : A →ₐ[RU] Rs) (hτ : ∀ a, τ (algebraMap A T a) = ψ (g a))

include hτ in
theorem comap_sectionPrime_chartSection (p : Ideal A) [p.IsPrime]
    [IsLocalization.AtPrime T p] :
    (sectionPrime (chartSection g)).comap (algebraMap A (chartBase RU Rs A)) = p := by
  ext a
  have hp : a ∈ p ↔ algebraMap A T a ∈ maximalIdeal T := by
    conv_lhs => rw [← IsLocalization.AtPrime.under_maximalIdeal T p]
    rfl
  rw [hp, Ideal.mem_comap, sectionPrime, Ideal.mem_comap, chartSection_algebraMap,
    mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    ← isUnit_map_iff τ (algebraMap A T a), hτ, isUnit_map_iff ψ]

include hτ in
/-- **Algebraic core.** If `T` is the localization of the chart ring `A` at `p`, `Rs` the
localization of `RU` at `q`, and the section `g : A → Rs` is compatible with a local map
`τ : T → O` and a local map `ψ : Rs → O`, then the localization of the base-changed chart at its
section prime is `T` (compatibly with `A`), and under this identification `τ` is
`ψ ∘ localSection`. -/
theorem exists_localizationEquiv (q : Ideal RU) [q.IsPrime] [IsLocalization.AtPrime Rs q]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime T p] :
    ∃ φ : Localization.AtPrime (sectionPrime (chartSection g)) ≃+* T,
      (∀ x, τ (φ x) = ψ (localSection (chartSection g) x)) ∧
      ∀ a : A, φ (algebraMap (chartBase RU Rs A) _ (algebraMap A (chartBase RU Rs A) a)) =
        algebraMap A T a := by
  set σ := chartSection g
  let L := Localization.AtPrime (sectionPrime σ)
  have := chartBase_isLocalization (A := A) (Rs := Rs) q
  have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A q.primeCompl) L (sectionPrime σ)
  have hc := comap_sectionPrime_chartSection τ ψ g hτ p
  subst hc
  let φ := IsLocalization.algEquiv
    ((sectionPrime σ).comap (algebraMap A (chartBase RU Rs A))).primeCompl L T
  refine ⟨φ.toRingEquiv, fun x => ?_, fun a => φ.commutes a⟩
  have hext : τ.comp (φ : L →+* T) = ψ.comp (localSection σ) := by
    refine IsLocalization.ringHom_ext
      ((sectionPrime σ).comap (algebraMap A (chartBase RU Rs A))).primeCompl
      (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    rw [hτ]
    change ψ (g a) = ψ (localSection σ (algebraMap (chartBase RU Rs A) L
      (algebraMap A (chartBase RU Rs A) a)))
    rw [localSection_algebraMap, chartSection_algebraMap]
  exact RingHom.congr_fun hext x

end ChartAlgebra

section Cotangent

variable {K₀ : Type*} [CommRing K₀] {B : Type*} [CommRing B] [IsLocalRing B] [Algebra K₀ B]

/-- For a formally smooth local `K₀`-algebra `B` whose residue field is formally smooth and
formally unramified over `K₀` (for instance a localization of `K₀`), the cotangent space
`𝔪/𝔪²` has the dimension of `Ω[B⁄K₀]`. -/
theorem finrank_cotangentSpace_eq_of_basis [Algebra.FormallySmooth K₀ B]
    [Algebra.FormallySmooth K₀ (ResidueField B)] [Subsingleton Ω[ResidueField B⁄K₀]]
    {n : ℕ} (b : Module.Basis (Fin n) B Ω[B⁄K₀]) :
    Module.finrank (ResidueField B) (CotangentSpace B) = n := by
  have hsurj : Function.Surjective (algebraMap B (ResidueField B)) :=
    Ideal.Quotient.mk_surjective
  let φ := KaehlerDifferential.kerCotangentToTensor K₀ B (ResidueField B)
  have hinj : Function.Injective φ :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj).2 inferInstance
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange K₀ B
    (ResidueField B) hsurj
  have hsur : Function.Surjective φ := fun y => (hex y).1 (Subsingleton.elim _ _)
  let e₁ := LinearEquiv.ofBijective φ ⟨hinj, hsur⟩
  have hker : RingHom.ker (algebraMap B (ResidueField B)) = maximalIdeal B :=
    Ideal.mk_ker
  let e₂' : (maximalIdeal B).Cotangent ≃ₗ[B] TensorProduct B (ResidueField B) Ω[B⁄K₀] :=
    hker ▸ e₁
  let e₂ : CotangentSpace B ≃ₗ[B] TensorProduct B (ResidueField B) Ω[B⁄K₀] := e₂'
  let e₃ := e₂.extendScalarsOfSurjective hsurj
  have : Module.Free B Ω[B⁄K₀] := Module.Free.of_basis b
  rw [e₃.finrank_eq, Module.finrank_baseChange, Module.finrank_eq_card_basis b,
    Fintype.card_fin]

end Cotangent

section GenericSection

variable {Rs : Type*} [CommRing Rs] [IsDomain Rs] {A₀ : Type*} [CommRing A₀] [Algebra Rs A₀]
variable (σ : A₀ →ₐ[Rs] Rs)

instance isPrime_ker_sectionAlgHom : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ

/-- The local ring of the base-changed chart at the generic point of the section. -/
abbrev genericSectionLocal : Type _ := Localization.AtPrime (RingHom.ker σ)

theorem residue_algebraMap_genericSection (a : A₀) :
    residue (genericSectionLocal σ) (algebraMap A₀ (genericSectionLocal σ) a) =
      algebraMap Rs (ResidueField (genericSectionLocal σ)) (σ a) := by
  have h1 : algebraMap Rs (ResidueField (genericSectionLocal σ)) (σ a) =
      residue _ (algebraMap A₀ (genericSectionLocal σ) (algebraMap Rs A₀ (σ a))) := by
    rw [← IsScalarTower.algebraMap_apply Rs A₀ (genericSectionLocal σ),
      ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h1, ← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker σ)]
  simp

theorem isUnit_algebraMap_genericSection {r : Rs} (hr : r ≠ 0) :
    IsUnit (algebraMap Rs (ResidueField (genericSectionLocal σ)) r) := by
  have h : algebraMap Rs A₀ r ∈ (RingHom.ker σ).primeCompl := by
    simpa [Ideal.mem_primeCompl_iff, RingHom.mem_ker] using hr
  have hu := IsLocalization.map_units (genericSectionLocal σ) (⟨_, h⟩ : (RingHom.ker σ).primeCompl)
  rw [IsScalarTower.algebraMap_apply Rs (genericSectionLocal σ)]
  exact hu.map _

/-- The residue field at the generic point of the section is the fraction field of `Rs`. -/
theorem isFractionRing_residueField_genericSection :
    IsFractionRing Rs (ResidueField (genericSectionLocal σ)) := by
  refine ⟨fun y => isUnit_algebraMap_genericSection σ (nonZeroDivisors.ne_zero y.2),
    fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · obtain ⟨b, rfl⟩ := residue_surjective z
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker σ).primeCompl b
    have hu : σ u ≠ 0 := fun h0 => u.2 (RingHom.mem_ker.2 h0)
    refine ⟨⟨σ a, ⟨σ u, mem_nonZeroDivisors_of_ne_zero hu⟩⟩, ?_⟩
    simp only
    rw [← residue_algebraMap_genericSection, ← residue_algebraMap_genericSection, ← map_mul,
      IsLocalization.mk'_spec]
  · by_contra hne
    have hxy : x - y ≠ 0 := sub_ne_zero.2 fun h' => hne (by rw [h'])
    have := (isUnit_algebraMap_genericSection σ hxy).ne_zero
    rw [map_sub, h, sub_self] at this
    exact this rfl

/-- At the generic point of the section of a standard smooth algebra of relative dimension `n`,
the cotangent space has dimension `n`. -/
theorem finrank_cotangentSpace_genericSection (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n Rs A₀] :
    Module.finrank (ResidueField (genericSectionLocal σ))
      (CotangentSpace (genericSectionLocal σ)) = n := by
  have : Algebra.IsStandardSmooth Rs A₀ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nontrivial A₀ := σ.toRingHom.domain_nontrivial
  have hrk := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Rs) (S := A₀) n
  have : Module.Finite A₀ Ω[A₀⁄Rs] := Module.rank_lt_aleph0_iff.1 (by
    rw [hrk]
    exact Cardinal.natCast_lt_aleph0)
  let b := Module.finBasisOfFinrankEq A₀ Ω[A₀⁄Rs] (Module.finrank_eq_of_rank_eq hrk)
  have := KaehlerDifferential.isLocalizedModule_map Rs A₀ (genericSectionLocal σ)
    (RingHom.ker σ).primeCompl
  let b' := Module.Basis.ofIsLocalizedModule (genericSectionLocal σ) (RingHom.ker σ).primeCompl
    (KaehlerDifferential.map Rs Rs A₀ (genericSectionLocal σ)) b
  have : Algebra.FormallySmooth A₀ (genericSectionLocal σ) :=
    Algebra.FormallySmooth.of_isLocalization (RingHom.ker σ).primeCompl
  have : Algebra.FormallySmooth Rs (genericSectionLocal σ) :=
    Algebra.FormallySmooth.comp Rs A₀ (genericSectionLocal σ)
  have := isFractionRing_residueField_genericSection σ
  have : Algebra.FormallySmooth Rs (ResidueField (genericSectionLocal σ)) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors Rs)
  have : Algebra.FormallyUnramified Rs (ResidueField (genericSectionLocal σ)) :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors Rs)
  exact finrank_cotangentSpace_eq_of_basis b'

/-- If the local ring at the generic point of the section is a discrete valuation ring, the
relative dimension is one. -/
theorem eq_one_of_genericSection_equiv (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n Rs A₀] {D : Type*} [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] (φ : genericSectionLocal σ ≃+* D) : n = 1 := by
  have : IsDomain (genericSectionLocal σ) := MulEquiv.isDomain D φ.toMulEquiv
  have : IsDiscreteValuationRing (genericSectionLocal σ) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing φ.symm
  rw [← finrank_cotangentSpace_genericSection σ n]
  exact IsLocalRing.finrank_CotangentSpace_eq_one _

end GenericSection

section Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {R : Type} [CommRing R]

/-- A point of `Spec R` is a prime ideal of `R`. -/
instance isPrime_asIdeal_specPoint (s : Spec (CommRingCat.of R)) : s.asIdeal.IsPrime :=
  PrimeSpectrum.isPrime s

/-- Mathlib's identification of the localization `R_s` with the stalk of `Spec R` at `s`. -/
def specStalkEquiv (s : Spec (CommRingCat.of R)) :
    Localization.AtPrime s.asIdeal ≃+* (Spec (CommRingCat.of R)).presheaf.stalk s :=
  (Spec.stalkIso (CommRingCat.of R) s).commRingCatIsoToRingEquiv.symm

theorem germ_appLE_of_eq_id {Y : Scheme} (h : Y ⟶ Y) (hh : h = 𝟙 Y) (U W : Y.Opens)
    (hle : W ≤ h ⁻¹ᵁ U) (x : Y) (hxW : x ∈ W) (hxU : x ∈ U) (r : Γ(Y, U)) :
    Y.presheaf.germ W x hxW (h.appLE U W hle r) = Y.presheaf.germ U x hxU r := by
  subst hh
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

instance isLocalHom_ringEquiv_toRingHom {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂]
    (ψ : S₁ ≃+* S₂) : IsLocalHom (ψ : S₁ →+* S₂) :=
  ⟨fun a ha => by simpa using ha.map (ψ.symm : S₂ →+* S₁)⟩

attribute [local instance] chartBaseAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (e : Spec (CommRingCat.of R) ⟶ X)

/-- **Chart at `e(s)`, any relative dimension.** For a smooth `f : X ⟶ Spec R` with a section
`e` and a point `s` with `R_s` a discrete valuation ring, there is a standard smooth `R_s`-algebra
`A₀` of some relative dimension `n` with a section `σ`, such that the localization of `A₀` at the
section prime is the stalk `𝒪_{X,e(s)}`, the stalk map of `e` becoming `localSection σ`, and the
localization of `A₀` at `ker σ` is the stalk at `e(η)`, `η` the generic point. -/
theorem exists_localModel_of_smooth [IsDomain R] [Smooth f] (he : e ≫ f = 𝟙 _)
    (s : Spec (CommRingCat.of R)) [IsDomain (Localization.AtPrime s.asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)] :
    ∃ (n : ℕ) (A₀ : Type) (_ : CommRing A₀) (_ : Algebra (Localization.AtPrime s.asIdeal) A₀),
      Algebra.IsStandardSmoothOfRelativeDimension n (Localization.AtPrime s.asIdeal) A₀ ∧
      ∃ σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal,
      ∃ (φ : Localization.AtPrime (sectionPrime σ) ≃+* X.presheaf.stalk (e s))
        (φη : Localization.AtPrime (RingHom.ker σ) ≃+*
          X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of R))))),
        (∀ a, (e.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a)) ∧
        ∀ (h : e (genericPoint (Spec (CommRingCat.of R))) ⤳ e s) (x : A₀),
          (X.presheaf.stalkSpecializes h).hom (φ (algebraMap A₀ _ x)) =
            φη (algebraMap A₀ _ x) := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hss⟩ := Smooth.exists_isStandardSmooth f (e s)
  have hsU : s ∈ U := by
    have h := hVU hxV
    have hfe : f (e s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
    rw [Scheme.Hom.mem_preimage, hfe] at h
    exact h
  let RU := Γ(Spec (CommRingCat.of R), U)
  let A := Γ(X, V)
  let _ : Algebra RU A := (f.appLE U V hVU).hom.toAlgebra
  have hstd : Algebra.IsStandardSmooth RU A := hss.toAlgebra
  obtain ⟨ι, κ, _, _, ⟨P⟩⟩ := hstd.out
  have hn : Algebra.IsStandardSmoothOfRelativeDimension P.dimension RU A :=
    ⟨⟨ι, κ, ‹_›, ‹_›, P, rfl⟩⟩
  let Rs := Localization.AtPrime s.asIdeal
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = specStalkEquiv s := ⟨_, rfl⟩
  let _ : Algebra RU Rs := (ψ.symm.toRingHom.comp
    ((Spec (CommRingCat.of R)).presheaf.germ U s hsU).hom).toAlgebra
  let q := (hU.primeIdealOf ⟨s, hsU⟩).asIdeal
  let _ : Algebra RU ((Spec (CommRingCat.of R)).presheaf.stalk s) :=
    ((Spec (CommRingCat.of R)).presheaf.germ U s hsU).hom.toAlgebra
  have hq : IsLocalization.AtPrime Rs q := by
    have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk s) q :=
      hU.isLocalization_stalk ⟨s, hsU⟩
    exact IsLocalization.isLocalization_of_algEquiv _
      (AlgEquiv.ofRingEquiv (f := ψ.symm) (fun _ => rfl))
  have hsV : s ∈ e ⁻¹ᵁ V := hxV
  let g : A →ₐ[RU] Rs :=
    { toRingHom := ψ.symm.toRingHom.comp
        (((Spec (CommRingCat.of R)).presheaf.germ (e ⁻¹ᵁ V) s hsV).hom.comp (e.app V).hom)
      commutes' := fun r => by
        have h1 := congrArg (fun φ => φ.hom r)
          (Scheme.Hom.appLE_comp_appLE e f U V (e ⁻¹ᵁ V) hVU le_rfl)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
        rw [← Scheme.Hom.app_eq_appLE] at h1
        change ψ.symm (((Spec (CommRingCat.of R)).presheaf.germ (e ⁻¹ᵁ V) s hsV).hom
          ((e.app V).hom ((f.appLE U V hVU).hom r))) =
            ψ.symm (((Spec (CommRingCat.of R)).presheaf.germ U s hsU).hom r)
        rw [h1]
        exact congrArg ψ.symm (germ_appLE_of_eq_id _ he _ _ _ _ _ _ _) }
  let p := (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal
  let _ : Algebra A (X.presheaf.stalk (e s)) := (X.presheaf.germ V (e s) hxV).hom.toAlgebra
  have hp : IsLocalization.AtPrime (X.presheaf.stalk (e s)) p :=
    hV.isLocalization_stalk ⟨e s, hxV⟩
  have hτ : ∀ a : A, (e.stalkMap s).hom (algebraMap A (X.presheaf.stalk (e s)) a) =
      (ψ : Rs →+* _) (g a) := by
    intro a
    change (e.stalkMap s).hom ((X.presheaf.germ V (e s) hxV).hom a) =
      ψ (ψ.symm (((Spec (CommRingCat.of R)).presheaf.germ (e ⁻¹ᵁ V) s hsV).hom
        ((e.app V).hom a)))
    rw [RingEquiv.apply_symm_apply]
    exact Scheme.Hom.germ_stalkMap_apply e V s hxV a
  obtain ⟨φ, hφ, hφA⟩ := exists_localizationEquiv (e.stalkMap s).hom (ψ : Rs →+* _) g hτ q p
  let η := genericPoint (Spec (CommRingCat.of R))
  have hηV : η ∈ e ⁻¹ᵁ V := (genericPoint_specializes s).mem_open (e ⁻¹ᵁ V).isOpen hsV
  have hξV : e η ∈ V := hηV
  let p' := (hV.primeIdealOf ⟨e η, hξV⟩).asIdeal
  let _ : Algebra A (X.presheaf.stalk (e η)) := (X.presheaf.germ V (e η) hξV).hom.toAlgebra
  have hp' : IsLocalization.AtPrime (X.presheaf.stalk (e η)) p' :=
    hV.isLocalization_stalk ⟨e η, hξV⟩
  have hO : IsField ((Spec (CommRingCat.of R)).presheaf.stalk η) :=
    Field.toIsField (Spec (CommRingCat.of R)).functionField
  have hg : ∀ a, g a = 0 ↔
      (e.stalkMap η).hom (algebraMap A (X.presheaf.stalk (e η)) a) = 0 := by
    intro a
    change ψ.symm (((Spec (CommRingCat.of R)).presheaf.germ (e ⁻¹ᵁ V) s hsV).hom
        ((e.app V).hom a)) = 0 ↔ (e.stalkMap η).hom ((X.presheaf.germ V (e η) hξV).hom a) = 0
    rw [Scheme.Hom.germ_stalkMap_apply e V η hξV a, map_eq_zero_iff _ ψ.symm.injective,
      map_eq_zero_iff _ (germ_injective_of_isIntegral _ s hsV),
      map_eq_zero_iff _ (germ_injective_of_isIntegral _ η hηV)]
  have hc := comap_ker_chartSection p' hO (e.stalkMap η).hom g hg
  obtain ⟨φη, hφηA⟩ := exists_localizationEquiv_of_comap
    (T := X.presheaf.stalk (e η)) q p' _ hc
  have hspec : ∀ (h : e η ⤳ e s) (x : chartBase RU Rs A),
      (X.presheaf.stalkSpecializes h).hom (φ (algebraMap (chartBase RU Rs A) _ x)) =
        φη (algebraMap (chartBase RU Rs A) _ x) := by
    intro h x
    have := chartBase_isLocalization (A := A) (Rs := Rs) q
    have hext : (X.presheaf.stalkSpecializes h).hom.comp ((φ : _ →+* _).comp
        (algebraMap (chartBase RU Rs A) (Localization.AtPrime (sectionPrime (chartSection g))))) =
        (φη : _ →+* _).comp (algebraMap (chartBase RU Rs A)
          (Localization.AtPrime (RingHom.ker (chartSection g)))) := by
      refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A q.primeCompl)
        (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hφA, hφηA]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    exact RingHom.congr_fun hext x
  subst hψ
  exact ⟨P.dimension, chartBase RU Rs A, inferInstance, inferInstance,
    Algebra.IsStandardSmoothOfRelativeDimension.baseChange _ _, chartSection g, φ, φη, hφ,
    hspec⟩

/-- **Node N5-bridge.** For a smooth `f : X ⟶ Spec R` over a domain with a section `e` whose
local ring at `e(η)` (`η` the generic point, so `e(η)` is the identity of the generic fibre) is a
discrete valuation ring (`η` given as any point equal to the generic point), and a point `s`
with `R_s` a discrete valuation ring: around `e(s)`
there is a standard smooth affine chart of relative dimension one over `R_s` with a section `σ`,
the stalk `𝒪_{X,e(s)}` is its localization at the section prime, and the stalk map of `e` is
`localSection σ` (through Mathlib's `R_s ≅ 𝒪_{Spec R,s}`). -/
theorem exists_localModel [IsDomain R] [Smooth f] (he : e ≫ f = 𝟙 _)
    (s : Spec (CommRingCat.of R)) [IsDomain (Localization.AtPrime s.asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)] (η : Spec (CommRingCat.of R))
    (hη : genericPoint (Spec (CommRingCat.of R)) = η) [IsDomain (X.presheaf.stalk (e η))]
    [IsDiscreteValuationRing (X.presheaf.stalk (e η))] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra (Localization.AtPrime s.asIdeal) A₀),
      Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀ ∧
      ∃ (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
        (φ : Localization.AtPrime (sectionPrime σ) ≃+* X.presheaf.stalk (e s)),
        ∀ a, (e.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a) := by
  subst hη
  obtain ⟨n, A₀, _, _, hn, σ, φ, φη, hφ, -⟩ := exists_localModel_of_smooth f e he s
  obtain rfl := eq_one_of_genericSection_equiv σ n φη
  exact ⟨A₀, inferInstance, inferInstance, hn, σ, φ, hφ⟩

/-- `exists_localModel` together with the generic point of the section: the localization of the
chart at `ker σ` is the stalk at `e(η)`, compatibly with `stalkSpecializes`. -/
theorem exists_localModel_generic [IsDomain R] [Smooth f] (he : e ≫ f = 𝟙 _)
    (s : Spec (CommRingCat.of R)) [IsDomain (Localization.AtPrime s.asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    [IsDomain (X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of R)))))]
    [IsDiscreteValuationRing (X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of R)))))] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra (Localization.AtPrime s.asIdeal) A₀),
      Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀ ∧
      ∃ (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
        (φ : Localization.AtPrime (sectionPrime σ) ≃+* X.presheaf.stalk (e s))
        (φη : Localization.AtPrime (RingHom.ker σ) ≃+*
          X.presheaf.stalk (e (genericPoint (Spec (CommRingCat.of R))))),
        (∀ a, (e.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a)) ∧
        ∀ (h : e (genericPoint (Spec (CommRingCat.of R))) ⤳ e s) (x : A₀),
          (X.presheaf.stalkSpecializes h).hom (φ (algebraMap A₀ _ x)) =
            φη (algebraMap A₀ _ x) := by
  obtain ⟨n, A₀, _, _, hn, σ, φ, φη, hφ, hsp⟩ := exists_localModel_of_smooth f e he s
  obtain rfl := eq_one_of_genericSection_equiv σ n φη
  exact ⟨A₀, inferInstance, inferInstance, hn, σ, φ, φη, hφ, hsp⟩

end Scheme

end ZInQ.Contrib.CMHeight62Full
