import Mathlib

/-!
# Local structure at the closed identity point (algebra form)

Let `R` be a discrete valuation ring with uniformizer `ϖ`, let `A` be a formally smooth
`R`-algebra whose module of Kähler differentials is free of rank one, and let `σ : A →ₐ[R] R`
be a section (an `R`-point). Write `I = ker σ` and `𝔭 = σ⁻¹(𝔪_R)` (the closed point of the
section), and `A_𝔭` for the localization. We prove:

* `exists_param`: there is `t ∈ I` with `σ (dt) = 1` for the coordinate of the basis of `Ω`;
* `cotangentBasis`: the conormal module `I/I²` is a free `R`-module of rank one with basis the
  class of `t`;
* `maximalIdeal_eq_span`: `𝔪_{A_𝔭} = (ϖ, t)`;
* `ker_localSection_eq_span`: the kernel of the localized section `A_𝔭 → R` is `(t)`;
* `ringKrullDim_eq_two` and `isRegularLocalRing`: `A_𝔭` is a regular local ring of dimension
  two.

`localStructure` bundles these under the hypotheses `Module.Free A Ω[A⁄R]` and
`Module.rank A Ω[A⁄R] = 1`; `localStructure_of_standardSmooth` derives them from
`Algebra.IsStandardSmoothOfRelativeDimension 1 R A`.

The lower bound on the dimension is the main point. A local derivation `D` with `D t = 1`
gives an `R`-algebra map `A → R[X]/(X²)` sending `t` to `X`; formal smoothness lifts it to
`A → R[X]/(X^(n+1))` for every `n`, and this shows that `s tⁿ ≠ 0` for every `s ∉ I`. Hence `I`
is not a minimal prime, so `ht 𝔭 ≥ ht I + 1 ≥ 2`. Krull's height theorem gives `≤ 2`.

## The scheme-to-algebra step

This is node N5 of the blueprint in algebra form. For `f : X ⟶ Spec R` with
`SmoothOfRelativeDimension 1 f` and a section `e`, the remaining step is as follows. Let `s` be
the closed point. The class gives affine opens `U ∋ s` of `Spec R` and `V ∋ e(s)` of `X` with
`V ≤ f⁻¹ U` and `Γ(U) → Γ(V)` standard smooth of relative dimension one. An open of `Spec R`
containing `s` is all of `Spec R`, so `Γ(U) = R`; `e⁻¹ V` is likewise all of `Spec R`, so `e`
restricts to an `R`-algebra map `σ : A = Γ(V) → R`. The stalk `𝒪_{X,e(s)}` is the localization
of `A` at `𝔭 = σ⁻¹(𝔪_R)` (`IsAffineOpen.isLocalization_stalk`), and the stalk map of `e` is the
localized section `localSection σ`. Apply `localStructure_of_standardSmooth`.

For a model that is only known to be `Smooth`, relative dimension one at `e(s)` must be supplied
separately (from the generic fibre being a curve: for a smooth morphism the relative dimension
is locally constant, and `Spec` of a discrete valuation ring is connected). Over a Dedekind base
`Spec 𝓞` one first base changes to the local ring at `s`, a discrete valuation ring.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing Polynomial

section Derivation

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
variable (σ : A →ₐ[R] R) (b : Module.Basis (Fin 1) A Ω[A⁄R])

theorem ker_isPrime [IsDomain R] : (RingHom.ker σ).IsPrime :=
  RingHom.ker_isPrime σ.toRingHom

/-- The `R`-valued derivation along the section `σ`: `a ↦ σ (coordinate of da)`. -/
def secDer (a : A) : R :=
  σ (b.repr (KaehlerDifferential.D R A a) 0)

theorem secDer_add (x y : A) : secDer σ b (x + y) = secDer σ b x + secDer σ b y := by
  simp [secDer]

theorem secDer_sub (x y : A) : secDer σ b (x - y) = secDer σ b x - secDer σ b y := by
  simp [secDer]

theorem secDer_mul (x y : A) :
    secDer σ b (x * y) = σ x * secDer σ b y + σ y * secDer σ b x := by
  simp [secDer, Derivation.leibniz]

theorem secDer_algebraMap (r : R) : secDer σ b (algebraMap R A r) = 0 := by
  simp [secDer]

theorem secDer_zero : secDer σ b 0 = 0 := by
  simp [secDer]

theorem secDer_one : secDer σ b 1 = 0 := by
  simp [secDer]

theorem secDer_eq_zero_of_mem_sq {x : A} (hx : x ∈ RingHom.ker σ ^ 2) : secDer σ b x = 0 := by
  rw [sq] at hx
  refine Submodule.mul_induction_on hx (fun i hi j hj => ?_) (fun x y hx hy => ?_)
  · rw [secDer_mul, RingHom.mem_ker.1 hi, RingHom.mem_ker.1 hj]
    ring
  · rw [secDer_add, hx, hy, add_zero]

/-- Key estimate: if `σ t = 0` and `D t = 1`, then `s * t ^ n ≠ 0` whenever `σ s ≠ 0`. -/
theorem mul_pow_ne_zero_of_secDer [Algebra.FormallySmooth R A] {t : A} (ht : σ t = 0)
    (hDt : secDer σ b t = 1) {s : A} (hs : σ s ≠ 0) (n : ℕ) : s * t ^ n ≠ 0 := by
  intro h0
  let B := R[X] ⧸ Ideal.span {(X : R[X]) ^ (n + 1)}
  let x : B := Ideal.Quotient.mk _ X
  have hx : x ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let J : Ideal B := Ideal.span {x ^ 2}
  have hJ : IsNilpotent J := by
    refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_pow, ← pow_mul, mul_comm, pow_mul, hx,
      zero_pow two_ne_zero, Ideal.span_singleton_eq_bot]
  let δ : A → B := fun a => algebraMap R B (σ a) + algebraMap R B (secDer σ b a) * x
  have hδmul : ∀ a c, δ (a * c) - δ a * δ c ∈ J := by
    intro a c
    refine Ideal.mem_span_singleton'.2
      ⟨-(algebraMap R B (secDer σ b a) * algebraMap R B (secDer σ b c)), ?_⟩
    simp only [δ, secDer_mul, map_mul, map_add]
    ring
  let g : A →ₐ[R] B ⧸ J :=
    { toFun := fun a => Ideal.Quotient.mk J (δ a)
      map_one' := by simp [δ, secDer_one]
      map_mul' := fun a c => by
        rw [← (Ideal.Quotient.mk J).map_mul]
        exact Ideal.Quotient.eq.2 (hδmul a c)
      map_zero' := by simp [δ, secDer_zero]
      map_add' := fun a c => by
        rw [← (Ideal.Quotient.mk J).map_add]
        congr 1
        simp only [δ, map_add, secDer_add]
        ring
      commutes' := fun r => by simp [δ, secDer_algebraMap] }
  let ψ := Algebra.FormallySmooth.lift J hJ g
  have key : ∀ a, ψ a - δ a ∈ J := fun a =>
    Ideal.Quotient.eq.1 (Algebra.FormallySmooth.mk_lift J hJ g a)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (key t)
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (key s)
  simp only [δ, ht, hDt, map_zero, map_one] at hc
  have htt : ψ t = x * (1 + c * x) := by linear_combination -hc
  have hss : ψ s = algebraMap R B (σ s) + x * (algebraMap R B (secDer σ b s) + c' * x) := by
    linear_combination -hc'
  have hψ : ψ (s * t ^ n) = 0 := by rw [h0, map_zero]
  rw [map_mul, map_pow, htt, hss, mul_pow] at hψ
  obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow (1 + c * x) 1 n
  set r := algebraMap R B (σ s)
  set d := algebraMap R B (secDer σ b s) + c' * x
  have hrx : r * x ^ n = 0 := by
    linear_combination hψ - r * x ^ n * he - (r * c * e + d * (1 + c * x) ^ n) * hx
  have hmk : Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ (n + 1)}) (C (σ s) * X ^ n) = 0 := by
    rw [map_mul, map_pow]
    exact hrx
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
  obtain ⟨q, hq⟩ := hmk
  have hcoeff := congrArg (fun p : R[X] => p.coeff n) hq
  simp [coeff_X_pow_mul'] at hcoeff
  exact hs hcoeff

/-- With such a `t`, the kernel of `σ` is not a minimal prime of `A`. -/
theorem ker_notMem_minimalPrimes [IsDomain R] [Algebra.FormallySmooth R A] {t : A}
    (ht : σ t = 0) (hDt : secDer σ b t = 1) : RingHom.ker σ ∉ minimalPrimes A := by
  intro hmin
  have := ker_isPrime σ
  let p := RingHom.ker σ
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (Localization.AtPrime p) p ⊥ hmin
  have htmem : algebraMap A (Localization.AtPrime p) t ∈ ((⊥ : Ideal A).map
      (algebraMap A (Localization.AtPrime p))).radical :=
    hrad ▸ Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 ht)
  rw [Ideal.map_bot] at htmem
  obtain ⟨n, hn⟩ := htmem
  rw [Ideal.mem_bot, ← map_pow, IsLocalization.map_eq_zero_iff p.primeCompl] at hn
  obtain ⟨⟨m, hm⟩, hm0⟩ := hn
  have hm' : σ m ≠ 0 := fun h => (Ideal.mem_primeCompl_iff.1 hm) (RingHom.mem_ker.2 h)
  exact mul_pow_ne_zero_of_secDer σ b ht hDt hm' n hm0

end Derivation

section Conormal

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
variable (σ : A →ₐ[R] R) (b : Module.Basis (Fin 1) A Ω[A⁄R])

/-- There is `t ∈ ker σ` whose differential has coordinate `1` along `σ`. -/
theorem exists_param : ∃ t : A, σ t = 0 ∧ secDer σ b t = 1 := by
  let _ : Algebra A R := σ.toRingHom.toAlgebra
  have : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq fun r => (σ.commutes r).symm
  have hsurj : Function.Surjective (algebraMap A R) := fun r => ⟨algebraMap R A r, σ.commutes r⟩
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A R hsurj
  obtain ⟨y, hy⟩ := (hex (1 ⊗ₜ b 0)).1 (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  refine ⟨x, hx, ?_⟩
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
  have := congrArg (fun z => (Algebra.TensorProduct.basis R b).repr z 0) hy
  simp [Algebra.TensorProduct.basis_repr_tmul] at this
  exact this

/-- Formal smoothness: an element of `ker σ` with vanishing derivative lies in `(ker σ)²`. -/
theorem mem_sq_of_secDer_eq_zero [Algebra.FormallySmooth R A] {x : A} (hx : σ x = 0)
    (hD : secDer σ b x = 0) : x ∈ RingHom.ker σ ^ 2 := by
  let _ : Algebra A R := σ.toRingHom.toAlgebra
  have : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq fun r => (σ.commutes r).symm
  have hsurj : Function.Surjective (algebraMap A R) := fun r => ⟨algebraMap R A r, σ.commutes r⟩
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := R) (A := R)
    (P := A) hsurj).2 inferInstance
  have hx' : x ∈ RingHom.ker (algebraMap A R) := hx
  have h0 : KaehlerDifferential.kerCotangentToTensor R A R
      ((RingHom.ker (algebraMap A R)).toCotangent ⟨x, hx'⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    apply (Algebra.TensorProduct.basis R b).repr.injective
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Algebra.TensorProduct.basis_repr_tmul]
    exact hD
  rw [← map_zero (KaehlerDifferential.kerCotangentToTensor R A R)] at h0
  exact (Ideal.toCotangent_eq_zero _ _).1 (hinj h0)

variable {t : A} (ht : σ t = 0) (hDt : secDer σ b t = 1)
include ht hDt

theorem sub_mem_sq [Algebra.FormallySmooth R A] {x : A} (hx : σ x = 0) :
    x - algebraMap R A (secDer σ b x) * t ∈ RingHom.ker σ ^ 2 := by
  refine mem_sq_of_secDer_eq_zero σ b ?_ ?_
  · simp [hx, ht]
  · rw [secDer_sub, secDer_mul, secDer_algebraMap, hDt, ht]
    simp

/-- `ker σ = (t) + (ker σ)²`. -/
theorem ker_le_span_sup_sq [Algebra.FormallySmooth R A] :
    RingHom.ker σ ≤ Ideal.span {t} ⊔ RingHom.ker σ ^ 2 := by
  intro x hx
  have hx' : σ x = 0 := RingHom.mem_ker.1 hx
  have h := sub_mem_sq σ b ht hDt hx'
  have : x = algebraMap R A (secDer σ b x) * t + (x - algebraMap R A (secDer σ b x) * t) := by
    ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)) h

theorem bijective_toSpanSingleton_cotangent [Algebra.FormallySmooth R A] :
    Function.Bijective (LinearMap.toSpanSingleton R _
      ((RingHom.ker σ).toCotangent ⟨t, RingHom.mem_ker.2 ht⟩)) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro r hr
      rw [LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul_of_tower,
        Ideal.toCotangent_eq_zero] at hr
      have := secDer_eq_zero_of_mem_sq σ b hr
      rw [Submodule.coe_smul_of_tower, Algebra.smul_def, secDer_mul, secDer_algebraMap, hDt] at this
      simpa using this
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
      refine ⟨secDer σ b x, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul_of_tower, Ideal.toCotangent_eq]
      have h := sub_mem_sq σ b ht hDt (RingHom.mem_ker.1 hx)
      have h' := (Ideal.neg_mem_iff _).2 h
      rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
      convert h' using 1
      ring

/-- The `R`-linear isomorphism `R ≃ I/I²`, `r ↦ r · [t]`. -/
def cotangentEquiv [Algebra.FormallySmooth R A] : R ≃ₗ[R] (RingHom.ker σ).Cotangent :=
  LinearEquiv.ofBijective _ (bijective_toSpanSingleton_cotangent σ b ht hDt)

/-- The conormal module `I/I²` of the section is free of rank one on the class of `t`. -/
def cotangentBasis [Algebra.FormallySmooth R A] :
    Module.Basis (Fin 1) R (RingHom.ker σ).Cotangent :=
  (Module.Basis.singleton (Fin 1) R).map (cotangentEquiv σ b ht hDt)

theorem cotangentBasis_apply [Algebra.FormallySmooth R A] (i : Fin 1) :
    cotangentBasis σ b ht hDt i = (RingHom.ker σ).toCotangent ⟨t, RingHom.mem_ker.2 ht⟩ := by
  simp [cotangentBasis, cotangentEquiv]

end Conormal

section Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (σ : A →ₐ[R] R)

/-- The prime of `A` at the closed point of the section: `σ⁻¹(𝔪_R)`. -/
abbrev sectionPrime : Ideal A := (maximalIdeal R).comap σ

/-- The section, localized at `sectionPrime σ` (the stalk map of the section). -/
def localSection : Localization.AtPrime (sectionPrime σ) →+* R :=
  IsLocalization.lift (M := (sectionPrime σ).primeCompl) (g := σ.toRingHom) fun y =>
    (IsLocalRing.notMem_maximalIdeal).1 (Ideal.mem_primeCompl_iff.1 y.2)

theorem localSection_algebraMap (a : A) :
    localSection σ (algebraMap A (Localization.AtPrime (sectionPrime σ)) a) = σ a :=
  IsLocalization.lift_eq _ a

variable {ϖ : R} (hϖ : Irreducible ϖ)
include hϖ

theorem sectionPrime_eq_ker_sup :
    sectionPrime σ = RingHom.ker σ ⊔ Ideal.span {algebraMap R A ϖ} := by
  apply le_antisymm
  · intro a ha
    have ha' : σ a ∈ Ideal.span {ϖ} := hϖ.maximalIdeal_eq ▸ ha
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 ha'
    have : a = (a - algebraMap R A (σ a)) + algebraMap R A r * algebraMap R A ϖ := by
      rw [← map_mul, hr]
      ring
    rw [this]
    refine Submodule.add_mem_sup ?_ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    simp
  · refine sup_le (fun a ha => ?_) ?_
    · simp [Ideal.mem_comap, RingHom.mem_ker.1 ha]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show σ (algebraMap R A ϖ) ∈ maximalIdeal R
      rw [σ.commutes]
      exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

theorem ker_lt_sectionPrime : RingHom.ker σ < sectionPrime σ := by
  rw [sectionPrime_eq_ker_sup σ hϖ]
  refine lt_of_le_of_ne le_sup_left fun h => hϖ.ne_zero ?_
  have hmem : algebraMap R A ϖ ∈ RingHom.ker σ :=
    h ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  simpa using hmem

variable [Algebra.FormallySmooth R A] (b : Module.Basis (Fin 1) A Ω[A⁄R])
variable {t : A} (ht : σ t = 0) (hDt : secDer σ b t = 1)
include ht hDt

theorem two_le_height_sectionPrime : 2 ≤ (sectionPrime σ).height := by
  have := ker_isPrime σ
  have h1 : (RingHom.ker σ).height ≠ 0 := fun h =>
    ker_notMem_minimalPrimes σ b ht hDt (Ideal.height_eq_zero_iff.1 h)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (ker_lt_sectionPrime σ hϖ)
  have h3 : (1 : ℕ∞) ≤ (RingHom.ker σ).height := Order.one_le_iff_ne_zero.2 h1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (RingHom.ker σ).height + 1 := by gcongr
    _ ≤ _ := h2

theorem two_le_ringKrullDim :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (sectionPrime σ)) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (sectionPrime σ)]
  calc (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ _ := WithBot.coe_le_coe.2 (two_le_height_sectionPrime σ hϖ b ht hDt)

variable [IsNoetherianRing A]

/-- In `A_𝔭`, the kernel of the section is generated by `t`. -/
theorem map_ker_eq_span :
    (RingHom.ker σ).map (algebraMap A (Localization.AtPrime (sectionPrime σ))) =
      Ideal.span {algebraMap A (Localization.AtPrime (sectionPrime σ)) t} := by
  set ι := algebraMap A (Localization.AtPrime (sectionPrime σ))
  apply le_antisymm
  · have hle := Ideal.map_mono (f := ι) (ker_le_span_sup_sq σ b ht hDt)
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at hle
    have hm : (RingHom.ker σ).map ι ≤ maximalIdeal _ := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono (ker_lt_sectionPrime σ hϖ).le
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (I := maximalIdeal _) ?_ (hle.trans (sup_le_sup_left ?_ _))
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rw [sq, Ideal.smul_eq_mul]
      exact Ideal.mul_mono_left hm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 ht)

/-- The kernel of the localized section (the stalk map of `e` at `e(s)`) is `(t)`. -/
theorem ker_localSection_eq_span :
    RingHom.ker (localSection σ) =
      Ideal.span {algebraMap A (Localization.AtPrime (sectionPrime σ)) t} := by
  rw [← map_ker_eq_span σ hϖ b ht hDt,
    ← IsLocalization.map_under (sectionPrime σ).primeCompl _ (RingHom.ker (localSection σ)),
    Ideal.under_def, RingHom.comap_ker]
  congr 2
  exact IsLocalization.lift_comp _

/-- `𝔪_{A_𝔭} = (ϖ, t)`. -/
theorem maximalIdeal_eq_span :
    maximalIdeal (Localization.AtPrime (sectionPrime σ)) =
      Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ,
        algebraMap A (Localization.AtPrime (sectionPrime σ)) t} := by
  set ι := algebraMap A (Localization.AtPrime (sectionPrime σ))
  calc maximalIdeal (Localization.AtPrime (sectionPrime σ)) = (sectionPrime σ).map ι :=
        Localization.AtPrime.map_eq_maximalIdeal.symm
    _ = (RingHom.ker σ ⊔ Ideal.span {algebraMap R A ϖ}).map ι := by
        rw [← sectionPrime_eq_ker_sup σ hϖ]
    _ = _ := by
        rw [Ideal.map_sup, map_ker_eq_span σ hϖ b ht hDt, Ideal.map_span, Set.image_singleton,
          Ideal.span_insert, sup_comm, ← IsScalarTower.algebraMap_apply]

theorem spanFinrank_maximalIdeal_le_two :
    (maximalIdeal (Localization.AtPrime (sectionPrime σ))).spanFinrank ≤ 2 := by
  rw [maximalIdeal_eq_span σ hϖ b ht hDt]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  simp

/-- `A_𝔭` has Krull dimension two. -/
theorem ringKrullDim_eq_two :
    ringKrullDim (Localization.AtPrime (sectionPrime σ)) = 2 := by
  refine le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_)
    (two_le_ringKrullDim σ hϖ b ht hDt)
  exact_mod_cast spanFinrank_maximalIdeal_le_two σ hϖ b ht hDt

/-- `A_𝔭` is a regular local ring. -/
theorem isRegularLocalRing : IsRegularLocalRing (Localization.AtPrime (sectionPrime σ)) := by
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [ringKrullDim_eq_two σ hϖ b ht hDt]
  exact_mod_cast spanFinrank_maximalIdeal_le_two σ hϖ b ht hDt

end Local

section Bundled

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

/-- **Node N5 (algebra form).** For a formally smooth Noetherian `R`-algebra `A` over a discrete
valuation ring with `Ω[A⁄R]` free of rank one, a section `σ` and a uniformizer `ϖ`, there is
`t ∈ ker σ` such that `A_𝔭` (`𝔭 = σ⁻¹(𝔪_R)`) is a regular local ring of dimension two with
`𝔪 = (ϖ, t)`, the kernel of the localized section is `(t)`, and `ker σ / (ker σ)²` is free of
rank one over `R` with basis the class of `t`. -/
theorem localStructure [Algebra.FormallySmooth R A] [IsNoetherianRing A]
    [Module.Free A Ω[A⁄R]] (hΩ : Module.rank A Ω[A⁄R] = 1) (σ : A →ₐ[R] R)
    {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (t : A) (ht : t ∈ RingHom.ker σ),
      IsRegularLocalRing (Localization.AtPrime (sectionPrime σ)) ∧
      ringKrullDim (Localization.AtPrime (sectionPrime σ)) = 2 ∧
      maximalIdeal (Localization.AtPrime (sectionPrime σ)) =
        Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ,
          algebraMap A (Localization.AtPrime (sectionPrime σ)) t} ∧
      RingHom.ker (localSection σ) =
        Ideal.span {algebraMap A (Localization.AtPrime (sectionPrime σ)) t} ∧
      ∃ B : Module.Basis (Fin 1) R (RingHom.ker σ).Cotangent,
        ∀ i, B i = (RingHom.ker σ).toCotangent ⟨t, ht⟩ := by
  have : Nontrivial A := σ.toRingHom.domain_nontrivial
  have : Module.Finite A Ω[A⁄R] := Module.rank_lt_aleph0_iff.1 (by
    rw [hΩ]
    exact Cardinal.one_lt_aleph0)
  let b : Module.Basis (Fin 1) A Ω[A⁄R] :=
    Module.finBasisOfFinrankEq A Ω[A⁄R] (Module.finrank_eq_of_rank_eq (by simpa using hΩ))
  obtain ⟨t, ht, hDt⟩ := exists_param σ b
  exact ⟨t, RingHom.mem_ker.2 ht, isRegularLocalRing σ hϖ b ht hDt,
    ringKrullDim_eq_two σ hϖ b ht hDt, maximalIdeal_eq_span σ hϖ b ht hDt,
    ker_localSection_eq_span σ hϖ b ht hDt, cotangentBasis σ b ht hDt,
    cotangentBasis_apply σ b ht hDt⟩

/-- **Node N5** for a standard smooth algebra of relative dimension one (the local form of a
smooth morphism of relative dimension one). -/
theorem localStructure_of_standardSmooth [Algebra.IsStandardSmoothOfRelativeDimension 1 R A]
    (σ : A →ₐ[R] R) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (t : A) (ht : t ∈ RingHom.ker σ),
      IsRegularLocalRing (Localization.AtPrime (sectionPrime σ)) ∧
      ringKrullDim (Localization.AtPrime (sectionPrime σ)) = 2 ∧
      maximalIdeal (Localization.AtPrime (sectionPrime σ)) =
        Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ,
          algebraMap A (Localization.AtPrime (sectionPrime σ)) t} ∧
      RingHom.ker (localSection σ) =
        Ideal.span {algebraMap A (Localization.AtPrime (sectionPrime σ)) t} ∧
      ∃ B : Module.Basis (Fin 1) R (RingHom.ker σ).Cotangent,
        ∀ i, B i = (RingHom.ker σ).toCotangent ⟨t, ht⟩ := by
  have : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Nontrivial A := σ.toRingHom.domain_nontrivial
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact localStructure
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1) σ hϖ

end Bundled

end ZInQ.Contrib.CMHeight62Full
