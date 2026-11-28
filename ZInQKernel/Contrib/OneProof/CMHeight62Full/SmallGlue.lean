import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreValuation
import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeStatements

/-!
# Small glue for the per-place assembly (blueprint node L7)

Short algebraic facts used by the per-place assembly of the finite-place step.

* `faithfulSMul_of_irreducible_mem_nonZeroDivisors`: if `R` is a discrete valuation ring with
  uniformizer `ϖ` and `ϖ` maps to a nonzerodivisor of a nontrivial `R`-algebra `A`, then
  `R → A` is injective.
* `localizationAtPrimeAlgebra`, `isFractionRing_localizationAtPrime`: the localization `S_𝔭` of
  a domain at a prime maps into the fraction field `K` of `S`, which is a fraction field of
  `S_𝔭`. `fractionFieldAlgebra`, `isScalarTower_fractionFieldAlgebra`, `algebraMap_eq_lift`:
  for `R → A` injective, the fraction field `F` of `R` maps into the fraction field `Ω` of `A`
  compatibly with `R`, and any such map is this one.
* `perfectField_residueField_ringOfIntegers`, `charZero_localizationAtPrime`,
  `isDiscreteValuationRing_localization_ringOfIntegers`: at a nonzero prime of a ring of
  integers the localization is a discrete valuation ring of characteristic zero with a finite,
  hence perfect, residue field.
* `isUniformizer_specialFibreValuation`: `ϖ` is a uniformizer of the special-fibre valuation.
* `reduce_specialFibreValuation_algebraMap`, `reduce_mem_specialFibrePlace`,
  `exists_reduce_mem_specialFibrePlace`, `isUniformizerAt_reduce_specialFibrePlace`: residues
  of elements of `A` lie in the special-fibre place, and the residue of `t` is a uniformizer.
* `mul_mem_poleSpaceIn`, `poleSpaceIn_mono`, `monomials_mem_poleSpaceIn`: `V_m · V_n ⊆ V_{m+n}`,
  so the seven monomials `1, x, y, x², xy, y², x³` lie in `V_6`.
* `valuation_eq_of_mem_poleSpaceIn_succ`: exact pole orders.
* `trdegLeOne_of_algEquiv`: `TrdegLeOne` along an isomorphism of `k`-algebras.

Only Mathlib and earlier files of this directory are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing NumberField IsDedekindDomain

namespace SmallGlue

/-! ## Injectivity of `R → A` -/

/-- If `ϖ` is a uniformizer of the discrete valuation ring `R` and its image in the nontrivial
`R`-algebra `A` is a nonzerodivisor, then `R → A` is injective. -/
theorem faithfulSMul_of_irreducible_mem_nonZeroDivisors {R A : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Nontrivial A] [Algebra R A] {ϖ : R}
    (hϖ : Irreducible ϖ) (h : algebraMap R A ϖ ∈ nonZeroDivisors A) : FaithfulSMul R A := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  rw [map_mul, map_pow] at hr
  have hu := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem h n)).mp hr
  exact ((u.isUnit.map (algebraMap R A)).ne_zero) hu

/-! ## Fraction fields -/

section Localization

variable (S K : Type*) [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
  (𝔭 : Ideal S) [𝔭.IsPrime]

/-- The map `S_𝔭 → K` from the localization at a prime into the fraction field. -/
abbrev localizationAtPrimeAlgebra : Algebra (Localization.AtPrime 𝔭) K :=
  (IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) (g := algebraMap S K)
    fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr
      (nonZeroDivisors.ne_zero (𝔭.primeCompl_le_nonZeroDivisors y.2)))).toAlgebra

theorem isScalarTower_localizationAtPrime :
    letI := localizationAtPrimeAlgebra S K 𝔭
    IsScalarTower S (Localization.AtPrime 𝔭) K := by
  let := localizationAtPrimeAlgebra S K 𝔭
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  exact (IsLocalization.lift_eq _ x).symm

/-- `K` is a fraction field of `S_𝔭`. -/
theorem isFractionRing_localizationAtPrime :
    letI := localizationAtPrimeAlgebra S K 𝔭
    IsFractionRing (Localization.AtPrime 𝔭) K := by
  let := localizationAtPrimeAlgebra S K 𝔭
  have := isScalarTower_localizationAtPrime S K 𝔭
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ K

theorem charZero_localizationAtPrime [CharZero S] : CharZero (Localization.AtPrime 𝔭) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors)

end Localization

section Tower

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [FaithfulSMul R A]
  (F Ω : Type*) [Field F] [Field Ω] [Algebra R F]
  [IsFractionRing R F] [Algebra A Ω] [IsFractionRing A Ω] [Algebra R Ω] [IsScalarTower R A Ω]

include A in
omit [IsFractionRing R F] in
theorem algebraMap_injective_of_tower : Function.Injective (algebraMap R Ω) := by
  rw [IsScalarTower.algebraMap_eq R A Ω]
  exact (IsFractionRing.injective A Ω).comp (FaithfulSMul.algebraMap_injective R A)

/-- The map `F → Ω` of fraction fields induced by `R → A`. -/
abbrev fractionFieldAlgebra : Algebra F Ω :=
  (IsFractionRing.lift (A := R) (K := F) (algebraMap_injective_of_tower R A Ω)).toAlgebra

theorem isScalarTower_fractionFieldAlgebra :
    letI := fractionFieldAlgebra R A F Ω
    IsScalarTower R F Ω := by
  let := fractionFieldAlgebra R A F Ω
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  exact (IsLocalization.lift_eq _ x).symm

variable {F Ω}

/-- Any map `F → Ω` compatible with `R` is the induced map. -/
theorem algebraMap_eq_lift [Algebra F Ω] [IsScalarTower R F Ω] :
    algebraMap F Ω =
      IsFractionRing.lift (A := R) (K := F) (algebraMap_injective_of_tower R A Ω) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors R) ?_
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
    IsFractionRing.lift_algebraMap]

end Tower

/-! ## Rings of integers: the localization at a nonzero prime -/

section RingOfIntegers

variable {L : Type*} [Field L] [NumberField L] (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime]

theorem finite_residueField_ringOfIntegers (h : 𝔭 ≠ ⊥) :
    Finite (ResidueField (Localization.AtPrime 𝔭)) := by
  have := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h
  have : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h
  exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝔭).2

/-- The residue field at a nonzero prime of a ring of integers is finite, hence perfect. -/
theorem perfectField_residueField_ringOfIntegers (h : 𝔭 ≠ ⊥) :
    PerfectField (ResidueField (Localization.AtPrime 𝔭)) := by
  have := finite_residueField_ringOfIntegers 𝔭 h
  infer_instance

theorem charZero_localization_ringOfIntegers : CharZero (Localization.AtPrime 𝔭) :=
  charZero_localizationAtPrime (𝓞 L) 𝔭

theorem isDiscreteValuationRing_localization_ringOfIntegers (h : 𝔭 ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) h _

/-- `L` is a fraction field of `(𝓞 L)_𝔭`. -/
theorem isFractionRing_localization_ringOfIntegers :
    letI := localizationAtPrimeAlgebra (𝓞 L) L 𝔭
    IsFractionRing (Localization.AtPrime 𝔭) L :=
  isFractionRing_localizationAtPrime (𝓞 L) L 𝔭

end RingOfIntegers

/-! ## The special-fibre valuation and its place -/

section SpecialFibre

open SpecialFibreValuation

variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [IsNoetherianRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]
  {Ω : Type*} [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
  {ϖ : R} (hϖ : Irreducible ϖ) [IsDomain (A ⧸ Ideal.span {algebraMap R A ϖ})]

/-- `ϖ` is a uniformizer of the special-fibre valuation (`IsUniformizer` over a fraction
field `F` of `R`). -/
theorem isUniformizer_specialFibreValuation [IsDomain R] [IsDiscreteValuationRing R]
    {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Algebra F Ω] [Algebra R Ω]
    [IsScalarTower R A Ω] [IsScalarTower R F Ω] :
    IsUniformizer (F := F) (specialFibreValuation A Ω hϖ) (algebraMap R F ϖ) := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hϖ.ne_zero
  · rw [← IsScalarTower.algebraMap_apply R F Ω]
    exact specialFibreValuation_algebraMap_base_lt_one hϖ ϖ
      ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
  · rw [← IsScalarTower.algebraMap_apply R F Ω]
    exact specialFibreValuation_eq_zpow hϖ hx

/-- The residue of `a ∈ A` in `κ_w` is the image of `a mod ϖ`. -/
theorem reduce_specialFibreValuation_algebraMap (a : A)
    (h : specialFibreValuation A Ω hϖ (algebraMap A Ω a) ≤ 1) :
    reduce (specialFibreValuation A Ω hϖ) (algebraMap A Ω a) h =
      specialFibreResidueMap A Ω hϖ (Ideal.Quotient.mk _ a) :=
  rfl

variable [IsDiscreteValuationRing (A ⧸ Ideal.span {algebraMap R A ϖ})]

/-- Residues of elements of `A` lie in `ē` (the input `hAP` of the local parameter node). -/
theorem reduce_mem_specialFibrePlace (a : A) :
    reduce (specialFibreValuation A Ω hϖ) (algebraMap A Ω a)
      (specialFibreValuation_algebraMap_le_one hϖ a) ∈ specialFibrePlace A Ω hϖ :=
  (mem_specialFibrePlace hϖ).mpr ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- The input `hAē` of `reduce_mem_polePart`. -/
theorem exists_reduce_mem_specialFibrePlace (a : A) :
    ∃ h : specialFibreValuation A Ω hϖ (algebraMap A Ω a) ≤ 1,
      reduce (specialFibreValuation A Ω hϖ) (algebraMap A Ω a) h ∈ specialFibrePlace A Ω hϖ :=
  ⟨_, reduce_mem_specialFibrePlace hϖ a⟩

/-- If `ker ρ = (t)` for an `R`-algebra retraction `ρ`, the residue of `t` is a uniformizer at
`ē` (the input `hπ` of the local parameter node). -/
theorem isUniformizerAt_reduce_specialFibrePlace [IsDomain R] [IsDiscreteValuationRing R]
    (ρ : A →ₐ[R] R) {t : A} (hker : RingHom.ker ρ = Ideal.span {t}) :
    IsUniformizerAt (specialFibrePlace A Ω hϖ) (reduce (specialFibreValuation A Ω hϖ)
      (algebraMap A Ω t) (specialFibreValuation_algebraMap_le_one hϖ t)) :=
  isUniformizerAt_specialFibrePlace hϖ ρ hker

end SpecialFibre

/-! ## Pole spaces: products and exact orders -/

section PoleSpaces

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra k Ω]
  (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F)

theorem exp_one_pow_add (m n : ℕ) :
    WithZero.exp (1 : ℤ) ^ (m + n) = WithZero.exp (1 : ℤ) ^ m * WithZero.exp (1 : ℤ) ^ n :=
  pow_add _ m n

/-- `V_m · V_n ⊆ V_{m+n}`. -/
theorem mul_mem_poleSpaceIn {m n : ℕ} {f g : Ω} (hf : f ∈ poleSpaceIn Ψ P m)
    (hg : g ∈ poleSpaceIn Ψ P n) : f * g ∈ poleSpaceIn Ψ P (m + n) := by
  rw [mem_poleSpaceIn_iff] at hf hg ⊢
  rw [map_mul]
  refine ⟨fun Q hQ => ?_, ?_⟩
  · rw [map_mul]
    exact mul_le_one' (hf.1 Q hQ) (hg.1 Q hQ)
  · rw [map_mul, exp_one_pow_add]
    exact mul_le_mul' hf.2 hg.2

theorem poleSpaceIn_mono {m n : ℕ} (h : m ≤ n) : poleSpaceIn Ψ P m ≤ poleSpaceIn Ψ P n :=
  Submodule.map_mono (poleSpace_mono P h)

theorem one_mem_poleSpaceIn (n : ℕ) : (1 : Ω) ∈ poleSpaceIn Ψ P n := by
  rw [mem_poleSpaceIn_iff, map_one, ← mem_poleSpace_iff]
  exact one_mem_poleSpace P

/-- The monomials of a Weierstrass equation lie in `V_6` (the input `hmono` of the integral
model node, with `V := V_6`). -/
theorem monomials_mem_poleSpaceIn {x y : Ω} (hx : x ∈ poleSpaceIn Ψ P 2)
    (hy : y ∈ poleSpaceIn Ψ P 3) :
    ∀ i, ![1, x, y, x ^ 2, x * y, y ^ 2, x ^ 3] i ∈ poleSpaceIn Ψ P 6 := by
  have hx2 : x ^ 2 ∈ poleSpaceIn Ψ P (2 + 2) := by
    rw [pow_two]
    exact mul_mem_poleSpaceIn Ψ P hx hx
  have hxy : x * y ∈ poleSpaceIn Ψ P (2 + 3) := mul_mem_poleSpaceIn Ψ P hx hy
  have hy2 : y ^ 2 ∈ poleSpaceIn Ψ P (3 + 3) := by
    rw [pow_two]
    exact mul_mem_poleSpaceIn Ψ P hy hy
  have hx3 : x ^ 3 ∈ poleSpaceIn Ψ P (2 + 2 + 2) := by
    rw [pow_succ]
    exact mul_mem_poleSpaceIn Ψ P hx2 hx
  intro i
  fin_cases i
  · exact one_mem_poleSpaceIn Ψ P 6
  · exact poleSpaceIn_mono Ψ P (by norm_num) hx
  · exact poleSpaceIn_mono Ψ P (by norm_num) hy
  · exact poleSpaceIn_mono Ψ P (by norm_num) hx2
  · exact poleSpaceIn_mono Ψ P (by norm_num) hxy
  · exact poleSpaceIn_mono Ψ P (by norm_num) hy2
  · exact poleSpaceIn_mono Ψ P (by norm_num) hx3

/-- In `ℤᵐ⁰`, a value strictly above `exp 1 ^ n` and at most `exp 1 ^ (n + 1)` equals
`exp 1 ^ (n + 1)`. -/
theorem eq_exp_one_pow_succ {v : WithZero (Multiplicative ℤ)} {n : ℕ}
    (h1 : WithZero.exp (1 : ℤ) ^ n < v) (h2 : v ≤ WithZero.exp (1 : ℤ) ^ (n + 1)) :
    v = WithZero.exp (1 : ℤ) ^ (n + 1) := by
  have hv : v ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le h1)
  rw [← WithZero.exp_log hv] at h1 h2 ⊢
  rw [← WithZero.exp_nsmul] at h1 h2 ⊢
  rw [WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  congr 1
  simp only [nsmul_eq_mul, mul_one] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  omega

/-- **Exact pole order.** If `f ∈ V_{n+1}` and `f ∉ V_n`, then `v_P(Ψ f) = exp 1 ^ (n + 1)`. -/
theorem valuation_eq_of_mem_poleSpaceIn_succ {n : ℕ} {f : Ω}
    (hf : f ∈ poleSpaceIn Ψ P (n + 1)) (hf' : f ∉ poleSpaceIn Ψ P n) :
    P.valuation (Ψ f) = WithZero.exp (1 : ℤ) ^ (n + 1) := by
  rw [mem_poleSpaceIn_iff] at hf hf'
  refine eq_exp_one_pow_succ (not_le.mp fun h => hf' ⟨hf.1, h⟩) hf.2

theorem valuation_eq_two_of_mem_poleSpaceIn {x : Ω} (hx : x ∈ poleSpaceIn Ψ P 2)
    (hx1 : x ∉ poleSpaceIn Ψ P 1) : P.valuation (Ψ x) = WithZero.exp (1 : ℤ) ^ 2 :=
  valuation_eq_of_mem_poleSpaceIn_succ Ψ P (n := 1) hx hx1

theorem valuation_eq_three_of_mem_poleSpaceIn {y : Ω} (hy : y ∈ poleSpaceIn Ψ P 3)
    (hy2 : y ∉ poleSpaceIn Ψ P 2) : P.valuation (Ψ y) = WithZero.exp (1 : ℤ) ^ 3 :=
  valuation_eq_of_mem_poleSpaceIn_succ Ψ P (n := 2) hy hy2

end PoleSpaces

/-! ## Transcendence degree at most one along an isomorphism -/

section Trdeg

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']

/-- `TrdegLeOne` is invariant under isomorphisms of `k`-algebras. -/
theorem trdegLeOne_of_algEquiv (e : K ≃ₐ[k] K') (h : TrdegLeOne k K) : TrdegLeOne k K' := by
  intro x hx
  set y := e.symm x with hy
  have hyt : Transcendental k y := by
    intro hya
    apply hx
    have := hya.algHom (e : K →ₐ[k] K')
    rwa [hy, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at this
  have := h y hyt
  have hmap : (Algebra.adjoin k {x}).map (e.symm : K' →ₐ[k] K) = Algebra.adjoin k {y} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  let f : Algebra.adjoin k {x} ≃ₐ[k] Algebra.adjoin k {y} :=
    (e.symm.subalgebraMap (Algebra.adjoin k {x})).trans (Subalgebra.equivOfEq _ _ hmap)
  refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq (f : Algebra.adjoin k {x} →+*
    Algebra.adjoin k {y}) (e.symm : K' →+* K) f.surjective e.symm.injective ?_
  ext z
  rfl

end Trdeg

end SmallGlue

end ZInQ.Contrib.CMHeight62Full
