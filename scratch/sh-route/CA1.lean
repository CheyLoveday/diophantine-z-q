import Mathlib

open IsLocalRing

set_option linter.style.haveILetI false

namespace ShRoute

/-! ## A. Valuation rings over a Dedekind domain are localizations -/

section Loc

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- `R → W` for a valuation subring `W` of `Frac R` containing `R`. -/
def toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : R →+* W :=
  (algebraMap R F).codRestrict W.toSubring hW

/-- The center `R ∩ 𝔪_W`. -/
def ctr (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : Ideal R :=
  (maximalIdeal W).comap (toW W hW)

theorem mem_ctr_iff (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) (r : R) :
    r ∈ ctr W hW ↔ algebraMap R F r ∈ W.nonunits := by
  change toW W hW r ∈ maximalIdeal W ↔ _
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
  rfl

instance ctr_isPrime (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) :
    (ctr W hW).IsPrime := Ideal.comap_isPrime _ _

theorem isUnit_toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {s : R}
    (hs : s ∉ ctr W hW) : IsUnit (toW W hW s) := by
  by_contra h
  exact hs ((mem_maximalIdeal _).mpr h)

theorem mem_of_mul_eq' (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {x : F}
    {a s : R} (hs : s ∉ ctr W hW) (h : x * algebraMap R F s = algebraMap R F a) : x ∈ W := by
  obtain ⟨u, hu⟩ := isUnit_toW W hW hs
  have h1 : ((u : W) : F) = algebraMap R F s := by rw [hu]; rfl
  have h2 : (((u⁻¹ : Wˣ) : W) : F) * ((u : W) : F) = 1 :=
    congrArg (fun z : W => (z : F)) (Units.inv_mul u)
  have : x = algebraMap R F a * (((u⁻¹ : Wˣ) : W) : F) := by
    rw [← h, h1.symm, _root_.mul_assoc, mul_comm ((u : W) : F), h2, _root_.mul_one]
  rw [this]
  exact mul_mem (hW a) (u⁻¹ : Wˣ).1.2

/-- **A valuation subring `W ⊇ R` of `Frac R` with nonzero center is the localization of `R` at
its center**: every `x ∈ W` is `a/s` with `a, s ∈ R`, `s ∉ 𝔭`. (Generalizes reduct-glue's
`mem_iff_exists` from `𝓞_L` to any Dedekind domain; same proof.) -/
theorem exists_of_mem (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W)
    (h0 : ctr W hW ≠ ⊥) {x : F} (hx : x ∈ W) :
    ∃ a s : R, s ∉ ctr W hW ∧ x * algebraMap R F s = algebraMap R F a := by
  let 𝔭 := ctr W hW
  let B := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 B
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (algebraMap R F b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R B a) (algebraMap R B b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl c
  have hinj := IsLocalization.injective B 𝔭.primeCompl_le_nonZeroDivisors
  have hspec := IsLocalization.mk'_spec B r s
  have hs : (s : R) ∉ ctr W hW := s.2
  rcases hc with h | h
  · have h' : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    have hL : (algebraMap R F a) * (algebraMap R F r) =
        (algebraMap R F b) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply hs
      have hX : (⟨_, hx⟩ : W) * toW W hW r = toW W hW s := by
        apply Subtype.ext
        change (algebraMap R F a / algebraMap R F b) * (algebraMap R F r) = algebraMap R F s
        rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
      change toW W hW s ∈ maximalIdeal W
      rw [← hX]
      exact Ideal.mul_mem_left _ _ hr
    · refine ⟨s, r, hr, ?_⟩
      rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
  · have h' : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    refine ⟨r, s, hs, ?_⟩
    have hL : (algebraMap R F b) * (algebraMap R F r) =
        (algebraMap R F a) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    rw [div_mul_eq_mul_div, ← hL, mul_div_cancel_left₀ _ hb0]

end Loc

/-! ## B. The inertia field of a finite Galois extension is unramified -/

section Key

theorem nonunits_comap {E M : Type*} [Field E] [Field M] (f : E →+* M) (W : ValuationSubring M)
    (x : E) : x ∈ (W.comap f).nonunits ↔ f x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  simp only [ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem div_mem_nonunits {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W.nonunits) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hn hd' ⊢
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

theorem div_mem {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W := by
  rw [← W.valuation_le_one_iff] at hn ⊢
  rw [ValuationSubring.mem_nonunits_iff] at hd'
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

/-- An element of `M` integral over a subring contained in `W` lies in `W`. -/
theorem mem_of_isIntegral {A M : Type*} [CommRing A] [Field M] [Algebra A M]
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W) {x : M}
    (hx : IsIntegral A x) : x ∈ W := by
  letI : Algebra A W := ((algebraMap A M).codRestrict W.toSubring hAW).toAlgebra
  haveI : IsScalarTower A W M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h2 : IsIntegral W x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K]
  [IsFractionRing A K] [Algebra A M] [IsScalarTower A K M]

instance instSMulCommClassGal : SMulCommClass (M ≃ₐ[K] M) A M where
  smul_comm σ a x := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A K M, AlgEquiv.commutes]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Key lemma (finite level).** `M/K` finite Galois, `A ⊆ K` a DVR with perfect residue field,
`W` a valuation ring of `M` over `A`. If `x ∈ W`, `x ≠ 0` is fixed by every `σ ∈ Gal(M/K)` acting
trivially modulo `𝔪_W`, then `x = ϖⁿ · (unit of W)` for a uniformizer `ϖ` of `A`. -/
theorem key_finite [PerfectField (ResidueField A)]
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W)
    (hctr : ∀ a : A, algebraMap A M a ∈ W.nonunits ↔ a ∈ maximalIdeal A)
    (ϖ : A) (hϖ : Irreducible ϖ) (x : M)
    (hfix : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ x = x)
    (hxW : x ∈ W) (hx0 : x ≠ 0) :
    ∃ n : ℕ, x / algebraMap A M ϖ ^ n ∈ W ∧ (x / algebraMap A M ϖ ^ n)⁻¹ ∈ W := by
  classical
  -- the ring of integers `S` of `M` over `A`
  let S := integralClosure A M
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain A K M
  haveI : Module.Finite A S := IsIntegralClosure.finite A K M S
  haveI : IsFractionRing S M := IsIntegralClosure.isFractionRing_of_finite_extension A K M S
  haveI : IsGaloisGroup (M ≃ₐ[K] M) A S := IsGaloisGroup.of_isFractionRing _ A S K M
  have hSW : ∀ s : S, algebraMap S M s ∈ W := fun s =>
    mem_of_isIntegral W hAW s.2
  let p := maximalIdeal A
  let P : Ideal S := ctr W hSW
  have hP : ∀ s : S, s ∈ P ↔ (s : M) ∈ W.nonunits := fun s => mem_ctr_iff W hSW s
  haveI : P.LiesOver p := by
    constructor
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hP]
    exact (hctr a).symm
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖp : ϖ ∈ p := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hAinj : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hP0 : P ≠ ⊥ := by
    intro h
    have : algebraMap A S ϖ ∈ P := by rw [hP]; exact (hctr ϖ).mpr hϖp
    rw [h, Ideal.mem_bot] at this
    apply hϖ0
    apply hAinj
    rw [map_zero]
    exact congrArg (fun z : S => (z : M)) this
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  haveI : PerfectField (A ⧸ p) := ‹PerfectField (ResidueField A)›
  haveI : FaithfulSMul A S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hAinj (congrArg (fun z : S => (z : M)) h)
  haveI : Module.IsTorsionFree A S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : PerfectField p.ResidueField := PerfectField.of_ringEquiv
    (RingEquiv.ofBijective (algebraMap (A ⧸ p) p.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField p))
  have hcard : Nat.card (P.inertia (M ≃ₐ[K] M)) = p.ramificationIdxIn S :=
    Ideal.card_inertia_eq_ramificationIdxIn p P
  -- the inertia field `E` and its ring of integers `R`
  let H := P.inertia (M ≃ₐ[K] M)
  let E : IntermediateField K M := FixedPoints.intermediateField H
  haveI : IsScalarTower A E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let R := integralClosure A E
  haveI : IsDedekindDomain R := integralClosure.isDedekindDomain A K E
  haveI : Module.Finite A R := IsIntegralClosure.finite A K E R
  haveI : IsFractionRing R E := IsIntegralClosure.isFractionRing_of_finite_extension A K E R
  have hRS : ∀ r : R, IsIntegral A (algebraMap E M (r : E)) := fun r =>
    r.2.map (IsScalarTower.toAlgHom A E M)
  let φ : R →+* S := ((algebraMap E M).comp (algebraMap R E)).codRestrict S (fun r => hRS r)
  letI : Algebra R S := φ.toAlgebra
  haveI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    change algebraMap A M a = algebraMap E M (algebraMap A E a)
    rw [← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.tower_top A
  haveI : IsGaloisGroup H E M := IsGaloisGroup.subgroup (M ≃ₐ[K] M) K M H
  haveI : IsGaloisGroup H R S := IsGaloisGroup.of_isFractionRing H R S E M
  haveI : Module.Finite R S := Module.Finite.of_restrictScalars_finite A R S
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply Subtype.ext
    apply (algebraMap E M).injective
    exact congrArg (fun z : S => (z : M)) h
  haveI : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  let 𝔮 : Ideal R := P.under R
  haveI : 𝔮.LiesOver p := Ideal.LiesOver.tower_bot P 𝔮 p
  haveI : Algebra.HasSeparableResidueFieldsAt R S 𝔮 :=
    Algebra.HasSeparableResidueFieldsAt.tower_top p 𝔮
  have hcard' : Nat.card (P.inertia H) = 𝔮.ramificationIdxIn S :=
    Ideal.card_inertia_eq_ramificationIdxIn 𝔮 P
  have htop : P.inertia H = ⊤ := by
    ext h
    simp only [Subgroup.mem_top, iff_true]
    intro s
    exact h.2 s
  have hcardH : Nat.card (P.inertia H) = Nat.card H := by
    rw [htop]; exact Subgroup.card_top
  have he1 := Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[K] M)
  have he2 := Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 P H
  have htower := Ideal.ramificationIdx_tower (R := A) 𝔮 P
  have hepos : P.ramificationIdx A ≠ 0 := by
    rw [← he1, ← hcard]; exact Nat.card_pos.ne'
  have he𝔮 : 𝔮.ramificationIdx A = 1 := by
    rw [← he2, ← hcard', hcardH, ← he1, ← hcard] at htower
    have hc : 0 < Nat.card H := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hc (by rw [one_mul]; exact htower.symm)
  sorry

end Key

end ShRoute
