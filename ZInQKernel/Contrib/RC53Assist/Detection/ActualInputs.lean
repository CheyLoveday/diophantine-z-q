import ZInQKernel.Contrib.RC53Assist.Detection.Inputs
import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.Assembly
import ZInQKernel.Contrib.OneProof.RC.Moving.MovingCharacter

/-!
# Tame characters, character cutouts, and retained comparison exports

The local tame character is a character of inertia at a finite precision.
Character cutout fields and retained cochain maps are kept separate from
class evaluations and from a detecting determinant.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Detection.Actual

open CategoryTheory Filter Topology Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Limits hiding Lambda evalOne evalZero evalTwo
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.Detection
open ZInQ.Contrib.RC53Assist.Detection.Inputs
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open scoped WeierstrassCurve Matrix TensorProduct BigOperators PowerSeries.WithPiTopology

section LocalTameCharacters

open TauCeti ValuativeRel IntermediateField
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} [NeZero n]
    {a : k} {β : AlgebraicClosure k}
    (hn : n.Coprime (ringChar 𝓀[k]))
    (hβ : β ^ n = algebraMap k (AlgebraicClosure k) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure k/k)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)

/-- The discrete tame logarithm is a genuine homomorphism on inertia.
No hypothesis that the entire local Galois group fixes roots of unity is used. -/
def inertiaLog : inertiaSubgroup k →* Multiplicative (ZMod n) where
  toFun σ := Multiplicative.ofAdd (kummerLog hβ hβ0 hζ σ.val)
  map_one' := by
    change kummerLog hβ hβ0 hζ (1 : Gal(AlgebraicClosure k/k)) = 0
    exact kummerLog_of_fix hβ hβ0 hζ (AlgEquiv.one_apply β)
  map_mul' σ τ := by
    let g : Gal(AlgebraicClosure k/k) := σ.val
    let h : Gal(AlgebraicClosure k/k) := τ.val
    change kummerLog hβ hβ0 hζ (g * h) =
      kummerLog hβ hβ0 hζ g + kummerLog hβ hβ0 hζ h
    rw [kummerLog_eq_iff, ZMod.val_add]
    have hm := pow_mod_orderOf (kummerVal β σ₀)
      ((kummerLog hβ hβ0 hζ g).val + (kummerLog hβ hβ0 hζ h).val)
    rw [← hζ.eq_orderOf] at hm
    rw [hm, pow_add, pow_kummerLog, pow_kummerLog,
      kummerVal_mul_of_mem hn hβ hβ0 σ.property]

/-- A finite universal coefficient character obtained from the actual tame
logarithm at an actual inertia group. -/
def tameScalar (i : ℕ)
    (ψ : ZMod n →+ Additive (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ) :
    inertiaSubgroup k →* (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ :=
  (AddMonoidHom.toMultiplicative ψ).comp
    (inertiaLog (hn := hn) (hβ := hβ) (hβ0 := hβ0) (hζ := hζ))

/-- The actual tame generator has the prescribed universal scalar value. -/
theorem tameScalar_generator (i : ℕ) [Fact (1 < n)]
    (ψ : ZMod n →+ Additive (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ)
    (hψ : ((Additive.toMul (ψ 1) : (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ) :
      ZInQ.Manuscript.RC.Moving.Acoef i) = 1 + ZInQ.Manuscript.RC.Moving.tA i)
    (hσ₀ : σ₀ ∈ inertiaSubgroup k) :
    ((tameScalar (hn := hn) (hβ := hβ) (hβ0 := hβ0) (hζ := hζ) i ψ ⟨σ₀, hσ₀⟩ :
      (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ) : ZInQ.Manuscript.RC.Moving.Acoef i) =
      1 + ZInQ.Manuscript.RC.Moving.tA i := by
  change ((Additive.toMul (ψ (kummerLog hβ hβ0 hζ σ₀)) :
    (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ) : ZInQ.Manuscript.RC.Moving.Acoef i) = _
  rw [kummerLog_self hβ hβ0 hζ]
  exact hψ

/-- Finite tame scalar characters and their actual inertia representatives are
constructed from a uniformizer and the existing universal finite character. -/
theorem exists_local_tame_scalar (i d : ℕ) (hid : 2 * i ≤ d) (hd : 0 < d)
    (hcop : (2 ^ d).Coprime (ringChar 𝓀[k])) :
    ∃ χ : inertiaSubgroup k →* (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ,
      ∃ σ : inertiaSubgroup k,
        ((χ σ : (ZInQ.Manuscript.RC.Moving.Acoef i)ˣ) :
          ZInQ.Manuscript.RC.Moving.Acoef i) = 1 + ZInQ.Manuscript.RC.Moving.tA i := by
  letI : NeZero (2 ^ d) := ⟨pow_ne_zero _ two_ne_zero⟩
  letI : Fact (1 < 2 ^ d) := ⟨Nat.one_lt_two_pow hd.ne'⟩
  obtain ⟨π, hπ⟩ := exists_isUniformizer k
  have hπv : (normalizedValuation k (Units.mk0 (π : k) π.ne_zero)).toAdd = 1 := by
    rw [show Units.mk0 (π : k) π.ne_zero = π from Units.ext rfl, (isUniformizer_def π).1 hπ,
      toAdd_ofAdd]
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) (π : k))
    (Nat.pos_of_ne_zero (NeZero.ne (2 ^ d)))
  have hγ0 : γ ≠ 0 := by
    intro h
    have hh := hγ
    rw [h, zero_pow (by positivity)] at hh
    exact π.ne_zero ((map_eq_zero _).mp hh.symm)
  obtain ⟨σ, hσ, hprim⟩ := exists_tame_generator hcop hγ hγ0 π.ne_zero hπv
  obtain ⟨ψ, hψ⟩ := ZInQ.Manuscript.RC.Moving.exists_psi i d hid
  refine ⟨tameScalar (hn := hcop) (hβ := hγ) (hβ0 := hγ0) (hζ := hprim) i ψ, ⟨σ, hσ⟩, ?_⟩
  apply tameScalar_generator
  simpa using hψ 1

end LocalTameCharacters

section FixedSupportInertia

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (α : GKS K S →* Lambdaˣ)

/-- At the derivative places of a moving label, the fixed-support coefficient
character is trivial on inertia. Tame cochain coordinates do not change this. -/
theorem movingLabel_character_on_inertia (L : MovingLabel K S)
    (σ : ∀ i, Gloc K (L.q i)) (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) (i : ℕ) :
    α (locMap K S (L.q i) (σ i)) = 1 := by
  rw [L.hψ i, hσ i, map_one, map_one]

/-- Any scalar sequence obtained from those fixed-support inertia characters
has limiting scalar one, even when the local tame cohomology is nontrivial. -/
theorem movingLabel_inertia_scalar_limit (L : MovingLabel K S)
    (σ : ∀ i, Gloc K (L.q i)) (hσ : ∀ i, urRes K (L.q i) (σ i) = 1)
    (U : Ultrafilter ℕ) :
    ulim U (fun i => ((α (locMap K S (L.q i) (σ i)) : Lambdaˣ) : Lambda)) = 1 := by
  have h : (fun i => ((α (locMap K S (L.q i) (σ i)) : Lambdaˣ) : Lambda)) =
      fun _ => (1 : Lambda) := by
    funext i
    rw [movingLabel_character_on_inertia S α L σ hσ i, Units.val_one]
  rw [h, ulim_const]

end FixedSupportInertia

section InertiaBindingObstruction

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hdegree : Module.finrank ℚ K = 2) (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]

/-- Derivative-label inertia cannot furnish the nonquadratic coefficient
inertia input for the fixed-support character. Conductor inertia is different. -/
theorem derivative_inertia_cannot_supply_nonquadratic
    (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1)
    (I : NonquadraticInertiaInput (S := S) (e := e) (α := α) (E := E) (C := C)
      (hdegree := hdegree) (U := U) (P := P))
    (htie : ∀ i, baseRestriction S e (I.element i) = locMap K S (L.q i) (σ i)) : False := by
  apply I.nonquadratic
  have hf : (fun i => ((α (baseRestriction S e (I.element i)) : Lambdaˣ) : Lambda)) =
      fun i => ((α (locMap K S (L.q i) (σ i)) : Lambdaˣ) : Lambda) := by
    funext i
    rw [htie i]
  rw [hf, movingLabel_inertia_scalar_limit S α L σ hσ U, map_one, one_pow]

end InertiaBindingObstruction

section IntegralTameNormalization

/-- The universal integral parameter is not fixed by a nontrivial residue
cardinality power. Finite moving characters must be treated at their precision. -/
theorem universal_parameter_power_ne_self (q : ℕ) (hq : 1 < q) :
    (1 + (PowerSeries.X : Lambda)) ^ q ≠ 1 + PowerSeries.X := by
  intro he
  have hc := congrArg (PowerSeries.coeff 1) he
  have hn : (q : ℤ_[2]) = 1 := by
    simpa [PowerSeries.coeff_one_pow] using hc
  have hq1 : q = 1 := by exact_mod_cast hn
  omega

/-- A coefficient-valued homomorphism with the tame Frobenius relation cannot
send inertia to the infinite universal parameter at one fixed odd place. -/
theorem no_integral_fixed_tame_normalization {G : Type} [Group G]
    (χ : G →* Lambdaˣ) (φ σ : G) (q : ℕ) (hq : 1 < q)
    (hrel : χ (φ * σ * φ⁻¹) = χ σ ^ q)
    (hval : ((χ σ : Lambdaˣ) : Lambda) = 1 + PowerSeries.X) : False := by
  have hconj : χ (φ * σ * φ⁻¹) = χ σ := by
    simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
  have hp : χ σ ^ q = χ σ := hrel.symm.trans hconj
  have hv := congrArg (fun u : Lambdaˣ => (u : Lambda)) hp
  apply universal_parameter_power_ne_self q hq
  simpa only [Units.val_pow_eq_pow_val, hval] using hv

/-- Normalized finite character values determine the integral scalar limit
before specialization; no compatibility of arbitrary coefficient lifts is needed. -/
theorem scalar_limit_of_finite_normalization (v : ℕ → Lambda)
    (hv : ∀ i, v i - (1 + PowerSeries.X) ∈ stageIdeal i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U v = 1 + PowerSeries.X := by
  have hm : ulimMat U (fun i => (fun _ _ : Fin 1 => v i : Matrix (Fin 1) (Fin 1) Lambda)) =
      ulimMat U (fun _ => (fun _ _ : Fin 1 => 1 + PowerSeries.X : Matrix (Fin 1) (Fin 1) Lambda)) :=
    ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU (Eventually.of_forall (fun i _ _ => hv i))
  have h := congrFun (congrFun hm 0) 0
  change ulim U v = ulim U (fun _ => (1 + PowerSeries.X : Lambda)) at h
  rw [ulim_const] at h
  exact h

end IntegralTameNormalization

section NonquadraticSpecialization

/-- Elements outside the chosen prime remain units in its residue field. -/
theorem residue_unit_of_not_mem (P : Ideal Lambda) [P.IsPrime] (a : Lambda) (ha : a ∉ P) :
    IsUnit (algebraMap Lambda (ResAt P) a) := by
  have hu := (IsLocalization.map_units (Localization.AtPrime P)
    (⟨a, ha⟩ : P.primeCompl)).map (algebraMap (Localization.AtPrime P) (ResAt P))
  rw [IsScalarTower.algebraMap_apply Lambda (Localization.AtPrime P) (ResAt P) a]
  exact hu

/-- The nonquadratic fibre condition is the prime exclusion of `t(t+2)`.
It is a coefficient condition, not an evaluation of a cohomology class. -/
theorem nonquadratic_parameter_of_not_mem (P : Ideal Lambda) [P.IsPrime]
    (hP : (PowerSeries.X : Lambda) * (PowerSeries.X + 2) ∉ P) :
    (algebraMap Lambda (ResAt P) (1 + PowerSeries.X)) ^ 2 ≠ 1 := by
  intro he
  have hu := residue_unit_of_not_mem P _ hP
  have hz : algebraMap Lambda (ResAt P) ((PowerSeries.X : Lambda) * (PowerSeries.X + 2)) = 0 := by
    rw [map_mul, map_add, map_ofNat]
    have hh : (1 + algebraMap Lambda (ResAt P) PowerSeries.X) ^ 2 = 1 := by
      simpa only [map_add, map_one] using he
    linear_combination hh
  exact hu.ne_zero hz

/-- Finite normalized tame values construct the nonquadratic scalar after
integral limits and specialization. -/
theorem nonquadratic_limit_of_finite_normalization (v : ℕ → Lambda)
    (hv : ∀ i, v i - (1 + PowerSeries.X) ∈ stageIdeal i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime]
    (hP : (PowerSeries.X : Lambda) * (PowerSeries.X + 2) ∉ P) :
    (algebraMap Lambda (ResAt P) (ulim U v)) ^ 2 ≠ 1 := by
  rw [scalar_limit_of_finite_normalization v hv U hU]
  exact nonquadratic_parameter_of_not_mem P hP

end NonquadraticSpecialization

section RationalLocalLifts

variable {K : Type} [Field K] [NumberField K]
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- Transport of an actual absolute Galois element to the rational fixing subgroup. -/
def rationalAbsoluteLift : Gal(AlgebraicClosure K/K) →* rationalBaseGroup e where
  toFun g := ⟨(e.symm.trans (g.restrictScalars ℚ)).trans e, fun x => by
    change e (g (e.symm (e (algebraMap K (AlgebraicClosure K) x)))) = _
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.commutes]⟩
  map_one' := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    simp [AlgEquiv.trans_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    simp [AlgEquiv.trans_apply, AlgEquiv.mul_apply]

/-- The transport is inverse to the existing actual rational restriction. -/
theorem galKOfQ_rationalAbsoluteLift (g : Gal(AlgebraicClosure K/K)) :
    galKOfQ e (rationalAbsoluteLift e g).val (rationalAbsoluteLift e g).property = g := by
  apply AlgEquiv.ext
  intro x
  change e.symm (e (g (e.symm (e x)))) = g x
  simp

/-- An actual local Galois element gives an actual rational representative. -/
def rationalLocalLift (q : HeightOneSpectrum (𝓞 K)) : Gloc K q →* rationalBaseGroup e :=
  (rationalAbsoluteLift e).comp (decompMap K q).toMonoidHom

/-- The fixed-support image of this rational representative is actual localization. -/
theorem baseRestriction_rationalLocalLift (S : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (σ : Gloc K q) :
    baseRestriction S e (rationalLocalLift e q σ) = locMap K S q σ := by
  let g : Gal(AlgebraicClosure K/K) := decompMap K q σ
  change gksOfQ S e (rationalAbsoluteLift e g).val (rationalAbsoluteLift e g).property = _
  unfold gksOfQ
  exact congrArg (fun h : Gal(AlgebraicClosure K/K) => resAbsCont K S h)
    (galKOfQ_rationalAbsoluteLift e g)

/-- Local inertia at a prime outside a support is in the actual kernel of the
fixed-support rational restriction. This statement is about Galois elements. -/
theorem rationalLocalLift_kernel_outside (S : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) (σ : Gloc K q)
    (hσ : urRes K q σ = 1) : baseRestriction S e (rationalLocalLift e q σ) = 1 := by
  obtain ⟨ψ, hψ⟩ := unramifiedAtFactorization K S q hq
  rw [baseRestriction_rationalLocalLift, hψ, hσ, map_one]

end RationalLocalLifts

section CharacterCutoutFields

/-- The field fixed by the actual kernel of a quadratic-subgroup character. -/
def characterCutout {A : Type} [CommGroup A] (H : Subgroup GalQ) (β : H →* A) :
    IntermediateField ℚ Qbar := IntermediateField.fixedField (Subgroup.map H.subtype β.ker)

/-- The missing cutout comparison is exactly that the actual character kernel
fixes the proposed field. The reverse implication is not supplied merely by a
field detecting a character at finite precision. -/
theorem le_characterCutout_iff {A : Type} [CommGroup A] (H : Subgroup GalQ)
    (β : H →* A) (F : IntermediateField ℚ Qbar) :
    F ≤ characterCutout H β ↔ ∀ g : H, β g = 1 → ∀ x ∈ F, g.val x = x := by
  constructor
  · intro h g hg x hx
    exact (IntermediateField.mem_fixedField_iff (Subgroup.map H.subtype β.ker) x).mp (h hx)
      g.val ⟨g, MonoidHom.mem_ker.mpr hg, rfl⟩
  · intro h x hx
    rw [characterCutout, IntermediateField.mem_fixedField_iff]
    rintro f ⟨g, hg, rfl⟩
    exact h g (MonoidHom.mem_ker.mp hg) x hx

/-- Inversion of the actual character under conjugation proves inversion on
its kernel-cutout field. No field-inversion conclusion is taken as input. -/
theorem inversion_on_characterCutout {A : Type} [CommGroup A]
    (H : Subgroup GalQ) [H.Normal] (τ : GalQ) (β : H →* A)
    (hβ : ∀ g : H, β ⟨τ * g.val * τ⁻¹,
      (inferInstance : H.Normal).conj_mem g.val g.property τ⟩ = (β g)⁻¹)
    (g : H) (x : Qbar) (hx : x ∈ characterCutout H β) :
    (τ * g.val * τ⁻¹) x = g.val⁻¹ x := by
  let cg : H := ⟨τ * g.val * τ⁻¹,
    (inferInstance : H.Normal).conj_mem g.val g.property τ⟩
  have hker : g * cg ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    change β g * β cg = 1
    rw [hβ g, mul_inv_cancel]
  have hmap : g.val * cg.val ∈ Subgroup.map H.subtype β.ker :=
    ⟨g * cg, hker, rfl⟩
  have he := (IntermediateField.mem_fixedField_iff (Subgroup.map H.subtype β.ker) x).mp hx
    (g.val * cg.val) hmap
  have h := congrArg (fun y : Qbar => g.val.symm y) he
  change g.val.symm (g.val (cg.val x)) = g.val.symm x at h
  change cg.val x = g.val.symm x
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- Agreement of two actual automorphisms on fields is preserved by compositum. -/
theorem automorphisms_agree_on_sup (F L : IntermediateField ℚ Qbar) (σ θ : GalQ)
    (hF : ∀ x ∈ F, σ x = θ x) (hL : ∀ x ∈ L, σ x = θ x) :
    ∀ x ∈ F ⊔ L, σ x = θ x := by
  have hf : θ⁻¹ * σ ∈ F.fixingSubgroup := by
    intro x
    change θ⁻¹ (σ x) = x
    rw [hF x x.property]
    simp
  have hl : θ⁻¹ * σ ∈ L.fixingSubgroup := by
    intro x
    change θ⁻¹ (σ x) = x
    rw [hL x x.property]
    simp
  have hs : θ⁻¹ * σ ∈ (F ⊔ L).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hf, hl⟩
  intro x hx
  have he := hs ⟨x, hx⟩
  change θ⁻¹ (σ x) = x at he
  simpa using congrArg (fun y : Qbar => θ y) he

/-- Two character-cutout bounds construct the chosen-field dihedral input.
The remaining comparison is field containment, not a class-evaluation condition. -/
theorem dihedralKernelFields_of_cutout_bounds
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hdegree : Module.finrank ℚ K = 2)
    (A D : ℕ → Type) [∀ i, CommGroup (A i)] [∀ i, CommGroup (D i)]
    (β : ∀ i, rationalBaseGroup e →* A i) (δ : ∀ i, rationalBaseGroup e →* D i)
    (hβ : ∀ i g, β i (baseConjugate (S := S) (e := e) (C := C) (hdegree := hdegree) g) = (β i g)⁻¹)
    (hδ : ∀ i g, δ i (baseConjugate (S := S) (e := e) (C := C) (hdegree := hdegree) g) = (δ i g)⁻¹)
    (B : ℕ → IntermediateField ℚ Qbar)
    (hcharacter : ∀ i, ZInQ.Contrib.RC53Assist.FrobeniusMatch.characterField S e α i ≤
      characterCutout (rationalBaseGroup e) (β i))
    (harithmetic : ∀ i, B i ≤ characterCutout (rationalBaseGroup e) (δ i)) :
    DihedralKernelFields S e α C B := by
  letI : (rationalBaseGroup e).Normal :=
    Subgroup.normal_of_index_eq_two (rationalBaseGroup_index_two e hdegree)
  intro i g x hx
  apply automorphisms_agree_on_sup
    (ZInQ.Contrib.RC53Assist.FrobeniusMatch.characterField S e α i) (B i)
    (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * g.val *
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)⁻¹) g.val⁻¹
  · intro y hy
    exact inversion_on_characterCutout (rationalBaseGroup e)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C) (β i) (hβ i) g y (hcharacter i hy)
  · intro y hy
    exact inversion_on_characterCutout (rationalBaseGroup e)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C) (δ i) (hδ i) g y (harithmetic i hy)
  · exact hx

/-- Conjugation acting by inversion forces its character-image group to be
abelian. Normal finite fields with nonabelian restriction image cannot be
silently used as dihedral kernel fields. -/
theorem image_commutative_of_conjugate_inversion {G J : Type} [Group G] [Group J]
    (ρ : G →* J) (τ : J) (hi : ∀ g, τ * ρ g * τ⁻¹ = (ρ g)⁻¹) (g h : G) :
    ρ g * ρ h = ρ h * ρ g := by
  have he : (ρ g)⁻¹ * (ρ h)⁻¹ = (ρ h)⁻¹ * (ρ g)⁻¹ := by
    calc
      (ρ g)⁻¹ * (ρ h)⁻¹ = (τ * ρ g * τ⁻¹) * (τ * ρ h * τ⁻¹) := by rw [hi, hi]
      _ = τ * ρ (g * h) * τ⁻¹ := by rw [map_mul]; group
      _ = (ρ (g * h))⁻¹ := hi (g * h)
      _ = (ρ h)⁻¹ * (ρ g)⁻¹ := by rw [map_mul, mul_inv_rev]
  have hi' := congrArg (fun z : J => z⁻¹) he
  simpa only [mul_inv_rev, inv_inv] using hi'.symm

end CharacterCutoutFields

section RetainedModelMaps

open ZInQ.Manuscript.RC.FibreDuality

/-- The finite model and its original cochain comparison are retained together
with the matrix diagram computed from precisely that model. -/
structure ModelDiagram {A : Type} [CommRing A] {G : GCx A} (P : StagePairingInput G) where
  model : GradedModel G
  diagram : StageMatrixDiagram A model.rank
  differential : diagram.dC = model.dC
  localization : diagram.res = modelRes model P
  global_pairing : diagram.glob = modelGlob model P
  local_pairing : diagram.loc = P.loc

/-- Positive-stage model production without erasing the inclusion, projection,
and homotopy connecting it to the actual arithmetic complex. -/
theorem modelDiagram_from_stage_inputs (i : ℕ) [NeZero i] (G : GCx (StageA i))
    (hflat : ∀ n, Module.Flat (StageA i) (G.X n))
    {Uq : GCx (StageA i)} {res : GHom G (ZInQ.Contrib.RC53Assist.InnerLimit.splitLocalComplex (StageA i))}
    {ι : GHom Uq (ZInQ.Contrib.RC53Assist.InnerLimit.splitLocalComplex (StageA i))}
    (Q : SelPairData (splitSelData G res Uq ι) (splitSelData G res Uq ι))
    (tr : (coneCx Q.resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hdual : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)))
    (hres : ResidualCohomologyFinite G) (lo hi : ℤ)
    (hbdd : ∀ n, n < lo ∨ hi < n →
      Module.finrank (IsLocalRing.ResidueField (StageA i)) (residualCohomologyAt G n) = 0) :
    ∃ D : ModelDiagram (stagePairingInputOfSel Q tr htr),
      ∀ n, D.model.rank n = Module.finrank (IsLocalRing.ResidueField (StageA i)) (residualCohomologyAt G n) := by
  letI : ∀ n, Module.Flat (StageA i) (G.X n) := hflat
  obtain ⟨R, hR⟩ := exists_gradedModel (stageA_isNilpotent_maximalIdeal i) G
    (finite_residualCohomologyAt_of hres)
  have hr : ∀ n, n < lo ∨ hi < n → R.rank n = 0 := fun n hn => (hR n).trans (hbdd n hn)
  obtain ⟨S, hd, hloc, hglob, hlocal⟩ := exists_stageMatrixDiagram R
    (stagePairingInputOfSel Q tr htr) (quasiIso_stageDualityMap_of_global Q tr htr hdual) lo hi hr
  exact ⟨⟨R, S, hd, hloc, hglob, hlocal⟩, hR⟩

/-- A cochain retract reflects every actual boundary. This uses the projection
and its cochain identity, not surjectivity of the model's degree-zero inclusion. -/
theorem boundary_reflection_of_retract {A : Type} [CommRing A] {G Q : GCx A}
    (R : GRetract G Q) (x : Q.X 1) (y : G.X 0)
    (hxy : R.i.f 1 1 rfl x = G.d 0 1 rfl y) : x ∈ LinearMap.range (Q.d 0 1 rfl) := by
  refine ⟨R.p.f 0 0 rfl y, ?_⟩
  have he := congrArg (R.p.f 1 1 rfl) hxy
  rw [R.p_i, R.p.comm 0 1 0 1 rfl rfl rfl rfl] at he
  exact he.symm

/-- The model inclusion is injective in every degree because its projection
is a left inverse. -/
theorem model_inclusion_injective {A : Type} [CommRing A] {G Q : GCx A}
    (R : GRetract G Q) (n : ℤ) : Function.Injective (R.i.f n n rfl) := by
  intro x y he
  have h := congrArg (R.p.f n n rfl) he
  simpa only [R.p_i] using h

end RetainedModelMaps

section ArithmeticModelExport

open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Contrib.RC53Assist.RetainedAssembly

variable {K : Type} [Field K] [NumberField K]
    {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
    {α : ∀ i, GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ}
    [∀ i, ZInQ.Manuscript.RC.CoefModules.IsOpenKer (α i)]
    [HasFullTwoTorsion K S₀ W]
    {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
    {R : StandardOldReference S₀ W α} {width : ℕ}

/-- The actual assembled arithmetic inputs construct model/cochain exports at
every positive stage, using the same produced pairing as the retained supplier. -/
theorem actual_stage_model_exports (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] :
    ∃ D : ModelDiagram (stagePairingInputOfSel
      (producedStages a p hK hS₀ h2 i).pairing
      (producedStages a p hK hS₀ h2 i).trace
      (producedStages a p hK hS₀ h2 i).trace_kills),
      ∀ n, D.model.rank n = Module.finrank (IsLocalRing.ResidueField (StageA i))
        (residualCohomologyAt (F.globalCx i) n) := by
  obtain ⟨B, hbdd, hB⟩ := a.residualSupport.producerBounds p hK hS₀ h2
  exact modelDiagram_from_stage_inputs i (F.globalCx i) (F.flat hS₀ a.oldFlat i)
    (producedStages a p hK hS₀ h2 i).pairing
    (producedStages a p hK hS₀ h2 i).trace
    (producedStages a p hK hS₀ h2 i).trace_kills
    (producedStages a p hK hS₀ h2 i).duality
    (a.residualSupport.residual_finite p hS₀ h2 i) 0 3 (hbdd i)

end ArithmeticModelExport

section RetainedTargetComparison

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- Sufficient retained comparison data without degree-zero surjectivity of
the finite model. The target evaluation maps belong to the actual comparison
complex, and its projection reflects boundaries in the retained model. -/
structure RetainedTargetComparison (n : ℕ) (Q : GCx (ResAt P)) where
  target : GCx (ResAt P)
  retract : GRetract target Q
  evalZero : target.X 0 →ₗ[ResAt P] FibrePair P
  evalOne : target.X 1 →ₗ[ResAt P] (RationalSequences → FibrePair P)
  evalTwo : target.X 2 →ₗ[ResAt P] (RationalSequences × RationalSequences → FibrePair P)
  degree_zero : ∀ x g, evalOne (target.d 0 1 rfl x) g = g • evalZero x - evalZero x
  degree_one : ∀ x g h, evalTwo (target.d 1 2 rfl x) (g, h) =
    g • evalOne x h - evalOne x (g * h) + evalOne x g
  zero_surjective : Function.Surjective evalZero
  one_injective : Function.Injective evalOne
  original : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1
  coordinates : Q.X 1 →ₗ[ResAt P] (Fin n → ResAt P)
  normalized : ∀ x (g : ℕ → rationalBaseGroup e),
    (evalOne (retract.i.f 1 1 rfl x) (baseSequenceInclusion e g)).1 =
      basisValue P U original (baseSequenceRestriction S e g) (coordinates x)

/-- Boundary reflection comes from the retained cochain projection. The
model's degree-zero map need not cover the whole coefficient module. -/
theorem principal_boundary_from_target {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedTargetComparison (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (x : Q.X 1) (hx : groupCohomology.IsCoboundary₁ (D.evalOne (D.retract.i.f 1 1 rfl x))) :
    x ∈ LinearMap.range (Q.d 0 1 rfl) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨y, hy⟩ := D.zero_surjective m
  have he : D.retract.i.f 1 1 rfl x = D.target.d 0 1 rfl y := by
    apply D.one_injective
    funext g
    rw [D.degree_zero, hy]
    exact (hm g).symm
  exact boundary_reflection_of_retract D.retract x y he

/-- Retained evaluation constructed from actual cochain comparison maps and
their homotopy-retract projection, rather than an assumed H¹ condition. -/
def retainedEvaluation_from_target {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedTargetComparison (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) :
    RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q where
  original := D.original
  coordinates := D.coordinates
  one := D.evalOne.comp (D.retract.i.f 1 1 rfl)
  two := D.evalTwo.comp (D.retract.i.f 2 2 rfl)
  cochain_identity x g h := by
    change D.evalTwo (D.retract.i.f 2 2 rfl (Q.d 1 2 rfl x)) (g, h) = _
    rw [D.retract.i.comm 1 2 1 2 rfl rfl rfl rfl]
    exact D.degree_one (D.retract.i.f 1 1 rfl x) g h
  principal_boundary x _ hx := principal_boundary_from_target S e α E U P D x hx
  projection := D.normalized

/-- Degree-zero boundary preservation for the constructed retained map. -/
theorem target_degree_zero_identity {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedTargetComparison (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (x : Q.X 0) (g : RationalSequences) :
    (retainedEvaluation_from_target S e α E U P D).one (Q.d 0 1 rfl x) g =
      g • D.evalZero (D.retract.i.f 0 0 rfl x) - D.evalZero (D.retract.i.f 0 0 rfl x) := by
  change D.evalOne (D.retract.i.f 1 1 rfl (Q.d 0 1 rfl x)) g = _
  rw [D.retract.i.comm 0 1 0 1 rfl rfl rfl rfl]
  exact D.degree_zero _ g

/-- The literal earlier embedding record is available when the additional
model degree-zero surjectivity is proved. This is not inferred from a retract. -/
def embedding_from_target {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedTargetComparison (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (h0 : Function.Surjective (D.evalZero.comp (D.retract.i.f 0 0 rfl))) :
    RetainedCochainEmbedding (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q where
  original := D.original
  coordinates := D.coordinates
  zero := D.evalZero.comp (D.retract.i.f 0 0 rfl)
  one := D.evalOne.comp (D.retract.i.f 1 1 rfl)
  two := D.evalTwo.comp (D.retract.i.f 2 2 rfl)
  differential_zero := target_degree_zero_identity S e α E U P D
  differential_one := (retainedEvaluation_from_target S e α E U P D).cochain_identity
  zero_surjective := h0
  one_injective := D.one_injective.comp (model_inclusion_injective D.retract 1)
  original_projection := D.normalized

/-- The earlier stronger embedding criterion forces at least four dimensions
in degree zero. A homotopy retract alone does not provide that requirement. -/
theorem embedding_requires_degree_zero_dimension {n : ℕ} {Q : GCx (ResAt P)}
    [FiniteDimensional (ResAt P) (Q.X 0)]
    (D : RetainedCochainEmbedding (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) :
    4 ≤ Module.finrank (ResAt P) (Q.X 0) := by
  have h := LinearMap.finrank_le_finrank_of_surjective D.zero_surjective
  simpa [FibrePair, Module.finrank_prod, Module.finrank_pi] using h

/-- A retained model with degree-zero rank below four cannot satisfy the
stronger embedding interface, regardless of its H¹ comparison. -/
theorem no_embedding_of_small_degree_zero {n : ℕ} {Q : GCx (ResAt P)}
    [FiniteDimensional (ResAt P) (Q.X 0)]
    (hr : Module.finrank (ResAt P) (Q.X 0) < 4) :
    IsEmpty (RetainedCochainEmbedding (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) := by
  refine ⟨fun D => ?_⟩
  exact (not_le_of_gt hr) (embedding_requires_degree_zero_dimension S e α E U P D)

end RetainedTargetComparison

section FirstCohomologyComparison

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- Boundary preservation plus proved boundary reflection gives a genuine
injective map on first cohomology; degree-zero surjectivity of the retained
model is not required. -/
theorem h1_map_of_boundary_preservation {n : ℕ} {Q : GCx (ResAt P)}
    (V : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (zero : Q.X 0 →ₗ[ResAt P] FibrePair P)
    (hzero : ∀ y g, V.one (Q.d 0 1 rfl y) g = g • zero y - zero y) :
    ∃ F : Q.toCC.homology 1 →ₗ[ResAt P]
      groupCohomology.H1 (Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P)),
      Function.Injective F ∧ ∀ a : LinearMap.ker (Q.d 1 2 rfl),
        F (clsAt Q 1 2 rfl a) = groupCohomology.H1π
          (Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P))
          (groupCohomology.cocyclesOfIsCocycle₁ (RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) V a)) := by
  let A := Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P)
  let f : LinearMap.ker (Q.d 1 2 rfl) →ₗ[ResAt P] groupCohomology.cocycles₁ A :=
    { toFun a := groupCohomology.cocyclesOfIsCocycle₁ (RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) V a)
      map_add' a b := Subtype.ext (V.one.map_add a.val b.val)
      map_smul' r a := Subtype.ext (V.one.map_smul r a.val) }
  let v := (groupCohomology.H1π A).hom.comp f
  have hb (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a = 0) : v a = 0 := by
    obtain ⟨y, hy⟩ := clsAt_eq_zero Q 0 1 2 rfl rfl a ha
    change groupCohomology.H1π A (f a) = 0
    rw [groupCohomology.H1π_eq_zero_iff]
    refine ⟨zero y, ?_⟩
    funext g
    change g • zero y - zero y = V.one a.val g
    rw [← hy, hzero]
  obtain ⟨F, hF⟩ := exists_factor_of_surjective (clsAt Q 1 2 rfl)
    (clsAt_surjective Q 1 2 rfl) v hb
  refine ⟨F, ?_, hF⟩
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro w hw
  change w = 0
  obtain ⟨a, rfl⟩ := clsAt_surjective Q 1 2 rfl w
  have hva : v a = 0 := (hF a).symm.trans (LinearMap.mem_ker.mp hw)
  change groupCohomology.H1π A (f a) = 0 at hva
  rw [groupCohomology.H1π_eq_zero_iff] at hva
  obtain ⟨m, hm⟩ := hva
  have hprincipal : groupCohomology.IsCoboundary₁ (V.one a.val) :=
    ⟨m, fun g => congrFun hm g⟩
  obtain ⟨y, hy⟩ := V.principal_boundary a.val a.property hprincipal
  have he : a = ⟨Q.d 0 1 rfl y, LinearMap.mem_ker.mpr (Q.d_d 0 1 2 rfl rfl y)⟩ :=
    Subtype.ext hy.symm
  rw [he]
  exact clsAt_boundary Q 0 1 2 rfl rfl y

/-- The target-comparison construction supplies the actual injective H¹ map
with its represented-cycle identity. Both differential degrees are preserved. -/
theorem h1_map_from_retained_target {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedTargetComparison (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) :
    ∃ F : Q.toCC.homology 1 →ₗ[ResAt P]
      groupCohomology.H1 (Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P)),
      Function.Injective F ∧ ∀ a : LinearMap.ker (Q.d 1 2 rfl),
        F (clsAt Q 1 2 rfl a) = groupCohomology.H1π
          (Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P))
          (groupCohomology.cocyclesOfIsCocycle₁
            (RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
              (U := U) (P := P) (retainedEvaluation_from_target S e α E U P D) a)) := by
  apply h1_map_of_boundary_preservation S e α E U P
    (retainedEvaluation_from_target S e α E U P D)
    (D.evalZero.comp (D.retract.i.f 0 0 rfl))
  exact target_degree_zero_identity S e α E U P D

end FirstCohomologyComparison

end ZInQ.Contrib.RC53Assist.Detection.Actual
