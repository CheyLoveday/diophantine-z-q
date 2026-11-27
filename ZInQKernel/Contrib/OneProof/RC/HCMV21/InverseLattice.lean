import ZInQKernel.Contrib.OneProof.RC.HCMV21.ShimuraJ

/-! The inverse-ideal action, in the actual finite adeles at conductor one.
The ideal of a finite idele is read with positive valuation; the lattice
whose points have integral translates is read with the inverse. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors

section NumberField
variable {F : Type*} [Field F] [NumberField F]

local notation "Af" => FiniteAdeleRing (𝓞 F) F
local notation "ι" => algebraMap F Af

/-- The completed lattice with local generator `t` at each place. -/
def completedIdeal (t : Afˣ) : Set Af :=
  {z | ((t⁻¹ : Afˣ) : Af) * z ∈ integralAdeles (𝓞 F) F}

omit [NumberField F] in
private theorem inv_mul_le_one (u : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (J : FractionalIdeal (𝓞 F)⁰ F) :
    (↑u⁻¹ : FractionalIdeal (𝓞 F)⁰ F) * J ≤ 1 ↔ J ≤ ↑u := by
  constructor
  · intro h
    have h' := mul_le_mul_right h (u : FractionalIdeal (𝓞 F)⁰ F)
    rwa [← mul_assoc, Units.mul_inv, one_mul, mul_one] at h'
  · intro h
    have h' := mul_le_mul_right h (↑u⁻¹ : FractionalIdeal (𝓞 F)⁰ F)
    rwa [Units.inv_mul] at h'

/-- Diagonal intersection recovers the fractional ideal of the idele. -/
theorem mem_completedIdeal_algebraMap_iff (t : Afˣ) (x : F) :
    ι x ∈ completedIdeal t ↔ x ∈ (toFractionalIdeal t).val := by
  change ((t⁻¹ : Afˣ) : Af) * ι x ∈ integralAdeles (𝓞 F) F ↔ _
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, mul_zero]
    exact iff_of_true ((integralAdeles (𝓞 F) F).zero_mem) ((toFractionalIdeal t).val.zero_mem)
  let xU : Fˣ := Units.mk0 x hx
  have hmul : ((t⁻¹ : Afˣ) : Af) * ι x =
      ((t⁻¹ * unitEmbedding (𝓞 F) F xU : Afˣ) : Af) := by
    rw [Units.val_mul, unitEmbedding_apply]
    rfl
  rw [hmul, ← toFractionalIdeal_le_one_iff, map_mul, map_inv,
    toFractionalIdeal_unitEmbedding, Units.val_mul, inv_mul_le_one,
    coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_le_iff_mem]
  rfl

/-- The coordinatewise lattice is the completion of the corresponding
fractional ideal. Density suffices because the integral adeles are open
and closed. -/
theorem closure_fractionalIdeal_eq_completedIdeal (t : Afˣ) :
    closure (ι '' ((toFractionalIdeal t).val : Set F)) = completedIdeal t := by
  have hc : IsClosed (completedIdeal t) :=
    (isClosed_integralAdeles (𝓞 F) F).preimage (continuous_const.mul continuous_id)
  have ho : IsOpen (completedIdeal t) :=
    (isOpen_integralAdeles (𝓞 F) F).preimage (continuous_const.mul continuous_id)
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ hc
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_completedIdeal_algebraMap_iff t x).2 hx
  · intro z hz
    apply mem_closure_iff_nhds.mpr
    intro U hU
    have hz' := (denseRange_algebraMap (𝓞 F) F) z
    obtain ⟨_, ⟨hyU, hyt⟩, x, rfl⟩ :=
      mem_closure_iff_nhds.mp hz' (U ∩ completedIdeal t) (Filter.inter_mem hU (ho.mem_nhds hz))
    exact ⟨ι x, hyU, x, (mem_completedIdeal_algebraMap_iff t x).1 hyt, rfl⟩

/-- Normalization of a translate at an arbitrary fractional-ideal reference
lattice. On completion, multiplying by the idele moves the integrality
condition by its inverse. -/
theorem mem_completedIdeal_mul_iff (s t : Afˣ) (z : Af) :
    (s : Af) * z ∈ completedIdeal t ↔ z ∈ completedIdeal (t * s⁻¹) := by
  change ((t⁻¹ : Afˣ) : Af) * ((s : Af) * z) ∈ integralAdeles (𝓞 F) F ↔
    ((((t * s⁻¹)⁻¹ : Afˣ) : Af) * z) ∈ integralAdeles (𝓞 F) F
  rw [mul_inv_rev, inv_inv, Units.val_mul]
  rw [← mul_assoc, mul_comm (t⁻¹ : Afˣ).val]

end NumberField

open T5Glue TauCeti.GlobalNumberFields
open ZInQ.RouteK.Rank5b

/-- Read the inverse lattice in the existing Shimura statement. The
reference `I` is an arbitrary fractional ideal, so its scaling
or its class need not be normalized to one. -/
theorem sInvLat_eq_div_fractionalIdeal (m : ℕ) [NeZero m]
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m))
    (I : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m)) (hI : I ≠ 0) :
    sInvLat m s (I : Set (QNeg m)) =
      ((I / (toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s)).val) :
        Set (QNeg m)) := by
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective (Units.mk0 I hI)
  let u := IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s
  have htv : (toFractionalIdeal t).val = I := congrArg Units.val ht
  have hval : (toFractionalIdeal (t * u⁻¹)).val =
      I / (toFractionalIdeal u).val := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, htv, div_eq_mul_inv]
  ext x
  change finPart s * algebraMap (QNeg m) (AfK m) x ∈ latHat m (I : Set (QNeg m)) ↔ _
  rw [← coe_toFiniteIdele, latHat, ← htv, closure_fractionalIdeal_eq_completedIdeal,
    mem_completedIdeal_mul_iff, mem_completedIdeal_algebraMap_iff, hval, htv]
  rfl

open TauCeti.ClassFieldTheory
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.Shimura
open ZInQ.Contrib.TYZGenus.CM (ιC)

/-- A fixed idele has a complex automorphism over its absolute Artin
symbol. This is the direction needed when the ideal representative has
already been chosen. -/
theorem exists_complexArtinCond (m : ℕ) [NeZero m]
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ∃ σ : ℂ ≃+* ℂ, ArtinCond m e σ s := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (absArt (QNeg m) (icl s))
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend (ιC.comp e.toRingHom)
    ((τ : TauCeti.AbsoluteGaloisGroup (QNeg m))).toRingEquiv
  refine ⟨σ, artinCond_of_abs e σ τ hσ s ?_⟩
  exact (congrArg Additive.ofMul hτ).trans (ofMul_absArt (QNeg m) (icl s))

/-- The arithmetic ideal formula with the inverse-lattice convention
discharged. This consumes the existing Shimura statement and identifies
the analytic translated period relative to the supplied reference. -/
theorem arithmetic_j_of_shimura (hCM : ShimuraMainCM)
    (m : ℕ) [NeZero m] (hm : Squarefree m)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      Complex.I * (Real.sqrt m : ℂ))
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m))
    (I : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m)) (hI : I ≠ 0) (a : (Ideal (𝓞 (QNeg m)))⁰)
    (hs : toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s) =
      FractionalIdeal.mk0 (QNeg m) a)
    (P Q : PeriodPair) (hP : (P.lattice : Set ℂ) = kappa m '' (I : Set (QNeg m)))
    (hQ : (Q.lattice : Set ℂ) =
      kappa m '' ((I / ((a : Ideal (𝓞 (QNeg m))) : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))) :
        Set (QNeg m)))
    (x : hilbertClassField (QNeg m)) (hx : ιC (e x) = P.jLattice) :
    ιC (e (hilbertClassArtinEquiv (QNeg m) (ClassGroup.mk0 a) x)) = Q.jLattice := by
  obtain ⟨σ, hσ⟩ := exists_complexArtinCond m e s
  refine ideal_j_reciprocity_of_shimura hCM m hm e he σ s hσ I a hs ?_ P Q hP hQ x hx
  rw [sInvLat_eq_div_fractionalIdeal m s I hI, hs]
  rfl

end ZInQ.Manuscript.RC.HCMV21
