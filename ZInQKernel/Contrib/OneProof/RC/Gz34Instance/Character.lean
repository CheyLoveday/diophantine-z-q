import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ChiLocal
import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.Norm.AbsNorm
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.TotallyPositive

/-! The norm character of tex 2413–2414. Descent from integral ideals to
the Picard group by its principal kernel is on-the-spot (c). -/

noncomputable section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields
  TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

private theorem norm_coprime_conductor (hK : Module.finrank ℚ K = 2)
    (I : integralIdealsPrimeTo (conductorOrder K c).conductorModulus) :
    (I : Ideal (𝓞 K)).absNorm.Coprime c := by
  refine Nat.coprime_of_dvd fun p hp hpI hpc => ?_
  obtain ⟨P, hP, hPp, hPI⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ hpI
  have hI := ((conductorOrder K c).mem_integralIdealsPrimeTo_conductorModulus_iff.mp I.2)
  have hP0 : P ≠ ⊥ := fun h => hI.1 (by simpa [h] using Ideal.dvd_iff_le.mp hPI)
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
  have hv : v ∈ primesAbove K p := by
    change ((p : ℤ) : 𝓞 K) ∈ P
    have hpP : (p : ℤ) ∈ P.under ℤ := hPp ▸ Ideal.subset_span (Set.mem_singleton _)
    simpa using hpP
  exact hP.ne_top (top_unique (hI.2 ▸ sup_le (Ideal.dvd_iff_le.mp hPI)
    (conductor_le_of_dvd hK hp hv hpc)))

private theorem norm_character_trivial_on_principal (hK : Module.finrank ℚ K = 2)
    (hTC : IsTotallyComplex K) (I : integralIdealsPrimeTo (conductorOrder K c).conductorModulus)
    (hI : (conductorOrder K c).picClass I = 1) :
    jacobiSym (I : Ideal (𝓞 K)).absNorm c = 1 := by
  obtain ⟨β, hβ, hIβ⟩ := ((conductorOrder K c).picClass_eq_one_iff I).mp hI
  obtain ⟨a, y, ha⟩ := (conductorOrder K c).mem_toRingOfIntegers.mp hβ
  have ha' : β = (a : 𝓞 K) + (c : 𝓞 K) * y := by
    apply RingOfIntegers.ext
    push_cast
    exact ha
  have hcong : β - (a : 𝓞 K) ∈ Ideal.span {(c : 𝓞 K)} := by
    rw [ha', add_sub_cancel_left, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hnorma : Algebra.norm ℤ (a : 𝓞 K) = a ^ 2 := by
    rw [← eq_intCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
  have hnormβ : 0 ≤ Algebra.norm ℤ β := by
    have hpos : IsTotallyPositive (β : K) := isTotallyPositive_iff.mpr fun w hw =>
      ((InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)) hw).elim
    have hn := NumberField.norm_nonneg_of_isTotallyPositive hpos
    rw [← Algebra.coe_norm_int] at hn
    exact_mod_cast hn
  have hnorm := Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem
    (mul_nonneg hnormβ (hnorma ▸ sq_nonneg a)) hcong
  rw [← hIβ, Ideal.absNorm_span_singleton, hnorma] at hnorm
  have hmod : ((I : Ideal (𝓞 K)).absNorm : ℤ) ≡ a ^ 2 [ZMOD c] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ c).mp
    rw [Int.cast_natCast, hnorm, ← Int.cast_natCast,
      Int.natAbs_of_nonneg (sq_nonneg a)]
  have hsym := jacobiSym.mod_left' hmod
  have hnonz : jacobiSym ((I : Ideal (𝓞 K)).absNorm : ℤ) c ≠ 0 :=
    jacobiSym.ne_zero (by simpa [Int.gcd_natCast_natCast] using
      (norm_coprime_conductor hK I).gcd_eq_one)
  rw [hsym] at hnonz
  rw [hsym, jacobiSym.pow_left]
  exact jacobiSym.sq_one (by
    by_contra hn
    have hz := (jacobiSym.eq_zero_iff_not_coprime (a := a) (b := c)).mpr hn
    exact hnonz (by rw [jacobiSym.pow_left, hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]))

/-- For an imaginary quadratic field the Jacobi symbol of the ideal norm at
conductor `c` descends to a quadratic character of its Picard group. -/
theorem exists_ringCharacter (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    {d : ℤ} (hd : d.natAbs = c) :
    ∃ χ : Pic (conductorOrder K c) →* ℂˣ, IsQuadRingClassChar K c d χ := by
  classical
  let O := conductorOrder K c
  let ψ : integralIdealsPrimeTo O.conductorModulus →* ℂˣ :=
    { toFun := fun I => Units.mk0 (jacobiSym ((I : Ideal (𝓞 K)).absNorm : ℤ) c : ℂ)
        (by exact_mod_cast jacobiSym.ne_zero (by simpa [Int.gcd_natCast_natCast] using
          (norm_coprime_conductor hK I).gcd_eq_one))
      map_one' := by apply Units.ext; simp
      map_mul' := fun I J => by
        apply Units.ext
        push_cast
        simp [jacobiSym.mul_left] }
  have hker (I : integralIdealsPrimeTo O.conductorModulus) (hI : O.picClass I = 1) : ψ I = 1 := by
    apply Units.ext
    change (jacobiSym (I : Ideal (𝓞 K)).absNorm c : ℂ) = 1
    rw [norm_character_trivial_on_principal hK hTC I hI, Int.cast_one]
  have hfiber (I J : integralIdealsPrimeTo O.conductorModulus) (hIJ : O.picClass I = O.picClass J) :
      ψ I = ψ J := by
    obtain ⟨M, hM⟩ := O.picClass_surjective (O.picClass I)⁻¹
    have h1 := hker (I * M) (by rw [map_mul, hM, mul_inv_cancel])
    have h2 := hker (J * M) (by rw [map_mul, ← hIJ, hM, mul_inv_cancel])
    exact mul_right_cancel ((map_mul ψ I M).symm.trans (h1.trans (h2.symm.trans (map_mul ψ J M))))
  let rep : Pic O → integralIdealsPrimeTo O.conductorModulus := fun t => (O.picClass_surjective t).choose
  have hrep (t : Pic O) : O.picClass (rep t) = t := (O.picClass_surjective t).choose_spec
  let χ : Pic O →* ℂˣ :=
    { toFun := fun t => ψ (rep t)
      map_one' := hker _ (hrep _)
      map_mul' := fun t u => (hfiber (rep (t * u)) (rep t * rep u)
        (by rw [hrep, map_mul, hrep, hrep])).trans (map_mul _ _ _) }
  have hχ (I : integralIdealsPrimeTo O.conductorModulus) : χ (O.picClass I) = ψ I :=
    hfiber _ _ (hrep _)
  refine ⟨χ, ?_, ?_⟩
  · intro t
    obtain ⟨I, rfl⟩ := O.picClass_surjective t
    rw [hχ]
    apply Units.ext
    change (jacobiSym (I : Ideal (𝓞 K)).absNorm c : ℂ) *
      (jacobiSym (I : Ideal (𝓞 K)).absNorm c : ℂ) = 1
    rw [← sq]
    exact_mod_cast jacobiSym.sq_one (by simpa [Int.gcd_natCast_natCast] using
      (norm_coprime_conductor hK I).gcd_eq_one)
  · intro v hv _
    rw [hχ ⟨v.asIdeal, hv⟩]
    simp [ψ, chiD, hd]


end ZInQ.Manuscript.RC.Gz34Instance
