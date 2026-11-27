import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Coefficients
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.UniformRing

/-! The algebraic valuation ring in the fixed complex field and the
integers of its completion come from one prime above two. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open NumberField IsDedekindDomain HeightOneSpectrum

/-- The field of the phases, when the character exponents are bounded by `e`. -/
abbrev PhaseField (e : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {z : ℂ | z ^ (2 ^ e) = 1}

instance (e : ℕ) : NumberField (PhaseField e) :=
  LocalWeights.characterField_numberField ⟨e, fun _ hz => hz⟩

theorem phaseField_mem {e f : ℕ} (hle : f ≤ e) {z : ℂ} (hz : z ^ (2 ^ f) = 1) :
    z ∈ PhaseField e :=
  IntermediateField.subset_adjoin ℚ _ (orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_pow_eq_one hz).trans (pow_dvd_pow 2 hle)))

/-- The prime is fixed before the operator indices are chosen. -/
structure Place (F : IntermediateField ℚ ℂ) [NumberField F] where
  v : HeightOneSpectrum (𝓞 F)
  aboveTwo : (2 : 𝓞 F) ∈ v.asIdeal

theorem place_exists (F : IntermediateField ℚ ℂ) [NumberField F] : Nonempty (Place F) := by
  obtain ⟨v, hv⟩ := LocalWeights.coefficientPlace_exists F
  exact ⟨⟨v, hv⟩⟩

namespace Place

variable {F : IntermediateField ℚ ℂ} [NumberField F] (V : Place F)

abbrev LocalField := V.v.adicCompletion F

abbrev LocalIntegers := ↥(V.v.adicCompletionIntegers F)

def complexIntegers : Subring ℂ :=
  ((V.v.valuation F).valuationSubring.toSubring).map F.subtype

theorem mem_complexIntegers_iff (x : F) :
    (x : ℂ) ∈ V.complexIntegers ↔ FinitePlace.embedding V.v x ∈ V.v.adicCompletionIntegers F := by
  change (∃ y : F, V.v.valuation F y ≤ 1 ∧ (y : ℂ) = (x : ℂ)) ↔ _
  rw [mem_adicCompletionIntegers, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
  exact ⟨fun ⟨y, hy, he⟩ => (Subtype.ext he : y = x) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem root_mem_complexIntegers {z : ℂ} (hz : z ∈ F) {m : ℕ} (hm : 0 < m)
    (hroot : z ^ m = 1) : z ∈ V.complexIntegers :=
  ⟨⟨z, hz⟩, LocalWeights.rootOfUnity_mem_coefficientRing F V.v hm
    (Subtype.ext (by simpa using hroot) : (⟨z, hz⟩ : F) ^ m = 1), rfl⟩

theorem odd_inv_mem (d : ℕ) (hd : ¬ 2 ∣ d) : (d : ℂ)⁻¹ ∈ V.complexIntegers := by
  have hin : (d : 𝓞 F) ∉ V.v.asIdeal := by
    obtain ⟨j, hj⟩ := (odd_iff_exists_bit1).mp (Nat.not_even_iff_odd.mp (even_iff_two_dvd.not.mpr hd))
    intro h
    have hmul := V.v.asIdeal.mul_mem_left (j : 𝓞 F) V.aboveTwo
    rw [mul_comm] at hmul
    have h1 : (1 : 𝓞 F) ∈ V.v.asIdeal := by
      convert V.v.asIdeal.sub_mem h hmul using 1
      rw [hj]
      push_cast
      ring
    exact V.v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have he : V.v.valuation F (d : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F)]
    exact le_antisymm (V.v.valuation_le_one (K := F) _) (le_of_not_gt (fun h =>
      hin ((V.v.valuation_lt_one_iff_mem (K := F) _).mp h)))
  exact ⟨(d : F)⁻¹, by change V.v.valuation F ((d : F)⁻¹) ≤ 1; rw [map_inv₀, he, inv_one],
    by simp⟩

theorem half_not_mem : (2 : ℂ)⁻¹ ∉ V.complexIntegers := by
  rintro ⟨x, hx, he⟩
  have hx' : x = (2 : F)⁻¹ := by
    apply F.subtype.injective
    simpa only [map_inv₀, map_ofNat] using he
  change V.v.valuation F x ≤ 1 at hx
  have hlt : V.v.valuation F (2 : F) < 1 := by
    rw [← map_ofNat (algebraMap (𝓞 F) F) (n := 2)]
    exact (V.v.valuation_lt_one_iff_mem (K := F) _).mpr V.aboveTwo
  have hn : V.v.valuation F (2 : F) ≠ 0 := by simp
  rw [hx', map_inv₀] at hx
  exact (not_le_of_gt hlt) ((inv_le_one₀ (pos_of_ne_zero hn)).mp hx)

private def twoPrime : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨2, Nat.prime_two⟩

private theorem liesOver_two : V.v.asIdeal.LiesOver twoPrime.asIdeal := by
  have hspan : twoPrime.asIdeal = Ideal.span {(2 : ℤ)} := by
    have h := Rat.HeightOneSpectrum.span_natGenerator twoPrime
    have hgen : Rat.HeightOneSpectrum.natGenerator twoPrime = 2 := by
      exact congrArg Subtype.val
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply ⟨2, Nat.prime_two⟩)
    rw [hgen] at h
    convert h.symm using 1
    have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ :=
      RingEquiv.ext fun x => by simp
    rw [he]
    exact (Ideal.map_id _).symm
  apply (Ideal.liesOver_iff V.v.asIdeal twoPrime.asIdeal).mpr
  rw [hspan]
  apply Ideal.IsMaximal.eq_of_le
    ((Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp Nat.prime_two)).isMaximal
      (by simp)) (Ideal.comap_ne_top _ V.v.isPrime.ne_top)
  exact Ideal.span_le.mpr (by simpa using V.aboveTwo)

/-- Extend the rational embedding to the completion at the *same* prime. -/
def padic : ℚ_[2] →+* V.LocalField :=
  letI := V.liesOver_two
  (adicCompletion.equiv F V.v).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (twoPrime.valuation ℚ)) (WithVal (V.v.valuation F)))
      (uniformContinuous_algebraMap_liesOver ℚ F twoPrime V.v).continuous).comp <|
    (adicCompletion.equiv ℚ twoPrime).toRingHom.comp
      (Padic.adicCompletionEquiv ℤ ⟨2, Nat.prime_two⟩).toAlgEquiv.toRingHom

private theorem continuous_padic : Continuous V.padic :=
  (adicCompletion.continuous_ofCompletion F V.v).comp
    (UniformSpace.Completion.continuous_map.comp
      ((adicCompletion.continuous_toCompletion ℚ twoPrime).comp
        (Padic.adicCompletionEquiv ℤ ⟨2, Nat.prime_two⟩).continuous))

private theorem padic_mem (x : ℤ_[2]) : V.padic (x : ℚ_[2]) ∈ V.v.adicCompletionIntegers F := by
  refine PadicInt.denseRange_natCast.induction_on x ?_ ?_
  · exact (Valued.isClosed_valuationSubring V.LocalField).preimage
      (V.continuous_padic.comp continuous_subtype_val)
  · intro n
    rw [PadicInt.coe_natCast, map_natCast]
    exact natCast_mem (V.v.adicCompletionIntegers F).toSubring n

def padicInt : ℤ_[2] →+* V.LocalIntegers :=
  (V.padic.comp (PadicInt.Coe.ringHom (p := 2))).codRestrict
    (V.v.adicCompletionIntegers F).toSubring V.padic_mem

theorem padic_agree (x : ℤ_[2]) :
    algebraMap V.LocalIntegers V.LocalField (V.padicInt x) = V.padic (x : ℚ_[2]) := rfl

end Place

end ZInQ.Manuscript.RC.EvenPlace
