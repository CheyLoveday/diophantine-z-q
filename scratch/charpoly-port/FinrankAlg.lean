import Mathlib

/-! charpoly-port scratch: the commutative-algebra core of `FinrankGenericPoint`. -/

open Polynomial

namespace CharPolyPortFinrank

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

omit [FaithfulSMul R S] in
/-- A nonzero element of a domain finite over a domain `R` divides a nonzero element of `R`. -/
theorem exists_dvd_algebraMap (b : S) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ b ∣ algebraMap R S r := by
  have hI : (Ideal.span {b}).comap (algebraMap R S) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hb (Ideal.mem_span_singleton_self b)
      (Algebra.IsIntegral.isIntegral b)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact ⟨r, hr0, Ideal.mem_span_singleton.mp hr⟩

/-- `Frac S` is the localization of `S` at the nonzero elements of `R`. -/
theorem isLocalization_algebraMapSubmonoid (L : Type u) [Field L] [Algebra S L] [IsFractionRing S L] :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L where
  map_units m := by
    obtain ⟨_, ⟨r, hr, rfl⟩⟩ := m
    apply IsLocalization.map_units L (M := nonZeroDivisors S) ⟨algebraMap R S r, ?_⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr
        (nonZeroDivisors.ne_zero hr))
  surj z := by
    obtain ⟨⟨x, n⟩, e⟩ := IsLocalization.surj (nonZeroDivisors S) z
    obtain ⟨r, hr0, c, hc⟩ := exists_dvd_algebraMap (R := R) (n : S) (nonZeroDivisors.ne_zero n.2)
    refine ⟨⟨x * c, ⟨algebraMap R S r, r, mem_nonZeroDivisors_of_ne_zero hr0, rfl⟩⟩, ?_⟩
    simp only at e ⊢
    rw [hc, map_mul, map_mul, ← mul_assoc, e]
  exists_of_eq {x y} h := ⟨1, by simp [IsFractionRing.injective S L h]⟩

/-- **The algebra core.** The rank of `S` at the zero prime of `R` is `[Frac S : Frac R]`. -/
theorem rankAtStalk_bot_eq_finrank (K L : Type u) [Field K] [Field L] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Module.Flat R S] :
    Module.rankAtStalk (R := R) S (⊥ : PrimeSpectrum R) = Module.finrank K L := by
  haveI := isLocalization_algebraMapSubmonoid (R := R) (S := S) L
  have hpush : Algebra.IsPushout R S K L :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mp inferInstance
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom R S L).toLinearMap := hpush.symm.out
  have hfree : Module.rankAtStalk (R := K) L (⊥ : PrimeSpectrum K) = Module.finrank K L :=
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L)) (⊥ : PrimeSpectrum K)
  rw [← hfree, Module.rankAtStalk_isBaseChange hbc]
  congr 1
  ext x
  simp only [PrimeSpectrum.comap_asIdeal]
  change x ∈ (⊥ : Ideal R) ↔ x ∈ Ideal.comap (algebraMap R K) (⊥ : Ideal K)
  rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

end CharPolyPortFinrank
