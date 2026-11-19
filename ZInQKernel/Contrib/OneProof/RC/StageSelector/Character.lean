import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusAction
import ZInQKernel.Contrib.TYZGenus.RingClassTwo
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ResidueDegree
import ZInQKernel.Contrib.TauCeti.NumberTheory.RamificationInertia.Unramified

/-! The conductor-one genus character of (O.1), tex 8213–8217 and 8261–8266.
The Lean construction through the action on a square root, using finite and
infinite reciprocity to place it in the class field, is on-the-spot (c). -/

noncomputable section

open NumberField Polynomial IsDedekindDomain TauCeti TauCeti.GlobalNumberFields
  TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.TYZGenus.RingClass (adjSqrt sqrtK sqrtK_sq isIntegral_sqrtK genS_sq)
open scoped NumberField

namespace ZInQ.Manuscript.RC.StageSelector

private theorem admissible_one_of_unramified {K M : Type} [Field K] [Field M]
    [NumberField K] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    (hK : IsTotallyComplex K)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) :
    IsAdmissibleModulus K M (Modulus.one K) := by
  apply isAdmissibleModulus_iff.mpr
  intro c hc
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
  apply (globalArtinMap_eq_zero_iff K M IsSepClosed.lift _).mp
  refine CharacterModule.eq_zero_of_character_apply fun χ => ?_
  let χ' : Additive (Abelianization (M ≃ₐ[K] M)) →+ AddCircle (1 : ℚ) := χ
  change χ' (globalArtinMap K M IsSepClosed.lift (.ofMul (x : IdeleClassGroup (𝓞 K) K))) = 0
  rw [apply_globalArtinMap_eq_finsum]
  have hf (v : HeightOneSpectrum (𝓞 K)) : localArtinAt K M v (v.ideleFiniteCoord x) = 1 := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
    have hP : (P : Ideal (𝓞 M)).IsPrime := P.2.1
    let w : HeightOneSpectrum (𝓞 M) :=
      ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot (P : Ideal (𝓞 M))⟩
    have : w.asIdeal.LiesOver v.asIdeal := P.2.2
    have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hu v _ hP this
    apply localArtinAt_eq_one_of_normalizedValuation_eq_one v w
    apply (normalizedValuation_eq_one_iff _).mpr
    have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
      (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))
    exact hequiv.eq_one_iff_eq_one.mpr (ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx v)
  simp only [hf, fun w => infiniteLocalArtinAt_eq_one_of_isComplex (L := M)
    (hK.isComplex w) (w.ideleInfiniteCoord x), ofMul_one, map_zero, finsum_zero,
    Finset.sum_const_zero, add_zero]

private theorem halfRoot_integral {M : Type} [Field M] [NumberField M]
    {d : ℤ} (hd : d % 4 = 1) {s : M} (hs : s ^ 2 = (d : M)) :
    IsIntegral ℤ ((1 + s) / 2) := by
  have hd' : d = 4 * (d / 4) + 1 := by omega
  refine ⟨X ^ 2 - X - C (d / 4), by monicity!, ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, aeval_C, algebraMap_int_eq]
  have h := congrArg (fun n : ℤ => (n : M)) hd'
  push_cast at h
  field_simp
  linear_combination hs + h

private def halfRoot {M : Type} [Field M] [NumberField M] {d : ℤ}
    (hd : d % 4 = 1) {s : M} (hs : s ^ 2 = (d : M)) : 𝓞 M :=
  ⟨(1 + s) / 2, halfRoot_integral hd hs⟩

private theorem fixes_root_of_congruent_half {K M : Type} [Field K] [Field M]
    [NumberField K] [NumberField M] [Algebra K M]
    {d : ℤ} (hd : d % 4 = 1) {s : M} (hs : s ^ 2 = (d : M))
    (σ : M ≃ₐ[K] M) (P : Ideal (𝓞 M)) (hP : (d : 𝓞 M) ∉ P)
    (hσ : σ • halfRoot hd hs - halfRoot hd hs ∈ P) : σ s = s := by
  have hs' : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs' with h | h
  · exact h
  · let a : 𝓞 M := σ • halfRoot hd hs - halfRoot hd hs
    have ha : (a : M) = -s := by
      change σ ((1 + s) / 2) - (1 + s) / 2 = -s
      rw [map_div₀, map_add, map_one, map_ofNat, h]
      ring
    have ha2 : a ^ 2 = (d : 𝓞 M) := by
      apply RingOfIntegers.ext
      simpa [ha] using hs
    exact False.elim (hP (ha2 ▸ P.pow_mem_of_mem hσ 2 (by decide)))

private theorem conductorOrder_maximal (K : Type) [Field K] [NumberField K] :
    conductorOrder K 1 = maximalNumberFieldOrder K := by
  ext x
  constructor
  · exact fun hx => conductorOrderSubalgebra_le_integralClosure K 1 hx
  · intro hx
    refine ⟨0, ⟨x, hx⟩, ?_⟩
    simp only [Int.cast_zero, zero_add, Nat.cast_one, one_mul]
    rfl

private theorem ringClassField_one (K : Type) [Field K] [NumberField K] :
    ringClassField (conductorOrder K 1) = hilbertClassField K := by
  rw [conductorOrder_maximal]
  rw [← IntermediateField.fieldRange_val (ringClassField (maximalNumberFieldOrder K)),
    fieldRange_eq_rayClassField_iff]
  rw [range_ideleClassNormMap_ringClassField, ker_ringClassIdeleQuotient_maximalNumberFieldOrder]

set_option maxHeartbeats 800000 in
/-- If the field contains a root of the product of two coprime odd discriminant
factors, the conductor-one class field contains a root of the second factor. -/
theorem sqrt_mem_conductorOne {K : Type} [Field K] [NumberField K]
    (hK : IsTotallyComplex K) {D d : ℤ} (hD : D % 4 = 1) (hd : d % 4 = 1)
    (hcop : IsCoprime D d) {u : K} (hu : u ^ 2 = ((D * d : ℤ) : K)) :
    ∃ s : ringClassField (conductorOrder K 1), s ^ 2 = (d : ringClassField (conductorOrder K 1)) := by
  classical
  let M := adjSqrt K d
  let s : M := IntermediateField.AdjoinSimple.gen K (sqrtK K d)
  have hs : s ^ 2 = (d : M) := genS_sq K d
  have hd0 : (d : M) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs0 : s ≠ 0 := fun h => hd0 (by simp [h] at hs; exact hs.symm)
  let t : M := algebraMap K M u / s
  have ht : t ^ 2 = (D : M) := by
    have hu' : algebraMap K M u ^ 2 = (D : M) * (d : M) := by
      rw [← map_pow, hu, map_intCast]; push_cast; rfl
    rw [div_pow, hu', hs, mul_div_cancel_right₀ _ hd0]
  have hdegree : Module.finrank K M ∣ 2 := by
    rw [show Module.finrank K M = (minpoly K (sqrtK K d)).natDegree from
      IntermediateField.adjoin.finrank (isIntegral_sqrtK K d)]
    have hle := natDegree_le_of_dvd
      (minpoly.dvd K (sqrtK K d) (p := X ^ 2 - C (d : K)) (by simp [sqrtK_sq]))
      (X_pow_sub_C_ne_zero (by decide : 0 < 2) (d : K))
    rw [natDegree_X_pow_sub_C] at hle
    have hpos := minpoly.natDegree_pos (isIntegral_sqrtK K d)
    interval_cases (minpoly K (sqrtK K d)).natDegree <;> decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_card_dvd_prime (p := 2) (by
    rw [IsGalois.card_aut_eq_finrank]; exact hdegree)
  have : IsAbelianGalois K M := IsAbelianGalois.of_isCyclic K M
  have hur (v : HeightOneSpectrum (𝓞 K)) : Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal := by
    have := v.isMaximal
    rw [Ideal.isUnramifiedIn_iff_forall_inertia_eq_bot (G := M ≃ₐ[K] M)]
    intro P hP
    have : P.IsPrime := hP.1
    refine eq_bot_iff.mpr fun σ hσ => ?_
    rw [Subgroup.mem_bot]
    have hfix : σ s = s := by
      by_cases hdP : (d : 𝓞 M) ∈ P
      · have hDP : (D : 𝓞 M) ∉ P := by
          intro hmem
          obtain ⟨a, b, hab⟩ := hcop
          have h1 := congrArg (fun x : ℤ => (x : 𝓞 M)) hab
          push_cast at h1
          exact Ideal.IsPrime.ne_top hP.1 (P.eq_top_iff_one.mpr
            (h1 ▸ P.add_mem (P.mul_mem_left (a : 𝓞 M) hmem) (P.mul_mem_left (b : 𝓞 M) hdP)))
        have hfixT := fixes_root_of_congruent_half hD ht σ P hDP (Ideal.mem_inertia.mp hσ _)
        have ht0 : t ≠ 0 := fun h => by
          have : (D : M) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
          exact this (by simpa [h] using ht.symm)
        have hmul : t * s = algebraMap K M u := div_mul_cancel₀ _ hs0
        have hmul' := congrArg σ hmul
        rw [map_mul, hfixT, AlgEquiv.commutes, ← hmul] at hmul'
        exact mul_left_cancel₀ ht0 hmul'
      · exact fixes_root_of_congruent_half hd hs σ P hdP (Ideal.mem_inertia.mp hσ _)
    apply AlgEquiv.coe_toAlgHom_injective
    refine IntermediateField.adjoin_algHom_ext K (fun x hx => ?_)
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hfix
  have hle : M ≤ ringClassField (conductorOrder K 1) := by
    rw [ringClassField_one, ← IntermediateField.fieldRange_val M]
    exact (isAdmissibleModulus_iff_le_rayClassField (Modulus.one K) M.val).mp (admissible_one_of_unramified hK hur)
  refine ⟨IntermediateField.inclusion hle s, ?_⟩
  rw [← map_pow, hs, map_intCast]

private theorem frob_fixes_root_at_two {K M : Type} [Field K] [Field M]
    [NumberField K] [NumberField M] [Algebra K M]
    {d : ℤ} (hd8 : d % 8 = 1) {s : M} (hs : s ^ 2 = (d : M))
    {σ : M ≃ₐ[K] M} {P : Ideal (𝓞 M)} [P.IsPrime]
    (h2 : (2 : 𝓞 M) ∈ P) (hσ : IsArithFrobAt (𝓞 K) σ P) : σ s = s := by
  have hd : d % 4 = 1 := by omega
  let a := halfRoot hd hs
  have ha : a ^ 2 - a = (d / 4 : ℤ) := by
    apply RingOfIntegers.ext
    change ((1 + s) / 2) ^ 2 - (1 + s) / 2 = ((d / 4 : ℤ) : M)
    have h := congrArg (fun n : ℤ => (n : M)) (show d = 4 * (d / 4) + 1 by omega)
    push_cast at h
    field_simp
    linear_combination hs + h
  have haP : a ^ 2 - a ∈ P := by
    rw [ha, show d / 4 = 2 * (d / 8) by omega]
    push_cast
    exact P.mul_mem_right _ h2
  let x := Ideal.Quotient.mk P a
  have hx : x ^ 2 = x := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem.mpr haP)
    simpa [x, map_sub, map_pow, sub_eq_zero] using hz
  have hxpow (n : ℕ) : x ^ (n + 1) = x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← sq, hx]
  have hpos := hσ.card_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hc : σ • a - a ∈ P := by
    have h := hσ a
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [map_sub, sub_eq_zero]
    have hm := (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    rw [map_sub, sub_eq_zero, map_pow, hn, Nat.succ_eq_add_one] at hm
    exact hm.trans (hxpow n)
  have hdP : (d : 𝓞 M) ∉ P := by
    intro h
    rw [show d = 2 * (d / 2) + 1 by omega] at h
    push_cast at h
    exact Ideal.IsPrime.ne_top ‹P.IsPrime›
      (P.eq_top_iff_one.mpr ((P.add_mem_iff_right (P.mul_mem_right _ h2)).mp h))
  exact fixes_root_of_congruent_half hd hs σ P hdP hc

/-- The action on a nonzero square root gives exactly the norm character of
(O.1), including the primes above two. This does not require a nontrivial
quadratic extension of the base field. -/
theorem exists_genusCharacter {K : Type} [Field K] [NumberField K]
    {d : ℤ} (hd8 : d % 8 = 1)
    {s : ringClassField (conductorOrder K 1)}
    (hs : s ^ 2 = (d : ringClassField (conductorOrder K 1))) :
    ∃ χ : Pic (conductorOrder K 1) →* ℂˣ, IsQuadRingClassChar K 1 d χ := by
  classical
  let O := conductorOrder K 1
  let H := ringClassField O
  let ι : H →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hd0 : (d : H) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs0 : s ≠ 0 := fun h => hd0 (by simp [h] at hs; exact hs.symm)
  let e := ringClassArtinEquiv O
  have hsign (g : H ≃ₐ[K] H) : g s / s = 1 ∨ g s / s = -1 := by
    have hsq : (g s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, map_intCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with he | he
    · exact Or.inl (by rw [he, div_self hs0])
    · exact Or.inr (by rw [he, neg_div, div_self hs0])
  let χ : Pic O →* ℂˣ :=
    { toFun := fun t => Units.mk0 (ι (e t s / s))
        (fun hz => div_ne_zero (by simpa only [map_zero] using (e t).injective.ne hs0) hs0
          (ι.injective (hz.trans (map_zero ι).symm)))
      map_one' := by
        apply Units.ext
        simp [e, div_self hs0]
      map_mul' := fun a b => by
        apply Units.ext
        change ι (e (a * b) s / s) = ι (e a s / s) * ι (e b s / s)
        rw [map_mul e, AlgEquiv.mul_apply, ← map_mul]
        have hb : e b s = (e b s / s) * s := (div_mul_cancel₀ _ hs0).symm
        conv_lhs => rw [hb, map_mul]
        rcases hsign (e b) with h | h <;> rw [h] <;> simp [neg_div] }
  refine ⟨χ, ?_, ?_⟩
  · intro t
    apply Units.ext
    change ι (e t s / s) * ι (e t s / s) = 1
    rcases hsign (e t) with h | h <;> simp [h]
  · intro v hv hdv
    let J : integralIdealsPrimeTo O.conductorModulus := ⟨v.asIdeal, hv⟩
    have : (J : Ideal (𝓞 K)).IsMaximal := v.isMaximal
    obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 H)))
    have : (P : Ideal (𝓞 H)).IsPrime := P.2.1
    have : (P : Ideal (𝓞 H)).LiesOver (J : Ideal (𝓞 K)) := P.2.2
    have hσ := isArithFrobAt_ringClassArtinEquiv_picClass O J (P : Ideal (𝓞 H))
    change ι (e (O.picClass J) s / s) = (chiD d v.asIdeal.absNorm : ℂ)
    have hlift (n : ℤ) (hn : (n : 𝓞 K) ∈ v.asIdeal) : (n : 𝓞 H) ∈ (P : Ideal (𝓞 H)) := by
      have : (n : 𝓞 K) ∈ (P : Ideal (𝓞 H)).under (𝓞 K) :=
        (Ideal.LiesOver.over (p := (J : Ideal (𝓞 K))) (P := (P : Ideal (𝓞 H)))) ▸ hn
      change algebraMap (𝓞 K) (𝓞 H) (n : 𝓞 K) ∈ (P : Ideal (𝓞 H)) at this
      simpa using this
    by_cases h2 : (2 : 𝓞 K) ∈ v.asIdeal
    · have h2P : (2 : 𝓞 H) ∈ (P : Ideal (𝓞 H)) := by
        simpa using hlift 2 (by simpa using h2)
      rw [frob_fixes_root_at_two hd8 hs h2P hσ, div_self hs0, map_one]
      have hp := prime_rationalPrimeBelow v
      have hpd := (v.intCast_mem_asIdeal_iff 2).mp (by simpa using h2)
      have hp2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast hpd)
      have hχ2 : jacobiSym 2 d.natAbs = 1 := by
        have hodd : Odd d.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
        rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
        have h1 : d.natAbs % 2 ≠ 0 := by omega
        rcases le_or_gt 0 d with h0 | h0
        · have : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg h0
          split_ifs <;> omega
        · have : (d.natAbs : ℤ) = -d := by omega
          split_ifs <;> omega
      rw [absNorm_eq_rationalPrimeBelow_pow, hp2]
      unfold chiD
      push_cast
      simp [jacobiSym.pow_left, hχ2]
    · have h2d : ((2 * d : ℤ) : 𝓞 K) ∉ v.asIdeal := by
        push_cast
        exact fun h => (v.isPrime.mem_or_mem h).elim h2 hdv
      have hint : IsIntegral ℤ s :=
        IsIntegral.of_pow (n := 2) (by decide) (by rw [hs]; exact isIntegral_intCast d)
      let s' : 𝓞 H := ⟨s, hint⟩
      have hs' : s' ^ 2 = (d : 𝓞 H) := by
        apply RingOfIntegers.ext
        push_cast
        exact hs
      have hf := frob_smul_sqrt (by omega : d % 4 = 1) s' hs'
        (e (O.picClass J)) (P : Ideal (𝓞 H)) v.asIdeal h2d hσ
      have he : e (O.picClass J) s = (chiD d v.asIdeal.absNorm : H) * s := by
        have heq : e (O.picClass J) s = ((e (O.picClass J) • s' : 𝓞 H) : H) := rfl
        rw [heq, hf]
        push_cast
        rfl
      rw [he, mul_div_cancel_right₀ _ hs0, map_intCast]

#print axioms admissible_one_of_unramified
#print axioms halfRoot_integral
#print axioms fixes_root_of_congruent_half
#print axioms conductorOrder_maximal
#print axioms ringClassField_one
#print axioms sqrt_mem_conductorOne
#print axioms frob_fixes_root_at_two
#print axioms exists_genusCharacter

end ZInQ.Manuscript.RC.StageSelector
