import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Character
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusSqrtMem
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.TauCeti.NumberTheory.RamificationInertia.Tower
import ZInQKernel.Progressions.QuadField.Signature

/-! Primitivity of the character of tex 2413 at conductor `|h|`.
For a proper divisor an omitted prime ramifies in `ℚ(√h)` but not in the
smaller ring class field. This conductor check is on-the-spot (c). -/

noncomputable section

open NumberField IsDedekindDomain ZInQ.Progressions TauCeti.GlobalNumberFields
  TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

variable {K : Type} [Field K] [NumberField K]

private theorem omitted_prime {c c' : ℕ} (hsq : Squarefree c) (hd : c' ∣ c) (hne : c' ≠ c) :
    ∃ p : ℕ, p.Prime ∧ p ∣ c ∧ ¬ p ∣ c' := by
  by_contra! h
  have hc' : c' ≠ 0 := fun he => hsq.ne_zero (by simpa [he] using hd)
  have h₁ : Squarefree c' := hsq.squarefree_of_dvd hd
  have hs : c.primeFactors ⊆ c'.primeFactors := by
    intro p hp
    obtain ⟨hpp, hpc, -⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpp, h p hpp hpc, hc'⟩
  exact hne (Nat.dvd_antisymm hd (by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, ← Nat.prod_primeFactors_of_squarefree h₁]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hs))

private theorem ringClass_unramified_at {c' p : ℕ} [NeZero c'] (hp : p.Prime)
    (hpK : ¬ (p : ℤ) ∣ discr K) (hpc : ¬ p ∣ c') :
    Algebra.IsUnramifiedIn (𝓞 (ringClassField (conductorOrder K c'))) (Ideal.span {(p : ℤ)}) := by
  let H := ringClassField (conductorOrder K c')
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP0 : P ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hp.ne_zero)
  have huK : Algebra.IsUnramifiedIn (𝓞 K) P :=
    (NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)).mp hpK
  apply Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr
  intro Q hQ hQP
  let q := Q.under (𝓞 K)
  have hqP : q.LiesOver P := inferInstance
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hP0 q⟩
  have hv : v ∈ primesAbove K p := by
    change ((p : ℤ) : 𝓞 K) ∈ q
    exact (Ideal.mem_of_liesOver q P (p : ℤ)).mp (Ideal.subset_span (Set.mem_singleton _))
  have huQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    isUnramifiedAt_ringClassField (conductorOrder K c') (not_dvd_conductor_of_not_dvd hp hv hpc) Q
  rw [Ideal.ramificationIdx_tower (R := ℤ) q Q,
    huK.ramificationIdx_eq_one hqP, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, mul_one]

private theorem no_square_root_at_omitted_prime {M : Type} [Field M] [NumberField M]
    {h : ℤ} {p : ℕ} (hsq : Squarefree h) (h4 : h % 4 = 1) (hp : p.Prime) (hph : (p : ℤ) ∣ h)
    (hu : Algebra.IsUnramifiedIn (𝓞 M) (Ideal.span {(p : ℤ)})) :
    ¬ ∃ s : M, s ^ 2 = (h : M) := by
  rintro ⟨s, hs⟩
  have hh1 : h ≠ 1 := fun he => (Nat.prime_iff_prime_int.mp hp).not_dvd_one (he ▸ hph)
  let : Fact (¬ IsSquare (h : ℚ)) := ⟨Qsqrt.not_isSquare_of_squarefree hsq hh1⟩
  let F := Qsqrt h
  let ι : F →ₐ[ℚ] M := QuadraticAlgebra.lift ⟨s, by
    rw [← sq, hs]; simp [Algebra.smul_def]⟩
  let : Algebra F M := ι.toRingHom.toAlgebra
  let : IsScalarTower ℚ F M := .of_algebraMap_eq fun x => (ι.commutes x).symm
  have hD : discr F = h := ZInQ.Contrib.CloudB3RC53.Companion.discr_eq_of_sq Qsqrt.finrank
    hsq h4 hh1 (by simpa using Qsqrt.ringHom_omega_sq (RingHom.id F))
  have huF : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}) := by
    intro P hP hPP
    exact TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn (S := 𝓞 M) hu P
  exact ((NumberField.not_dvd_discr_iff_isUnramifiedIn F (𝓞 F) (Nat.prime_iff_prime_int.mp hp)).mpr
    huF) (by rw [hD]; exact hph)

omit [NumberField K] in
private theorem not_mem_of_no_root {F : Type} [Field F] [Algebra K F]
    {A B : IntermediateField K F} {s : A} {h : ℤ} (hs : s ^ 2 = (h : A))
    (hn : ¬ ∃ t : B, t ^ 2 = (h : B)) : (s : F) ∉ B := by
  intro hm
  apply hn
  refine ⟨⟨s, hm⟩, ?_⟩
  apply B.val.injective
  rw [map_pow, map_intCast]
  exact ((map_pow A.val s 2).symm.trans ((congrArg A.val hs).trans (map_intCast A.val h)))

omit [NumberField K] in
private theorem exists_moves_of_not_mem {F : Type} [Field F] [Algebra K F]
    {A B : IntermediateField K F} [IsGalois K A] {s : A} (hs : (s : F) ∉ B) :
    ∃ σ : A ≃ₐ[K] A, (∀ x : A, (x : F) ∈ B → σ x = x) ∧ σ s ≠ s := by
  classical
  let L := B.comap A.val
  have hs' : s ∉ L := hs
  rw [← IntermediateField.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff] at hs'
  push Not at hs'
  obtain ⟨σ, hσ, hneσ⟩ := hs'
  exact ⟨σ, fun x hx => (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ x hx, hneσ⟩

private theorem ringCharacter_ne_one_of_moves {h : ℤ} [NeZero h.natAbs]
    (h4 : h % 4 = 1) {χ : Pic (conductorOrder K h.natAbs) →* ℂˣ}
    (hχ : IsQuadRingClassChar K h.natAbs h χ)
    {s : ringClassField (conductorOrder K h.natAbs)} (hs : s ^ 2 = (h : ℤ))
    (σ : ringClassField (conductorOrder K h.natAbs) ≃ₐ[K] ringClassField (conductorOrder K h.natAbs))
    (hm : σ s ≠ s) : χ ((ringClassArtinEquiv (conductorOrder K h.natAbs)).symm σ) ≠ 1 := by
  intro ht
  apply hm
  have h := genus_action h4 hχ s hs σ
  simpa only [chiSign, ht, Units.val_one, eq_self, ite_true, Int.cast_one, one_mul] using h

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2048 in
/-- The norm character of conductor `|h|` is primitive if `h` is an odd
fundamental discriminant prime to the base field discriminant. The case
`h = 1` is included; there are then no proper divisors to test. -/
theorem ringCharacter_primitive {h : ℤ} [NeZero h.natAbs]
    (hsq : Squarefree h) (h4 : h % 4 = 1) (hcop : IsCoprime h (discr K))
    {χ : Pic (conductorOrder K h.natAbs) →* ℂˣ} (hχ : IsQuadRingClassChar K h.natAbs h χ) :
    IsPrimitiveRingClassChar K h.natAbs χ := by
  classical
  intro c' _ hd hne
  obtain ⟨p, hp, hph, hpc'⟩ := omitted_prime (Int.squarefree_natAbs.mpr hsq) hd hne
  have hph' : (p : ℤ) ∣ h := Int.natCast_dvd.mpr hph
  have hpK : ¬ (p : ℤ) ∣ discr K := fun hpd =>
    (Nat.prime_iff_prime_int.mp hp).not_isUnit (hcop.isRelPrime hph' hpd)
  let H := ringClassField (conductorOrder K h.natAbs)
  let H' := ringClassField (conductorOrder K c')
  obtain ⟨s, hs⟩ := exists_sqrt_mem_ringClassField h4 hχ
  have hn : ¬ ∃ t : H', t ^ 2 = (h : H') := no_square_root_at_omitted_prime hsq h4 hp hph'
    (ringClass_unramified_at (K := K) hp hpK hpc')
  have hm : (s : SeparableClosure K) ∉ H' := not_mem_of_no_root (A := H) (B := H') hs hn
  obtain ⟨σ, hfix, hmove⟩ := exists_moves_of_not_mem (A := H) (B := H') hm
  exact ⟨σ, hfix, ringCharacter_ne_one_of_moves h4 hχ hs σ hmove⟩


end ZInQ.Manuscript.RC.Gz34Instance
