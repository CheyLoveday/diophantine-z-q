import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.FrobSqrt
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Points
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-!
# GenusOdd: `Gal(H_c/K)` acts on a square root of `d` in `H_c` through `χ_d ∘ N` (PROVED)

`genus_action`: if `s ∈ H_c` with `s² = d` (`d ≡ 1 mod 4`) and `χ = χ_d ∘ N` on `Pic(O_c)`
(`IsQuadRingClassChar`), then `σ s = χ(σ) s` for every `σ ∈ Gal(H_c/K)`. Proof: the elements with
this property form a subgroup; it contains every arithmetic Frobenius at a prime over a prime
`v ∤ 2 d f_O` of `K` (Euler's criterion, `frob_smul_sqrt`; the Frobenius is the Artin image of the
class of `v` by the splitting law `isArithFrobAt_ringClassArtinEquiv_picClass` and uniqueness at
an unramified prime); these generate `Gal(H_c/K)` (`closure_isArithFrobAt_eq_top`).
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

section

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

/-- Galois automorphisms of `H_c` agreeing on `𝓞_{H_c}` are equal (PROVED). -/
theorem algEquiv_eq_of_smul_eq
    {σ τ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)}
    (h : ∀ x : 𝓞 (ringClassField (conductorOrder K c)), σ • x = τ • x) : σ = τ := by
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := 𝓞 (ringClassField (conductorOrder K c))) y
  rw [map_div₀, map_div₀]
  have ha : σ (a : ringClassField (conductorOrder K c)) = τ a :=
    congrArg (fun z : 𝓞 (ringClassField (conductorOrder K c)) =>
      (z : ringClassField (conductorOrder K c))) (h a)
  have hb : σ (b : ringClassField (conductorOrder K c)) = τ b :=
    congrArg (fun z : 𝓞 (ringClassField (conductorOrder K c)) =>
      (z : ringClassField (conductorOrder K c))) (h b)
  have ea : algebraMap (𝓞 (ringClassField (conductorOrder K c)))
      (ringClassField (conductorOrder K c)) a = (a : ringClassField (conductorOrder K c)) := rfl
  have eb : algebraMap (𝓞 (ringClassField (conductorOrder K c)))
      (ringClassField (conductorOrder K c)) b = (b : ringClassField (conductorOrder K c)) := rfl
  rw [ea, eb, ha, hb]

theorem mem_primeTo_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ (conductorOrder K c).conductor) :
    v.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K c).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  refine ⟨v.ne_bot, ?_⟩
  by_contra hne
  have hle : v.asIdeal ⊔ (conductorOrder K c).conductor = v.asIdeal :=
    (v.isMaximal.eq_of_le hne le_sup_left).symm
  exact hv (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle.le))

/-- **A Frobenius at an unramified prime is the Artin image of the class of the prime below**
(PROVED; splitting law plus uniqueness of the Frobenius at an unramified prime). -/
theorem frob_eq_artin {σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)}
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ (conductorOrder K c).conductor)
    (w : HeightOneSpectrum (𝓞 (ringClassField (conductorOrder K c))))
    [w.asIdeal.LiesOver v.asIdeal] (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    σ = ringClassArtinEquiv (conductorOrder K c)
      ((conductorOrder K c).picClass ⟨v.asIdeal, mem_primeTo_of_not_dvd hv⟩) := by
  have := v.isMaximal
  have hart := isArithFrobAt_ringClassArtinEquiv_picClass (conductorOrder K c)
    ⟨v.asIdeal, mem_primeTo_of_not_dvd hv⟩ w.asIdeal
  have := isUnramifiedAt_ringClassField (conductorOrder K c) hv w.asIdeal
  have heq := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ hart
    (Ideal.primeCompl_le_nonZeroDivisors _)
  exact algEquiv_eq_of_smul_eq fun x => congrArg (fun φ => φ x) heq

/-- **The genus action** (PROVED): `Gal(H_c/K)` acts on a square root `s ∈ H_c` of `d ≡ 1 (mod 4)`
through `χ = χ_d ∘ N`. -/
theorem genus_action {d : ℤ} (hd : d % 4 = 1) {χ : Pic (conductorOrder K c) →* ℂˣ}
    (hχ : IsQuadRingClassChar K c d χ) (s : ringClassField (conductorOrder K c))
    (hs : s ^ 2 = (d : ringClassField (conductorOrder K c)))
    (σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)) :
    σ s = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) :
      ringClassField (conductorOrder K c)) * s := by
  set art := ringClassArtinEquiv (conductorOrder K c)
  -- the subgroup of elements acting on `s` through `χ`
  let G' : Subgroup (ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)) :=
    { carrier := {τ | τ s = (chiSign χ (art.symm τ) : ringClassField (conductorOrder K c)) * s}
      one_mem' := by
        show (1 : ringClassField (conductorOrder K c) ≃ₐ[K] _) s = _
        rw [map_one]; unfold chiSign; simp
      mul_mem' := fun {a b} ha hb => by
        show (a * b) s = _
        rw [AlgEquiv.mul_apply, hb, map_mul, map_intCast, ha, map_mul, chiSign_mul hχ.1]
        push_cast; ring
      inv_mem' := fun {a} ha => by
        show a⁻¹ s = _
        have h1 : s = a⁻¹ ((chiSign χ (art.symm a) : ringClassField (conductorOrder K c)) * s) := by
          rw [← ha]; simp
        rw [map_mul, map_intCast] at h1
        rw [map_inv, chiSign_inv hχ.1]
        have hsq := chiSign_sq (χ := χ) (art.symm a)
        calc a⁻¹ s = ((chiSign χ (art.symm a) * chiSign χ (art.symm a) : ℤ) :
              ringClassField (conductorOrder K c)) * a⁻¹ s := by rw [hsq]; simp
          _ = (chiSign χ (art.symm a) : ringClassField (conductorOrder K c)) *
              ((chiSign χ (art.symm a) : ringClassField (conductorOrder K c)) * a⁻¹ s) := by
              push_cast; ring
          _ = _ := by rw [← h1] }
  -- the excluded primes
  have hd0 : d ≠ 0 := by rintro rfl; norm_num at hd
  set I : Ideal (𝓞 K) := (conductorOrder K c).conductor * Ideal.span {((2 * d : ℤ) : 𝓞 K)}
  have hI : I ≠ 0 := by
    refine mul_ne_zero (conductorOrder K c).conductor_ne_bot ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (mul_ne_zero two_ne_zero hd0 : (2 * d : ℤ) ≠ 0)
  set S := (Ideal.finite_factors hI).toFinset
  have hgen := closure_isArithFrobAt_eq_top (K := K) (L := ringClassField (conductorOrder K c)) S
  have hle : Subgroup.closure {τ : ringClassField (conductorOrder K c) ≃ₐ[K]
      ringClassField (conductorOrder K c) | ∃ v ∉ S,
      ∃ w : {w : HeightOneSpectrum (𝓞 (ringClassField (conductorOrder K c))) //
        w.asIdeal.LiesOver v.asIdeal}, IsArithFrobAt (𝓞 K) τ w.1.asIdeal} ≤ G' := by
    rw [Subgroup.closure_le]
    rintro τ ⟨v, hv, w, hτ⟩
    have hvI : ¬ v.asIdeal ∣ I := by simpa [S] using hv
    have hvc : ¬ v.asIdeal ∣ (conductorOrder K c).conductor := fun h => hvI (dvd_mul_of_dvd_left h _)
    have h2d : ((2 * d : ℤ) : 𝓞 K) ∉ v.asIdeal := fun h =>
      hvI (dvd_mul_of_dvd_right (Ideal.dvd_span_singleton.mpr h) _)
    have hdv : ((d : ℤ) : 𝓞 K) ∉ v.asIdeal := fun h => h2d (by
      push_cast; exact v.asIdeal.mul_mem_left 2 h)
    have := v.isMaximal
    have := w.2
    -- `s` as an integer of `H_c`
    have hint : IsIntegral ℤ s := IsIntegral.of_pow (n := 2) (by norm_num)
      (by rw [hs, ← eq_intCast (algebraMap ℤ (ringClassField (conductorOrder K c))) d]
          exact isIntegral_algebraMap)
    set s' : 𝓞 (ringClassField (conductorOrder K c)) := ⟨s, hint⟩
    have hs' : s' ^ 2 = (d : 𝓞 (ringClassField (conductorOrder K c))) := by
      apply RingOfIntegers.ext; push_cast; exact hs
    have hfrob := frob_smul_sqrt (K := K) (L := ringClassField (conductorOrder K c)) hd s' hs' τ
      w.1.asIdeal v.asIdeal h2d hτ
    have hart := frob_eq_artin hvc w.1 hτ
    -- the value of `χ` at the class of `v`
    have hval := hχ.2 v (mem_primeTo_of_not_dvd hvc) hdv
    have hsign : chiSign χ (art.symm τ) = jacobiSym (Ideal.absNorm v.asIdeal) d.natAbs := by
      rw [hart, MulEquiv.symm_apply_apply]
      have := chiSign_coe hχ.1 ((conductorOrder K c).picClass ⟨v.asIdeal, mem_primeTo_of_not_dvd hvc⟩)
      rw [hval] at this
      exact_mod_cast this
    show τ s = _
    have hτs : τ s = ((τ • s' : 𝓞 (ringClassField (conductorOrder K c))) :
        ringClassField (conductorOrder K c)) := rfl
    rw [hτs, hfrob, hsign]
    push_cast
    rfl
  have hσ : σ ∈ G' := by
    have := hle (hgen ▸ Subgroup.mem_top σ)
    exact this
  exact hσ

end

end ZInQ.Contrib.CloudB3RC53.GenusOdd
