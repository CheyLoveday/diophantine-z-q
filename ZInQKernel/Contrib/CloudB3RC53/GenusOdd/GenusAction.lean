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

end

end ZInQ.Contrib.CloudB3RC53.GenusOdd
