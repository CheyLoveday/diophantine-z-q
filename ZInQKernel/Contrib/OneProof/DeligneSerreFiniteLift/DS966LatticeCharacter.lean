import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966PowerFactors
import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.ComplexSpecialization

/-! # The same-quotient complex character from an integral local lift -/

noncomputable section

namespace DS966Small

open NumberField Polynomial Matrix
open scoped NumberField

/-- If an integral local lift is given, the resulting complex representation on
the same finite group has integral character and determinant values in the root
candidate sets, with the prescribed reductions. Kind: PROVED. -/
theorem complex_character_of_prescribed_lattice {K A L k H : Type*}
    [Field K] [NumberField K] [CommRing A] [Field L] [Algebra K L] [Algebra K ℂ]
    [Field k] [Group H] [Fintype H]
    (a : 𝓞 K →+* A) (i : A →+* L) (hi : Function.Injective i)
    (res : A →+* k) (f : 𝓞 K →+* k)
    (ha : ∀ x : 𝓞 K, i (a x) = algebraMap K L x)
    (hf : ∀ x : 𝓞 K, res (a x) = f x)
    {m : ℕ} (hm : 0 < m) (hdiv : Fintype.card H ∣ m) (hs : (X ^ m - C 1 : K[X]).Splits)
    (r : H →* GL (Fin 2) A) (ρ : H →* GL (Fin 2) k)
    (hred : (Matrix.GeneralLinearGroup.map res).comp r = ρ) :
    ∃ σ : H →* GL (Fin 2) ℂ, ∀ h : H, ∃ x y : 𝓞 K,
      x ^ m = 1 ∧ y ^ m = 1 ∧
      (σ h : Matrix (Fin 2) (Fin 2) ℂ).trace = algebraMap K ℂ ((x + y : 𝓞 K) : K) ∧
      (σ h : Matrix (Fin 2) (Fin 2) ℂ).det = algebraMap K ℂ ((x * y : 𝓞 K) : K) ∧
      (ρ h : Matrix (Fin 2) (Fin 2) k).trace = f (x + y) ∧
      (ρ h : Matrix (Fin 2) (Fin 2) k).det = f (x * y) := by
  classical
  let R := (Matrix.GeneralLinearGroup.map i).comp r
  have hfac (h : H) : ∃ x y : 𝓞 K, x ^ m = 1 ∧ y ^ m = 1 ∧
      (R h : Matrix (Fin 2) (Fin 2) L).trace = algebraMap K L ((x + y : 𝓞 K) : K) ∧
      (R h : Matrix (Fin 2) (Fin 2) L).det = algebraMap K L ((x * y : 𝓞 K) : K) ∧
      (ρ h : Matrix (Fin 2) (Fin 2) k).trace = f (x + y) ∧
      (ρ h : Matrix (Fin 2) (Fin 2) k).det = f (x * y) := by
    have hp : h ^ m = 1 := by
      obtain ⟨b, hb⟩ := hdiv
      rw [hb, pow_mul, pow_card_eq_one, one_pow]
    let q := (Units.coeHom (Matrix (Fin 2) (Fin 2) L)).comp R
    have hpow : (R h : Matrix (Fin 2) (Fin 2) L) ^ m = 1 := by
      change q h ^ m = 1
      rw [← map_pow, hp, map_one]
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      charpoly_integral_factors_from_power_splits (algebraMap K L) hm hs _ hpow
    let B : Matrix (Fin 2) (Fin 2) A := r h
    have hc : (B.map i).charpoly = (X - C (algebraMap K L x)) * (X - C (algebraMap K L y)) := hxy
    let j := (algebraMap K L).comp (algebraMap (𝓞 K) K)
    have hr := DS966Lifting.common_lattice_factors j i hi f res B
      (x := x) (y := y) ⟨a x, ha x, hf x⟩ ⟨a y, ha y, hf y⟩ hc
    have hρ : B.map res = (ρ h : Matrix (Fin 2) (Fin 2) k) :=
      congrArg (fun w : H →* GL (Fin 2) k => (w h : Matrix (Fin 2) (Fin 2) k)) hred
    rw [hρ] at hr
    obtain ⟨ht, hd⟩ := DS966Lifting.trace_det_of_factors hxy
    obtain ⟨ht', hd'⟩ := DS966Lifting.trace_det_of_factors hr
    refine ⟨x, y, hx, hy, ?_, ?_, ?_, ?_⟩
    · simpa only [map_add] using ht
    · simpa only [map_mul] using hd
    · simpa only [map_add] using ht'
    · simpa only [map_mul] using hd'
  choose x y hx hy ht hd htr hdr using hfac
  obtain ⟨σ, hσ⟩ := DeligneSerre.exists_complex_representation_of_trace_det R
    (fun h => ((x h + y h : 𝓞 K) : K)) (fun h => ((x h * y h : 𝓞 K) : K)) ht hd
  exact ⟨σ, fun h => ⟨x h, y h, hx h, hy h, (hσ h).1, (hσ h).2, htr h, hdr h⟩⟩

end DS966Small
