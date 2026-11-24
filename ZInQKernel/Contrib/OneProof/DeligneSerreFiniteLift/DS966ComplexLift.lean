import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966GlobalResidueLift
import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966LatticeCharacter

/-! # Complex lifting on the same finite quotient with prescribed characteristic data -/

noncomputable section

namespace DS966Small

open TauCeti ValuativeRel NumberField Polynomial Matrix
open scoped NumberField

/-- A two-dimensional representation of a finite group of order prime to `ℓ`
has a complex lift on that same group, with both characteristic roots at each
element paired with integral roots of unity under the specified reduction on
`𝓞 K`. The coefficient field `K` contains the roots of the power polynomial;
its algebra structure on `ℂ` is the chosen embedding. Kind: PROVED. -/
theorem exists_complex_character_lift {K H : Type*} [Field K] [NumberField K] [Algebra K ℂ]
    [Group H] [Fintype H] (ℓ : ℕ) [Fact ℓ.Prime]
    (f : 𝓞 K →+* AlgebraicClosure (ZMod ℓ)) (hcard : ¬ ℓ ∣ Fintype.card H)
    {m : ℕ} (hm : 0 < m) (hdiv : Fintype.card H ∣ m) (hs : (X ^ m - C 1 : K[X]).Splits)
    (ρ : H →* GL (Fin 2) (AlgebraicClosure (ZMod ℓ))) :
    ∃ σ : H →* GL (Fin 2) ℂ, ∀ h : H, ∃ x y : 𝓞 K,
      x ^ m = 1 ∧ y ^ m = 1 ∧
      (σ h : Matrix (Fin 2) (Fin 2) ℂ).trace = algebraMap K ℂ ((x + y : 𝓞 K) : K) ∧
      (σ h : Matrix (Fin 2) (Fin 2) ℂ).det = algebraMap K ℂ ((x * y : 𝓞 K) : K) ∧
      (ρ h : Matrix (Fin 2) (Fin 2) (AlgebraicClosure (ZMod ℓ))).trace = f (x + y) ∧
      (ρ h : Matrix (Fin 2) (Fin 2) (AlgebraicClosure (ZMod ℓ))).det = f (x * y) := by
  let k := AlgebraicClosure (ZMod ℓ)
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  let _ : CharP k ℓ := CharP.of_ringHom_of_ne_zero (algebraMap (ZMod ℓ) k) ℓ hℓ
  let v := placeOfReduction f hℓ
  let F := v.adicCompletion K
  let g := residueMapAtCompletion f v rfl
  obtain ⟨L, _, _, _, _, _, _, _, _, red, r, hr, hred⟩ := lift_with_global_reduction f hℓ
    (algebraic_of_embedding_into_algClosure_zmod ℓ g) hcard ρ
  let a₀ : 𝓞 K →+* 𝒪[F] := (algebraMap (𝓞 K) F).codRestrict _
    (v.algebraMap_mem_integer_adicCompletion (K := K))
  let a : 𝓞 K →+* 𝒪[L] := (algebraMap 𝒪[F] 𝒪[L]).comp a₀
  let _ := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  exact complex_character_of_prescribed_lattice a (Subring.subtype 𝒪[L])
    Subtype.val_injective red f (fun _ => rfl) hred hm hdiv hs r ρ hr

end DS966Small
