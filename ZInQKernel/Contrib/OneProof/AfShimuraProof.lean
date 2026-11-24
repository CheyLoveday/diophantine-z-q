import ZInQKernel.Contrib.OneProof.AbVarQuotientComplement
import ZInQKernel.Contrib.OneProof.ShimuraQuotientImageSum
import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFiniteProof

/-! The abelian variety quotient and coefficient-field action in `AfShimura`. -/

noncomputable section

namespace AfTateLam

open CategoryTheory AlgebraicGeometry LeafModCurves PkgI3
open PkgI4 (CF coeff IsNormalizedEigenform)
open ShimuraSteps.Quotient (imageSum_exists abVarQuotientBySubvarietyExists
  kills_iff_kills_imageSum)

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J A : AbVar ℚ}
  {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J} {π : AbVar.Hom J A}

private theorem exists_afQuotient (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) :
    ∃ (A : AbVar ℚ) (π : AbVar.Hom J A), IsAfQuotient χ f tp δ A π := by
  let I : Set (AbVar.End J) := {t | ∃ h : HeckeFree N, evF χ f h = 0 ∧ heckeJ tp δ h = t}
  obtain ⟨C, i, hi⟩ := imageSum_exists I
  obtain ⟨A, π, hπ⟩ := abVarQuotientBySubvarietyExists J C i hi.closed
  have kills_iff {B : AbVar ℚ} (φ : AbVar.Hom J B) :
      KillsIf χ f tp δ φ ↔ i.hom ≫ φ.hom = (0 : AbVar.Hom C B).hom := by
    rw [← kills_iff_kills_imageSum hi φ]
    constructor
    · rintro h _ ⟨g, hg, rfl⟩
      exact h g hg
    · intro h g hg
      exact h _ ⟨g, hg, rfl⟩
  exact ⟨A, π, hπ.surjective, (kills_iff π).mpr hπ.kernel.w,
    fun B φ hφ => hπ.lift_unique B φ ((kills_iff φ).mp hφ)⟩

private theorem af_coeffField_finite (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) :
    FiniteDimensional ℚ (coeffField f) := by
  letI : NeZero N := ⟨by omega⟩
  exact eigenformCoeffFieldFinite_proof N 2 χ f le_rfl
    (DSCoeffExt.isNormalizedEigenformDS_of hf)

end AfTateLam

end
