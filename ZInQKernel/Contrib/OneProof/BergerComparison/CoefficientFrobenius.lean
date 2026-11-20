import ZInQKernel.Contrib.OneProof.BergerComparison.MaximalEvaluation
import ZInQKernel.Contrib.OneProof.BergerComparison.DividedPowerCompletion

/-! The integral map from the maximal image to the crystalline image.
The Frobenius substitution is first made in formal divided-power series,
then evaluated, and only then descended to the maximal image. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries Ideal
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 350000

private abbrev loc := algebraMap (Ainf p) (AinfP p)

private abbrev toPlus := ofLoc p

private abbrev ev := evalB p (algebraMap_mem_ith p (theta_xi' p))

/-- The actual crystalline integral image, as a subring of the completion. -/
def crystallineIntegral : Subring (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  (dividedPowerRestricted p).map (ev p)

theorem mem_crystallineIntegral (b : BDeRhamPlus 𝓞_ℂ_[p] p) :
    b ∈ crystallineIntegral p ↔ b ∈ AcrisOf p (xi p) (theta_xi' p) := by
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dpSeries p f, ⟨f, hf, rfl⟩, rfl⟩

private abbrev phiXiDiv : BDeRhamPlus 𝓞_ℂ_[p] p :=
  toPlus p (loc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹))

private theorem exists_phiXiDiv :
    ∃ x : dividedPowerRestricted p, ev p x.val = phiXiDiv p := by
  obtain ⟨s, hs, he⟩ := (mem_crystallineIntegral p _).mpr (frobenius_xi_div_p_mem_acris p)
  exact ⟨⟨s, hs⟩, he⟩

private def phiXiLift : dividedPowerRestricted p := Classical.choose (exists_phiXiDiv p)

private theorem eval_phiXiLift : ev p (phiXiLift p).val = phiXiDiv p :=
  Classical.choose_spec (exists_phiXiDiv p)

private def coeffLift : Ainf p →+* dividedPowerRestricted p :=
  (PowerSeries.C.comp (loc p)).codRestrict (dividedPowerRestricted p) (fun a =>
    ⟨C a, C_mem_restricted p a, dpSeries_C p a⟩)

private def evalDP : dividedPowerRestricted p →+* crystallineIntegral p :=
  ((ev p).comp (dividedPowerRestricted p).subtype).codRestrict (crystallineIntegral p)
    (fun s => ⟨s.val, s.property, rfl⟩)

private theorem evalDP_coeffLift (a : Ainf p) :
    (evalDP p (coeffLift p a) : BDeRhamPlus 𝓞_ℂ_[p] p) = toPlus p (loc p a) :=
  psEval_C _ (algebraMap_mem_ith p (theta_xi' p)) _

private def frobBeforeDescent : restricted p →+* crystallineIntegral p :=
  (evalDP p).comp (restrictedEval p ((coeffLift p).comp WittVector.frobenius) (phiXiLift p))

theorem polynomial_mem_restricted (Q : Polynomial (Ainf p)) :
    (Q : (Ainf p)⟦X⟧) ∈ restricted p := fun k =>
  ⟨Q.natDegree + 1, fun n hn => by
    change (p : Ainf p)^k ∣ PowerSeries.coeff n (Q : (Ainf p)⟦X⟧)
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _⟩

/-- The formula on finite polynomials agrees with Witt coefficient Frobenius
and the prescribed crystalline generator. -/
theorem frobBeforeDescent_polynomial (Q : Polynomial (Ainf p)) :
    (frobBeforeDescent p ⟨Q, polynomial_mem_restricted p Q⟩ : BDeRhamPlus 𝓞_ℂ_[p] p) =
      Q.eval₂ ((toPlus p).comp ((loc p).comp WittVector.frobenius)) (phiXiDiv p) := by
  change ((evalDP p (restrictedEval p _ _ ⟨Q, _⟩) : crystallineIntegral p) :
    BDeRhamPlus 𝓞_ℂ_[p] p) = _
  rw [restrictedEval_polynomial]
  change (((crystallineIntegral p).subtype.comp (evalDP p))
    (Q.eval₂ _ _)) = _
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext a
    exact evalDP_coeffLift p _
  · exact eval_phiXiLift p

/-- The linear relation, viewed inside the restricted source ring. -/
def maximalRelSub : restricted p :=
  ⟨maximalRelation p, by
    have e :
        ((Polynomial.C (xi p) - Polynomial.X * Polynomial.C (p : Ainf p) :
          Polynomial (Ainf p)) : (Ainf p)⟦X⟧) = maximalRelation p := by
      simp only [maximalRelation, Polynomial.coe_sub, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_X]
    rw [← e]
    exact polynomial_mem_restricted p _⟩

private theorem frobBeforeDescent_relation : frobBeforeDescent p (maximalRelSub p) = 0 := by
  apply Subtype.ext
  have h : (maximalRelSub p) =
      ⟨(Polynomial.C (xi p) - Polynomial.X * Polynomial.C (p : Ainf p) : Polynomial (Ainf p)),
        polynomial_mem_restricted p _⟩ := by
    apply Subtype.ext
    simp only [maximalRelSub, maximalRelation, Polynomial.coe_sub, Polynomial.coe_C,
      Polynomial.coe_mul, Polynomial.coe_X]
  rw [h, frobBeforeDescent_polynomial]
  change _ = (0 : BDeRhamPlus 𝓞_ℂ_[p] p)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_natCast, RingHom.comp_apply, map_natCast]
  rw [← map_natCast (toPlus p) p, ← map_mul, mul_assoc, mul_comm (qpToLoc p _),
    natCast_mul_qp p p hp.out.ne_zero, mul_one, sub_self]

/-- The maximal evaluation, with target its embedded image. -/
def maxToImage : restricted p →+* Amax p :=
  ((maximalEval p).comp (restricted p).subtype).codRestrict (Amax p)
    (fun f => ⟨f.val, f.property, rfl⟩)

theorem maxToImage_surjective : Function.Surjective (maxToImage p) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

private theorem ker_maxToImage_le : RingHom.ker (maxToImage p) ≤ RingHom.ker (frobBeforeDescent p) := by
  intro f hf
  have h : maximalEval p f.val = 0 := congrArg Subtype.val (RingHom.mem_ker.mp hf)
  obtain ⟨g, hg, hfg⟩ := (maximalEval_zero_iff p f.property).mp h
  have he : f = maximalRelSub p * ⟨g, hg⟩ := Subtype.ext hfg
  rw [he, RingHom.mem_ker, map_mul, frobBeforeDescent_relation, zero_mul]

/-- Witt Frobenius on the entire embedded integral maximal ring,
with image in the embedded integral crystalline ring. -/
def integralFrobenius : Amax p →+* crystallineIntegral p :=
  (maxToImage p).liftOfSurjective (maxToImage_surjective p)
    ⟨frobBeforeDescent p, ker_maxToImage_le p⟩

theorem integralFrobenius_polynomial (Q : Polynomial (Ainf p)) :
    (integralFrobenius p (maxToImage p ⟨Q, polynomial_mem_restricted p Q⟩) :
      BDeRhamPlus 𝓞_ℂ_[p] p) =
      Q.eval₂ ((toPlus p).comp ((loc p).comp WittVector.frobenius)) (phiXiDiv p) := by
  rw [integralFrobenius, RingHom.liftOfSurjective_comp_apply]
  exact frobBeforeDescent_polynomial p Q

end ZInQ.Manuscript.BergerComparison
