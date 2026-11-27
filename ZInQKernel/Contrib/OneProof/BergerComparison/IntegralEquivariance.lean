import ZInQKernel.Contrib.OneProof.BergerComparison.MaximalSeparation

/-! Galois equivariance on both actual integral coefficient images.
Finite polynomial expressions suffice by p-adic separation. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries
open PanBergerSplit (Ainf AinfP flatAct locAct locAct_algebraMap locAct_qpToLoc)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 400000

private abbrev loc := algebraMap (Ainf p) (AinfP p)
private abbrev wittAct (σ : GQp p) := WittVector.map (p := p) (flatAct p σ)
private abbrev plusAct (σ : GQp p) := DR.bdrPlusMap p (oAct p σ)
private abbrev wittIntoPlus := (ofLoc p).comp (loc p)

private abbrev phiOmega := loc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹)

private def includeCrystalline : crystallineIntegral p →+* Amax p :=
  (crystallineIntegral p).subtype.codRestrict (Amax p) (fun y =>
    acrisOf_le_amax p (theta_xi' p) (ker_fontaineTheta_Cp p)
      ((mem_crystallineIntegral p y.val).mp y.property))

/-- The Galois action restricts to the integral maximal image. -/
def galoisMaximal (σ : GQp p) : Amax p →+* Amax p :=
  ((plusAct p σ).comp (Amax p).subtype).codRestrict (Amax p) (fun y => by
    obtain ⟨y', hy', he⟩ := bdrAct_amax p σ y.property
    rw [bdrAct_toBdR] at he
    have h := toBdR_injective p he
    change plusAct p σ y.val = y' at h
    simpa only [RingHom.comp_apply, Subring.subtype_apply, h] using hy')

private theorem wittAct_frob (σ : GQp p) (a : Ainf p) :
    wittAct p σ (WittVector.frobenius a) = WittVector.frobenius (wittAct p σ a) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp [WittVector.map_coeff, frobenius_def]

private theorem plusAct_witt (σ : GQp p) :
    (plusAct p σ).comp (wittIntoPlus p) = (wittIntoPlus p).comp (wittAct p σ) := by
  apply RingHom.ext
  intro a
  change plusAct p σ (ofLoc p (loc p a)) = ofLoc p (loc p (wittAct p σ a))
  rw [bdrPlusMap_ofLoc]
  exact congrArg (ofLoc p) (locAct_algebraMap p σ a)

private theorem plusAct_omega (σ : GQp p) {c : Ainf p}
    (hc : wittAct p σ (xi p) = xi p * c) :
    plusAct p σ (ofLoc p (omegaP p)) = ofLoc p (omegaP p) * wittIntoPlus p c := by
  rw [bdrPlusMap_ofLoc]
  change ofLoc p (locAct p σ (omegaP p)) = _
  rw [omegaP, map_mul, locAct_qpToLoc, xi', locAct_algebraMap, hc,
    RingHom.comp_apply, ← map_mul]
  simp only [map_mul]
  ring

private theorem plusAct_phiOmega (σ : GQp p) {c : Ainf p}
    (hc : wittAct p σ (xi p) = xi p * c) :
    plusAct p σ (ofLoc p (phiOmega p)) =
      ofLoc p (phiOmega p) * wittIntoPlus p (WittVector.frobenius c) := by
  rw [bdrPlusMap_ofLoc]
  change ofLoc p (locAct p σ (phiOmega p)) = _
  rw [map_mul, locAct_qpToLoc, locAct_algebraMap, wittAct_frob, hc,
    RingHom.comp_apply, ← map_mul]
  simp only [map_mul, phiOmega]
  ring

/-- On polynomials, maximal evaluation is ordinary evaluation at ξ/p. -/
theorem maximalEval_polynomial (Q : Polynomial (Ainf p)) :
    maximalEval p Q = Q.eval₂ (wittIntoPlus p) (ofLoc p (omegaP p)) := by
  change psEval (Ith p) (omegaP_mem p) (PowerSeries.map (loc p) ↑Q) = _
  rw [← Polynomial.polynomial_map_coe]
  have he (R : Polynomial (AinfP p)) :
      psEval (Ith p) (omegaP_mem p) R =
        algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p)) (R.eval (omegaP p)) := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_psEval, mk_eval_trunc _ (omegaP_mem p)]
    rfl
  rw [he, Polynomial.eval_map]
  change ofLoc p (Q.eval₂ (loc p) (omegaP p)) = _
  exact Polynomial.hom_eval₂ _ _ _ _

private theorem galoisMaximal_polynomial (σ : GQp p) {c : Ainf p}
    (hc : wittAct p σ (xi p) = xi p * c) (Q : Polynomial (Ainf p)) :
    galoisMaximal p σ (maxToImage p ⟨Q, polynomial_mem_restricted p Q⟩) =
      maxToImage p ⟨(Q.map (wittAct p σ)).comp (Polynomial.X * Polynomial.C c),
        polynomial_mem_restricted p _⟩ := by
  apply Subtype.ext
  change plusAct p σ (maximalEval p Q) =
    maximalEval p ((Q.map (wittAct p σ)).comp (Polynomial.X * Polynomial.C c))
  rw [maximalEval_polynomial, maximalEval_polynomial, Polynomial.hom_eval₂, plusAct_witt,
    plusAct_omega p σ hc, Polynomial.eval₂_comp, Polynomial.eval₂_map,
    Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]

/-- Frobenius on the embedded integral maximal ring commutes with the
Galois action, with equality already in the de Rham plus ring. -/
theorem integralFrobenius_galois (σ : GQp p) (b : Amax p) :
    (integralFrobenius p (galoisMaximal p σ b) : BDeRhamPlus 𝓞_ℂ_[p] p) =
      plusAct p σ (integralFrobenius p b : BDeRhamPlus 𝓞_ℂ_[p] p) := by
  let F := (includeCrystalline p).comp (integralFrobenius p)
  let g₁ := F.comp ((galoisMaximal p σ).comp (maxToImage p))
  let g₂ := (galoisMaximal p σ).comp (F.comp (maxToImage p))
  have h : g₁ = g₂ := by
    apply restricted_to_amax_ext
    intro Q
    obtain ⟨c, hc⟩ := wittMap_xi_mem p σ
    apply Subtype.ext
    change (integralFrobenius p (galoisMaximal p σ
        (maxToImage p ⟨Q, polynomial_mem_restricted p Q⟩)) : BDeRhamPlus 𝓞_ℂ_[p] p) =
        plusAct p σ (integralFrobenius p (maxToImage p ⟨Q, polynomial_mem_restricted p Q⟩)
          : BDeRhamPlus 𝓞_ℂ_[p] p)
    rw [galoisMaximal_polynomial p σ hc, integralFrobenius_polynomial,
      integralFrobenius_polynomial]
    change ((Q.map (wittAct p σ)).comp (Polynomial.X * Polynomial.C c)).eval₂
      ((wittIntoPlus p).comp WittVector.frobenius) (ofLoc p (phiOmega p)) =
      plusAct p σ (Q.eval₂ ((wittIntoPlus p).comp WittVector.frobenius) (ofLoc p (phiOmega p)))
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_map, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.hom_eval₂, plusAct_phiOmega p σ hc]
    congr 1
    apply RingHom.ext
    intro a
    change wittIntoPlus p (WittVector.frobenius (wittAct p σ a)) =
      plusAct p σ (wittIntoPlus p (WittVector.frobenius a))
    rw [← wittAct_frob p σ a]
    exact (DFunLike.congr_fun (plusAct_witt p σ) _).symm
  obtain ⟨Q, rfl⟩ := maxToImage_surjective p b
  exact congrArg Subtype.val (DFunLike.congr_fun h Q)

end ZInQ.Manuscript.BergerComparison
