import ZInQKernel.Contrib.OneProof.RC.Height.BaseZeroCST
import ZInQKernel.Contrib.OneProof.RC.Central.BaseZero

/-!
# Lane RC22 (glue sweep, central share): regularity at a known simple zero, with the height half
# of its input discharged

Proposition `ex:arith-central-calibration` of the 11/5 manuscript (`diophantine_zq.tex`, lines
3987–4140) uses `u_prim(0)` at known simple zeros; Version 19 (proof of the same proposition) adds
that the generic coordinate is regular there and specializes to the central tensor, because the
retained cycle has nonzero central class: "(4.5) and the height formula at the known simple zero"
(the explicit height formula makes the specified point nontorsion: 11/5 tex 2464, 8268–8272,
9439–9440).

Lane RC15 proves this as `ZInQ.Manuscript.RC.Central.simpleZero_specialization`, with the
hypothesis `hz0 : ∃ i, ρ (z i) ≠ 0` (`z̄ ≠ 0`). Lane RC19 proved the height half: the conductor-one
Heegner trace `P` is not torsion when the product `L`-function has nonzero derivative at `1`
(`ZInQ.Manuscript.RC.Height.not_isOfFinAddOrder_of_CST`). This file composes the two, replacing
`hz0` by RC19's inputs, lane RC15's (4.5) in the form of `baseZero_node` (`h45`, ELLIOT) with
`Lm ≠ 0`, and the injectivity modulo torsion of the composite Kummer map (`hkum`, GLUE).

Every theorem in this file is PROVED (from the stated remaining inputs).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Manuscript.RC.GlueSweep.Central

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  Matrix

open Classical in
/-- **The generic coordinate specializes at a known simple zero, with `z̄ ≠ 0` derived from the
height formula** (11/5 tex 2464, 8268–8272, 9439–9440 for the height formula; V19's proof of
`ex:arith-central-calibration` for the specialization; lane RC15's (4.5), tex 3911–3915).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.simpleZero_specialization`, whose hypothesis
`hz0 : ∃ i, ρ (z i) ≠ 0` is removed. Discharger (height half): lane RC19's
`ZInQ.Manuscript.RC.Height.not_isOfFinAddOrder_of_CST` (the specified point `P`, trace of the
conductor-one Heegner point, is not torsion when an entire continuation `Lf` of
`L(E, s) L(E^{(k)}, s)` has `Lf'(1) ≠ 0`).

PROVED, from the remaining inputs: ellipticity of `E`; `CSTThm11Split` (PRINT) with its
conductor-one Heegner data and the trace identity `hP`; lane RC19's GLUE
`LFactorizationConductorOne E K k`; the known simple zero (`Lf`, `hLf`, `hLfeq`, `hderiv`); lane
RC15's `hcentral`, `hz`, `hu`; (4.5) at the simple zero as in lane RC15's `baseZero_node`
(`h45 : z̄ = Lm · κ(P)`, ELLIOT) with `Lm ≠ 0`; and `hkum` (GLUE: the composite of the rational
Kummer map and the comparison `i` does not kill a nontorsion point). -/
theorem simpleZero_specialization_of_CST {E : WeierstrassCurve ℚ} [E.IsElliptic] {k : ℚ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hL : ZInQ.Manuscript.RC.Height.LFactorizationConductorOne E K k) (hCST : CSTThm11Split)
    (Lf : ℂ → ℂ) (hLf : Differentiable ℂ Lf)
    (hLfeq : ∀ s : ℂ, 3 / 2 < s.re → Lf s = E.LSeries s * (qtwist E k).LSeries s)
    (hderiv : deriv Lf 1 ≠ 0)
    {A Fr : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field Fr]
    [Algebra A Fr] [IsFractionRing A Fr] (ρ : A →+* ℚ_[2])
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (D.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : D *ᵥ z = 0) (uprim : Fr)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord (D.map (algebraMap A Fr))
      (fun i => algebraMap A Fr (z i)) (fun i => algebraMap A Fr (w i)) uprim)
    (kum : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ) (hLm : Lm ≠ 0)
    (h45 : (fun i => ρ (z i)) = (Lm : ℚ_[2]) • kum P)
    (hkum : ¬ IsOfFinAddOrder P → kum P ≠ 0) :
    (D.map (algebraMap A Fr)).det = 0 ∧
      ∃ u₀ : A, algebraMap A Fr u₀ = uprim ∧
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord (D.map ρ) (fun i => ρ (z i))
          (fun i => ρ (w i)) (ρ u₀) := by
  have hPnt : ¬ IsOfFinAddOrder P :=
    ZInQ.Manuscript.RC.Height.not_isOfFinAddOrder_of_CST E k f hf Lat hLat hnCM scale hscale K hK2
      hKc hD3 hD4 hsplit a₀ b₀ c₀ hH ι y hy P hP hL hCST Lf hLf hLfeq hderiv
  have hκ : kum P ≠ 0 := hkum hPnt
  have hLm' : (Lm : ℚ_[2]) ≠ 0 := by exact_mod_cast hLm
  have hz0 : ∃ i, ρ (z i) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have h0 : (Lm : ℚ_[2]) • kum P = 0 := by
      rw [← h45]
      funext i
      exact hcon i
    exact hκ ((smul_eq_zero.mp h0).resolve_left hLm')
  exact ZInQ.Manuscript.RC.Central.simpleZero_specialization (F := Fr) ρ hρ D hcentral z w hz hz0
    uprim hu

end ZInQ.Manuscript.RC.GlueSweep.Central
