import ZInQKernel.Contrib.CloudB3RC53.CoordLink.PreCoreQI

/-!
# E1a, part 8: the retained comparison in the non-degenerate example (non-vacuity)

For the example of `CoreExample.lean` (lane ClearingComplex's witness `identification2_example`,
class `1` on `H₁`, functional `1` on `H₂`; core `D = (0)`, class `1`, functional `−t`), the chain
map `f : C_x → core` with `f¹ = (1 on H₁)`, `f² = (−t⁻¹ on H₂, 0 on the new local summand)` has the
augmented compatibility, the augmented `C_x` is acyclic, and the cone torsion is the canonical sign
(`retainedComparison_ex`); `coordLink_comparisonExample` is E1a there from
`coordLink_of_comparison`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

/-- A based complex with nonzero torsion is acyclic. -/
theorem nonempty_contraction_of_torsion_ne_zero {K : Type*} [Field K] {κe κo : Type*}
    [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo] (C : BasedCx K κe κo)
    (σ : κe ≃ κo) (h : torsion C σ ≠ 0) : Nonempty (Contraction C) := by
  by_contra hn
  apply h
  unfold torsion
  simp only [hn, dite_false]

/-- `a = s a τ⁻¹`, `a ≠ 0` give `τ = s`. -/
theorem solve_tau {K : Type*} [Field K] {a s τ : K} (ha : a ≠ 0) (h : a = s * a * τ⁻¹) :
    τ = s := by
  have hτ : τ ≠ 0 := by
    intro h0
    rw [h0, _root_.inv_zero, mul_zero] at h
    exact ha h
  have h2 : a * τ = a * s := by
    calc a * τ = s * a * τ⁻¹ * τ := by rw [← h]
      _ = a * s := by rw [mul_assoc, inv_mul_cancel₀ hτ]; ring
  exact mul_left_cancel₀ ha h2

variable (b : ℕ) (x : Addr b)

/-- The sign-evaluated pre-cancellation complex of the example. -/
abbrev CxEx : ClearingComplex.PreComplex (FractionRing OO) := Cev ((Mex b).C.map (φO b)) x

/-- The chain map of the example. -/
def fEx : FourMap (PreComplex'.toFour (CxEx b x)) (twoTerm (coreEx.D.map ψO)) where
  f0 := 0
  f1 := fun _ j => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)) j
  f2 := fun _ j => Sum.elim (Sum.elim (fun _ => 0)
    (Sum.elim (fun _ => -(ψO PowerSeries.X)⁻¹) (fun _ => 0))) (fun _ => 0) j
  f3 := 0
  c0 := by
    have e0 : IsEmpty (Fin (CxEx b x).m0) := by change IsEmpty (Fin 0); infer_instance
    exact Matrix.ext fun i j => isEmptyElim j
  c1 := by
    have hd1 : ∀ i j, (PreComplex'.toFour (CxEx b x)).d1 i j = 0 := by
      intro i j
      rcases i with i | i
      · change (((preEx b).X.map (φO b)).map (evK (sgnChar x))) i j = 0
        simp [preEx]; rfl
      · change (((preEx b).Y.map (φO b)).map (evK (sgnChar x))) i j = 0
        simp [preEx]; rfl
    refine Matrix.ext fun i j => ?_
    change (∑ k, (coreEx.D.map ψO) i k * _) = ∑ k, _ * (PreComplex'.toFour (CxEx b x)).d1 k j
    simp [hd1, coreEx]
    exact Finset.sum_eq_zero fun k _ => zero_mul _
  c2 := Matrix.ext fun i _ => i.elim

theorem hzFEx : (fEx b x).f1 *ᵥ (evK (sgnChar x) ∘ zCore b) = ψO ∘ coreEx.zc := by
  have e0 : IsEmpty (Fin (CxEx b x).m0) := by change IsEmpty (Fin 0); infer_instance
  have e1 : IsEmpty (Fin (CxEx b x).m1) := by change IsEmpty (Fin 0); infer_instance
  funext i
  simp [fEx, mulVec, dotProduct, Fintype.sum_sum_type, coreEx]
  change evK (sgnChar x) 1 = algebraMap OO (FractionRing OO) (algebraMap Lam OO 1)
  rw [map_one, map_one, map_one]

theorem hlFEx : (ψO ∘ coreEx.wc) ᵥ* (fEx b x).f2 = evK (sgnChar x) ∘ lamCore b := by
  funext j
  rcases j with (a | (u | a)) | n
  · exact (show IsEmpty (Fin (CxEx b x).m1) by change IsEmpty (Fin 0); infer_instance).elim a
  · simp [fEx, vecMul, dotProduct, coreEx, lamCore]
    change ((Finset.univ : Finset (Fin 1)).card : FractionRing OO) *
      (ψO PowerSeries.X * (ψO PowerSeries.X)⁻¹) = evK (sgnChar x) 1
    rw [mul_inv_cancel₀ ψO_X_ne_zero, mul_one, map_one]
    simp
  · exact (show IsEmpty (Fin (CxEx b x).m2) by change IsEmpty (Fin 0); infer_instance).elim a
  · simp [fEx, vecMul, dotProduct, coreEx, lamCore]
    exact (map_zero (evK (O := OO) (sgnChar x))).symm

/-- The family of the example (address dimension `b`). -/
def famEx : Family := ⟨b, ∅, fun _ => 0⟩

theorem kmCoord_CxEx :
    kmCoord (PreComplex'.toFour (CxEx b x)) (evK (sgnChar x) ∘ zCore b)
      (evK (sgnChar x) ∘ lamCore b) (hzev (hzC (Mex b).isUnit_B (hzCore b)) x)
      (hlamev (hlamCore b) x) (σPre (Mex b).C.m0 (Mex b).C.m1 (Mex b).C.m2 (Mex b).C.N) =
      -ψO PowerSeries.X := by
  obtain ⟨hc⟩ := exists_contraction _ (FourCx.isExact_toBased _ coreEx.exact)
  exact (preCoreLink_ex (famEx b) x).trans (kmCoord_twoTerm _ _ _ _ _ _ hc hcoreK)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
/-- **Non-vacuity: the retained comparison holds in the non-degenerate example.** -/
theorem retainedComparison_ex :
    RetainedComparison (Mex b) x (zCore b) (lamCore b) (hzCore b) (hlamCore b)
      (coreEx.D.map ψO) (ψO ∘ coreEx.zc) (ψO ∘ coreEx.wc) coreEx.hz coreEx.hw := by
  obtain ⟨hD⟩ := exists_contraction _ (FourCx.isExact_toBased _ coreEx.exact)
  have hτC : torsion ((PreComplex'.toFour (CxEx b x)).aug (evK (sgnChar x) ∘ zCore b)
      (evK (sgnChar x) ∘ lamCore b) (hzev (hzC (Mex b).isUnit_B (hzCore b)) x)
      (hlamev (hlamCore b) x)).toBased
        (σPre (Mex b).C.m0 (Mex b).C.m1 (Mex b).C.m2 (Mex b).C.N) = ψO PowerSeries.X := by
    have := kmCoord_CxEx b x
    unfold kmCoord at this
    linear_combination -this
  have hτD : torsion ((twoTerm (coreEx.D.map ψO)).aug (ψO ∘ coreEx.zc) (ψO ∘ coreEx.wc)
      coreEx.hz coreEx.hw).toBased (σ₀ 1) = ψO PowerSeries.X := by
    have := kmCoord_twoTerm _ _ _ _ _ _ hD hcoreK
    unfold kmCoord at this
    exact neg_inj.mp this
  obtain ⟨hC⟩ := nonempty_contraction_of_torsion_ne_zero _ _ (hτC ▸ ψO_X_ne_zero)
  refine ⟨fEx b x, hzFEx b x, hlFEx b x, ⟨hC⟩, ?_⟩
  have key := torsion_eq_of_cone ((fEx b x).augMap _ _ (hzev (hzC (Mex b).isUnit_B (hzCore b)) x)
    (hlamev (hlamCore b) x) _ _ coreEx.hz coreEx.hw (hzFEx b x) (hlFEx b x)) hC hD (σ₀ 1)
    (σPre (Mex b).C.m0 (Mex b).C.m1 (Mex b).C.m2 (Mex b).C.N)
  have key2 := hτC.symm.trans key
  rw [hτD] at key2
  exact solve_tau ψO_X_ne_zero key2

/-- **E1a in the example, from `coordLink_of_comparison`** (non-degenerate: `ũ = −t`). -/
theorem coordLink_comparisonExample (ℓ : ℕ) (F : Family) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep (ddEx ℓ) F e g →
      CoordLink (Mex F.b).toIdentification.B (kappaOf (Mex F.b)) (φO F.b 1) 0 e g
        (cOf (Mex F.b).D (zCore F.b) (transportFun ((Mex F.b).C.map (φO F.b)) (lamCore F.b))
          (hzCore F.b) (hμ_cancel ((Mex F.b).C.map (φO F.b)) (Mex F.b).isUnit_B (hlamCore F.b))) :=
  coordLink_of_comparison (ddEx ℓ) F (Mex F.b) (zCore F.b) (lamCore F.b) (hzCore F.b)
    (hlamCore F.b) 1 hunitEx (fun _ => 0) (fun _ => -PowerSeries.X) (repEx ℓ F)
    (trianglesEx ℓ F) (hcompatEx ℓ F) (fun _ => coreEx) (hcoreEx ℓ F)
    (fun x _ => retainedComparison_ex F.b x)

end ZInQ.Contrib.CloudB3RC53.CoordLink
