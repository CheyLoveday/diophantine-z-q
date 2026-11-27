import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Heegner
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner

/-! The reference sign in Cornut–Jetchev, evaluated at the stage's chosen
place. The realization of the print and its identification with geometric
reduction are kept explicit. -/

noncomputable section

open scoped WeierstrassCurve Classical
open WeierstrassCurve NumberField TauCeti.ClassFieldTheory
open ZInQ.Contrib.ChebFD.C10 (GQ)
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler Visibility WitnessSpec PMGeometry PrintsArith

/-- Tex 9256–9279: the action from the printed theorem identifies the image
of each source conjugate with the corresponding target translate in the
single reference sign and level fiber. -/
theorem cj_reference_class (CJ : CJReductionData) (J : CJ.PrintRealization)
    (print : J.P.Thm31) {X : Type*} (x₀ : CJ.CMPts)
    (target : CJ.Emb → X) (z : CJ.Pic → X)
    (hz : ∀ c, target (c • CJ.red x₀) = z c) (c : CJ.Pic) :
    target (CJ.red (c • x₀)) = z c := by
  rw [(CJ.thm3_1KappaOne_of_print J print).2, hz]

section Datum

variable {C : WeierstrassCurve ℤ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (C⁄ℚ)) :
    Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {hstar D : ℤ}
  (dat : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
  {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
  {a b : ℚ} {R : Order a b}
  {A : PMGeometry.Adelic (ell := p) (N := newformLevel (C⁄ℚ)) R} {ap : ℕ → ℤ}
  [(ReducedEquation C p).IsElliptic]

/-- Tex 9195–9296: the printed action and same-place point reduction give
the reference sum. The stage map is matched only at this datum, and the
input about the modular parametrization is pointwise. -/
theorem cj_lamOf_reduction
    (w : DatumPlace dat v) (hg : ¬ (p : ℤ) ∣ C.Δ)
    (Mθ : ℕ → ℕ) (θ L : ℕ) (d : PM.Evaluation (ResidueAt v) (ReducedEquation C p) (Mθ θ))
    (selG : (D' : ℤ) → Option (HeegnerDatum (C⁄ℚ) f Lat κ (D' * hstar) 1 hstar))
    (ev : StageKummer (C⁄ℚ) f Lat κ hstar Mθ)
    (hsel : selG D = some dat)
    (hev : letI := Classical.decEq (DatumField dat)
      ev θ D dat = (PM.lam d).comp (datumReduction dat v w hg))
    {O : Type*} [CommRing O]
    (CJ : CJReductionData) (J : CJ.PrintRealization) (print : J.P.Thm31)
    (x₀ : CJ.CMPts) (e : CJ.Pic ≃ DatumGalois dat) (target : CJ.Emb → ClassSet R)
    (z : CJ.Pic → ClassSet R) (hz : ∀ c, target (c • CJ.red x₀) = z c)
    (χF : CJ.Pic → O)
    (hχF : letI := dat.field; letI := dat.nf; letI := dat.nz
      ∀ c, χF c = ((chiSign dat.χ
        ((ringClassArtinEquiv (conductorOrder dat.K 1)).symm (e c)) : ℤ) : O))
    (I : letI := Classical.decEq (DatumField dat)
      InputsAtDatum A ap (datumReduction dat v w hg) (conjugate dat ∘ e)
        (fun c => target (CJ.red (c • x₀))))
    {u : ClassSet R → ℤ} (hu : letI := Classical.decEq (DatumField dat)
      PM.IsLift I.model.geometry d L u) :
    (2 : O) ^ Mθ θ ∣ ∑ c, χF c * (u (z c) : O) - (lamOf Mθ L selG ev θ D : O) := by
  have h := lamOf_reduction_at dat v w hg Mθ θ L d selG ev hsel hev e
    (fun c => target (CJ.red (c • x₀))) χF hχF I hu
  have hs : (∑ c, χF c * (u (target (CJ.red (c • x₀))) : O)) =
      ∑ c, χF c * (u (z c) : O) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [cj_reference_class CJ J print x₀ target z hz c]
  rw [← hs]
  exact h

end Datum

end ZInQ.Manuscript.RC.O7Actual
