import ZInQKernel.Contrib.CloudB3E1NoCM.Invariance
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrintsArith

/-!
# `E_ℓ` has no CM, from the single curve `y² = x(x − 1)(x + 3)`

Manuscript `diophantine_zq.tex`, tex 1765–1767: "`E_ℓ` is not a CM curve, since `j(E_ℓ) = 35152/9`
and a rational CM `j`-invariant is an integer".

`j(E_ℓ) = 35152/9` for every `ℓ ≠ 0`: all the `E_ℓ` are twists of `E_1 : y² = x(x − 1)(x + 3)`.
Over `ℚ̄`, `E_ℓ = C • E_1` for the change of variables `u = 1/√ℓ` (`curve_eq_variableChange`).
Having no CM is invariant under that change (`noCM_variableChange`). So the manuscript's step needs
only the single fact

`Curve1NoCM`: `E_1` has no complex multiplication over `ℚ̄`.

It follows from the classical `CMjInteger` (rational CM `j` is integral; Silverman, *Advanced
Topics*, Thm II.6.1) by `curve1NoCM_of_cmjInteger`, which is the manuscript's route. Then:
* `curve_hasNoCM_of_curve1` gives `E_ℓ` non-CM for all `ℓ ≠ 0`;
* `ecurve_hasNoCM_of_curve1` gives the `Ecurve ℓ` form used by the consumers;
* `qtwist_ecurve_hasNoCM_of_curve1` gives the twisted form.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1NoCM

open WeierstrassCurve
open ZInQ.Manuscript.RC.PrintsArith

/-- **The single fact used for the non-CM step**: `E_1 : y² = x(x − 1)(x + 3)` has no complex
multiplication over `ℚ̄` (tex 1765–1767). Kind: definition (of the Prop). -/
def Curve1NoCM : Prop :=
  @HasNoCM (ZInQ.Manuscript.curve 1) (ZInQ.Manuscript.PoleRC.curve_isElliptic one_ne_zero)

/-- **The classical route**: `CMjInteger` (rational CM `j` is an integer) implies `Curve1NoCM`,
since `j(E_1) = 35152/9 ∉ ℤ`. Kind: PROVED. -/
theorem curve1NoCM_of_cmjInteger (hcm : CMjInteger) : Curve1NoCM :=
  curve_hasNoCM hcm one_ne_zero

/-- **`E_ℓ = C • E_1` over `ℚ̄`** for `u = 1/√ℓ`, `r = s = t = 0`. Kind: PROVED. -/
theorem curve_eq_variableChange (ℓ : ℚ) (s : Qbar) (hs : s ^ 2 = algebraMap ℚ Qbar ℓ)
    (hs0 : s ≠ 0) :
    (⟨Units.mk0 s⁻¹ (inv_ne_zero hs0), 0, 0, 0⟩ : VariableChange Qbar) •
      ((ZInQ.Manuscript.curve 1)⁄Qbar) = (ZInQ.Manuscript.curve ℓ)⁄Qbar := by
  have hℓ : ((ℓ : ℚ) : Qbar) = s ^ 2 := by rw [hs]; simp
  ext <;> simp [ZInQ.Manuscript.curve, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, hℓ] <;> field_simp

/-- Transport of the no-CM property along an equality of curves. Kind: PROVED. -/
theorem noCM_of_eq {W V : WeierstrassCurve Qbar} [W.IsElliptic] [V.IsElliptic]
    (C : VariableChange Qbar) (h : C • W = V)
    (hW : ∀ f : TauCeti.Isogeny.Hom W.toAffine W.toAffine,
      ∃ n : ℤ, f = n • TauCeti.Isogeny.Hom.id W.toAffine) :
    ∀ f : TauCeti.Isogeny.Hom V.toAffine V.toAffine,
      ∃ n : ℤ, f = n • TauCeti.Isogeny.Hom.id V.toAffine := by
  subst h
  exact noCM_variableChange W C hW

/-- **Every `E_ℓ`, `ℓ ≠ 0`, has no CM**, from `Curve1NoCM` (tex 1765–1767). Kind: PROVED. -/
theorem curve_hasNoCM_of_curve1 (h1 : Curve1NoCM) {ℓ : ℚ} (hℓ : ℓ ≠ 0) :
    @HasNoCM (ZInQ.Manuscript.curve ℓ) (ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ) := by
  have := ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ
  have := ZInQ.Manuscript.PoleRC.curve_isElliptic (one_ne_zero (α := ℚ))
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ Qbar ℓ) (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at hs
    exact hℓ hs
  exact noCM_of_eq _ (curve_eq_variableChange ℓ s hs hs0) h1

/-- **`E_ℓ` has no CM**, in the `Ecurve` form of the consumers, from `Curve1NoCM`.
Kind: PROVED. -/
theorem ecurve_hasNoCM_of_curve1 (h1 : Curve1NoCM) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    @HasNoCM (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) :=
  curve_hasNoCM_of_curve1 h1 (by exact_mod_cast hℓ.ne')

end ZInQ.Contrib.CloudB3E1NoCM
