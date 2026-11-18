import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateOdd
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Precision

/-!
# Lane RC22 (glue sweep), Tate share: `det ρ_T(Fr_ℓ) = ℓ` in lane RC10's precision rule (H12)

Manuscript (11/5 version), proof of Proposition `ex:arith-finite-heegner`, paragraph 6, tex
3088–3100: (H12) `ρ_T(Fr_ℓ) ≡ J (mod 2^{a+1})` gives `2^{a+1} ∣ a_ℓ` and `2^{a+1} ∣ ℓ + 1`. Lane RC10
(`RC/HeegnerAlgebra/Precision.lean`) proves this (`H12_divisibility_Z2`) from the GLUE inputs
`tr ρ_T(Fr_ℓ) = a_ℓ` and `det ρ_T(Fr_ℓ) = ℓ` ("the determinant is the cyclotomic character by the
Weil pairing"), taken as hypotheses `htr`, `hdet` about an abstract matrix `F`.

Here `F` is the genuine matrix of `ρ₂(σ)` (lane RC17's `tateMatrix`, in lane RC9's basis of `T₂E`)
and the determinant hypothesis is discharged by the tree's proved identity `det ρ₂ = χ₂`
(`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic`), for `σ` acting on the
`2`-power roots of unity as `ζ ↦ ζ^ℓ` (the action of a Frobenius at a place over the odd prime
`ℓ`, which stays a hypothesis). `tr ρ_T(Fr_ℓ) = a_ℓ` (Silverman V.2.3.1 with VII.3.1(b)) is not
proved in the tree and stays a hypothesis.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.TateWiring
open scoped WeierstrassCurve

/-- **`det ρ₂(σ) = ℓ` for `σ` acting on `μ_{2^∞}` as `ζ ↦ ζ^ℓ`** (tex 3091–3096, "the determinant is
the cyclotomic character by the Weil pairing"): the determinant of the matrix of `ρ₂(σ)` on `T₂E`
is `ℓ ∈ ℤ₂`. Kind: PROVED from the hypothesis on `σ` (the Frobenius action on `μ_{2^∞}`), for every
elliptic `E/ℚ`. Consumer: the GLUE hypothesis `hdet` of lane RC10's `H12_divisibility_Z2`;
discharger: `ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic` (through
`toZModPow_det_eq_of_frob` at every level). -/
theorem det_tateMatrix_eq_of_frob (E : WeierstrassCurve ℚ) [E.IsElliptic] {ℓ : ℕ} (σ : GalQ)
    (hfrob : ∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ ^ ℓ) :
    (tateMatrix E σ).det = (ℓ : ℤ_[2]) := by
  rw [det_tateMatrix]
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_det_eq_of_frob E σ (hfrob k), map_natCast]

/-- **(H12) for the genuine Tate representation** (tex 3091–3096): if the matrix of `ρ₂(σ)` is
`J + 2^{a+1} X` with `tr J = 0`, `det J = -1`, its trace is `a_ℓ`, and `σ` acts on `μ_{2^∞}` as
`ζ ↦ ζ^ℓ`, then `2^{a+1} ∣ a_ℓ` and `2^{a+1} ∣ ℓ + 1`. Kind: PROVED from those hypotheses (the
trace identity `tr ρ_T(Fr_ℓ) = a_ℓ` and the Frobenius action on `μ_{2^∞}` remain). Consumer: lane
RC10's `H12_divisibility_Z2` (hypothesis `hdet` discharged by `det_tateMatrix_eq_of_frob`). -/
theorem H12_divisibility_tate (E : WeierstrassCurve ℚ) [E.IsElliptic] (a : ℕ) (aℓ : ℤ) {ℓ : ℕ}
    (σ : GalQ) (hfrob : ∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ ^ ℓ)
    (J X : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hFJ : tateMatrix E σ = J + (2 : ℤ_[2]) ^ (a + 1) • X) (htrJ : J.trace = 0)
    (hdetJ : J.det = -1) (htr : (tateMatrix E σ).trace = (aℓ : ℤ_[2])) :
    (2 : ℤ) ^ (a + 1) ∣ aℓ ∧ (2 : ℤ) ^ (a + 1) ∣ (ℓ : ℤ) + 1 :=
  ZInQ.Manuscript.RC.HeegnerAlgebra.H12_divisibility_Z2 a aℓ (ℓ : ℤ) (tateMatrix E σ) J X hFJ
    htrJ hdetJ htr (by rw [det_tateMatrix_eq_of_frob E σ hfrob, Int.cast_natCast])

end ZInQ.Manuscript.RC.GlueSweep.Tate
