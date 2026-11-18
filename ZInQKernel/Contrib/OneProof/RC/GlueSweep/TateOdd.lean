import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrintsArith
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image
import ZInQKernel.Contrib.CloudB3RC53.DetTateCyclotomic.Equality
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic
import ZInQKernel.Contrib.OneProof.RC.Odd.Detector
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev

/-!
# Lane RC22 (glue sweep), Tate share: the Galois inputs of lane RC12's detecting stage

Manuscript (11/5 version), Appendix F, proof of Proposition `ex:app-detector`, tex 8319–8376.
Lane RC12 (`RC/Odd/Detector.lean`) proves the algebra of this paragraph over abstract data and
lists as hypotheses, among others, "Serre's open image (GLUE/PRINT)" and "the Weil-pairing identity
`det ρ(Fr_{ℓ₀}) = ℓ₀` (GLUE)". Two of these inputs are about the genuine `2`-adic representations
that exist in the tree; here they are derived:

* tex 8319–8321, "The curve `A` is non-CM. Open image supplies ... a central scalar `z ≠ 1` in its
  Tate image", for `A = E_ℓ^{(D)}` (`ZInQ.Contrib.CloudB3RC53.qtwist (Ecurve ℓ) D`, `D ≠ 0`):
  `qtwist_ecurve_hasNoCM` (from `CMjInteger`: `A` is again a curve of the family, lane RC8's
  `qtwist_curve`) and `qtwist_ecurve_serre_scalar` (`ρ_A(g) = (1 + 2^n) · id`, from `SerreThm3`).
  The consumer is lane RC12's `IsCocycle.coboundary_of_central` (hypotheses `hρz`, `hζ`, with
  `z = ρ_A(g)` central in the image and `ζ − 1 = 2^n` a unit of `ℚ₂`).
* tex 8372–8374, "The determinant also gives `ℓ₀ ≡ −1 (mod 2^M)`": `ell0_congr_neg_one` derives the
  hypothesis `h : ((ℓ₀ : ℤ) : ZMod (2 ^ M)) = -1` of lane RC12's `mod_four_of_neg_one` from the proved
  identity `det ρ₂ = χ₂` (`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic`), for an
  element `σ ∈ G_ℚ` acting on `μ_{2^M}` as `ζ ↦ ζ^{ℓ₀}` (the action of a Frobenius at a place over
  `ℓ₀`, an input that stays a hypothesis) whose matrix is congruent modulo `2^M` to a matrix `C`
  with `det C = −1`; `ell0_mod_four` composes it with lane RC12's `mod_four_of_neg_one`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.TateWiring ZInQ.Contrib.CloudB3RC53
open scoped WeierstrassCurve

/-! ### The twist `A = E_ℓ^{(D)}` is non-CM and has a central scalar in its Tate image -/

/-- The twist `E_ℓ^{(D)}`, `ℓ > 0`, `D ≠ 0`, is elliptic (lane RC8's `qtwist_isElliptic`). -/
theorem qtwist_ecurve_isElliptic {ℓ : ℕ} (hℓ : 0 < ℓ) {D : ℚ} (hD : D ≠ 0) :
    (qtwist (Ecurve ℓ) D).IsElliptic :=
  @ZInQ.Manuscript.RC.PrintsAnalytic.qtwist_isElliptic (Ecurve ℓ) (ecurve_isElliptic hℓ) D hD

/-- **The twist `A = E_ℓ^{(D)}` has no complex multiplication** (tex 8319, "The curve `A` is
non-CM"). Kind: PROVED from `CMjInteger` (GLUE): `A = E_{Dℓ}` (lane RC8's `qtwist_curve`), whose
`j`-invariant is `35152/9` (lane RC9's `curve_hasNoCM`). -/
theorem qtwist_ecurve_hasNoCM (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) {D : ℚ} (hD : D ≠ 0) :
    @HasNoCM (qtwist (Ecurve ℓ) D) (qtwist_ecurve_isElliptic hℓ hD) := by
  have h := ZInQ.Manuscript.RC.PrintsAnalytic.qtwist_curve (ℓ : ℚ) D
  have hne : D * (ℓ : ℚ) ≠ 0 := mul_ne_zero hD (by exact_mod_cast hℓ.ne')
  generalize qtwist_ecurve_isElliptic hℓ hD = inst
  revert inst
  rw [show Ecurve ℓ = ZInQ.Manuscript.curve (ℓ : ℚ) from rfl, h]
  intro inst
  exact curve_hasNoCM hcm hne

/-- **A central scalar `z ≠ 1` in the Tate image of `A = E_ℓ^{(D)}`** (tex 8319–8321): some
`g ∈ G_ℚ` acts on `T₂A` as `u = 1 + 2^n`, `n ≥ 2` (so `ρ_A(g)` is central in `ρ_A(G_ℚ)`, and
`u − 1 = 2^n` is invertible over `ℚ₂`). Kind: PROVED from `SerreThm3` (PRINT) and `CMjInteger`
(GLUE). Consumer: the hypotheses `hρz`, `hζ` of lane RC12's `IsCocycle.coboundary_of_central`;
dischargers: lane RC9's `serre_scalar` and `qtwist_ecurve_hasNoCM`. -/
theorem qtwist_ecurve_serre_scalar (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {D : ℚ} (hD : D ≠ 0) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ, ∀ x : TateMod (qtwist (Ecurve ℓ) D) 2,
      tateRep (qtwist (Ecurve ℓ) D) 2 g x = (1 + (2 : ℤ_[2]) ^ n) • x :=
  @serre_scalar hS (qtwist (Ecurve ℓ) D) (qtwist_ecurve_isElliptic hℓ hD)
    (qtwist_ecurve_hasNoCM hcm hℓ hD)

/-! ### The determinant step `ℓ₀ ≡ −1 (mod 2^M)` -/

-- `toZModPow_det_eq_of_frob` (`det ρ₂(σ) ≡ ℓ₀ (mod 2^M)`) is in `TateChebotarev.lean` (Lane RC27).

/-- **`ℓ₀ ≡ −1 (mod 2^M)`** (tex 8372–8374, "The determinant also gives `ℓ₀ ≡ −1 (mod 2^M)`"): if
`σ ∈ G_ℚ` acts on the `2^M`-th roots of unity as `ζ ↦ ζ^{ℓ₀}` and its matrix `ρ₂(σ)` (lane RC17's
`tateMatrix`, in lane RC9's basis of `T₂E`) is congruent modulo `2^M` to a matrix `C` with
`det C = −1`, then `ℓ₀ ≡ −1 (mod 2^M)`. Kind: PROVED from the hypotheses on `σ` (the Frobenius action
on `μ_{2^M}` and the Chebotarev congruence `Fr_{ℓ₀} ≡ C`) and the proved `det ρ₂ = χ₂`. Consumer: the
hypothesis `h` of lane RC12's `mod_four_of_neg_one` (the GLUE "`det ρ(Fr_{ℓ₀}) = ℓ₀`" of
`RC/Odd/Detector.lean`), through lane RC12's `det_congr`; discharger:
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic`. -/
theorem ell0_congr_neg_one (E : WeierstrassCurve ℚ) [E.IsElliptic] {M ℓ₀ : ℕ} (σ : GalQ)
    (hfrob : ∀ ζ : Qbar, ζ ^ (2 ^ M) = 1 → σ ζ = ζ ^ ℓ₀)
    (C : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hCdet : C.det = -1)
    (hσC : (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ) =
      (PadicInt.toZModPow M).mapMatrix C) :
    ((ℓ₀ : ℤ) : ZMod (2 ^ M)) = -1 := by
  have h1 : PadicInt.toZModPow M (LinearMap.det (tateRep E 2 σ)) = -1 := by
    rw [← det_tateMatrix E σ, ZInQ.Manuscript.RC.Odd.det_congr (PadicInt.toZModPow M) hσC, hCdet,
      map_neg, map_one]
  rw [Int.cast_natCast, ← toZModPow_det_eq_of_frob E σ hfrob, h1]

/-- **`ℓ₀ ≡ 3 (mod 4)`** (tex 8374, 8437) for `M ≥ 2`. Kind: PROVED from the same hypotheses as
`ell0_congr_neg_one`. Consumer: lane RC12's `mod_four_of_neg_one` (hypothesis `h` discharged by
`ell0_congr_neg_one`). -/
theorem ell0_mod_four (E : WeierstrassCurve ℚ) [E.IsElliptic] {M ℓ₀ : ℕ} (hM : 2 ≤ M) (σ : GalQ)
    (hfrob : ∀ ζ : Qbar, ζ ^ (2 ^ M) = 1 → σ ζ = ζ ^ ℓ₀)
    (C : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hCdet : C.det = -1)
    (hσC : (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ) =
      (PadicInt.toZModPow M).mapMatrix C) :
    ℓ₀ % 4 = 3 :=
  ZInQ.Manuscript.RC.Odd.mod_four_of_neg_one hM (ell0_congr_neg_one E σ hfrob C hCdet hσC)

/-- **`Fr_{ℓ₀} ≡ C (mod 2^M)` and `ℓ₀ ≡ −1 (mod 2^M)` for Chebotarev primes** (tex 8362–8374): if
`ρ₂(σ)` has matrix `C` with `det C = −1` (Elliot's `σ = hτ`), then for every `M`, finite `F₀` (e.g.
`ℚ(√D_w, √h_*)`) and finite `S` there is a Frobenius `h` at a prime `ℓ₀ ∉ S` with `h = σ` on `F₀`,
`ρ₂(h) ≡ C (mod 2^M)` and `ℓ₀ ≡ −1 (mod 2^M)`. Kind: PROVED from the tree's Chebotarev and
`det ρ₂ = χ₂` (no remaining hypothesis beyond the data). Consumer: lane RC12's
`mod_four_of_neg_one` / `det_congr` step (its hypothesis `h` with the GLUE "`det ρ(Fr_{ℓ₀}) = ℓ₀`"
and the Chebotarev GLUE both discharged); also lane RC10's (H12) half `2^{a+1} ∣ ℓ + 1` (with
`C = J`). Dischargers: `exists_frob_congr`, `ell0_congr_neg_one`. (Lane RC27: moved here from
`TateChebotarev.lean`, statement and proof unchanged.) -/
theorem exists_ell0_congr_neg_one (E : WeierstrassCurve ℚ) [E.IsElliptic] (σ : GalQ)
    (C : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hσC : tateMatrix E σ = C) (hCdet : C.det = -1) (M : ℕ)
    (F₀ : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F₀] (S : Finset ℕ) :
    ∃ (h : GalQ) (ℓ₀ : ℕ), ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ZInQ.Contrib.ChebFD.C10.IsFrobAt h ℓ₀ ∧
      (∀ x ∈ F₀, h x = σ x) ∧
      (PadicInt.toZModPow M).mapMatrix (tateMatrix E h) = (PadicInt.toZModPow M).mapMatrix C ∧
      ((ℓ₀ : ℤ) : ZMod (2 ^ M)) = -1 := by
  obtain ⟨h, ℓ₀, hprime, hnot, -, hF, hF₀, hcong, hfrob⟩ := exists_frob_congr E σ M F₀ S
  rw [hσC] at hcong
  exact ⟨h, ℓ₀, hprime, hnot, hF, hF₀, hcong, ell0_congr_neg_one E h hfrob C hCdet hcong⟩

end ZInQ.Manuscript.RC.GlueSweep.Tate
