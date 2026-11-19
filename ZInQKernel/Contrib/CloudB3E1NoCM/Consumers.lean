import ZInQKernel.Contrib.CloudB3E1NoCM.Curve1
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateKummer
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateOdd
import ZInQKernel.Contrib.CloudB3E1RingClass.Complete

/-!
# The consumers of the non-CM step, from `Curve1NoCM`

Manuscript `diophantine_zq.tex`, tex 1765–1767, 3500–3702, 8319.

These are variants of the consumers of `CMjInteger`, with that GLUE replaced by the single fact
`Curve1NoCM`, which `CMjInteger` implies (`curve1NoCM_of_cmjInteger`):
* `tateImageEcurveN`, the fixed Tate image of `E_ℓ`. It is definitionally lane RC17's
  `tateImageEcurveS` (`tateImageEcurveN_eq`), since both only use a proof of `HasNoCM E_ℓ`;
* `movingSettingEcurveN` and `moving_character_ecurve_genuineN`, lane RC17's moving data and
  moving character for `E_ℓ`;
* `qtwist_ecurve_hasNoCM_of_curve1`, the twist `A = E_ℓ^{(D)}` non-CM (tex 8319);
* `moving_character_genuineN` and `moving_character_completeN`, lane E1's moving character on the
  genuine ring-class data.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1NoCM

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.GlueSweep.Tate
open ZInQ.Contrib.CloudB3E1RingClass
open scoped nonZeroDivisors

/-- **The fixed Tate image of `E_ℓ`, from `Curve1NoCM`** (tex 3597–3605). Kind: definition. -/
def tateImageEcurveN (hS : SerreThm3) (h1 : Curve1NoCM) {ℓ : ℕ} (hℓ : 0 < ℓ) : TateImage :=
  @tateImageOf (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hS
    (ecurve_hasNoCM_of_curve1 h1 hℓ)

/-- It is lane RC17's `tateImageEcurveS`. Kind: PROVED. -/
theorem tateImageEcurveN_eq (hS : SerreThm3) (h1 : Curve1NoCM) (hcm : CMjInteger) {ℓ : ℕ}
    (hℓ : 0 < ℓ) : tateImageEcurveN hS h1 hℓ = tateImageEcurveS hS hcm hℓ := rfl

/-- **Lane RC4's `MovingSetting` for `E_ℓ`, from `Curve1NoCM`** (tex 3530–3595, 3662–3693).
Kind: definition. -/
def movingSettingEcurveN (hS : SerreThm3) (h1 : Curve1NoCM) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {n : ℕ}
    (M : MovingDataK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) :
    MovingSetting (tateImageEcurveN hS h1 hℓ) n :=
  @movingSettingOf (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hS
    (ecurve_hasNoCM_of_curve1 h1 hℓ) hT n M.toMovingData

/-- **Proposition `ex:arith-moving-character` for `E_ℓ`, from `Curve1NoCM`** (tex 3500–3702).
Kind: PROVED. -/
theorem moving_character_ecurve_genuineN (hS : SerreThm3) (h1 : Curve1NoCM) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {n : ℕ}
    (M : MovingDataK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  @moving_character_genuineK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hS
    (ecurve_hasNoCM_of_curve1 h1 hℓ) hT n M B S

/-- **The twist `A = E_ℓ^{(D)}` has no CM, from `Curve1NoCM`** (tex 8319): `A = E_{Dℓ}`.
Kind: PROVED. -/
theorem qtwist_ecurve_hasNoCM_of_curve1 (h1 : Curve1NoCM) {ℓ : ℕ} (hℓ : 0 < ℓ) {D : ℚ}
    (hD : D ≠ 0) :
    @HasNoCM (ZInQ.Contrib.CloudB3RC53.qtwist (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) D)
      (qtwist_ecurve_isElliptic hℓ hD) := by
  have h := ZInQ.Manuscript.RC.PrintsAnalytic.qtwist_curve (ℓ : ℚ) D
  have hne : D * (ℓ : ℚ) ≠ 0 := mul_ne_zero hD (by exact_mod_cast hℓ.ne')
  generalize qtwist_ecurve_isElliptic hℓ hD = inst
  revert inst
  rw [show ZInQ.Contrib.CloudB3RC53.Ecurve ℓ = ZInQ.Manuscript.curve (ℓ : ℚ) from rfl, h]
  intro inst
  exact curve_hasNoCM_of_curve1 h1 hne

section Genuine

variable {K : Type} [Field K] [NumberField K] {s : ℕ} {C : RingClassSetup K s} {n ℓ : ℕ}

/-- **The moving character on the genuine groups, from `Curve1NoCM`** (tex 2729–2737,
3500–3506, 4258–4268). Kind: PROVED. -/
theorem moving_character_genuineN (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n C)
    (hS : SerreThm3) (h1 : Curve1NoCM) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ n)),
        -- surjective on the genuine inertia group at the place over `r`
        (∀ y : ZMod (2 ^ n), ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion K),
          ξ (locMap K (C.Sr r) (C.placeR r) σ) = Multiplicative.ofAdd y) ∧
        -- trivial on the genuine decomposition groups at `2N`
        (∀ v ∈ P, ∀ σ : Gloc K v, ξ (locMap K (C.Sr r) v σ) = 1) ∧
        -- value `1` at the active orientations, `−1` at their conjugates
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion K) φ →
            ξ (locMap K (C.Sr r) (C.𝔭 j) φ) = Multiplicative.ofAdd 1) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion K) φ →
            ξ (locMap K (C.Sr r) (C.𝔭bar j) φ) = Multiplicative.ofAdd (-1)) ∧
        -- the trace bounds
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ0, hin, h2N, hact, hb1, hb2, hb3, hb4, hb5⟩ :=
    moving_character_ecurve_genuineN hS h1 hℓ hT I.toMovingDataK B S
  have hgood' : GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r := hgood
  let res := ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
  let ξ0' : Additive (setupGal C r) →+ ZMod (2 ^ n) := ξ0
  let ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ n)) :=
    (AddMonoidHom.toMultiplicative ξ0').comp res
  have hξ : ∀ g, ξ g = Multiplicative.ofAdd (ξ0' (Additive.ofMul (res g))) := fun _ => rfl
  refine ⟨r, hrS, hrp, hgood', hr1, ξ, ?_, ?_, ?_, ?_, hb1, hb2, hb3, hb4, hb5⟩
  · intro y
    obtain ⟨z, hz, hzy⟩ := hin y
    obtain ⟨σ, hσ, hσz⟩ := (show Additive.toMul z ∈ inertiaGal (max r 1) (max_one_ne_zero r)
      (C.Sr r) (C.hSr r) (C.placeR r) from hz)
    refine ⟨σ, hσ, ?_⟩
    rw [hξ, ← hzy]
    exact congrArg (fun w => Multiplicative.ofAdd (ξ0' (Additive.ofMul w))) hσz
  · intro v hv σ
    obtain ⟨j, hj, hvj⟩ := hP v hv
    have hz : Additive.ofMul (res (locMap K (C.Sr r) v σ)) ∈
        setupDecomp C r j ⊔ setupDecompBar C r j := by
      rcases hvj with rfl | rfl
      · exact AddSubgroup.mem_sup_left (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
      · exact AddSubgroup.mem_sup_right (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
    rw [hξ]
    change Multiplicative.ofAdd (ξ0 _) = 1
    rw [h2N j hj _ hz]
    rfl
  · intro j hj φ hφ
    have hnm := (I.not_mem hgood' j).1
    have h1 := locGal_frobeniusLift (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭 j) hnm
      (primeToIdeal _ _ (C.𝔭 j) hnm) rfl hφ
    rw [hξ]
    congr 1
    have h2 : Additive.ofMul (res (locMap K (C.Sr r) (C.𝔭 j) φ)) = I.toMovingDataK.q r j := by
      change Additive.ofMul (locGal _ _ _ _ (C.𝔭 j) φ) = setupQ C r j
      rw [setupQ_eq hnm, h1]
    rw [h2]
    exact (hact j hj).1
  · intro j hj φ hφ
    have hnm := (I.not_mem hgood' j).2
    have h1 := locGal_frobeniusLift (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭bar j)
      hnm (primeToIdeal _ _ (C.𝔭bar j) hnm) rfl hφ
    rw [hξ]
    congr 1
    have h2 : Additive.ofMul (res (locMap K (C.Sr r) (C.𝔭bar j) φ)) =
        I.toMovingDataK.qbar r j := by
      change Additive.ofMul (locGal _ _ _ _ (C.𝔭bar j) φ) = setupQbar C r j
      rw [setupQbar_eq hnm, h1]
    rw [h2]
    exact (hact j hj).2

end Genuine

section Complete

variable {s : ZInQ.Contrib.ChebFD.C10.Qbar} {S : ℕ} {C : RingClassSetup (quadField s) S} {n : ℕ}

theorem moving_character_completeN {ℓ : ℕ}
    (I : GenuineMovingComplete (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n s C)
    (hS : ZInQ.Manuscript.RC.PrintsArith.SerreThm3) (h1 : Curve1NoCM)
    (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 (quadField s))))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (T : Finset ℕ) :
    ∃ r : ℕ, r ∉ T ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) s I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : ZInQ.Manuscript.RC.SelmerComplex.GKS (quadField s) (C.Sr r) →*
          Multiplicative (ZMod (2 ^ n)),
        (∀ y : ZMod (2 ^ n), ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion (quadField s)),
          ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.placeR r) σ) =
            Multiplicative.ofAdd y) ∧
        (∀ v ∈ P, ∀ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) v,
          ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) v σ) = 1) ∧
        (∀ j, I.act j → ∀ φ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion (quadField s)) φ →
            ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.𝔭 j) φ) =
              Multiplicative.ofAdd 1) ∧
        (∀ j, I.act j → ∀ φ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion (quadField s)) φ →
            ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.𝔭bar j) φ) =
              Multiplicative.ofAdd (-1)) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveN hS h1 hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  moving_character_genuineN I.toInputs hS h1 hℓ hT P hP B T

end Complete

end ZInQ.Contrib.CloudB3E1NoCM
