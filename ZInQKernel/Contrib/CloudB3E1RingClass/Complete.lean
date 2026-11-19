import ZInQKernel.Contrib.CloudB3E1RingClass.Final
import ZInQKernel.Contrib.CloudB3E1RingClass.InertiaSetup

/-!
# The genuine moving data with no open interface field

Manuscript `diophantine_zq.tex`, tex 3528–3595, 3662–3693.

`kummerDelta_inertia` proves `inertia_eq` for the genuine `δ = kummerDelta`, using
`setupInertia_eq_range_deltaR` (`InertiaSetup.lean`). Hence `GenuineMovingComplete`, which is
`GenuineMovingFinal` without `inertia_eq`, gives a genuine `GenuineMovingInputs`
(`GenuineMovingComplete.toInputs`) and the RC0 moving character (`moving_character_complete`).
Its fields are only:
* the data `D` (`s² = D`), `act`, `over2N`, `Sexc`;
* facts about `K = ℚ(s)` and the chosen primes: `finrank ℚ K = 2`, `𝒪_K^× = {±1}`, the `p_j` distinct
  and in `Sexc`, `𝔭_j ≠ 𝔭̄_j`, the classes `[𝔭_j]` generating `Cl(K)`, the active primes odd, the
  discriminant primes in `Sexc`, and `placeR_over`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open scoped nonZeroDivisors

variable {s : Qbar} {S : ℕ}

/-- **`inertia_eq` for the genuine `δ`** (tex 3679–3681). Kind: PROVED. -/
theorem kummerDelta_inertia (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc)
    (C : RingClassSetup (quadField s) S)
    (placeR_over : ∀ r, GoodPrime E s Sexc r →
      ((r : ℤ) : 𝓞 (quadField s)) ∈ (C.placeR r).asIdeal) :
    ∀ r, GoodPrime E s Sexc r → ∀ v,
      setupInertia C r = (kummerDelta hK E Sexc hSdisc C r v).range := by
  intro r hgood v
  rw [kummerDelta_of_good hK hSdisc C hgood v]
  refine setupInertia_eq_range_deltaR C (max_prime_of_good hgood) _ hK ?_
  rw [max_eq_left hgood.1.one_lt.le, ← Int.cast_natCast]
  exact placeR_over r hgood

/-- **The facts still assumed for the genuine moving data** (tex 3528–3595, 3662–3693): the data
and facts about `K` and the setup only. Kind: definition (of the structure). -/
structure GenuineMovingComplete (E : WeierstrassCurve ℚ) (n : ℕ) (s : Qbar) {S : ℕ}
    (C : RingClassSetup (quadField s) S) where
  hK : Module.finrank ℚ (quadField s) = 2
  hunits : ∀ ε : (𝓞 (quadField s))ˣ, ε = 1 ∨ ε = -1
  D : ℚ
  sqrtD_sq : s ^ 2 = algebraMap ℚ Qbar D
  act : Fin S → Prop
  [decAct : DecidablePred act]
  over2N : Fin S → Prop
  act_not_over2N : ∀ j, act j → ¬ over2N j
  hinj : Function.Injective C.p
  hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j
  hgen : Subgroup.closure (Set.range fun j =>
    ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤
  h2 : ∀ j, act j → (2 : 𝓞 (quadField s)) ∉ (C.𝔭 j).asIdeal
  Sexc : Finset ℕ
  p_mem : ∀ j, C.p j ∈ Sexc
  hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc
  placeR_over : ∀ r, GoodPrime E s Sexc r → ((r : ℤ) : 𝓞 (quadField s)) ∈ (C.placeR r).asIdeal

attribute [instance] GenuineMovingComplete.decAct

variable {E : WeierstrassCurve ℚ} {n : ℕ} {C : RingClassSetup (quadField s) S}

/-- `GenuineMovingFinal` with `inertia_eq` PROVED. Kind: definition. -/
def GenuineMovingComplete.toFinal (I : GenuineMovingComplete E n s C) :
    GenuineMovingFinal E n s C where
  hK := I.hK
  hunits := I.hunits
  D := I.D
  sqrtD_sq := I.sqrtD_sq
  act := I.act
  over2N := I.over2N
  act_not_over2N := I.act_not_over2N
  hinj := I.hinj
  hne := I.hne
  hgen := I.hgen
  h2 := I.h2
  Sexc := I.Sexc
  p_mem := I.p_mem
  hSdisc := I.hSdisc
  placeR_over := I.placeR_over
  inertia_eq := kummerDelta_inertia I.hK I.hSdisc C I.placeR_over

/-- **The genuine `MovingInputs`, every interface field PROVED** (tex 3528–3595, 3662–3693).
Kind: definition. -/
def GenuineMovingComplete.toInputs (I : GenuineMovingComplete E n s C) :
    GenuineMovingInputs E n C :=
  I.toFinal.toInputs

open ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.Moving in
/-- **The moving character on the genuine groups, from the data and facts about `K` alone**
(tex 2729–2737, 3500–3506, 4258–4268). Kind: PROVED. -/
theorem moving_character_complete {ℓ : ℕ}
    (I : GenuineMovingComplete (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n s C)
    (hS : ZInQ.Manuscript.RC.PrintsArith.SerreThm3) (hcm : ZInQ.Manuscript.RC.PrintsArith.CMjInteger)
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
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  moving_character_final I.toFinal hS hcm hℓ hT P hP B T

end ZInQ.Contrib.CloudB3E1RingClass
