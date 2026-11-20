import ZInQKernel.Contrib.CloudB3E1RingClass.MovingGenuine
import ZInQKernel.Contrib.CloudB3E1RingClass.CSTBridge

/-!
# The moving character factors through the ring class field

Manuscript `diophantine_zq.tex`, tex 2847–2855 ("`θ` is a character of `Δ_f = Gal(H_f/K)`"),
3500–3506.

The moving character of `moving_character_genuine` is, by construction, restriction to the ring
class field `H_r` followed by a character of `Gal(H_r/K)`. This file exposes that:
* `moving_character_genuine_res`: the same conclusion, plus `ξ g = 1` whenever `g` restricts to the
  identity of `H_r`;
* `ringClassRes_eq_one_of_fix`: an element of `G_{K,S'}` fixing `H_r` inside `K_{S₁}` restricts to the
  identity of `H_r ⊂ K_{S}`, `S = C.Sr r`;
* `movingPsi_genuine_pi`: `movingPsi_genuine`, plus the clause that `Ψ = (1 + t)^ξ` is trivial on
  the elements fixing `H_r`, stated in the exact form of lane E2's `PiOfDelta r`
  (`H20PresClassMatch.lean`).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3E2.NormCochain (toAlgClosure ringClassField_le_KS)
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs resAbs_surjective resAbs_apply_coe resUnr_comp)
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {s : ℕ} {C : RingClassSetup K s} {n ℓ : ℕ}

/-- The order `ℤ + f𝒪_K` depends only on `f`. Kind: PROVED. -/
theorem ringClassOrder_congr {f f' : ℕ} (e : f = f') (hf : f ≠ 0) (hf' : f' ≠ 0) :
    ringClassOrder (K := K) f hf = ringClassOrder (K := K) f' hf' := by
  subst e; rfl

/-- **An element fixing `H_r` restricts to the identity of `H_r`** (tex 2847–2855). Kind: PROVED. -/
theorem ringClassRes_eq_one_of_fix {r : ℕ} [NeZero r] (hr : r.Prime) {S S' S₁ : Set (HeightOneSpectrum (𝓞 K))}
    {hS : ∀ v : HeightOneSpectrum (𝓞 K), ((max r 1 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S}
    (hS' : S ⊆ S') (h1 : S₁ ⊆ S')
    (hS₁ : ∀ v : HeightOneSpectrum (𝓞 K), ((r : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) (g : GKS K S')
    (hg : ∀ z : KS K S₁, (z : AlgebraicClosure K) ∈
        toAlgClosure (ringClassField (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K r)) →
      galS K S₁ (inflMap K h1 g) z = z) :
    ringClassRes (max r 1) (max_one_ne_zero r) S hS (inflMap K hS' g) = 1 := by
  have hmax : max r 1 = r := max_eq_left hr.one_lt.le
  have hO : ringClassOrder (K := K) (max r 1) (max_one_ne_zero r) =
      ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K r :=
    (ringClassOrder_congr hmax _ _).trans (ringClassOrder_eq_conductorOrder r)
  obtain ⟨σ, hσ⟩ := resAbs_surjective K S' g
  have hinfl : ∀ {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ S') (y : KS K T),
      ((galS K T (inflMap K hT g) y : KS K T) : AlgebraicClosure K) = σ (y : AlgebraicClosure K) := by
    intro T hT y
    have h2 : inflMap K hT g = resAbs K T σ := by rw [← hσ]; exact resUnr_comp K hT σ
    rw [show galS K T (inflMap K hT g) = resAbs K T σ from h2, resAbs_apply_coe]
  -- the conductor primes of `ℤ + r𝒪_K` lie in `S₁`
  have hcond : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal ∣ (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K r).conductor → v ∈ S₁ := by
    intro v hv
    refine hS₁ v ?_
    rw [← ringClassOrder_eq_conductorOrder r] at hv
    have hle := Ideal.le_of_dvd hv
    have := span_le_conductor_ringClassOrder (K := K) r (NeZero.ne r)
    exact hle (this (Ideal.mem_span_singleton_self _))
  ext x
  rw [ringClassRes, AlgEquiv.one_apply]
  have hc := AlgEquiv.restrictNormal_commutes (inflMap K hS' g)
    (ringClassFieldOf (max r 1) (max_one_ne_zero r) S hS) x
  have hc' := congrArg (fun w : KS K S => (w : AlgebraicClosure K)) hc
  simp only [IntermediateField.algebraMap_apply] at hc'
  refine Eq.trans hc' ?_
  change ((galS K S (inflMap K hS' g) (x : KS K S) : KS K S) : AlgebraicClosure K) = _
  rw [hinfl hS']
  -- `x` lies in `H_r ⊂ K̄`
  have hx : ((x : KS K S) : AlgebraicClosure K) ∈
      toAlgClosure (ringClassField (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K r)) := by
    have := (IntermediateField.mem_restrict _ _).mp x.2
    rw [← hO]; exact this
  let z : KS K S₁ := ⟨_, ringClassField_le_KS _ S₁ hcond hx⟩
  have hz : ((galS K S₁ (inflMap K h1 g) z : KS K S₁) : AlgebraicClosure K) =
      ((x : KS K S) : AlgebraicClosure K) := congrArg (fun w : KS K S₁ => (w : AlgebraicClosure K))
    (hg z hx)
  rw [hinfl h1] at hz
  exact hz

theorem moving_character_genuine_res (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ n)),
        -- `ξ` factors through `Gal(H_r/K)`
        (∀ g, ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) g = 1 → ξ g = 1) ∧
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
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ0, hin, h2N, hact, hb1, hb2, hb3, hb4, hb5⟩ :=
    moving_character_ecurve_genuineS hS hcm hℓ hT I.toMovingDataK B S
  have hgood' : GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r := hgood
  let res := ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
  let ξ0' : Additive (setupGal C r) →+ ZMod (2 ^ n) := ξ0
  let ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ n)) :=
    (AddMonoidHom.toMultiplicative ξ0').comp res
  have hξ : ∀ g, ξ g = Multiplicative.ofAdd (ξ0' (Additive.ofMul (res g))) := fun _ => rfl
  refine ⟨r, hrS, hrp, hgood', hr1, ξ, ?_, ?_, ?_, ?_, ?_, hb1, hb2, hb3, hb4, hb5⟩
  · intro g hg
    rw [hξ, hg, ofMul_one, map_zero]
    rfl
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

open ZInQ.Manuscript.RC.CoefModules in
/-- **`Ψ = (1 + t)^ξ` on the genuine groups, factoring through `Gal(H_r/K)`** (tex 2729–2737, 2781–2783, 4266–4268), with values
in `A_i^×` and `n = 2i`:
* `Ψ = 1 + t` on a genuine inertia element at `r`;
* `Ψ` is trivial at `2N`;
* `Ψ = 1 + t` on every Frobenius lift at the active orientations, and `(1 + t)^{-1}` at their
  conjugates;
* `Ψ` factors through `Gal(H_r/K)`: it is trivial on every element fixing `H_r`, in the form of
  lane E2's `PiOfDelta r` (tex 2847–2855).
Kind: PROVED. -/
theorem movingPsi_genuine_pi {i : ℕ} [NeZero i]
    (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (2 * i) C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ (2 * i))),
        (∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion K),
          movingCharS i ξ (locMap K (C.Sr r) (C.placeR r) σ) = onePlusT i) ∧
        (∀ v ∈ P, ∀ σ : Gloc K v, movingCharS i ξ (locMap K (C.Sr r) v σ) = 1) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion K) φ →
            movingCharS i ξ (locMap K (C.Sr r) (C.𝔭 j) φ) = onePlusT i) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion K) φ →
            movingCharS i ξ (locMap K (C.Sr r) (C.𝔭bar j) φ) = (onePlusT i)⁻¹) ∧
        -- `Ψ` factors through `Gal(H_r/K)`, in the form of `PiOfDelta r`
        ∀ [NeZero r] {S' S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS' : C.Sr r ⊆ S') (h1 : S₁ ⊆ S'),
          (∀ v : HeightOneSpectrum (𝓞 K), ((r : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) →
          ∀ g : GKS K S', (∀ z : KS K S₁,
              (z : AlgebraicClosure K) ∈
                toAlgClosure (ringClassField (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K r)) →
              galS K S₁ (inflMap K h1 g) z = z) →
            movingCharS i ξ (inflMap K hS' g) = 1 := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ, hres, hin, h2N, hact, hbar, -⟩ :=
    moving_character_genuine_res I hS hcm hℓ hT P hP B S
  have h1 : 1 < 2 ^ (2 * i) := Nat.one_lt_two_pow (by have := NeZero.ne i; omega)
  have hone : ∀ g, ξ g = Multiplicative.ofAdd 1 → movingCharS i ξ g = onePlusT i := by
    intro g hg
    have : Fact (1 < 2 ^ (2 * i)) := ⟨h1⟩
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ g) = _
    rw [hg, ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom_apply, toAdd_ofAdd, ZMod.val_one,
      pow_one]
  refine ⟨r, hrS, hrp, hgood, hr1, ξ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨σ, hσ, hσ1⟩ := hin 1
    exact ⟨σ, hσ, hone _ hσ1⟩
  · intro v hv σ
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ _) = 1
    rw [h2N v hv σ, map_one]
  · intro j hj φ hφ
    exact hone _ (hact j hj φ hφ)
  · intro j hj φ hφ
    have : Fact (1 < 2 ^ (2 * i)) := ⟨h1⟩
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ _) = _
    rw [hbar j hj φ hφ, ofAdd_neg, map_inv, ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom_apply,
      toAdd_ofAdd, ZMod.val_one, pow_one]
  · intro _ S' S₁ hS' h1 hS₁ g hg
    have hξ1 := hres (inflMap K hS' g) (ringClassRes_eq_one_of_fix hrp hS' h1 hS₁ g hg)
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ _) = 1
    rw [hξ1, map_one]

end ZInQ.Contrib.CloudB3E1RingClass
