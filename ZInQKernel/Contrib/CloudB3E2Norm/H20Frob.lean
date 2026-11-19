import ZInQKernel.Contrib.CloudB3E2Norm.H20AmbientS
import ZInQKernel.Contrib.CloudB3E2Norm.H20PresStage
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Frob
import ZInQKernel.Contrib.CloudB3E1RingClass.Frobenius

/-!
# The Frobenius of the norm relation and the leaf's point factor

Manuscript `diophantine_zq.tex`, tex 2931–2932 (`σ_q` a Frobenius at a prime above `q`),
tex 3915, 4144–4145, 4158–4172 (the point factor `e_q = a_q − z − z⁻¹`, `z = χ_h(σ_q) Ψ(σ_q)` the
scalar Frobenius value).

The Shapiro-level norm identity (`H20Assembly.h1_shapiro`, pushed to the stages by
`H20PresStage.hnorm_pres_of_transferK`) has point factor `φ(e_q)`, `e_q = a − θ(σ) − θ(σ)⁻¹` with
`θ = χ_h [π]`, for the element `σ ∈ G_{K,S}` of the norm relation. Lane RC32's chain uses
`pointFactor (a i) (z i) (zi i)` with the leaf's values, which lane RC32's Frobenius inputs tie to
the stage character at the arithmetic Frobenius of the place `w` (`CharValueAt α w z`,
`CommonCoordinate16Frob`: `α(Frob_w) = z`, `Frob_w = urFrobElt K w`). This file pins `σ` as the
image of an arithmetic Frobenius lift at `w` and identifies the point factors.

* `locMap_frobLift` (PROVED): an arithmetic Frobenius lift `φ ∈ G_{K_w}` maps to `urFrobElt K w`
  in `G_{K,S₀}` (`w ∉ S₀`); `inflMap_locMap_frobLift` (PROVED): for `σ = p_w(φ) ∈ G_{K,S}`,
  `infl(σ) = Frob_w`.
* **`eq_frobLift`** (PROVED): `φ(e_q) = pointFactor a z z⁻¹` with `z = α(Frob_w)` (pushed to the
  stage ring `k`), `α = alphaStage = χ_h · ψ ∘ π`; **`eq_frobLift_stage`**,
  **`charValueAt_frobLift`** (PROVED): for lane RC32's stage `StageRing s`, `z` is
  `stageRingChar s α (Frob_w)`, the value with `CharValueAt (stageRingChar s α) w z`.
* **`exists_sigma_frob`** (PROVED, lane E1's `exists_frobeniusLift_locGal`): at a place `w` not over
  `f` with ideal `J`, there is `σ = p_w(φ) ∈ G_{K,S}`, `φ` an arithmetic Frobenius lift, with
  `infl(σ) = Frob_w` and restriction to `H_f` the Artin class of `J` (the `σ` of the norm relation,
  tex 2931–2932).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Contrib.CloudB3E1RingClass
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

/-! ### The Frobenius element of a lift -/

section Lift

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}

/-- **An arithmetic Frobenius lift at `w ∉ S₀` maps to `Frob_w` in `G_{K,S₀}`** (tex 3478–3487).
Kind: PROVED. -/
theorem locMap_frobLift (w : NewPlaces K S₀ S) (φ : Gloc K w.1)
    (hφ : TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ) :
    locMap K S₀ w.1 φ = urFrobElt K w := by
  rw [urFactor_spec K w φ, urFrobElt, frobElt_eUr]
  exact congrArg (urFactor K w) hφ

/-- **`infl(p_w(φ)) = Frob_w`** for an arithmetic Frobenius lift `φ` at `w ∉ S₀`. Kind: PROVED. -/
theorem inflMap_locMap_frobLift (hS : S₀ ⊆ S) (w : NewPlaces K S₀ S) (φ : Gloc K w.1)
    (hφ : TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ) :
    inflMap K hS (locMap K S w.1 φ) = urFrobElt K w :=
  (locMap_compat K hS w.1 φ).trans (locMap_frobLift w φ hφ)

end Lift

/-! ### The point factor -/

section PointFactor

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  (k : Type) [CommRing k] [StageIsoA k i]
  (HP : Subgroup (GKS K S)) [HP.Normal] (hHP : HP ≤ (alphaInfl hS s hs hs0 π).ker)

/-- **The point factor at `σ = p_w(φ)`** (tex 3915, 4144–4145, 4158–4172): `φ(e_q)` is
`pointFactor a z z⁻¹` with `z = α(Frob_w)` in `k`, `α = alphaStage = χ_h · ψ ∘ π` (PROVED). -/
theorem eq_frobLift (a : ℤ) (w : NewPlaces K S₀ S) (φ : Gloc K w.1)
    (hφ : TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ) :
    phiK i ψ k (eq_ HP (thetaH hS s hs hs0 π HP hHP) a (locMap K S w.1 φ)) =
      pointFactor (a : k)
        ((eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i))
        ((eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ : (Acoef i)ˣ) :
          Acoef i)) := by
  have hz : phiK i ψ k (frobValue HP (thetaH hS s hs hs0 π HP hHP) (locMap K S w.1 φ)) =
      (eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i) := by
    change (eK k i).symm (h20RingHom ψ ((alphaShap s hs hs0 π
      (inflMap K hS (locMap K S w.1 φ)) : (MonoidAlgebra ℤ Δ)ˣ) : MonoidAlgebra ℤ Δ)) = _
    rw [h20RingHom_alphaShap, inflMap_locMap_frobLift hS w φ hφ]
  have hzi : phiK i ψ k (frobValueInv HP (thetaH hS s hs hs0 π HP hHP) (locMap K S w.1 φ)) =
      (eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ : (Acoef i)ˣ) :
        Acoef i) := by
    have h1 : phiK i ψ k (frobValueInv HP (thetaH hS s hs hs0 π HP hHP) (locMap K S w.1 φ)) *
        phiK i ψ k (frobValue HP (thetaH hS s hs hs0 π HP hHP) (locMap K S w.1 φ)) = 1 := by
      rw [← map_mul, frobValueInv, frobValue, Units.inv_mul, map_one]
    rw [hz] at h1
    have h2 : (eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ : (Acoef i)ˣ) :
        Acoef i) * (eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc _ = _ * ((eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w) : Acoef i) *
          (eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w))⁻¹ : (Acoef i)ˣ) :
            Acoef i)) := by rw [mul_comm _ ((eK k i).symm _), h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  simp only [eq_, pointFactor, map_sub, map_intCast, hz, hzi]

/-- **The point factor at lane RC32's stage** `StageRing s` (PROVED): `z` is the value of the stage
character `stageRingChar s α` at `Frob_w`. -/
theorem eq_frobLift_stage (a : ℤ) (w : NewPlaces K S₀ S) (φ : Gloc K w.1)
    (hφ : TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ) :
    letI := stageIsoA i
    phiK i ψ (StageRing i) (eq_ HP (thetaH hS s hs hs0 π HP hHP) a (locMap K S w.1 φ)) =
      pointFactor (a : StageRing i)
        (stageRingChar i (alphaStage i s hs hs0 π ψ) (urFrobElt K w) : StageRing i)
        (((stageRingChar i (alphaStage i s hs hs0 π ψ) (urFrobElt K w))⁻¹ :
          (StageRing i)ˣ) : StageRing i) := by
  let := stageIsoA i
  exact eq_frobLift hS i s hs hs0 π ψ (StageRing i) HP hHP a w φ hφ

/-- **The leaf's character value** (tex 4144–4145): `z = stageRingChar s α (Frob_w)` satisfies
lane RC32's `CharValueAt` at `w`. Kind: PROVED. -/
theorem charValueAt_frobLift (w : NewPlaces K S₀ S) :
    CharValueAt (stageRingChar i (alphaStage i s hs hs0 π ψ)) w
      (stageRingChar i (alphaStage i s hs hs0 π ψ) (urFrobElt K w) : StageRing i) := rfl

end PointFactor

/-! ### The `σ` of the norm relation -/

section Sigma

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (f : ℕ) (hf : f ≠ 0)
  (hSf : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- **The `σ` of the norm relation** (tex 2931–2932; lane E1's `exists_frobeniusLift_locGal`): at
a new place `w` not over `f`, with ideal `J`, there is `σ = p_w(φ) ∈ G_{K,S}` with `φ` an
arithmetic Frobenius lift at `w`, so that `infl(σ) = Frob_w` (the leaf's Frobenius,
`eq_frobLift`) and the restriction of `σ` to `H_f` is the Artin class of `J`. Kind: PROVED. -/
theorem exists_sigma_frob (w : NewPlaces K S₀ S) (hwf : (f : 𝓞 K) ∉ w.1.asIdeal)
    (J : TauCeti.GlobalNumberFields.integralIdealsPrimeTo
      (ringClassOrder (K := K) f hf).conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) = w.1.asIdeal) :
    ∃ φ : Gloc K w.1, TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ ∧
      inflMap K hS (locMap K S w.1 φ) = urFrobElt K w ∧
      ringClassRes f hf S hSf (locMap K S w.1 φ) = artinClass f hf S hSf J := by
  obtain ⟨φ, hφ, hloc⟩ := exists_frobeniusLift_locGal f hf S hSf w.1 hwf J hJ
  exact ⟨φ, hφ, inflMap_locMap_frobLift hS w φ hφ, hloc⟩

end Sigma

/-! ### The leaf's scalar Frobenius value -/

section Leaf

open ZInQ.Manuscript.RC.Limits (stageMap stageEquiv stageEquiv_mk truncQuot X_pow_dvd_sub_trunc)
open ZInQ.Manuscript.RC.HeegnerAlgebra (tA)

/-- `Λ → A_i` sends `t` to `t`. Kind: PROVED. -/
theorem stageMap_X (i : ℕ) : stageMap i PowerSeries.X = tA i := by
  change truncQuot _ i (PowerSeries.map _ PowerSeries.X) = _
  rw [PowerSeries.map_X]
  change Ideal.Quotient.mk _ (PowerSeries.trunc i PowerSeries.X) = Ideal.Quotient.mk _ Polynomial.X
  rw [Ideal.Quotient.eq, ← neg_sub, Ideal.neg_mem_iff]
  have h := X_pow_dvd_sub_trunc i (Polynomial.X : Polynomial (ZMod (2 ^ i)))
  rw [Polynomial.coe_X] at h
  exact Ideal.mem_span_singleton.2 h

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)

/-- **The leaf's `z` is the stage character at `Frob_w`** (tex 4144–4145, 4286–4292; lane RC32's
`CharValueAt` input): if `χ_h(Frob_w)` is the leaf's sign `x(ε(F̃r_q))` (`frobSign`) and the
moving character takes the value `1 + t` at `Frob_w`, then `CharValueAt` holds at `w` for the
stage character `stageRingChar s (χ_h · ψ ∘ π)` and the leaf's value `zAt Fam x q` at the stage
(PROVED; the two hypotheses are the scalar content of the input). -/
theorem charValueAt_leaf (w : NewPlaces K S₀ S) (Fam : ZInQ.Manuscript.RC.Family)
    (x : ZInQ.Manuscript.RC.Addr Fam.b) (q : ℕ)
    (hsign : quadChar s hs hs0 (urFrobElt K w) = frobSign Fam x q)
    (hpsi : ψ (π (urFrobElt K w)) = ZInQ.Manuscript.RC.CoefModules.onePlusT i) :
    CharValueAt (stageRingChar i (alphaStage i s hs hs0 π ψ)) w
      (stageMk i (zAt Fam x q : LamI)) := by
  unfold CharValueAt
  change (stageEquiv i).symm ((alphaStage i s hs hs0 π ψ (urFrobElt K w) : (Acoef i)ˣ) :
    Acoef i) = _
  rw [RingEquiv.symm_apply_eq, stageMk, stageEquiv_mk]
  simp only [alphaStage, charMul_apply, MonoidHom.comp_apply, Units.val_mul, hsign, hpsi, zAt,
    onePlusT_val, map_mul, intUnitsTo]
  rw [map_add, map_one, stageMap_X]
  simp [ZInQ.Manuscript.RC.CoefModules.onePlusT]

end Leaf

end ZInQ.Contrib.CloudB3E2.NormCochain
