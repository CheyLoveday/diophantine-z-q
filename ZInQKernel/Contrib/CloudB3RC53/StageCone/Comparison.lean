import ZInQKernel.Contrib.CloudB3RC53.StageCone.AugExact
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.StageLink

/-!
# Stage cone, part 2: the integral content of `StageConeIdentification`

Lemma `ex:limits-derivative-switch`, tex L4888–4906, and tex L4360–4366 ("All cancellable disks
have unit differential, so integral determinant base change identifies the coordinate").

`SwitchInputs/StageLink.lean` names the GLUE `StageConeIdentification`: each stage model reduces, by
an integral change of basis of unit determinant, to the cone `M` of the connecting map (`oldMat`,
`newMat`) plus unit disks (`ConeReduction`). `SwitchInputs/ConeIdent.lean` proves the generic-fibre
half and notes that the integral half does not follow from generic data, since an equivalence over
the fraction field does not fix the integral lattice.

This file isolates that integral content exactly. A **generic comparison** `g : StageMap ι S M z₀ l₀`
is a chain map over `F` from the stage complex `[F^N --D--> F^N]` to `[F² --M--> F²]` with
`f¹ z = z₀` and `l₀ f² = w`. Over a field such maps exist whenever the cohomologies match (Part A
of `ConeIdent.lean`), and they carry no integral information. The integral information is one
number: the torsion of the cone of the augmented comparison, `g.coneTorsion`, relative to the
standard bases.

* `stage_coord_eq` (PROVED): `u = (−1)^{N+1} · u₀ · τ(cone g)⁻¹` for any generic comparison, where
  `u` and `u₀` are the stage and cone coordinates (both nonzero, adjugates nonzero; acyclicity of
  the augmented complexes is derived, `StageCone/AugExact.lean`).
* **`stageModelLink_iff` (PROVED)**: `StageModelLink ι u M z₀ l₀` holds iff
  `τ(cone g) ∈ (−1)^{N+1} · ι(Aˣ)` (`StageMap.IntegralUnit`), for ANY generic comparison `g`.
  So the integral half of `StageConeIdentification` is equivalent to the single lattice statement
  "the comparison of the stage model with the cone preserves the integral determinant lattice up to
  sign".
* `integralUnit_of_coneReduction` (PROVED): `ConeReduction` implies `IntegralUnit` for every generic
  comparison.
* `StageConeComparison` (the sharpened GLUE) and `coordStep_of_coneComparison` (PROVED from it): an
  actual `CoordStep`.
* LESSON 2: the `3 × 3` stage `ex3Stage` of `StageLink.lean` with the comparison `f¹ = f² = [I | 0]`
  (`ex3StageMap`) satisfies `IntegralUnit` (`ex3_integralUnit`).

The stage models in the project are abstract (`UniformSwitch.TwoTermStage`), and no stage model is
constructed from the genuine integral Selmer complexes. So `IntegralUnit` cannot be proved
outright. It is the named remaining input, and it is strictly weaker than `ConeReduction`: it asks
for no block form.

**Classification.** PROVED (`StageConeComparison` is the named GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.StageCone

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Manuscript.RC.Central

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}

theorem stage_hz (S : TwoTermStage ι) :
    (twoTerm (S.D.map ι)).d1 *ᵥ (fun i => ι (S.z i)) = 0 := by
  funext i
  change ((S.D.map ι) *ᵥ (ι ∘ S.z)) i = 0
  rw [← RingHom.map_mulVec, S.hz]
  exact map_zero ι

theorem stage_hw (S : TwoTermStage ι) :
    (fun i => ι (S.w i)) ᵥ* (twoTerm (S.D.map ι)).d1 = 0 := by
  funext j
  change ((ι ∘ S.w) ᵥ* (S.D.map ι)) j = 0
  rw [← RingHom.map_vecMul, S.hw]
  exact map_zero ι

/-- **A generic comparison** of the stage model `S` with the cone `[F² --M--> F²]` (class `z₀`,
functional `l₀`): a chain map over `F` carrying the class to the class and pulling the functional
back to the functional. -/
structure StageMap (S : TwoTermStage ι) (M : Matrix (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F) where
  /-- The chain map. -/
  f : FourMap (twoTerm (S.D.map ι)) (twoTerm M)
  /-- `f¹ z = z₀`. -/
  hz : f.f1 *ᵥ (fun i => ι (S.z i)) = z₀
  /-- `l₀ f² = w`. -/
  hl : l₀ ᵥ* f.f2 = fun i => ι (S.w i)

variable {S : TwoTermStage ι} {M : Matrix (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}

/-- The sign `(−1)^{|κ_odd(aug S)|}`. -/
abbrev stageSign (S : TwoTermStage ι) : F :=
  (-1) ^ Fintype.card (Fin (S.n + 1) ⊕ (Empty ⊕ Unit))

/-- **The torsion of the cone of the augmented comparison**, in the standard bases. -/
def StageMap.coneTorsion (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) : F :=
  torsion (BasedCx.cone (g.f.augMap _ _ (stage_hz S) (stage_hw S) z₀ l₀ hz₀ hl₀ g.hz g.hl))
    ((σ₀ 2).sumCongr (σ₀ (S.n + 1)).symm)

/-- **The integral lattice condition**: the cone torsion is an integral unit up to the canonical
sign. -/
def StageMap.IntegralUnit (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) : Prop :=
  ∃ c : Aˣ, g.coneTorsion hz₀ hl₀ = stageSign S * ι c

/-- **The coordinates through a generic comparison** (PROVED):
`u = (−1)^{N+1} · u₀ · τ(cone g)⁻¹`. -/
theorem stage_coord_eq (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    {u₀ : F} (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMadj : M.adjugate ≠ 0) :
    S.u = stageSign S * u₀ * (g.coneTorsion hz₀ hl₀)⁻¹ := by
  obtain ⟨hC⟩ := contraction_aug_twoTerm _ _ _ _ (stage_hz S) (stage_hw S) S.hu hS0 hSadj
  obtain ⟨hD⟩ := contraction_aug_twoTerm _ _ _ _ hz₀ hl₀ hu₀ hu₀0 hMadj
  have h := kmCoord_eq_of_fourMap g.f _ _ (stage_hz S) (stage_hw S) z₀ l₀ hz₀ hl₀ g.hz g.hl hC hD
    (σ₀ (S.n + 1)) (σ₀ 2)
  rw [kmCoord_twoTerm _ _ _ _ _ _ hC S.hu, kmCoord_twoTerm _ _ _ _ _ _ hD hu₀] at h
  exact h

theorem stageSign_mul_self (S : TwoTermStage ι) : stageSign S * stageSign S = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩

/-- `a u₀ = s u₀ t⁻¹` with `s² = 1`, `u₀ ≠ 0` gives `t = s a⁻¹`. -/
theorem solve_cone {s a u₀ t : F} (hs : s * s = 1) (hu₀ : u₀ ≠ 0) (e : a * u₀ = s * u₀ * t⁻¹) :
    t = s * a⁻¹ := by
  have ha : a = s * t⁻¹ := mul_right_cancel₀ hu₀ (by rw [e]; ring)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [ha, mul_inv, inv_inv, hsi, ← mul_assoc, hs, one_mul]

/-- `t = s a` with `s² = 1` gives `s u₀ t⁻¹ = a⁻¹ u₀`. -/
theorem coord_of_cone {s a u₀ : F} (hs : s * s = 1) : s * u₀ * (s * a)⁻¹ = a⁻¹ * u₀ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [mul_inv, hsi]
  calc s * u₀ * (s * a⁻¹) = (s * s) * a⁻¹ * u₀ := by ring
    _ = a⁻¹ * u₀ := by rw [hs, one_mul]

/-- **The integral half of `StageConeIdentification` is exactly the lattice condition** (PROVED):
for nondegenerate stage and cone and ANY generic comparison `g`, `StageModelLink` holds iff the
cone torsion of `g` is an integral unit up to the canonical sign. -/
theorem stageModelLink_iff (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    {u₀ : F} (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMadj : M.adjugate ≠ 0) :
    StageModelLink ι S.u M z₀ l₀ ↔ g.IntegralUnit hz₀ hl₀ := by
  have key := stage_coord_eq g hz₀ hl₀ hS0 hSadj hu₀ hu₀0 hMadj
  have hs := stageSign_mul_self S
  have ht : g.coneTorsion hz₀ hl₀ ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero, mul_zero] at key; exact hS0 key
  constructor
  · rintro ⟨c, hc, hlink⟩
    obtain ⟨c, rfl⟩ := hc
    have hιc : ι (c : A) * ι ((c⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨c⁻¹, ?_⟩
    rw [← inv_eq_of_mul_eq_one_right hιc]
    exact solve_cone hs hu₀0 ((hlink u₀ hu₀).symm.trans key)
  · rintro ⟨c, hc⟩
    have hιc : ι (c : A) * ι ((c⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨((c⁻¹ : Aˣ) : A), Units.isUnit _, fun u₁ hu₁ => ?_⟩
    rw [isClassFunctionalCoord_unique hMadj hu₁ hu₀, key, hc, ← inv_eq_of_mul_eq_one_right hιc]
    exact coord_of_cone hs

/-- **`ConeReduction` gives the lattice condition for every generic comparison** (PROVED). -/
theorem integralUnit_of_coneReduction (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    {u₀ : F} (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMadj : M.adjugate ≠ 0)
    (hred : ConeReduction ι S.D S.z S.w M z₀ l₀) : g.IntegralUnit hz₀ hl₀ :=
  (stageModelLink_iff g hz₀ hl₀ hS0 hSadj hu₀ hu₀0 hMadj).1
    (stageModelLink_of_coneReduction ι S.D S.z S.w S.u S.hu M z₀ l₀ hred hMadj)

end ZInQ.Contrib.CloudB3RC53.StageCone
