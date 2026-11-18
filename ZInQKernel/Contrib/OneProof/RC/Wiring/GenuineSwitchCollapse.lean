import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf

/-!
**Theorem 5.3, Lane RC0 round 4: exactly what a one-stage collapse of `RegularityInputsG` needs**

The configuration family of `RegularityInputsG` is an existential of the leaf (the address's
coefficient module and local conditions are not defined in the tree). This file states precisely
what the remaining freedom amounts to (PROVED):

* `regularityInputsG_of_unitFibre`: if at every height-one prime `𝔭 ≠ (2)` (with `2 ≠ 0` in `k(𝔭)`)
  there is ONE genuine Galois Selmer complex over `k(𝔭)` (`IsGaloisSelData`) homotopy equivalent to
  the one-stage fiber `[k --0--> k]` (cohomology dimensions `0, 1, 1, 0`), then `RegularityInputsG u`
  holds for every `u ∈ Λ[1/2]`; with `RegularityInputsG.mem_lambdaHalf`,
  `regularityInputsG_iff_of_unitFibre` (under `E`, the leaf is equivalent to its target).

So a collapse of the new leaf to its target needs this statement `E` about genuine continuous
Galois cohomology, which involves neither `u` nor the address. `E` is not available in Lean, and its
trivial candidate fails (`exZeroFamily_no_data`, `GenuineSwitchNonVacuity.lean`). Pinning the family
to the address's actual complex (a definition) removes the freedom altogether.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.Uniform Module CategoryTheory
  Matrix

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily GenuineSwitchData twoTermFiberComplex)

section Collapse

variable (P : Ideal Lambda) [P.IsPrime]

/-- The one-stage fiber `[k --0--> k]` in degrees one and two (the fiber of `oneStageAt P r`, which
does not depend on `r`). -/
abbrev unitFibre : CochainComplex (ModuleCat.{0} (ResAt P)) ℤ :=
  twoTermFiberComplex (resAt P) (oneStageAt P 1)

theorem unitFibre_d12 : (unitFibre P).d 1 2 = 0 := by
  change ModuleCat.ofHom (((oneStageAt P 1).D.map (resAt P)).mulVecLin) = 0
  rw [show ((oneStageAt P 1).D.map (resAt P)).mulVecLin = 0 from by
    apply LinearMap.ext; intro x; ext i; simp [oneStageAt]; rfl]
  rfl

theorem unitFibre_d01 : (unitFibre P).d 0 1 = 0 := by
  change ModuleCat.ofHom (0 : PUnit.{1} →ₗ[ResAt P] (Fin (0 + 1) → ResAt P)) = 0
  rfl

variable {P}

/-- `e.hom ∘ e.inv` is the identity in degree one of the one-stage fiber (both neighbouring
differentials vanish). -/
theorem unitFibre_hom_inv {C : CochainComplex (ModuleCat.{0} (ResAt P)) ℤ}
    (e : HomotopyEquiv C (unitFibre P)) (x : (unitFibre P).X 1) :
    (e.hom.f 1).hom ((e.inv.f 1).hom x) = x := by
  have hh := e.homotopyInvHomId.comm 1
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl), unitFibre_d12, unitFibre_d01,
    Limits.zero_comp, Limits.comp_zero, zero_add, zero_add] at hh
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) hh
  simpa using this

/-- The one-configuration family over a genuine fiber `F` with a model `e` of `F` by the one-stage
fiber, actual class the preimage of `1` and actual functional `r̄` pulled back. -/
def collapseFamily (F : SelData (ResAt P)) (e : HomotopyEquiv (selCx F).toCC (unitFibre P))
    (r : Localization.AtPrime P) : SwitchFamily (ResAt P) (Localization.AtPrime P) where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := F
  t := algebraMap Lambda (Localization.AtPrime P) PowerSeries.X
  zAct := (e.inv.f 1).hom (fun _ => (1 : ResAt P))
  hzAct := by
    have h := congrArg (fun f => (ModuleCat.Hom.hom f) (fun _ => (1 : ResAt P))) (e.inv.comm 1 2)
    refine h.trans ?_
    simp only [unitFibre_d12, Limits.zero_comp]
    rfl
  lamAct :=
    { toFun := fun y => (fun _ => resAt P r) ⬝ᵥ ((e.hom.f 2).hom y : Fin (0 + 1) → ResAt P)
      map_add' := fun y y' => by
        change (fun _ => resAt P r) ⬝ᵥ ((e.hom.f 2).hom (y + y') : Fin (0 + 1) → ResAt P) = _
        rw [map_add]
        exact dotProduct_add _ _ _
      map_smul' := fun c y => by
        change (fun _ => resAt P r) ⬝ᵥ ((e.hom.f 2).hom (c • y) : Fin (0 + 1) → ResAt P) = _
        rw [map_smul]
        exact dotProduct_smul _ _ _ }
  hlamAct y := by
    change (fun _ => resAt P r) ⬝ᵥ ((e.hom.f 2).hom (((selCx F).toCC.d 1 2).hom y) :
      Fin (0 + 1) → ResAt P) = 0
    have h := congrArg (fun f => (ModuleCat.Hom.hom f) y) (e.hom.comm 1 2)
    have h' : (e.hom.f 2).hom (((selCx F).toCC.d 1 2).hom y) = 0 := by
      refine h.symm.trans ?_
      simp [unitFibre_d12]
    exact (congrArg (fun v : Fin (0 + 1) → ResAt P => (fun _ => resAt P r) ⬝ᵥ v) h').trans
      (dotProduct_zero _)

/-- The genuine switching datum over `collapseFamily` starting at the coordinate `ι r`
(`oneStageAt P r`; no switch is demanded since the fiber dimension is one). -/
def collapseData (F : SelData (ResAt P)) (e : HomotopyEquiv (selCx F).toCC (unitFibre P))
    (r : Localization.AtPrime P) (h2 : (2 : ResAt P) ≠ 0) (u : FractionRing Lambda)
    (hu : UniformSwitch.toFracAt P r = u) :
    GenuineSwitchData (collapseFamily F e r) (UniformSwitch.toFracAt P) (resAt P) u where
  stage _ := oneStageAt P r
  model _ := e
  hz0 := by
    refine (unitFibre_hom_inv e _).trans ?_
    show @Eq (Fin (0 + 1) → ResAt P) (fun _ => (1 : ResAt P))
      (fun i => resAt P ((oneStageAt P r).z i))
    funext i
    simp [oneStageAt]
  hw0 y := rfl
  hu0 := hu
  σ _ := LinearMap.id
  h2 _ := h2
  hσ _ _ := LinearMap.id_comp _
  primitive _ _ := ⟨0, by simp [oneStageAt]⟩
  switch_mixed _ _ _ h := absurd h (by rw [oneStageAt_fiberDim]; exact lt_irrefl 1)
  switch_single _ _ _ _ h := absurd h (by rw [oneStageAt_fiberDim]; exact lt_irrefl 1)

/-- **The remaining freedom of `RegularityInputsG`, exactly**: given, at every height-one prime
`𝔭 ≠ (2)`, `2 ≠ 0` in `k(𝔭)` and one genuine Galois Selmer complex over `k(𝔭)` homotopy equivalent
to the one-stage fiber, `RegularityInputsG u` holds for every `u ∈ Λ[1/2]`. Kind: PROVED. -/
theorem regularityInputsG_of_unitFibre {u : FractionRing Lambda} (hu : u ∈ lambdaHalfToFrac.range)
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      (2 : ResAt P) ≠ 0 ∧ ∃ F : SelData (ResAt P), IsGaloisSelData F ∧
        Nonempty (HomotopyEquiv (selCx F).toCC (unitFibre P))) :
    RegularityInputsG u := by
  refine Or.inr fun P _ hP hne => ?_
  obtain ⟨r, hr⟩ := (mem_range_lambdaHalf_iff_forall_height_one u).mp hu P hP hne
  obtain ⟨h2, F, hF, ⟨e⟩⟩ := hE P hP hne
  exact ⟨collapseFamily F e r, ⟨fun _ => hF, rfl⟩, ⟨collapseData F e r h2 u hr⟩⟩

/-- **Under `E` the new height-one inputs are target-shaped**: with one genuine one-stage fiber at
every height-one prime, `RegularityInputsG u ↔ u ∈ Λ[1/2]`. Without `E` (not available) no such
equivalence is known. Kind: PROVED. -/
theorem regularityInputsG_iff_of_unitFibre
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      (2 : ResAt P) ≠ 0 ∧ ∃ F : SelData (ResAt P), IsGaloisSelData F ∧
        Nonempty (HomotopyEquiv (selCx F).toCC (unitFibre P))) (u : FractionRing Lambda) :
    RegularityInputsG u ↔ u ∈ lambdaHalfToFrac.range :=
  ⟨fun h => h.mem_lambdaHalf, fun hu => regularityInputsG_of_unitFibre hu hE⟩

end Collapse

end ZInQ.Manuscript.RC.Wiring
