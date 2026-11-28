import ZInQKernel.Contrib.OneProof.HeightModelM4.Wedge
import ZInQKernel.Contrib.OneProof.HeightModelM5.GlobalOmega
import ZInQKernel.Contrib.OneProof.HeightModelM5.GenericGermTop

/-!
# The global sections of `ε*Ω^g` are the tree's `printedDetLattice`

For a group model `𝒢` of `A` over `𝓞_L`, with structure map `f = 𝒢.G.hom` and unit section
`e = 𝒢.unitSection`, `GG.pullOmegaTop f e g` is the sheaf `⋀^g e*Ω¹_{𝒢/𝓞_L}` on `S = Spec 𝓞_L`:
the sheafification of `V ↦ ⋀^g Γ(V, e*Ω¹)`, built from Mathlib's sheaf of modules `e*Ω¹`.
`GlobalPullOmegaTop 𝒢 g` is its module of global sections `Γ(S, ε*Ω^g)`.

* `toHodgeLine`: `⋀^g` of the generic fibre `𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}⁄𝓞_L]` maps injectively to the
  tree's Hodge line `hodgeSpace g = L ⊗ ⋀^g (𝔪_ξ/𝔪_ξ²)`, through `θ⁻¹` and `𝒪_{S,η} ≅ L`; it is
  linear thanks to the wedge identity `etaFieldEquiv_smul_wedge`.
* `genericGermPullOmegaTop`: the `𝓞_L`-linear map `Γ(S, ε*Ω^g) → hodgeSpace g`, the germ at the
  generic point followed by the stalk formulas and `toHodgeLine`.
* `printedDetLattice_eq_sheaf`: it is injective and its image is `printedDetLattice 𝒢 g`.

The image is the intersection over `s` of the images of the stalks `(ε*Ω^g)_s`
(`GG.range_genericGermTop`). Each of them contains `printedDetLattice` (a wedge of elements of
`printedOmega` is a wedge of germs at `s`), and an element in all of them has, at every maximal
ideal, a multiple by a unit there in `printedDetLattice` (`exists_smul_mem_iInf`), so lies in it.
The general argument is in `GenericGermTop.lean`; this file instantiates it.
-/

open CategoryTheory AlgebraicGeometry Opposite
open NumberField KaehlerDifferential
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM5

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

/-- `𝓞_L` acts on `𝔪_ξ/𝔪_ξ²` through `𝒪_{𝒢,ξ}`. -/
theorem cotangent_isScalarTower : IsScalarTower (𝓞 L) 𝒢.genStalk 𝒢.cotangent :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] cotangent_isScalarTower

/-- The global sections `Γ(S, ε*Ω^g)` of `⋀^g e*Ω¹_{𝒢/𝓞_L}`. -/
abbrev GlobalPullOmegaTop (g : ℕ) : Type :=
  Γ(GG.pullOmegaTop 𝒢.G.hom 𝒢.unitSection g, ⊤)

/-- `Γ(S, ε*Ω^g)` is an `𝓞_L`-module through `𝓞_L ≅ Γ(S, 𝒪_S)`. -/
noncomputable instance (g : ℕ) : Module (𝓞 L) (GlobalPullOmegaTop 𝒢 g) :=
  Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom

/-- **`⋀^g` of the generic fibre in the Hodge line**:
`w₁ ∧ ⋯ ∧ w_g ↦ 1 ⊗ θ⁻¹ w₁ ∧ ⋯ ∧ θ⁻¹ w_g`, linear over `𝒪_{S,η} ≅ L`. -/
noncomputable abbrev toHodgeLine (g : ℕ) :=
  GG.toHodge (R := 𝓞 L) (K := L) (E := Reta L) (B := 𝒢.genStalk) (V := 𝒢.cotangent)
    (W := (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) HeightModelM4.etaFieldEquiv
    (HeightModelM3.thetaEquiv 𝒢) (algebraMap_surjective 𝒢) g
    (fun x v i => HeightModelM4.etaFieldEquiv_smul_wedge 𝒢 v i x)

theorem toHodgeLine_injective (g : ℕ) : Function.Injective (toHodgeLine 𝒢 g) :=
  GG.toHodge_injective _ _ _ g _

/-- **The generic germ of the global sections of `ε*Ω^g`**, in the tree's Hodge line. -/
noncomputable def genericGermPullOmegaTop (g : ℕ) :
    GlobalPullOmegaTop 𝒢 g →ₗ[𝓞 L] 𝒢.hodgeSpace g where
  toFun m := toHodgeLine 𝒢 g
    (GG.genericGermTop 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes g m)
  map_add' a b := by
    simp only [map_add]
  map_smul' a m := by
    have h1 := GG.genericGermTop_smul 𝒢.G.hom 𝒢.unitSection
      HeightModelM2.genericPt_specializes g
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom a) m
    change toHodgeLine 𝒢 g (GG.genericGermTop 𝒢.G.hom 𝒢.unitSection
        HeightModelM2.genericPt_specializes g
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom a • m)) = a • _
    refine (congrArg (toHodgeLine 𝒢 g) h1).trans ?_
    refine (GG.toHodge_smul _ _ _ g _ _ _).trans ?_
    exact (congrArg (· • _) (HeightModelM4.etaFieldEquiv_algebraMap a)).trans
      (algebraMap_smul L a _)

theorem genericGermPullOmegaTop_apply (g : ℕ) (m : GlobalPullOmegaTop 𝒢 g) :
    genericGermPullOmegaTop 𝒢 g m = toHodgeLine 𝒢 g
      (GG.genericGermTop 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes g m) :=
  rfl

/-- **The generic germ of `Γ(S, ε*Ω^g)` is injective.** -/
theorem genericGermPullOmegaTop_injective (g : ℕ) :
    Function.Injective (genericGermPullOmegaTop 𝒢 g) :=
  (toHodgeLine_injective 𝒢 g).comp (GG.genericGermTop_injective 𝒢.G.hom 𝒢.unitSection
    HeightModelM2.genericPt_specializes g fun s => HeightModelM3.sigma_injective s)

/-! ## The image of a stalk -/

/-- The image in the Hodge line of the stalk of `ε*Ω^g` at `s`. -/
noncomputable def stalkTopMap (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L))) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat)
        (X := (Spec (CommRingCat.of (𝓞 L))).toPresheafedSpace)
        (GG.pullOmegaTop 𝒢.G.hom 𝒢.unitSection g).val.presheaf s →
      𝒢.hodgeSpace g :=
  fun y => toHodgeLine 𝒢 g
    (GG.rhoTop 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes g s y)

/-- The map from the stalk is semilinear along `σ` and `𝒪_{S,η} ≅ L`. -/
theorem stalkTopMap_smul (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L)))
    (r : (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (X := (Spec (CommRingCat.of (𝓞 L))).toPresheafedSpace)
      (GG.pullOmegaTop 𝒢.G.hom 𝒢.unitSection g).val.presheaf s) :
    stalkTopMap 𝒢 g s (r • y) =
      HeightModelM4.etaFieldEquiv (HeightModelM3.sigma s r) • stalkTopMap 𝒢 g s y := by
  have h := GG.rhoTop_smul 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes g s r y
  exact (congrArg (toHodgeLine 𝒢 g) h).trans (GG.toHodge_smul _ _ _ g _ _ _)

theorem stalkTopMap_add (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L)))
    (y z : TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (X := (Spec (CommRingCat.of (𝓞 L))).toPresheafedSpace)
      (GG.pullOmegaTop 𝒢.G.hom 𝒢.unitSection g).val.presheaf s) :
    stalkTopMap 𝒢 g s (y + z) = stalkTopMap 𝒢 g s y + stalkTopMap 𝒢 g s z := by
  simp only [stalkTopMap, map_add]

theorem stalkTopMap_zero (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L))) :
    stalkTopMap 𝒢 g s 0 = 0 := by
  simp only [stalkTopMap, map_zero]

/-- The value on a wedge of germs. -/
theorem stalkTopMap_symm_ιMulti (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L)))
    (m : Fin g → TopCat.Presheaf.stalk (C := Ab)
      (pullOmega 𝒢.G.hom 𝒢.unitSection).val.presheaf s) :
    stalkTopMap 𝒢 g s ((schemeWedgeStalkEquiv (GG.pullPre 𝒢.G.hom 𝒢.unitSection) g s).symm
        (exteriorPower.ιMulti _ g m)) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (HeightModelM3.thetaEquiv 𝒢).symm
        (GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s (m i))) := by
  have h := GG.rhoTop_symm_ιMulti 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes g
    s m
  exact (congrArg (toHodgeLine 𝒢 g) h).trans (GG.toHodge_ιMulti _ _ _ g _ _)

/-- The values of the map from the stalk at `s` on germs lie in `printedOmegaAt s`. -/
theorem phi_mem_printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L)))
    (m : TopCat.Presheaf.stalk (C := Ab) (pullOmega 𝒢.G.hom 𝒢.unitSection).val.presheaf s) :
    GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s m ∈
      printedOmegaAt 𝒢 s := by
  have h : GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s m ∈
      Set.range (HeightModelM3.stalkToGeneric 𝒢 s) :=
    ⟨GG.pullStalkEquiv 𝒢.G.hom 𝒢.unitSection s m, rfl⟩
  rw [HeightModelM3.range_stalkToGeneric] at h
  exact h

/-- Every element of `printedOmegaAt s` is the value of the map from the stalk at `s`. -/
theorem exists_phi_eq (s : Spec (CommRingCat.of (𝓞 L)))
    {u : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (hu : u ∈ printedOmegaAt 𝒢 s) :
    ∃ m : TopCat.Presheaf.stalk (C := Ab) (pullOmega 𝒢.G.hom 𝒢.unitSection).val.presheaf s,
      GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s m = u := by
  have h : u ∈ Set.range (HeightModelM3.stalkToGeneric 𝒢 s) := by
    rw [HeightModelM3.range_stalkToGeneric]; exact hu
  obtain ⟨t, ht⟩ := h
  refine ⟨(GG.pullStalkEquiv 𝒢.G.hom 𝒢.unitSection s).symm t, ?_⟩
  rw [GG.phi_apply, LinearEquiv.apply_symm_apply]
  exact ht

/-- The image of the stalk at `s` contains `printedDetLattice`. -/
theorem printedDetLattice_le_stalk (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L)))
    {x : 𝒢.hodgeSpace g} (hx : x ∈ printedDetLattice 𝒢 g) :
    x ∈ Set.range (stalkTopMap 𝒢 g s) := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hv : ∀ i, theta' 𝒢 (v i : 𝒢.cotangent) ∈ printedOmegaAt 𝒢 s := fun i =>
      (Submodule.mem_iInf _).mp (v i).2 s
    choose m hm using fun i => exists_phi_eq 𝒢 s (hv i)
    refine ⟨(schemeWedgeStalkEquiv (GG.pullPre 𝒢.G.hom 𝒢.unitSection) g s).symm
      (exteriorPower.ιMulti _ g m), ?_⟩
    rw [stalkTopMap_symm_ιMulti]
    refine congrArg _ (congrArg _ (funext fun i => ?_))
    rw [hm i]
    exact (HeightModelM3.thetaEquiv 𝒢).symm_apply_apply (v i : 𝒢.cotangent)
  | zero => exact ⟨0, stalkTopMap_zero 𝒢 g s⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, stalkTopMap_add 𝒢 g s a b⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨baseStalk s c • a, ?_⟩
    rw [stalkTopMap_smul, HeightModelM3.sigma_baseStalk]
    exact (congrArg (· • _) (HeightModelM4.etaFieldEquiv_algebraMap c)).trans
      (algebraMap_smul L c _)

/-- An element of `printedOmegaAt s` has a multiple by some `d ∉ s` in every stalk. -/
theorem exists_smul_mem_iInf_of_mem (s : Spec (CommRingCat.of (𝓞 L)))
    {u : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (hu : u ∈ printedOmegaAt 𝒢 s) :
    ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • u ∈ ⨅ s', printedOmegaAt 𝒢 s' := by
  have h : HeightModelM2.IsSecNear 𝒢 s u := HeightModelM2.printedOmegaAt_le_secNear 𝒢 s hu
  obtain ⟨V, W, hs, hVW, hmem⟩ := h
  exact HeightModelM2.exists_smul_mem_iInf 𝒢 hs hVW hmem

/-- **Locally at `s`, the image of the stalk lies in `printedDetLattice`**: every element has a
multiple by some `d ∉ s` there. -/
theorem exists_smul_stalkTopMap_mem (g : ℕ) (s : Spec (CommRingCat.of (𝓞 L)))
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (X := (Spec (CommRingCat.of (𝓞 L))).toPresheafedSpace)
      (GG.pullOmegaTop 𝒢.G.hom 𝒢.unitSection g).val.presheaf s) :
    ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • stalkTopMap 𝒢 g s y ∈ printedDetLattice 𝒢 g := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  letI : Algebra (𝓞 L) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) :=
    (baseStalk s).toAlgebra
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
  obtain ⟨ω, rfl⟩ :=
    (schemeWedgeStalkEquiv (GG.pullPre 𝒢.G.hom 𝒢.unitSection) g s).symm.surjective y
  have hω : ω ∈ Submodule.span ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
      (Set.range (exteriorPower.ιMulti ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) g)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    rw [stalkTopMap_symm_ιMulti]
    have hd : ∀ i, ∃ d : 𝓞 L, d ∉ s.asIdeal ∧
        d • GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s (m i) ∈
          ⨅ s', printedOmegaAt 𝒢 s' := fun i =>
      exists_smul_mem_iInf_of_mem 𝒢 s (phi_mem_printedOmegaAt 𝒢 s (m i))
    choose d hd hdu using hd
    refine ⟨∏ i, d i, ?_, ?_⟩
    · intro h
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hd i hi
    · have hmem : ∀ i, d i • (HeightModelM3.thetaEquiv 𝒢).symm
          (GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s (m i)) ∈
            printedOmega 𝒢 := by
        intro i
        show theta' 𝒢 (d i • (HeightModelM3.thetaEquiv 𝒢).symm
          (GG.phi 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s (m i))) ∈
            ⨅ s', printedOmegaAt 𝒢 s'
        rw [map_smul]
        change d i • (HeightModelM3.thetaEquiv 𝒢) ((HeightModelM3.thetaEquiv 𝒢).symm _) ∈ _
        rw [LinearEquiv.apply_symm_apply]
        exact hdu i
      rw [← TensorProduct.tmul_smul, ← AlternatingMap.map_smul_univ]
      exact Submodule.subset_span ⟨fun i => ⟨_, hmem i⟩, rfl⟩
  | zero =>
    refine ⟨1, fun h => s.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
    rw [map_zero, stalkTopMap_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, fun h => (s.isPrime.mem_or_mem h).elim hd₁ hd₂, ?_⟩
    rw [map_add, stalkTopMap_add, smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h₁
    · rw [mul_smul]; exact Submodule.smul_mem _ _ h₂
  | smul r x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj s.asIdeal.primeCompl r
    have hat' : HeightModelM3.sigma s r * baseStalk (genericPt L) (t : 𝓞 L) =
        baseStalk (genericPt L) a := by
      have h0 := congrArg (HeightModelM3.sigma s) hat
      rwa [map_mul, show algebraMap (𝓞 L) _ (t : 𝓞 L) = baseStalk s t from rfl,
        show algebraMap (𝓞 L) _ a = baseStalk s a from rfl, HeightModelM3.sigma_baseStalk,
        HeightModelM3.sigma_baseStalk] at h0
    have hL : algebraMap (𝓞 L) L (t : 𝓞 L) *
        HeightModelM4.etaFieldEquiv (HeightModelM3.sigma s r) = algebraMap (𝓞 L) L a := by
      rw [← HeightModelM4.etaFieldEquiv_algebraMap, ← HeightModelM4.etaFieldEquiv_algebraMap,
        ← map_mul, mul_comm]
      exact congrArg _ hat'
    have e1 : stalkTopMap 𝒢 g s
        ((schemeWedgeStalkEquiv (GG.pullPre 𝒢.G.hom 𝒢.unitSection) g s).symm (r • x)) =
        HeightModelM4.etaFieldEquiv (HeightModelM3.sigma s r) • stalkTopMap 𝒢 g s
          ((schemeWedgeStalkEquiv (GG.pullPre 𝒢.G.hom 𝒢.unitSection) g s).symm x) :=
      (congrArg (stalkTopMap 𝒢 g s) (GG.schemeWedgeStalkEquiv_symm_smul 𝒢.G.hom 𝒢.unitSection
        g s r x)).trans (stalkTopMap_smul 𝒢 g s r _)
    refine ⟨d * t, fun h => (s.isPrime.mem_or_mem h).elim hd t.2, ?_⟩
    rw [e1]
    generalize stalkTopMap 𝒢 g s
      ((schemeWedgeStalkEquiv (GG.pullPre 𝒢.G.hom 𝒢.unitSection) g s).symm x) = z at h ⊢
    have e2 : (d * (t : 𝓞 L)) • (HeightModelM4.etaFieldEquiv (HeightModelM3.sigma s r) • z) =
        a • (d • z) := by
      rw [mul_smul,
        ← smul_assoc (t : 𝓞 L) (HeightModelM4.etaFieldEquiv (HeightModelM3.sigma s r)) z,
        Algebra.smul_def (t : 𝓞 L) (HeightModelM4.etaFieldEquiv (HeightModelM3.sigma s r)), hL,
        algebraMap_smul L a z, smul_comm d a z]
    rw [e2]
    exact Submodule.smul_mem _ a h

/-! ## The global sections -/

theorem range_genericGermPullOmegaTop_eq_iInter (g : ℕ) :
    Set.range (genericGermPullOmegaTop 𝒢 g) = ⋂ s, Set.range (stalkTopMap 𝒢 g s) := by
  haveI : Nonempty (Spec (CommRingCat.of (𝓞 L))) := ⟨genericPt L⟩
  exact GG.range_comp_eq_iInter _ _
    (GG.range_genericGermTop 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes g
      fun s => HeightModelM3.sigma_injective s) _ (toHodgeLine_injective 𝒢 g)

/-- **The global sections of `ε*Ω^g` are the tree's lattice**: the generic germ
`Γ(S, ε*Ω^g) → hodgeSpace g` is injective, with image `printedDetLattice 𝒢 g`. -/
theorem printedDetLattice_eq_sheaf (g : ℕ) (hg : A.dim = g) :
    Function.Injective (genericGermPullOmegaTop 𝒢 g) ∧
      LinearMap.range (genericGermPullOmegaTop 𝒢 g) = printedDetLattice 𝒢 g := by
  refine ⟨genericGermPullOmegaTop_injective 𝒢 g, ?_⟩
  ext x
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    have hx : genericGermPullOmegaTop 𝒢 g m ∈ ⋂ s, Set.range (stalkTopMap 𝒢 g s) := by
      rw [← range_genericGermPullOmegaTop_eq_iInter]; exact ⟨m, rfl⟩
    apply GG.mem_of_forall_maximal
    intro M hM
    let s : Spec (CommRingCat.of (𝓞 L)) := ⟨M, hM.isPrime⟩
    obtain ⟨y, hy⟩ := Set.mem_iInter.1 hx s
    obtain ⟨d, hd, hdy⟩ := exists_smul_stalkTopMap_mem 𝒢 g s y
    refine ⟨d, hd, ?_⟩
    rw [← hy]
    exact hdy
  · intro hx
    have hx' : x ∈ ⋂ s, Set.range (stalkTopMap 𝒢 g s) :=
      Set.mem_iInter.2 fun s => printedDetLattice_le_stalk 𝒢 g s hx
    rw [← range_genericGermPullOmegaTop_eq_iInter] at hx'
    exact hx'

end ZInQ.HeightModelM5
