import ZInQKernel.Contrib.CloudB3RC53.ContBridge.ComplexIso
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.InnerConjugation
import ZInQKernel.Contrib.CloudB3RC53.TameModel.UnramifiedQIso
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.TameComplex
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Fibre
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Lambda
import ZInQKernel.Contrib.CloudB3RC53.TameQuotient.TameCharacter
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization

/-!
# All-degree continuous cochain contractions

A central local group element acting by a scalar whose difference from one is
invertible contracts the full continuous cochain complex. The contraction is the
continuous prism homotopy divided by that scalar difference. It applies to
lattice-topologized coefficients as well as discrete coefficients.

The primitive inertia and moving-character scalar calculations are stated for
the actual coefficient fibre and the actual restricted local actions. A central
element of a quotient is not assumed to be central in the absolute local group.
The comparison needed to inflate a quotient contraction is kept separate.

Manuscript support: 2813–2815, 3731–3735, 3759–3779, and 5055–5061.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.StrictSymmFull.LocalContractions

open CategoryTheory CategoryTheory.Limits
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.ContBridge

section Central

variable {k G : Type} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  (X : TopRep.{0} k G)

omit [LocallyCompactSpace G] in
/-- Right translation evaluates by translating every homogeneous argument. -/
theorem translate_evaluation (a : G) (m : ℕ) (F : (TopRep.resolutionX X m).V)
    (x : Fin m → G) :
    evIt X m ((TauCeti.ContinuousCohomology.resolutionTranslate X a m).hom F) x =
      evIt X m F (fun i => x i * a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [evIt_succ, TauCeti.ContinuousCohomology.resolutionTranslate_succ_apply, ih]
    rfl

omit [LocallyCompactSpace G] in
/-- On invariant homogeneous cochains a central scalar action is literal scalar translation. -/
theorem translate_scalar (a : G) (c : k) (hcentral : ∀ g : G, g * a = a * g)
    (hscalar : ∀ m : X.V, X.ρ a m = c • m) (n : ℕ)
    (F : (TopRep.resolutionX X (n + 1)).ρ.invariants) :
    (TauCeti.ContinuousCohomology.resolutionTranslate X a (n + 1)).hom F.1 = c • F.1 := by
  apply Inv.evalIt_ext X n
  intro x
  have e₁ := evIt_succ_eq_evalIt X n
    ((TauCeti.ContinuousCohomology.resolutionTranslate X a (n + 1)).hom F.1) x
  have e₂ := evIt_succ_eq_evalIt X n (c • F.1) x
  rw [← e₁, ← e₂, translate_evaluation]
  have hx : (fun i => x i * a) = (fun i => a * x i) := funext fun i => hcentral (x i)
  rw [hx, evIt_invariant X (n + 1) F.1 F.2 a x, hscalar, evIt_smul]

/-- The continuous prism operator restricted to invariant cochains. -/
def invariantPrism (a : G) (n : ℕ) :
    ((TopRep.resolutionX X (n + 2)).ρ.invariants) →ₗ[k]
      ((TopRep.resolutionX X (n + 1)).ρ.invariants) :=
  (TauCeti.ContinuousCohomology.translateHomotopy X a (n + 1)).toLinearMap.domRestrict _ |>.codRestrict _
    (fun F => TauCeti.ContinuousCohomology.translateHomotopy_mem_invariants X a F.2)

/-- The coefficient-scaled prism operator in all positive cochain degrees. -/
def scaledPrism (a : G) (c : k) (n : ℕ) :
    ((TopRep.resolutionX X (n + 2)).ρ.invariants) →ₗ[k]
      ((TopRep.resolutionX X (n + 1)).ρ.invariants) :=
  Ring.inverse (c - 1) • invariantPrism X a n

/-- Coercion of the scaled prism to the original resolution. -/
theorem scaledPrism_coe (a : G) (c : k) (n : ℕ)
    (F : (TopRep.resolutionX X (n + 2)).ρ.invariants) :
    (scaledPrism X a c n F).1 =
      Ring.inverse (c - 1) • TauCeti.ContinuousCohomology.translateHomotopy X a (n + 1) F.1 := rfl

/-- The differential on invariant cochains, with its domain fixed explicitly. -/
def invariantD (n : ℕ) :
    (TopRep.resolutionX X (n + 1)).ρ.invariants →ₗ[k]
      (TopRep.resolutionX X (n + 2)).ρ.invariants :=
  ((TopRep.homogeneousCochains X).d n (n + 1)).hom.toLinearMap

omit [LocallyCompactSpace G] in
/-- The invariant differential is the restriction of the original resolution differential. -/
theorem invariantD_coe (n : ℕ) (F : (TopRep.resolutionX X (n + 1)).ρ.invariants) :
    (invariantD X n F).1 = (TopRep.d X (n + 1)).hom F.1 :=
  TopRep.homogeneousCochains.d_apply X n F

/-- The all-degree homogeneous contraction identity in positive degree. -/
theorem scaledPrism_identity (a : G) (c : k)
    (hcentral : ∀ g : G, g * a = a * g) (hscalar : ∀ m : X.V, X.ρ a m = c • m)
    (hc : IsUnit (c - 1)) (n : ℕ)
    (F : (TopRep.resolutionX X (n + 2)).ρ.invariants) :
    invariantD X n (scaledPrism X a c n F) +
      scaledPrism X a c (n + 1) (invariantD X (n + 1) F) = F := by
  apply Subtype.ext
  simp only [Submodule.coe_add]
  rw [invariantD_coe, scaledPrism_coe, scaledPrism_coe, invariantD_coe]
  have he := TauCeti.ContinuousCohomology.d_translateHomotopy_add_translateHomotopy_d X a (n + 1) F.1
  rw [translate_scalar X a c hcentral hscalar (n + 1) F] at he
  have hcF : c • F.1 - F.1 = (c - 1) • F.1 := by rw [sub_smul, one_smul]
  rw [map_smul, ← smul_add, he, hcF, smul_smul, Ring.inverse_mul_cancel _ hc, one_smul]

/-- Degree zero has no preceding cochain term; the same prism gives its identity. -/
theorem scaledPrism_identity_zero (a : G) (c : k)
    (hcentral : ∀ g : G, g * a = a * g) (hscalar : ∀ m : X.V, X.ρ a m = c • m)
    (hc : IsUnit (c - 1)) (F : (TopRep.resolutionX X 1).ρ.invariants) :
    scaledPrism X a c 0 (invariantD X 0 F) = F := by
  apply Subtype.ext
  rw [scaledPrism_coe, invariantD_coe]
  have he := TauCeti.ContinuousCohomology.d_translateHomotopy_add_translateHomotopy_d X a 0 F.1
  have hz : TauCeti.ContinuousCohomology.translateHomotopy X a 0 F.1 = 0 := rfl
  simp only [hz, map_zero, zero_add] at he
  rw [translate_scalar X a c hcentral hscalar 0 F] at he
  have hcF : c • F.1 - F.1 = (c - 1) • F.1 := by rw [sub_smul, one_smul]
  rw [he, hcF, smul_smul, Ring.inverse_mul_cancel _ hc, one_smul]

/-- The homogeneous complex with topologies forgotten, retaining all degrees. -/
abbrev homogeneousComplex : CochainComplex (ModuleCat k) ℕ :=
  ((forget₂ (TopModuleCat k) (ModuleCat k)).mapHomologicalComplex _).obj
    (TopRep.homogeneousCochains X)

/-- The prism maps as morphisms of the homogeneous complex. -/
def homogeneousPrismMaps (a : G) (c : k) (i j : ℕ) :
    (homogeneousComplex X).X i ⟶ (homogeneousComplex X).X j :=
  if h : j + 1 = i then
    ((homogeneousComplex X).XIsoOfEq h.symm).hom ≫ ModuleCat.ofHom (scaledPrism X a c j)
  else 0

/-- The supported component of the homogeneous prism family. -/
theorem homogeneousPrismMaps_succ (a : G) (c : k) (n : ℕ) :
    homogeneousPrismMaps X a c (n + 1) n = ModuleCat.ofHom (scaledPrism X a c n) := by
  rw [homogeneousPrismMaps, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.id_comp]

/-- The central scalar action gives an explicit full homogeneous contraction. -/
def homogeneousContraction (a : G) (c : k)
    (hcentral : ∀ g : G, g * a = a * g) (hscalar : ∀ m : X.V, X.ρ a m = c • m)
    (hc : IsUnit (c - 1)) : Homotopy (𝟙 (homogeneousComplex X)) 0 where
  hom := homogeneousPrismMaps X a c
  zero i j hij := dite_eq_right hij
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
        homogeneousPrismMaps_succ, add_zero, HomologicalComplex.zero_f_apply, add_zero]
      ext F
      exact (scaledPrism_identity_zero X a c hcentral hscalar hc F).symm
    | succ n =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
        homogeneousPrismMaps_succ, homogeneousPrismMaps_succ,
        HomologicalComplex.zero_f_apply, add_zero]
      ext F
      change F = scaledPrism X a c (n + 1) (invariantD X (n + 1) F) +
        invariantD X n (scaledPrism X a c n F)
      exact (scaledPrism_identity X a c hcentral hscalar hc n F).symm.trans (add_comm _ _)

variable (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)

/-- Transfer the explicit homogeneous contraction through the all-degree cochain dictionary. -/
def continuousContraction (a : G) (c : k)
    (hcentral : ∀ g : G, g * a = a * g) (hscalar : ∀ m : X.V, X.ρ a m = c • m)
    (hc : IsUnit (c - 1)) :
    Homotopy (𝟙 (contSub X hcont).toCx) 0 := by
  let e := cxIso X hcont
  have H := ((homogeneousContraction X a c hcentral hscalar hc).compLeft e.inv).compRight e.hom
  simpa only [Category.comp_id, Category.assoc, Iso.inv_hom_id, comp_zero, zero_comp]
    using H

end Central

section Extension

variable {k : Type} [CommRing k] (C : CochainComplex (ModuleCat k) ℕ)

/-- Extend homotopy components by zero to negative cochain degrees. -/
def extendHomotopyMaps (H : Homotopy (𝟙 C) 0) :
    ∀ i j : ℤ, (natCx C).toCC.X i ⟶ (natCx C).toCC.X j
  | Int.ofNat n, Int.ofNat m => H.hom n m
  | _, _ => 0

/-- The original adjacent differential is retained by extension to integer degrees. -/
theorem extended_adjacent_d (n : ℕ) :
    (show C.X n ⟶ C.X (n + 1) from (natCx C).toCC.d (n : ℤ) ((n + 1 : ℕ) : ℤ)) =
      C.d n (n + 1) := by
  ext x
  exact GCx.toCC_d_hom (natCx C) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega) x

/-- Extending a contracting homotopy retains its identity in every integer degree. -/
def extendContraction (H : Homotopy (𝟙 C) 0) : Homotopy (𝟙 (natCx C).toCC) 0 where
  hom := extendHomotopyMaps C H
  zero i j hij := by
    cases i with
    | ofNat n =>
      cases j with
      | ofNat m =>
        exact H.zero n m (by
          intro h
          apply hij
          change (m : ℤ) + 1 = (n : ℤ)
          exact_mod_cast h)
      | negSucc m => rfl
    | negSucc n => rfl
  comm i := by
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        erw [dNext_eq (extendHomotopyMaps C H)
            (show (ComplexShape.up ℤ).Rel (Int.ofNat 0) (Int.ofNat 1) from rfl),
          prevD_eq (extendHomotopyMaps C H)
            (show (ComplexShape.up ℤ).Rel (Int.negSucc 0) (Int.ofNat 0) from rfl)]
        ext x
        change C.X 0 at x
        change (x : C.X 0) =
          (show C.X 0 from (H.hom 1 0).hom (((natCx C).toCC.d 0 1).hom x)) +
          (0 : C.X 0) + (0 : C.X 0)
        have he := congrArg (fun f => f.hom x) (H.comm 0)
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
          HomologicalComplex.zero_f_apply] at he
        change x = (H.hom 1 0).hom ((C.d 0 1).hom x) + (0 : C.X 0) + 0 at he
        have hd := GCx.toCC_d_hom (natCx C) 0 1 rfl x
        have hh := congrArg (fun y : C.X 1 => (H.hom 1 0).hom y) hd
        exact he.trans (congrArg (fun y : C.X 0 => y + 0 + 0) hh.symm)
      | succ n =>
        erw [dNext_eq (extendHomotopyMaps C H)
            (show (ComplexShape.up ℤ).Rel (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) from by
              change ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ); omega),
          prevD_eq (extendHomotopyMaps C H)
            (show (ComplexShape.up ℤ).Rel (Int.ofNat n) (Int.ofNat (n + 1)) from by
              change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ); omega)]
        ext x
        change C.X (n + 1) at x
        change (x : C.X (n + 1)) =
          (show C.X (n + 1) from (H.hom (n + 2) (n + 1)).hom
            (((natCx C).toCC.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom x)) +
          (show C.X (n + 1) from ((natCx C).toCC.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom
            ((H.hom (n + 1) n).hom x)) + (0 : C.X (n + 1))
        have he := congrArg (fun f => f.hom x) (H.comm (n + 1))
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
          HomologicalComplex.zero_f_apply] at he
        change x = (H.hom (n + 2) (n + 1)).hom ((C.d (n + 1) (n + 2)).hom x) +
          (C.d n (n + 1)).hom ((H.hom (n + 1) n).hom x) + (0 : C.X (n + 1)) at he
        have hd₁ := GCx.toCC_d_hom (natCx C) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) (by omega) x
        have hh₁ := congrArg (fun y : C.X (n + 2) => (H.hom (n + 2) (n + 1)).hom y) hd₁
        have hh₂ := GCx.toCC_d_hom (natCx C) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
          ((H.hom (n + 1) n).hom x)
        exact he.trans (congrArg (fun y : C.X (n + 1) => y + 0)
          (congrArg₂ (fun u v : C.X (n + 1) => u + v) hh₁ hh₂).symm)
    | negSucc n =>
      ext x
      exact Subsingleton.elim (α := PUnit) _ _

end Extension

section ContinuousModule

variable {k G M : Type} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [SMulCommClass G k M] [ContinuousSMul k M] [ContinuousSMul G M]

/-- The actual continuous module action as a bundled representation. -/
def moduleAction : G →* (M →L[k] M) where
  toFun g := ⟨{ toFun := fun m => g • m
                map_add' := smul_add g
                map_smul' := fun c m => smul_comm g c m }, continuous_const_smul g⟩
  map_one' := by ext m; exact one_smul G m
  map_mul' g h := by ext m; exact mul_smul g h m

/-- Bundle the actual coefficient module without changing its topology or its action. -/
def moduleRep : TopRep.{0} k G := TopRep.of (ContRepresentation.ofMonoidHom (moduleAction (k := k) (G := G) (M := M)))

/-- The all-degree cochain dictionary uses the same actual coefficient module and action. -/
def moduleDictionary :
    (contSub (moduleRep (k := k) (G := G) (M := M))
      (show Continuous fun p : G × M => p.1 • p.2 from continuous_smul)).toCx ≅ contCochains k G M :=
  Iso.refl _

/-- The full continuous cochain complex contracts in every degree under the central scalar criterion. -/
def fullContinuousContraction (a : G) (c : k)
    (hcentral : ∀ g : G, g * a = a * g) (hscalar : ∀ m : M, a • m = c • m)
    (hc : IsUnit (c - 1)) : Homotopy (𝟙 (natCx (contCochains k G M)).toCC) 0 := by
  let X := moduleRep (k := k) (G := G) (M := M)
  let hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2 :=
    show Continuous fun p : G × M => p.1 • p.2 from continuous_smul
  have H : Homotopy (𝟙 (contCochains k G M)) 0 :=
    continuousContraction X hcont a c hcentral hscalar hc
  exact extendContraction (contCochains k G M) H

end ContinuousModule

section ContinuousConstantScalar

variable {k G M : Type} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [SMulCommClass G k M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- The all-degree contraction only requires continuous constant scalar maps.
A discrete auxiliary scalar topology is used for the homogeneous dictionary;
it does not change the actual coefficient topology or the continuous cochains. -/
def fullContinuousConstContraction (a : G) (c : k)
    (hcentral : ∀ g : G, g * a = a * g) (hscalar : ∀ m : M, a • m = c • m)
    (hc : IsUnit (c - 1)) : Homotopy (𝟙 (natCx (contCochains k G M)).toCC) 0 := by
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  have : ContinuousSMul k M := by
    refine ⟨?_⟩
    rw [continuous_prod_of_discrete_left]
    intro c
    exact continuous_const_smul c
  exact fullContinuousContraction a c hcentral hscalar hc

end ContinuousConstantScalar

section OpenKernelContinuity

open Filter Topology

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

/-- A group character with open kernel is locally constant, hence continuous
for the retained topology on its values. -/
theorem continuous_character_of_open_kernel (χ : G →* H)
    (hker : IsOpen (χ.ker : Set G)) : Continuous χ := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU := hker.preimage (show Continuous (fun x : G => g⁻¹ * x) from continuous_const.mul continuous_id)
  have hg : g ∈ (fun x : G => g⁻¹ * x) ⁻¹' (χ.ker : Set G) := by
    change χ (g⁻¹ * g) = 1
    rw [inv_mul_cancel, map_one]
  have hc : ContinuousAt (fun _ : G => χ g) g := continuousAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hg] with x hx
  have he : χ (g⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv] at he
  exact (inv_mul_eq_one.mp he).symm

end OpenKernelContinuity

section FibreActions

open NumberField IsDedekindDomain TensorProduct
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ)

/-- The actual coefficient fibre restricted to the local group at an old place. -/
abbrev fibreAt (v : Places K S) : Type := ResMod (locMap K S v.1) (VP K S W P α)

/-- The actual local action, as a fibre-linear endomorphism. -/
def fibreAction (v : Places K S) (σ : Gloc K v.1) : Module.End (ResAt P) (fibreAt W P α v) where
  toFun m := σ • m
  map_add' := smul_add σ
  map_smul' c m := smul_comm σ c m

omit [IsHeightOneOdd P] in
/-- If the actual Tate action is trivial at an inertia element, its action on the
actual coefficient fibre is exactly the reduced character scalar. -/
theorem fibre_action_of_tate_fix (v : Places K S) (σ : Gloc K v.1)
    (hT : ∀ Q : TateS K S W, locMap K S v.1 σ • Q = Q) :
    ∀ m : fibreAt W P α v,
      σ • m = algebraMap Lambda (ResAt P) ((α (locMap K S v.1 σ) : Lambdaˣ) : Lambda) • m := by
  intro m
  change VP K S W P α at m
  change locMap K S v.1 σ • m =
    algebraMap Lambda (ResAt P) ((α (locMap K S v.1 σ) : Lambdaˣ) : Lambda) • m
  induction m using VP.induction with
  | zero => rw [smul_zero, smul_zero]
  | tmul c Q =>
    rw [VP.smul_tmul, coe_resChar, hT]
    change (algebraMap Lambda (ResAt P) ((α (locMap K S v.1 σ) : Lambdaˣ) : Lambda) * c) ⊗ₜ[ℤ_[2]] Q =
      algebraMap Lambda (ResAt P) ((α (locMap K S v.1 σ) : Lambdaˣ) : Lambda) • (c ⊗ₜ[ℤ_[2]] Q)
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

variable (χ : GKS K S →* ℤˣ) (ξ : GKS K S →* Multiplicative ℤ_[2])

omit [IsHeightOneOdd P] in
/-- The primitive inertia calculation for the actual fibre of χ(1+t)^ξ. -/
theorem fibre_primitive_inertia (v : Places K S) (σ : Gloc K v.1)
    (hT : ∀ Q : TateS K S W, locMap K S v.1 σ • Q = Q)
    (hχ : χ (locMap K S v.1 σ) = -1) (hξ : ξ (locMap K S v.1 σ) = 1) :
    ∀ m : fibreAt W P (lambdaChar χ ξ) v, σ • m = -m := by
  intro m
  have he := fibre_action_of_tate_fix W P (lambdaChar χ ξ) v σ hT m
  have hzero : Multiplicative.toAdd (1 : Multiplicative ℤ_[2]) = 0 := rfl
  rw [coe_lambdaChar, hχ, hξ, hzero, onePlusTPow_zero, mul_one,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one,
    neg_one_smul] at he
  exact he

/-- The unit hypothesis at every permitted odd height-one localization is discharged
for the actual primitive inertia-minus-one operator. -/
theorem fibre_primitive_inertia_unit (v : Places K S) (σ : Gloc K v.1)
    (hT : ∀ Q : TateS K S W, locMap K S v.1 σ • Q = Q)
    (hχ : χ (locMap K S v.1 σ) = -1) (hξ : ξ (locMap K S v.1 σ) = 1) :
    IsUnit (fibreAction W P (lambdaChar χ ξ) v σ - 1) := by
  have he : fibreAction W P (lambdaChar χ ξ) v σ - 1 =
      algebraMap (ResAt P) (Module.End (ResAt P) (fibreAt W P (lambdaChar χ ξ) v)) (-2) := by
    ext m
    change σ • m - m = (-2 : ResAt P) • m
    rw [fibre_primitive_inertia W P χ ξ v σ hT hχ hξ m]
    rw [show (-2 : ResAt P) = -(1 + 1) from by ring, neg_smul, add_smul, one_smul,
      sub_eq_add_neg, neg_add]
  rw [he]
  exact (isUnit_two_resAt (IsHeightOneOdd.height_eq (P := P)) (IsHeightOneOdd.ne_two (P := P))).neg.map _

omit [IsHeightOneOdd P] in
/-- The moving inertia calculation uses the actual character value ξ(σ)=1 and
keeps the actual unramified Tate action. -/
theorem fibre_moving_inertia (v : Places K S) (σ : Gloc K v.1)
    (hT : ∀ Q : TateS K S W, locMap K S v.1 σ • Q = Q)
    (hχ : χ (locMap K S v.1 σ) = 1)
    (hξ : Multiplicative.toAdd (ξ (locMap K S v.1 σ)) = 1) :
    ∀ m : fibreAt W P (lambdaChar χ ξ) v,
      σ • m = (1 + algebraMap Lambda (ResAt P) (PowerSeries.X : Lambda)) • m := by
  intro m
  have he := fibre_action_of_tate_fix W P (lambdaChar χ ξ) v σ hT m
  have hpow : onePlusTPow (1 : ℤ_[2]) = (1 + PowerSeries.X : Lambda) := by
    simpa only [Nat.cast_one, pow_one] using onePlusTPow_natCast 1
  rw [coe_lambdaChar, hχ, hξ, Units.val_one, Int.cast_one, one_mul, hpow,
    map_add, map_one] at he
  exact he

/-- Away from the central moving localization, the actual moving inertia-minus-one
operator is a unit. -/
theorem fibre_moving_inertia_unit (v : Places K S) (σ : Gloc K v.1)
    (hT : ∀ Q : TateS K S W, locMap K S v.1 σ • Q = Q)
    (hχ : χ (locMap K S v.1 σ) = 1)
    (hξ : Multiplicative.toAdd (ξ (locMap K S v.1 σ)) = 1)
    (hP : P ≠ Ideal.span {(PowerSeries.X : Lambda)}) :
    IsUnit (fibreAction W P (lambdaChar χ ξ) v σ - 1) := by
  have he : fibreAction W P (lambdaChar χ ξ) v σ - 1 =
      algebraMap (ResAt P) (Module.End (ResAt P) (fibreAt W P (lambdaChar χ ξ) v))
        (algebraMap Lambda (ResAt P) (PowerSeries.X : Lambda)) := by
    ext m
    change σ • m - m = algebraMap Lambda (ResAt P) (PowerSeries.X : Lambda) • m
    rw [fibre_moving_inertia W P χ ξ v σ hT hχ hξ m, add_smul, one_smul,
      add_sub_cancel_left]
  rw [he]
  have hu := (movingInertiaUnit_proof P (IsHeightOneOdd.height_eq (P := P)) hP).2
  have hu' : IsUnit (algebraMap Lambda (ResAt P) (PowerSeries.X : Lambda)) := by
    have h := hu.map (resAt P).toMonoidHom
    change IsUnit (algebraMap Lambda (ResAt P) (PowerSeries.X : Lambda)) at h
    exact h
  exact hu'.map _

omit [IsHeightOneOdd P] in
/-- Actual primitive inertia supplies the tame matrix relation for every retained
local Frobenius operator, without an operator-commutation premise. -/
theorem primitive_fibre_tame_relation (v : Places K S) (φ σ : Gloc K v.1) (r : ℕ)
    (hσ : ∀ m : fibreAt W P α v, σ • m = -m) :
    (fibreAction W P α v φ - normQ r (fibreAction W P α v σ)) *
        (fibreAction W P α v σ - 1) =
      (fibreAction W P α v σ - 1) * (fibreAction W P α v φ - 1) := by
  have he : fibreAction W P α v σ = -1 := by
    ext m
    exact hσ m
  apply (tameCommutator_proof (ResAt P) (fibreAt W P α v) r
    (fibreAction W P α v φ) (fibreAction W P α v σ)).2.2
  · rw [he]; noncomm_ring
  · rw [he]; noncomm_ring

/-- The manuscript's tame complex with the actual retained fibre operators. -/
def primitiveFibreTameComplex (v : Places K S) (φ σ : Gloc K v.1) (r : ℕ)
    (hσ : ∀ m : fibreAt W P α v, σ • m = -m) : CochainComplex (ModuleCat (ResAt P)) ℤ :=
  tameComplex (fibreAction W P α v φ - 1) (fibreAction W P α v σ - 1)
    (fibreAction W P α v φ - normQ r (fibreAction W P α v σ))
    (primitive_fibre_tame_relation W P α v φ σ r hσ)

end FibreActions

section ActualPrimes

open NumberField IsDedekindDomain TauCeti ValuativeRel
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Contrib.CloudB3RC53.TameQuotient ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)

/-- The actual global square root in the local algebraic closure, through the retained embedding. -/
def localRoot (v : Places K S) : AlgebraicClosure (v.1.adicCompletion K) :=
  decompLift K v.1 (s : AlgebraicClosure K)

include hs in
/-- The retained global-to-local square root is a root of the actual localized radicand. -/
theorem localRoot_square (v : Places K S) :
    localRoot s v ^ 2 = algebraMap (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))
      (algebraMap K (v.1.adicCompletion K) h) := by
  have hh : (s : AlgebraicClosure K) ^ 2 = algebraMap K (AlgebraicClosure K) h :=
    congrArg (fun x : KS K S => (x : AlgebraicClosure K)) hs
  rw [localRoot, ← map_pow, hh, decompLift_algebraMap]
  rfl

/-- The localization action commutes with the retained square-root embedding. -/
theorem localRoot_localization (v : Places K S) (σ : Gloc K v.1) :
    decompLift K v.1 ((galS K S (locMap K S v.1 σ) s : KS K S) : AlgebraicClosure K) =
      (@id (AlgebraicClosure (v.1.adicCompletion K) ≃ₐ[v.1.adicCompletion K]
        AlgebraicClosure (v.1.adicCompletion K)) σ) (localRoot s v) := by
  have hres := resAbs_apply_coe K S
    (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v.1 σ)) s
  exact (congrArg (decompLift K v.1) hres).trans
    (decompLift_decompMap K v.1 σ (s : AlgebraicClosure K))

/-- A local inertia element moving the actual square root has quadratic-character value minus one. -/
theorem actual_quadChar_inertia_value (v : Places K S) (σ : Gloc K v.1)
    (hmove : (@id (AlgebraicClosure (v.1.adicCompletion K) ≃ₐ[v.1.adicCompletion K]
        AlgebraicClosure (v.1.adicCompletion K)) σ) (localRoot s v) = -localRoot s v) :
    quadChar s hs hs0 (locMap K S v.1 σ) = -1 := by
  have hsneg : galS K S (locMap K S v.1 σ) s = -s := by
    apply Subtype.ext
    apply (decompLift K v.1).injective
    rw [localRoot_localization s v σ, hmove]
    change -localRoot s v = decompLift K v.1 (-(s : AlgebraicClosure K))
    rw [map_neg]
    rfl
  have hne := neg_ne_self_of_ne_zero s hs0
  simp [quadChar, hsneg, hne]

/-- At an actual old prime of odd residue characteristic where the radicand is a
uniformizer, a genuine inertia element realizes the primitive quadratic sign. -/
theorem exists_actual_primitive_inertia (v : Places K S)
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K]))
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : (normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0)).toAdd = 1) :
    ∃ σ : Gloc K v.1,
      σ ∈ TauCeti.inertiaSubgroup (v.1.adicCompletion K) ∧
        quadChar s hs hs0 (locMap K S v.1 σ) = -1 := by
  have hroot := localRoot_square s hs v
  have hroot0 : localRoot s v ≠ 0 := by
    rw [localRoot]
    exact (map_ne_zero (decompLift K v.1)).2 (by
      intro hz
      exact hs0 (Subtype.ext hz))
  obtain ⟨σ, hσI, hσroot⟩ := exists_tame_generator hodd hroot hroot0 hh0 hv
  have hmove : σ (localRoot s v) = -localRoot s v := by
    rw [apply_eq_kummerVal_mul hroot0, hσroot.eq_neg_one_of_two_right, neg_one_mul]
  exact ⟨σ, hσI, actual_quadChar_inertia_value s hs hs0 v σ hmove⟩

/-- Inertia is killed by the actual unramified restriction. -/
theorem urRes_inertia_one (v : Places K S) (σ : Gloc K v.1)
    (hσ : σ ∈ TauCeti.inertiaSubgroup (v.1.adicCompletion K)) : urRes K v.1 σ = 1 := by
  change restrictMaximalUnramifiedHom (v.1.adicCompletion K) σ = 1
  rw [← ker_restrictMaximalUnramifiedHom] at hσ
  exact hσ

end ActualPrimes

section SmallSupport

open NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K]
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]

/-- Inclusion of actual torsion commutes with the actual local Galois action,
using the retained decomposition map rather than a freely chosen lift. -/
theorem inclTors_actual_local_action (N : ℕ) [NeZero N]
    (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (Q : TorsS K S W N) :
    inclTors (S := S) W N (locMap K S v σ • Q) =
      Multiplicative.toAdd (W.torsionGaloisAction (N : ℤ)
        (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v σ)))
        (inclTors (S := S) W N Q) := by
  let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := decompMap K v σ
  have hcomp : τ.toAlgHom.comp (inclS K S) =
      (inclS K S).comp (galS K S (locMap K S v σ)).toAlgHom := by
    ext x
    exact (resAbs_apply_coe K S τ x).symm
  apply Subtype.ext
  rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply, coe_inclTors, coe_inclTors,
    coe_smul_torsS, Affine.Point.map_map, Affine.Point.map_map]
  exact congrArg (fun f : KS K S →ₐ[K] AlgebraicClosure K =>
    Affine.Point.map f (Q : (W.baseChange (KS K S)).toAffine.Point)) hcomp.symm

/-- The actual full torsion over a smaller coefficient support is fixed by
inertia at every old place outside that support. -/
theorem torsion_fixed_outside_coefficient_support (N : ℕ) [NeZero N]
    (hFull : FullTorsion K S₀ W N) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S₀) (σ : Gloc K v) (hσ : σ ∈ TauCeti.inertiaSubgroup (v.adicCompletion K))
    (Q : TorsS K S W N) : locMap K S v σ • Q = Q := by
  have hur : urRes K v σ = 1 := by
    change TauCeti.restrictMaximalUnramifiedHom (v.adicCompletion K) σ = 1
    rw [← TauCeti.ker_restrictMaximalUnramifiedHom] at hσ
    exact hσ
  have hloc : locMap K S₀ v σ = 1 := locMap_eq_one_of_urRes_eq_one K S₀ v hv σ hur
  obtain ⟨Q₀, hQ₀⟩ := (inclTors_bijective (S := S₀) W N hFull).2 (inclTors (S := S) W N Q)
  have h0 := inclTors_actual_local_action (S := S₀) W N v σ Q₀
  rw [hloc, one_smul, hQ₀] at h0
  apply inclTors_injective W N
  exact (inclTors_actual_local_action W N v σ Q).trans h0.symm

/-- This removes the Tate-inertia premise for actual coefficients: full two-power
torsion over the smaller coefficient support supplies it in every degree of the inverse limit. -/
theorem tate_fixed_outside_coefficient_support [HasFullTwoTorsion K S₀ W]
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S₀)
    (σ : Gloc K v) (hσ : σ ∈ TauCeti.inertiaSubgroup (v.adicCompletion K))
    (Q : TateS K S W) : locMap K S v σ • Q = Q := by
  apply TateS.ext'
  intro n
  have : NeZero (2 ^ n : ℕ) := ⟨pow_ne_zero n two_ne_zero⟩
  have he := torsion_fixed_outside_coefficient_support (S := S) (S₀ := S₀) W (2 ^ n)
    (HasFullTwoTorsion.full (K := K) (S := S₀) (W := W) n) v hv σ hσ (projLev n Q)
  exact congrArg Subtype.val he

/-- The moving character inflated from the smaller support is unramified at
an actual old place outside that support. -/
theorem inflated_character_inertia_one (hS : S₀ ⊆ S)
    {A : Type} [Group A] (ξ₀ : GKS K S₀ →* A)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S₀)
    (σ : Gloc K v) (hσ : σ ∈ TauCeti.inertiaSubgroup (v.adicCompletion K)) :
    ξ₀ (inflMap K hS (locMap K S v σ)) = 1 := by
  have hur : urRes K v σ = 1 := by
    change TauCeti.restrictMaximalUnramifiedHom (v.adicCompletion K) σ = 1
    rw [← TauCeti.ker_restrictMaximalUnramifiedHom] at hσ
    exact hσ
  rw [locMap_compat K hS v σ, locMap_eq_one_of_urRes_eq_one K S₀ v hv σ hur, map_one]

end SmallSupport

section ActualPrimitiveFibre

open NumberField IsDedekindDomain TauCeti ValuativeRel
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S₀ W]
  (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])

/-- At an actual old primitive prime, the retained coefficient fibre admits a
unit inertia-minus-one operator. The Tate and moving-character inertia premises
are consequences of the smaller coefficient support, not additional operator inputs. -/
theorem exists_actual_old_primitive_unit (v : Places K S) (hv₀ : v.1 ∉ S₀)
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K]))
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : (normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0)).toAdd = 1) :
    ∃ σ : Gloc K v.1,
      σ ∈ inertiaSubgroup (v.1.adicCompletion K) ∧
      (∀ m : fibreAt W P (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v,
        σ • m = -m) ∧
      IsUnit (fibreAction W P
        (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v σ - 1) := by
  obtain ⟨σ, hσI, hσχ⟩ := exists_actual_primitive_inertia s hs hs0 v hodd hh0 hv
  have hT : ∀ Q : TateS K S W, locMap K S v.1 σ • Q = Q :=
    tate_fixed_outside_coefficient_support (S₀ := S₀) W v.1 hv₀ σ hσI
  have hξ : (ξ₀.comp (inflMap K hS).toMonoidHom) (locMap K S v.1 σ) = 1 :=
    inflated_character_inertia_one hS ξ₀ v.1 hv₀ σ hσI
  exact ⟨σ, hσI,
    fibre_primitive_inertia W P (quadChar s hs hs0) _ v σ hT hσχ hξ,
    fibre_primitive_inertia_unit W P (quadChar s hs hs0) _ v σ hT hσχ hξ⟩

/-- The displayed tame contraction is now bound to the actual old primitive prime
and actual fibre. Its construction uses no retained-cochain comparison as input. -/
theorem exists_actual_old_primitive_tame_contraction (v : Places K S) (hv₀ : v.1 ∉ S₀)
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K]))
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : (normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0)).toAdd = 1)
    (φ : Gloc K v.1) (r : ℕ) :
    ∃ σ : Gloc K v.1, σ ∈ inertiaSubgroup (v.1.adicCompletion K) ∧
      ∃ hσ : ∀ m : fibreAt W P
        (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v, σ • m = -m,
        Nonempty (Homotopy (𝟙 (primitiveFibreTameComplex W P
          (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v φ σ r hσ)) 0) := by
  obtain ⟨σ, hσI, hσ, hunit⟩ := exists_actual_old_primitive_unit hS W P s hs hs0 ξ₀ v hv₀ hodd hh0 hv
  refine ⟨σ, hσI, hσ, ?_⟩
  exact tameComplexContractible_proof (ResAt P)
    (fibreAt W P (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v)
    _ _ _ _ (Or.inr hunit)

end ActualPrimitiveFibre

namespace PrimitiveQuotientModel

open NumberField IsDedekindDomain
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α₀ : GKS K S₀ →* Lambdaˣ) [IsContChar α₀]

/-- The actual unramified local Galois group at a retained place. -/
def UrGroup (q : NewPlaces K S₀ S) : Type := GUr K q.1
instance urGroup (q : NewPlaces K S₀ S) : Group (UrGroup q) :=
  inferInstanceAs (Group (GUr K q.1))
instance urTopology (q : NewPlaces K S₀ S) : TopologicalSpace (UrGroup q) :=
  inferInstanceAs (TopologicalSpace (GUr K q.1))
instance urTopologicalGroup (q : NewPlaces K S₀ S) : IsTopologicalGroup (UrGroup q) :=
  inferInstanceAs (IsTopologicalGroup (GUr K q.1))
instance urCompact (q : NewPlaces K S₀ S) : CompactSpace (UrGroup q) :=
  inferInstanceAs (CompactSpace (GUr K q.1))
instance urT2 (q : NewPlaces K S₀ S) : T2Space (UrGroup q) := krullTopology_t2
instance urLocallyCompact (q : NewPlaces K S₀ S) : LocallyCompactSpace (UrGroup q) := inferInstance

/-- The retained canonical unramified factor, with the same group and topology. -/
def actMap (q : NewPlaces K S₀ S) : UrGroup q →ₜ* GKS K S₀ where
  toFun := urFactor K q
  map_one' := map_one (urFactor K q)
  map_mul' := map_mul (urFactor K q)
  continuous_toFun := (urFactor K q).continuous

/-- The actual restriction to the unramified local quotient. -/
def quotientUrRes (q : NewPlaces K S₀ S) : Gloc K q.1 →ₜ* UrGroup q where
  toFun := urRes K q.1
  map_one' := map_one (urRes K q.1)
  map_mul' := map_mul (urRes K q.1)
  continuous_toFun := (urRes K q.1).continuous

/-- The retained unramified restriction is onto. -/
theorem quotientUrRes_surjective (q : NewPlaces K S₀ S) :
    Function.Surjective (quotientUrRes q) := urRes_surjective K q.1

/-- The actual smaller-support fibre, with the quadratic and unramified quotient actions retained. -/
def Carrier (_q : NewPlaces K S₀ S) : Type := VP K S₀ W P α₀

instance carrierAdd (q : NewPlaces K S₀ S) : AddCommGroup (Carrier W P α₀ q) :=
  inferInstanceAs (AddCommGroup (VP K S₀ W P α₀))
instance carrierModule (q : NewPlaces K S₀ S) : Module (ResAt P) (Carrier W P α₀ q) :=
  inferInstanceAs (Module (ResAt P) (VP K S₀ W P α₀))
instance carrierTop (q : NewPlaces K S₀ S) : TopologicalSpace (Carrier W P α₀ q) :=
  inferInstanceAs (TopologicalSpace (VP K S₀ W P α₀))
instance carrierTopAdd (q : NewPlaces K S₀ S) : IsTopologicalAddGroup (Carrier W P α₀ q) :=
  inferInstanceAs (IsTopologicalAddGroup (VP K S₀ W P α₀))
instance carrierContinuousConstantScalar (q : NewPlaces K S₀ S) :
    ContinuousConstSMul (ResAt P) (Carrier W P α₀ q) :=
  inferInstanceAs (ContinuousConstSMul (ResAt P) (VP K S₀ W P α₀))

instance baseAction (q : NewPlaces K S₀ S) :
    DistribMulAction (GKS K S₀) (Carrier W P α₀ q) :=
  inferInstanceAs (DistribMulAction (GKS K S₀) (VP K S₀ W P α₀))
instance baseScalarComm (q : NewPlaces K S₀ S) :
    SMulCommClass (GKS K S₀) (ResAt P) (Carrier W P α₀ q) :=
  inferInstanceAs (SMulCommClass (GKS K S₀) (ResAt P) (VP K S₀ W P α₀))
instance baseContinuous (q : NewPlaces K S₀ S) :
    ContinuousSMul (GKS K S₀) (Carrier W P α₀ q) :=
  inferInstanceAs (ContinuousSMul (GKS K S₀) (VP K S₀ W P α₀))

/-- The quadratic sign acts by the identity or negation on the actual fibre. -/
def signAction (q : NewPlaces K S₀ S) (ε : ℤˣ) (m : Carrier W P α₀ q) : Carrier W P α₀ q :=
  if ε = 1 then m else -m

omit [IsHeightOneOdd P] [IsContChar α₀] in
/-- Integer-unit scalar multiplication is the same quadratic sign action. -/
theorem intUnits_signAction (q : NewPlaces K S₀ S) (ε : ℤˣ) (m : Carrier W P α₀ q) :
    (ε : ℤ) • m = signAction W P α₀ q ε m := by
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp only [Units.val_one, one_smul, signAction, ite_true]
  · simp only [Units.val_neg, Units.val_one, neg_one_smul, signAction, ite_eq_right hn]

omit [IsHeightOneOdd P] [IsContChar α₀] in
/-- The quadratic sign action is jointly continuous for the actual lattice topology. -/
theorem signAction_continuous (q : NewPlaces K S₀ S) :
    Continuous (fun p : ℤˣ × Carrier W P α₀ q => signAction W P α₀ q p.1 p.2) := by
  rw [continuous_prod_of_discrete_left]
  intro ε
  by_cases hε : ε = 1
  · have hc : Continuous (fun m : Carrier W P α₀ q => m) := continuous_id
    exact hc.congr fun m => (ite_eq_left hε).symm
  · have hc : Continuous (fun m : Carrier W P α₀ q => -m) := continuous_neg
    exact hc.congr fun m => (ite_eq_right hε).symm

/-- The quotient action combines the actual unramified factor with the quadratic sign. -/
instance quotientAction (q : NewPlaces K S₀ S) :
    DistribMulAction (UrGroup q × ℤˣ) (Carrier W P α₀ q) where
  smul g m := (g.2 : ℤ) • (actMap q g.1 • m)
  one_smul m := by
    change (1 : ℤ) • (actMap q 1 • m) = m
    rw [map_one, one_smul, one_smul]
  mul_smul g h m := by
    change ((g.2 * h.2 : ℤˣ) : ℤ) • (actMap q (g.1 * h.1) • m) =
      (g.2 : ℤ) • (actMap q g.1 • ((h.2 : ℤ) • (actMap q h.1 • m)))
    rw [Units.val_mul, map_mul, mul_smul, mul_smul]
    exact congrArg (fun x : Carrier W P α₀ q => (g.2 : ℤ) • x)
      (smul_comm (actMap q g.1) (h.2 : ℤ) (actMap q h.1 • m)).symm
  smul_zero g := by
    change (g.2 : ℤ) • (actMap q g.1 • (0 : Carrier W P α₀ q)) = 0
    rw [smul_zero, smul_zero]
  smul_add g x y := by
    change (g.2 : ℤ) • (actMap q g.1 • (x + y)) =
      (g.2 : ℤ) • (actMap q g.1 • x) + (g.2 : ℤ) • (actMap q g.1 • y)
    rw [smul_add, smul_add]

instance quotientScalarComm (q : NewPlaces K S₀ S) :
    SMulCommClass (UrGroup q × ℤˣ) (ResAt P) (Carrier W P α₀ q) where
  smul_comm g c m := by
    change (g.2 : ℤ) • (actMap q g.1 • (c • m)) = c • ((g.2 : ℤ) • (actMap q g.1 • m))
    rw [smul_comm (actMap q g.1) c, smul_comm (g.2 : ℤ) c]

/-- The quotient action remains jointly continuous for the actual lattice topology. -/
instance quotientContinuous (q : NewPlaces K S₀ S) :
    ContinuousSMul (UrGroup q × ℤˣ) (Carrier W P α₀ q) where
  continuous_smul := by
    change Continuous (fun p : (UrGroup q × ℤˣ) × Carrier W P α₀ q =>
      (p.1.2 : ℤ) • (actMap q p.1.1 • p.2))
    have hg : Continuous (fun p : (UrGroup q × ℤˣ) × Carrier W P α₀ q =>
        actMap q p.1.1 • p.2) :=
      ((actMap q).continuous.comp (continuous_fst.comp continuous_fst)).smul continuous_snd
    have hsign := (signAction_continuous W P α₀ q).comp
      ((continuous_snd.comp continuous_fst).prodMk hg)
    exact hsign.congr fun p =>
      (intUnits_signAction W P α₀ q p.1.2 (actMap q p.1.1 • p.2)).symm

/-- The primitive quadratic sign is central in the quotient, without a claim
that an inertia lift is central in the absolute local group. -/
theorem primitive_central (q : NewPlaces K S₀ S) :
    ∀ g : UrGroup q × ℤˣ, g * (1, -1) = (1, -1) * g := by
  intro g
  apply Prod.ext
  · exact (mul_one g.1).trans (one_mul g.1).symm
  · exact mul_comm g.2 (-1)

omit [IsHeightOneOdd P] [IsContChar α₀] in
/-- The quotient primitive sign acts literally by minus one on the actual coefficient fibre. -/
theorem primitive_scalar (q : NewPlaces K S₀ S) :
    ∀ m : Carrier W P α₀ q, ((1, -1) : UrGroup q × ℤˣ) • m = (-1 : ResAt P) • m := by
  intro m
  change (-1 : ℤ) • (actMap q 1 • m) = (-1 : ResAt P) • m
  rw [map_one, one_smul, neg_one_smul, neg_one_smul]

/-- The full continuous cochains of the genuine primitive quadratic/unramified
quotient model contract in all integer degrees. This does not identify inflation
with a homotopy equivalence of absolute local cochains. -/
def contraction (q : NewPlaces K S₀ S) :
    Homotopy (𝟙 (natCx (contCochains (ResAt P) (UrGroup q × ℤˣ)
      (Carrier W P α₀ q))).toCC) 0 := by
  have hfiniteSigns : Finite ℤˣ := by
    let f : ℤˣ → Bool := fun u => decide (u = 1)
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    have hf : Function.Injective f := by
      intro u v he
      rcases Int.units_eq_one_or u with rfl | rfl <;>
        rcases Int.units_eq_one_or v with rfl | rfl <;> simp_all [f]
    exact Finite.of_injective f hf
  have hcompactSigns : CompactSpace ℤˣ := inferInstance
  have hcompactProduct : CompactSpace (UrGroup q × ℤˣ) := inferInstance
  have hT2Product : T2Space (UrGroup q × ℤˣ) := inferInstance
  have hlocallyCompact : LocallyCompactSpace (UrGroup q × ℤˣ) := inferInstance
  have h2 := isUnit_two_resAt (IsHeightOneOdd.height_eq (P := P)) (IsHeightOneOdd.ne_two (P := P))
  have he : (-1 : ResAt P) - 1 = -(2 : ResAt P) := by ring
  have hunit : IsUnit ((-1 : ResAt P) - 1) := by rw [he]; exact h2.neg
  exact fullContinuousConstContraction (a := (1, -1)) (c := (-1 : ResAt P))
    (primitive_central q) (primitive_scalar W P α₀ q) hunit

section ActualQuotient

variable (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)

/-- The actual local restriction and quadratic character into the primitive quotient model. -/
def quadraticQuotientMap (q : NewPlaces K S₀ S) : Gloc K q.1 →ₜ* (UrGroup q × ℤˣ) where
  toFun σ := (quotientUrRes q σ, quadChar s hs hs0 (locMap K S q.1 σ))
  map_one' := by
    apply Prod.ext
    · exact map_one (quotientUrRes q)
    · change quadChar s hs hs0 (locMap K S q.1 1) = 1
      rw [map_one, map_one]
  map_mul' σ τ := by
    apply Prod.ext
    · exact map_mul (quotientUrRes q) σ τ
    · change quadChar s hs hs0 (locMap K S q.1 (σ * τ)) =
        quadChar s hs hs0 (locMap K S q.1 σ) * quadChar s hs hs0 (locMap K S q.1 τ)
      rw [map_mul, map_mul]
  continuous_toFun := (quotientUrRes q).continuous.prodMk
    ((continuous_character_of_open_kernel (quadChar s hs hs0)
      (IsOpenKer.isOpen_ker (α := quadChar s hs hs0))).comp (locMap K S q.1).continuous)

/-- A genuine primitive inertia element maps to the central quadratic sign. -/
theorem quadraticQuotientMap_primitive (q : NewPlaces K S₀ S) (σ : Gloc K q.1)
    (hσI : σ ∈ TauCeti.inertiaSubgroup (q.1.adicCompletion K))
    (hσχ : quadChar s hs hs0 (locMap K S q.1 σ) = -1) :
    quadraticQuotientMap s hs hs0 q σ = (1, -1) := by
  apply Prod.ext
  · exact urRes_inertia_one (S := S) ⟨q.1, q.2.1⟩ σ hσI
  · exact hσχ

/-- With the actual primitive inertia sign, the retained local map is onto the
quadratic/unramified quotient, not merely a map into an unrelated group. -/
theorem quadraticQuotientMap_surjective (q : NewPlaces K S₀ S) (σ : Gloc K q.1)
    (hσI : σ ∈ TauCeti.inertiaSubgroup (q.1.adicCompletion K))
    (hσχ : quadChar s hs hs0 (locMap K S q.1 σ) = -1) :
    Function.Surjective (quadraticQuotientMap s hs hs0 q) := by
  have hσur : quotientUrRes q σ = 1 :=
    urRes_inertia_one (S := S) ⟨q.1, q.2.1⟩ σ hσI
  let ψ := (quadChar s hs hs0).comp (locMap K S q.1).toMonoidHom
  intro y
  obtain ⟨γ, hγ⟩ := quotientUrRes_surjective q y.1
  by_cases he : ψ γ = y.2
  · exact ⟨γ, Prod.ext hγ he⟩
  · have hsψ : ψ σ = -1 := hσχ
    have hswap : ψ γ * (-1) = y.2 := by
      rw [Int.units_ne_iff_eq_neg.mp he]
      simp only [neg_mul_neg, mul_one]
    refine ⟨γ * σ, Prod.ext ?_ ?_⟩
    · change quotientUrRes q (γ * σ) = y.1
      rw [map_mul, hσur, mul_one, hγ]
    · change ψ (γ * σ) = y.2
      rw [map_mul, hsψ, hswap]

omit [IsHeightOneOdd P] [IsContChar α₀] in
/-- Inflation of the quotient action is the actual quadratic twist of the
smaller-support fibre, with its canonical retained local Galois action. -/
theorem pullback_action (q : NewPlaces K S₀ S) (σ : Gloc K q.1) (m : Carrier W P α₀ q) :
    quadraticQuotientMap s hs hs0 q σ • m =
      (show Carrier W P α₀ q from
        ((quadChar s hs hs0 (locMap K S q.1 σ) : ℤˣ) : ℤ) •
          (locMap K S₀ q.1 σ • (show VP K S₀ W P α₀ from m))) := by
  change ((quadChar s hs hs0 (locMap K S q.1 σ) : ℤˣ) : ℤ) •
      (urFactor K q (urRes K q.1 σ) • (show VP K S₀ W P α₀ from m)) =
    ((quadChar s hs hs0 (locMap K S q.1 σ) : ℤˣ) : ℤ) •
      (locMap K S₀ q.1 σ • (show VP K S₀ W P α₀ from m))
  exact congrArg (fun g : GKS K S₀ =>
    ((quadChar s hs hs0 (locMap K S q.1 σ) : ℤˣ) : ℤ) •
      (g • (show VP K S₀ W P α₀ from m))) (urFactor_spec K q σ).symm

end ActualQuotient

end PrimitiveQuotientModel

end ZInQ.Contrib.RC53Assist.StrictSymmFull.LocalContractions
