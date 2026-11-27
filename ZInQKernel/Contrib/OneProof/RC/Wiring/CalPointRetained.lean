import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointAlgebra
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeafLit

/-!
# Theorem 5.3, Lane RC34: the free lines of the retained integral central model

Definition `ex:arith-coordinate` (`diophantine_zq.tex`, tex 3877–3892: "the coordinate of
`[z] ⊗ [λ]` … in the retained integral determinant basis") and the proof of Proposition
`ex:arith-central-calibration` (tex 4005–4021, 4057–4064). The RC53 group's retained central
complex `retainedCentralComplex G hfinite` (a bounded finite free model of the compact central
Kummer complex, with the quasi-isomorphism `retainedCentralComparison`) has, under the
calibration shape `H : CalibrationCohomologyShape (compactCentralComplex G)`, the integral
normalization `retainedCentralNormalization` to the matrix-disk normal form (a free line in
degrees one and two and three disks), with retained coordinates `retainedCentralCoordinates`.
The free-line coordinate `(.inl ())` of a degree-one cycle is the class coefficient `a₀` of
lane RC35's Knudsen–Mumford identification `centralKMIdentOf`, and the value of a closed
functional on the degree-two free generator is its functional coefficient `b₀`.

This file relates these coordinates to the intrinsic free-line coefficients of cohomology.

* Generic: `mkCycle`, `cls` (the class of a cochain with zero differential), `cls_naturality`,
  `cls_surjective`, `homologyFunctional` (a functional on cochains vanishing on boundaries
  induces one on cohomology) and `homologyFunctional_cls`.
* Retained model: `freeCoord1`, `freeCoord2` (the free-line coordinates), `freeCoord1_boundary`,
  `freeCoord2_boundary` (they vanish on boundaries), the free generators `e1`, `e2` (closed, of
  free coordinate one), `ev1`, `ev2` (the induced functionals on cohomology).
* `freeCoord1_eq_freeCoeff`: for any free-line generator `g` of the first cohomology,
  `a₀ = freeCoord1 z₀ = (free coefficient of [z₀] on g) · ev1 g`, and `ev1 g` is a unit
  (`isUnit_ev1`): the retained free coordinate is the intrinsic free-line coefficient up to a
  unit.
* `isUnit_freeCoeff_e2`: the class of the degree-two free generator has unit coefficient on any
  free-line generator of the second cohomology.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open CategoryTheory

/-! ### Classes of cycles and functionals on cohomology -/

section Cycles

variable {R : Type} [CommRing R] (C : CochainComplex (ModuleCat.{0} R) ℤ)

/-- The cycle of a cochain with zero differential. Kind: definition. -/
def mkCycle (n : ℤ) (x : C.X n) (hx : (C.d n (n + 1)).hom x = 0) : C.cycles n :=
  (C.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (C.X n) x)) (n + 1) (by simp)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa using hx)).hom 1

/-- The cycle of `x` has underlying cochain `x`. PROVED. -/
theorem iCycles_mkCycle (n : ℤ) (x : C.X n) (hx : (C.d n (n + 1)).hom x = 0) :
    (C.iCycles n).hom (mkCycle C n x hx) = x := by
  have h := congrArg (fun f => f.hom (1 : R)) (C.liftCycles_i
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (C.X n) x)) (n + 1) (by simp)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa using hx))
  unfold mkCycle
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h

/-- The underlying cochain of a cycle has zero differential. PROVED. -/
theorem iCycles_closed (n : ℤ) (z : C.cycles n) :
    (C.d n (n + 1)).hom ((C.iCycles n).hom z) = 0 := by
  have h := congrArg (fun f => f.hom z) (C.iCycles_d n (n + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- Every cycle is the cycle of its underlying cochain. PROVED. -/
theorem mkCycle_iCycles (n : ℤ) (z : C.cycles n) :
    mkCycle C n ((C.iCycles n).hom z) (iCycles_closed C n z) = z := by
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance
  rw [iCycles_mkCycle]

/-- **The class of a cochain with zero differential** in cohomology. Kind: definition. -/
def cls (n : ℤ) (x : C.X n) (hx : (C.d n (n + 1)).hom x = 0) : C.homology n :=
  (C.homologyπ n).hom (mkCycle C n x hx)

/-- **Every cohomology class is the class of a cocycle.** PROVED. -/
theorem cls_surjective (n : ℤ) (y : C.homology n) :
    ∃ (x : C.X n) (hx : (C.d n (n + 1)).hom x = 0), cls C n x hx = y := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance y
  refine ⟨(C.iCycles n).hom z, iCycles_closed C n z, ?_⟩
  unfold cls
  rw [mkCycle_iCycles]

/-- A chain map carries cocycles to cocycles. PROVED. -/
theorem map_closed {D : CochainComplex (ModuleCat.{0} R) ℤ} (φ : C ⟶ D) (n : ℤ) {x : C.X n}
    (hx : (C.d n (n + 1)).hom x = 0) : (D.d n (n + 1)).hom ((φ.f n).hom x) = 0 := by
  have h := congrArg (fun f => f.hom x) (φ.comm n (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, hx, map_zero]

/-- **Naturality of classes**: a chain map carries the class of `x` to the class of its image.
PROVED. -/
theorem cls_naturality {D : CochainComplex (ModuleCat.{0} R) ℤ} (φ : C ⟶ D) (n : ℤ) (x : C.X n)
    (hx : (C.d n (n + 1)).hom x = 0) :
    (HomologicalComplex.homologyMap φ n).hom (cls C n x hx) =
      cls D n ((φ.f n).hom x) (map_closed C φ n hx) := by
  unfold cls
  have hnat := congrArg (fun f => f.hom (mkCycle C n x hx))
    (HomologicalComplex.homologyπ_naturality φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat]
  congr 1
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).1 inferInstance
  have h := congrArg (fun f => f.hom (mkCycle C n x hx)) (HomologicalComplex.cyclesMap_i φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, iCycles_mkCycle, iCycles_mkCycle]

/-- The class of a coboundary is zero. PROVED. -/
theorem cls_boundary (n : ℤ) (y : C.X (n - 1)) (hy : (C.d n (n + 1)).hom
    ((C.d (n - 1) n).hom y) = 0) : cls C n ((C.d (n - 1) n).hom y) hy = 0 := by
  unfold cls
  refine (C.moduleCat_homologyπ_eq_zero_iff (n := n) (m := n - 1) (by simp) _).2 ⟨y, ?_⟩
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance
  have hd := congrArg (fun f => f.hom y) (C.toCycles_i (n - 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd
  rw [hd, iCycles_mkCycle]

/-- The cycle functional `φ ∘ i` vanishes on the kernel of the class map when `φ` vanishes on
boundaries. PROVED. -/
theorem cycleFunctional_vanish (n : ℤ) (φ : C.X n →ₗ[R] R)
    (hφ : ∀ y : C.X (n - 1), φ ((C.d (n - 1) n).hom y) = 0) :
    LinearMap.ker (C.homologyπ n).hom ≤ LinearMap.ker (φ ∘ₗ (C.iCycles n).hom) := by
  intro z hz
  obtain ⟨y, hy⟩ := (C.moduleCat_homologyπ_eq_zero_iff (n := n) (m := n - 1) (by simp) z).1 hz
  rw [LinearMap.mem_ker, LinearMap.comp_apply, ← hy]
  have hd := congrArg (fun f => f.hom y) (C.toCycles_i (n - 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd
  rw [hd]
  exact hφ y

/-- **A functional on cochains vanishing on boundaries induces a functional on cohomology.**
Kind: definition. -/
def homologyFunctional (n : ℤ) (φ : C.X n →ₗ[R] R)
    (hφ : ∀ y : C.X (n - 1), φ ((C.d (n - 1) n).hom y) = 0) : C.homology n →ₗ[R] R :=
  ((LinearMap.ker (C.homologyπ n).hom).liftQ (φ ∘ₗ (C.iCycles n).hom)
    (cycleFunctional_vanish C n φ hφ)).comp
    (LinearMap.quotKerEquivOfSurjective (C.homologyπ n).hom
      ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)).symm.toLinearMap

/-- **The induced functional on the class of a cocycle is the value of the functional.**
PROVED. -/
theorem homologyFunctional_cls (n : ℤ) (φ : C.X n →ₗ[R] R)
    (hφ : ∀ y : C.X (n - 1), φ ((C.d (n - 1) n).hom y) = 0) (x : C.X n)
    (hx : (C.d n (n + 1)).hom x = 0) : homologyFunctional C n φ hφ (cls C n x hx) = φ x := by
  unfold homologyFunctional cls
  have e : (LinearMap.quotKerEquivOfSurjective (C.homologyπ n).hom
      ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)).symm
        ((C.homologyπ n).hom (mkCycle C n x hx)) =
      Submodule.Quotient.mk (mkCycle C n x hx) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply,
    LinearMap.comp_apply, iCycles_mkCycle]

end Cycles

/-! ### The free lines of the retained central model -/

section Retained

open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve
  centralFullTorsion blockComplex blockComplex_d0 blockComplex_d1 blockComplex_d2 blockD0 blockD1
  blockD2)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape retainedCentralComplex
  retainedCentralCoordinates retainedCentralNormalization centralDiskMatrix)
open ZInQ.Manuscript.RC53Assist.CentralKummer (compactKummerComplex)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactCentralComplex G).homology n))
  (H : CalibrationCohomologyShape (compactCentralComplex G))

/-- **The free-line coordinate in degree one** (lane RC35's `retainedA0`). Kind: definition. -/
def freeCoord1 : (retainedCentralComplex G hfinite).X 1 →ₗ[ℤ_[2]] ℤ_[2] :=
  (LinearMap.proj (Sum.inl ())).comp (retainedCentralCoordinates G hfinite H 1).toLinearMap

/-- **The free-line coordinate in degree two.** Kind: definition. -/
def freeCoord2 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  (LinearMap.proj (Sum.inl ())).comp (retainedCentralCoordinates G hfinite H 2).toLinearMap

/-- `freeCoord1` is the first component of the normal-form coordinates. PROVED. -/
theorem freeCoord1_apply (z : (retainedCentralComplex G hfinite).X 1) :
    freeCoord1 G hfinite H z =
      (((retainedCentralNormalization G hfinite H).inv.f 1).hom z).1 := rfl

/-- `freeCoord2` is the first component of the normal-form coordinates. PROVED. -/
theorem freeCoord2_apply (z : (retainedCentralComplex G hfinite).X 2) :
    freeCoord2 G hfinite H z =
      (((retainedCentralNormalization G hfinite H).inv.f 2).hom z).1 := rfl

/-- **The degree-one free coordinate vanishes on boundaries** (the first disk enters the
torsion coordinates only). PROVED. -/
theorem freeCoord1_boundary (y : (retainedCentralComplex G hfinite).X (1 - 1)) :
    freeCoord1 G hfinite H (((retainedCentralComplex G hfinite).d (1 - 1) 1).hom y) = 0 := by
  rw [freeCoord1_apply]
  have h := congrArg (fun f => f.hom y) ((retainedCentralNormalization G hfinite H).inv.comm 0 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change ((((retainedCentralNormalization G hfinite H).inv.f 1).hom
    (((retainedCentralComplex G hfinite).d 0 1).hom y))).1 = 0
  rw [← h, blockComplex_d0]
  rfl

/-- **The degree-two free coordinate vanishes on boundaries.** PROVED. -/
theorem freeCoord2_boundary (y : (retainedCentralComplex G hfinite).X (2 - 1)) :
    freeCoord2 G hfinite H (((retainedCentralComplex G hfinite).d (2 - 1) 2).hom y) = 0 := by
  rw [freeCoord2_apply]
  have h := congrArg (fun f => f.hom y) ((retainedCentralNormalization G hfinite H).inv.comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change ((((retainedCentralNormalization G hfinite H).inv.f 2).hom
    (((retainedCentralComplex G hfinite).d 1 2).hom y))).1 = 0
  rw [← h, blockComplex_d1]
  rfl

/-- **The degree-one free generator** of the retained model (free coordinate one, all disk
coordinates zero). Kind: definition. -/
def e1 : (retainedCentralComplex G hfinite).X 1 :=
  (retainedCentralCoordinates G hfinite H 1).symm (Pi.single (Sum.inl ()) 1)

/-- **The degree-two free generator** of the retained model (lane RC35's argument of `b₀`).
Kind: definition. -/
def e2 : (retainedCentralComplex G hfinite).X 2 :=
  (retainedCentralCoordinates G hfinite H 2).symm (Pi.single (Sum.inl ()) 1)

/-- The free coordinate of `e1` is one. PROVED. -/
theorem freeCoord1_e1 : freeCoord1 G hfinite H (e1 G hfinite H) = 1 := by
  change (retainedCentralCoordinates G hfinite H 1 ((retainedCentralCoordinates G hfinite H 1).symm
    (Pi.single (Sum.inl ()) 1))) (Sum.inl ()) = 1
  rw [LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_same _ _

/-- The free coordinate of `e2` is one. PROVED. -/
theorem freeCoord2_e2 : freeCoord2 G hfinite H (e2 G hfinite H) = 1 := by
  change (retainedCentralCoordinates G hfinite H 2 ((retainedCentralCoordinates G hfinite H 2).symm
    (Pi.single (Sum.inl ()) 1))) (Sum.inl ()) = 1
  rw [LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_same _ _

/-- In normal-form coordinates `e1` is `(1, 0, 0)`. PROVED. -/
theorem inv_e1 : ((retainedCentralNormalization G hfinite H).inv.f 1).hom (e1 G hfinite H) =
    ((1 : ℤ_[2]), (0 : Fin _ → ℤ_[2]), (0 : Fin _ → ℤ_[2])) := by
  have h : retainedCentralCoordinates G hfinite H 1 (e1 G hfinite H) = Pi.single (Sum.inl ()) 1 :=
    LinearEquiv.apply_symm_apply _ _
  change ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates ℤ_[2] _ _
    (((retainedCentralNormalization G hfinite H).inv.f 1).hom (e1 G hfinite H)) = _ at h
  apply (ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates ℤ_[2] _ _).injective
  rw [h]
  funext k
  rcases k with u | i | i
  · cases u
    exact Pi.single_eq_same _ _
  · exact Pi.single_eq_of_ne Sum.inr_ne_inl _
  · exact Pi.single_eq_of_ne Sum.inr_ne_inl _

/-- In normal-form coordinates `e2` is `(1, 0, 0)`. PROVED. -/
theorem inv_e2 : ((retainedCentralNormalization G hfinite H).inv.f 2).hom (e2 G hfinite H) =
    ((1 : ℤ_[2]), (0 : Fin _ → ℤ_[2]), (0 : Fin _ → ℤ_[2])) := by
  have h : retainedCentralCoordinates G hfinite H 2 (e2 G hfinite H) = Pi.single (Sum.inl ()) 1 :=
    LinearEquiv.apply_symm_apply _ _
  change ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates ℤ_[2] _ _
    (((retainedCentralNormalization G hfinite H).inv.f 2).hom (e2 G hfinite H)) = _ at h
  apply (ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates ℤ_[2] _ _).injective
  rw [h]
  funext k
  rcases k with u | i | i
  · cases u
    exact Pi.single_eq_same _ _
  · exact Pi.single_eq_of_ne Sum.inr_ne_inl _
  · exact Pi.single_eq_of_ne Sum.inr_ne_inl _

/-- The normal-form components of the normalization are injective. PROVED. -/
theorem inv_injective (n : ℤ) :
    Function.Injective ((retainedCentralNormalization G hfinite H).inv.f n).hom :=
  (ModuleCat.mono_iff_injective
    (HomologicalComplex.Hom.isoApp (retainedCentralNormalization G hfinite H) n).inv).1
      inferInstance

/-- **`e1` is a cycle.** PROVED. -/
theorem e1_closed :
    ((retainedCentralComplex G hfinite).d 1 (1 + 1)).hom (e1 G hfinite H) = 0 := by
  apply inv_injective G hfinite H (1 + 1)
  have hc := congrArg (fun f => f.hom (e1 G hfinite H))
    ((retainedCentralNormalization G hfinite H).inv.comm 1 (1 + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  rw [map_zero, ← hc, inv_e1]
  change blockD1 (centralDiskMatrix G hfinite 2)
    ((1 : ℤ_[2]), (0 : Fin _ → ℤ_[2]), (0 : Fin _ → ℤ_[2])) = 0
  simp [blockD1]

/-- **`e2` is a cycle.** PROVED. -/
theorem e2_closed :
    ((retainedCentralComplex G hfinite).d 2 (2 + 1)).hom (e2 G hfinite H) = 0 := by
  apply inv_injective G hfinite H (2 + 1)
  have hc := congrArg (fun f => f.hom (e2 G hfinite H))
    ((retainedCentralNormalization G hfinite H).inv.comm 2 (2 + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  rw [map_zero, ← hc, inv_e2]
  change blockD2 (centralDiskMatrix G hfinite 3)
    ((1 : ℤ_[2]), (0 : Fin _ → ℤ_[2]), (0 : Fin _ → ℤ_[2])) = 0
  simp [blockD2]

/-- The functional on the first cohomology induced by the free coordinate. Kind: definition. -/
def ev1 : (retainedCentralComplex G hfinite).homology 1 →ₗ[ℤ_[2]] ℤ_[2] :=
  homologyFunctional _ 1 (freeCoord1 G hfinite H) (freeCoord1_boundary G hfinite H)

/-- The functional on the second cohomology induced by the free coordinate.
Kind: definition. -/
def ev2 : (retainedCentralComplex G hfinite).homology 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  homologyFunctional _ 2 (freeCoord2 G hfinite H) (freeCoord2_boundary G hfinite H)

/-- `ev1` on the class of a cocycle is its free coordinate. PROVED. -/
theorem ev1_cls (z : (retainedCentralComplex G hfinite).X 1)
    (hz : ((retainedCentralComplex G hfinite).d 1 (1 + 1)).hom z = 0) :
    ev1 G hfinite H (cls _ 1 z hz) = freeCoord1 G hfinite H z :=
  homologyFunctional_cls _ 1 _ _ z hz

/-- `ev2` on the class of a cocycle is its free coordinate. PROVED. -/
theorem ev2_cls (z : (retainedCentralComplex G hfinite).X 2)
    (hz : ((retainedCentralComplex G hfinite).d 2 (2 + 1)).hom z = 0) :
    ev2 G hfinite H (cls _ 2 z hz) = freeCoord2 G hfinite H z :=
  homologyFunctional_cls _ 2 _ _ z hz

/-- **`ev1` is a unit on any free-line generator of the first cohomology.** PROVED. -/
theorem isUnit_ev1 {g : (retainedCentralComplex G hfinite).homology 1}
    (hg : IsFreeLineGenerator ℤ_[2] g) : IsUnit (ev1 G hfinite H g) := by
  have h := functional_apply (ev1 G hfinite H) hg (cls _ 1 _ (e1_closed G hfinite H))
  rw [ev1_cls, freeCoord1_e1] at h
  exact isUnit_iff_exists_inv'.mpr ⟨_, h.symm⟩

/-- **The retained free coordinate is the intrinsic free-line coefficient up to a unit**:
`a₀ = freeCoord1 z₀ = (coefficient of [z₀] on g) · ev1 g`. PROVED. -/
theorem freeCoord1_eq_freeCoeff {g : (retainedCentralComplex G hfinite).homology 1}
    (hg : IsFreeLineGenerator ℤ_[2] g) (z : (retainedCentralComplex G hfinite).X 1)
    (hz : ((retainedCentralComplex G hfinite).d 1 (1 + 1)).hom z = 0) :
    freeCoord1 G hfinite H z = freeCoeff hg (cls _ 1 z hz) * ev1 G hfinite H g := by
  rw [← ev1_cls G hfinite H z hz]
  exact functional_apply _ hg _

/-- **The class of the degree-two free generator has unit coefficient on any free-line
generator of the second cohomology.** PROVED. -/
theorem isUnit_freeCoeff_e2 {g₂ : (retainedCentralComplex G hfinite).homology 2}
    (hg₂ : IsFreeLineGenerator ℤ_[2] g₂) :
    IsUnit (freeCoeff hg₂ (cls _ 2 _ (e2_closed G hfinite H))) := by
  have h := functional_apply (ev2 G hfinite H) hg₂ (cls _ 2 _ (e2_closed G hfinite H))
  rw [ev2_cls, freeCoord2_e2] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h.symm⟩

end Retained

end ZInQ.Manuscript.RC.CalPoint
