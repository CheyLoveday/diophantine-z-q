import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentBlock
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentBlockMap

/-!
# Theorem 5.3, Lane RC35: the genuine Knudsen–Mumford identification of `C_K`

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), Definition
`ex:arith-coordinate` (tex 3877–3890), Lemma `ex:arith-central-specialization` (tex 3895–3910).

The identification of `KmIdentCentral` with its target replaced by the genuine one: the retained
integral model `retainedCentralComplex G hfinite` of the ordinary compact Kummer complex `C_K`
(the RC53 group's construction, quasi-isomorphic to `C_K` over `ℤ₂`), with coefficients extended
to `ℚ₂[[t]]` along the constant map `constQt` (the case `t = 0` of the text, where the moving
character is trivial, tex 4280), as Selmer data with zero local conditions (`modelSel`).

* `centralKMTarget`, `centralKMSel`: the target.
* `centralKMMap`, `centralKMMap_quasiIso`: the comparison from the core-and-disks model (the free
  lines identically onto the retained free lines, the disks to zero), a quasi-isomorphism
  (`retainedKMMap_quasiIso` of `KmIdentBlockMap`); `centralKMMap_compact_quasiIso`: composed with
  the base change of the RC53 group's comparison `retainedCentralComparison`, a quasi-isomorphism
  onto the base change of `C_K` itself.
* `centralKMLam lam0`: the functional `λ₀ ⊗ ℚ₂[[t]]` (`centralKMLam_tmul`).
* `centralKMIdent G hfinite H a b`: the identification with class `a e₁` and functional
  `b · (free-line functional)`.
* `centralKMIdentOf G hfinite H Z`: the identification pinned by a central cycle `z₀` and a
  closed functional `λ₀` (`CentralClassFunctional`): its functional IS `λ₀ ⊗ ℚ₂[[t]]`, and its
  class is the class of `z₀ ⊗ 1` (`centralKMIdentOf_class`: they differ by a coboundary). **G3**:
  `centralKMIdentOf_a`, `_b`, `_u₀`, `_core` (`central (a b u₀) = a₀ b₀` exactly),
  `_coord` (the coordinate is `centralKMCoord G hfinite Z.aUnit Z.bUnit`, the coordinate of the
  model identification of `KmIdentCentral`).

Kinds: definitions and PROVED. No input.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.KmIdent

open Matrix CategoryTheory
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom SelData selCx)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (ghomComp GHom.toCC GHom.toCC_comp)
open ZInQ.Manuscript.RC.SelmerComplex (ofCC)
open ZInQ.Manuscript.RC53Assist.CentralSelmer (scalarChangedComplex)
open ZInQ.Contrib.CloudB3RC53.Calibration (central_mul)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape centralDiskMatrix
  centralDiskMatrix_det_ne_zero retainedCentralComplex retainedCentralCoordinates
  retainedCentralComparison)

attribute [local instance] Nat.fact_prime_two

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
  (H : CalibrationCohomologyShape (compactCentralComplex G))

/-! ### The target and the comparison -/

/-- **The target**: the retained integral model of `C_K` with coefficients extended to
`ℚ₂[[t]]` along the constants. Kind: definition. -/
abbrev centralKMTarget : GCx (PowerSeries ℚ_[2]) :=
  ofCC (scalarChangedComplex constQt (retainedCentralComplex G hfinite))

/-- The target as Selmer data with zero local conditions. Kind: definition. -/
abbrev centralKMSel : SelData (PowerSeries ℚ_[2]) :=
  modelSel (centralKMTarget G hfinite)

/-- The constant disk determinants are units. Kind: PROVED. -/
theorem isUnit_constQt_det (j : ℤ) : IsUnit (constQt (centralDiskMatrix G hfinite j).det) := by
  rw [← constUnit_val _ (centralDiskMatrix_det_ne_zero G hfinite j)]
  exact Units.isUnit _

/-- **The comparison** from the core-and-disks model with the constructed integral disks to the
genuine target: the free lines identically onto the retained free lines, the disks to zero,
followed by the inclusion into the Selmer complex of zero local conditions. Kind: definition. -/
def centralKMMap :
    GHom (kummerModel (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2]))
        ((centralKMDisk G hfinite 1 : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2])
        (centralKMDisk G hfinite 2) (centralKMDisk G hfinite 3)).toBased.toGCx
      (selCx (centralKMSel G hfinite)) :=
  ghomComp (retainedKMMap G hfinite H constQt _ _ _) (modelIncl _)

/-- **The comparison is a quasi-isomorphism.** Kind: PROVED. -/
theorem centralKMMap_quasiIso : QuasiIso (GHom.toCC (centralKMMap G hfinite H)) := by
  unfold centralKMMap
  rw [← GHom.toCC_comp]
  have := retainedKMMap_quasiIso G hfinite H constQt (centralKMDisk G hfinite 1).isUnit
    (centralKMDisk G hfinite 2).isUnit (centralKMDisk G hfinite 3).isUnit
    (isUnit_constQt_det G hfinite 1) (isUnit_constQt_det G hfinite 2)
    (isUnit_constQt_det G hfinite 3)
  have := quasiIso_modelIncl (centralKMTarget G hfinite)
  infer_instance

/-- **The comparison onto the base change of `C_K` itself is a quasi-isomorphism**: the model,
mapped to the base-changed retained model, followed by the base change of the RC53 group's
integral comparison `retainedCentralComparison G hfinite` into `compactCentralComplex G`.
Kind: PROVED. -/
theorem centralKMMap_compact_quasiIso :
    QuasiIso (GHom.toCC (retainedKMMap G hfinite H constQt
        ((centralKMDisk G hfinite 1 : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2])
        (centralKMDisk G hfinite 2) (centralKMDisk G hfinite 3)) ≫
      (ofCCIso (scalarChangedComplex constQt (retainedCentralComplex G hfinite))).hom ≫
        ((ModuleCat.extendScalars constQt).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (retainedCentralComparison G hfinite)) :=
  retainedKMMap_compact_quasiIso G hfinite H constQt (centralKMDisk G hfinite 1).isUnit
    (centralKMDisk G hfinite 2).isUnit (centralKMDisk G hfinite 3).isUnit
    (isUnit_constQt_det G hfinite 1) (isUnit_constQt_det G hfinite 2)
    (isUnit_constQt_det G hfinite 3)

/-! ### The functional -/

/-- **The functional `λ₀ ⊗ ℚ₂[[t]]`** of a degree-two functional `λ₀` of the retained integral
model, on the Selmer complex of the target. Kind: definition. -/
def centralKMLam (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) :
    (selCx (centralKMSel G hfinite)).X 2 →ₗ[PowerSeries ℚ_[2]] PowerSeries ℚ_[2] :=
  retainedKMFunctional G hfinite constQt lam0 ∘ₗ (modelProj (centralKMTarget G hfinite)).f 2 2 rfl

/-- `λ₀ ⊗ ℚ₂[[t]]` on pure tensors: `s ⊗ x ↦ s · λ₀(x)`. Kind: PROVED. -/
theorem centralKMLam_tmul (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (s : PowerSeries ℚ_[2]) (x : (retainedCentralComplex G hfinite).X 2) :
    centralKMLam G hfinite lam0
        ((modelIncl (centralKMTarget G hfinite)).f 2 2 rfl (bcTmul constQt _ 2 s x)) =
      s * constQt (lam0 x) :=
  retainedKMFunctional_tmul G hfinite constQt lam0 s x

/-- The functional on the image of the model's degree-two vectors. Kind: PROVED. -/
theorem centralKMLam_map (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (y : ((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit → PowerSeries ℚ_[2]) :
    centralKMLam G hfinite lam0 ((centralKMMap G hfinite H).f 2 2 rfl ⟨vec2 y, vec2_mem _ _⟩) =
      constQt (lam0 (e₂R G hfinite H)) * y ke₂' :=
  retainedKMFunctional_map G hfinite H constQt _ _ _ lam0 y

/-- The weighted degree-two coordinate of the model's functional. Kind: PROVED. -/
theorem kw_smul_one_dot (b : PowerSeries ℚ_[2])
    (y : ((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit → PowerSeries ℚ_[2]) :
    kw (b • (1 : Fin 1 → PowerSeries ℚ_[2])) ⬝ᵥ y = b * y ke₂' := by
  simp [kw, dotProduct, Fintype.sum_sum_type, ke₂']

/-! ### The identification -/

/-- **The genuine Knudsen–Mumford identification of `C_K`** with class coefficient `a` and
functional coefficient `b` (units of `ℚ₂[[t]]`): the normalized core `[0]` of size one
(`z₀ = λ₀ = u₀ = 1`), the class `a e₁`, the functional `b e₂*`, the constructed integral disks;
the comparison `centralKMMap` into the base-changed retained integral model of `C_K`; the
functional `b · (λ_free ⊗ ℚ₂[[t]])` with `λ_free` the free-line coordinate of degree two.
Kind: definition. -/
def centralKMIdent (a b : (PowerSeries ℚ_[2])ˣ) :
    KummerModelIdentification (centralKMSel G hfinite) where
  n := 1
  Dc := 0
  δ₁ := centralKMDisk G hfinite 1
  δ₂ := centralKMDisk G hfinite 2
  δ₃ := centralKMDisk G hfinite 3
  z₀ := 1
  w₀ := 1
  u₀ := 1
  a := a
  b := b
  z := (a : PowerSeries ℚ_[2]) • 1
  w := (b : PowerSeries ℚ_[2]) • 1
  hzdef := rfl
  hwdef := rfl
  hz := twoTerm_zero_hz_smul _
  hw := twoTerm_zero_hw_smul _
  hcore := unitCoreContraction a b
  hu₀ := isClassFunctionalCoord_zero_one
  φ := centralKMMap G hfinite H
  qis := centralKMMap_quasiIso G hfinite H
  zSel := (centralKMMap G hfinite H).f 1 1 rfl
    ⟨vec1 (kz ((a : PowerSeries ℚ_[2]) • 1)), vec1_mem _ _⟩
  lamSel := (b : PowerSeries ℚ_[2]) • centralKMLam G hfinite (retainedFree2 G hfinite H)
  hclass := rfl
  hfun y := by
    rw [LinearMap.smul_apply, smul_eq_mul, centralKMLam_map, kw_smul_one_dot]
    have h1 : retainedFree2 G hfinite H (e₂R G hfinite H) = 1 := retainedB0_free2
    rw [h1, map_one, one_mul]

/-- **The genuine identification pinned by a central class and functional**: class coefficient
`a₀` and functional coefficient `b₀`, the free-line coefficients of `z₀`, `λ₀` in the retained
integral basis, and the functional `λ₀ ⊗ ℚ₂[[t]]` itself. Kind: definition. -/
def centralKMIdentOf (Z : CentralClassFunctional G hfinite H) :
    KummerModelIdentification (centralKMSel G hfinite) where
  n := 1
  Dc := 0
  δ₁ := centralKMDisk G hfinite 1
  δ₂ := centralKMDisk G hfinite 2
  δ₃ := centralKMDisk G hfinite 3
  z₀ := 1
  w₀ := 1
  u₀ := 1
  a := Z.aUnit
  b := Z.bUnit
  z := ((Z.aUnit : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) • 1
  w := ((Z.bUnit : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) • 1
  hzdef := rfl
  hwdef := rfl
  hz := twoTerm_zero_hz_smul _
  hw := twoTerm_zero_hw_smul _
  hcore := unitCoreContraction Z.aUnit Z.bUnit
  hu₀ := isClassFunctionalCoord_zero_one
  φ := centralKMMap G hfinite H
  qis := centralKMMap_quasiIso G hfinite H
  zSel := (centralKMMap G hfinite H).f 1 1 rfl
    ⟨vec1 (kz (((Z.aUnit : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) • 1)), vec1_mem _ _⟩
  lamSel := centralKMLam G hfinite Z.lam0
  hclass := rfl
  hfun y := by
    rw [centralKMLam_map, kw_smul_one_dot]
    rfl

variable {G hfinite H}

/-! ### G3 and the faithfulness of the pinned identification -/

/-- **G3**: the class coefficient of the genuine identification is `C(a₀)`. Kind: PROVED. -/
theorem centralKMIdentOf_a (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentOf G hfinite H Z).a =
      PowerSeries.C ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) := rfl

/-- **G3**: the functional coefficient of the genuine identification is `C(b₀)`.
Kind: PROVED. -/
theorem centralKMIdentOf_b (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentOf G hfinite H Z).b =
      PowerSeries.C ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) := rfl

/-- **G3**: the core coordinate of the genuine identification is `1`. Kind: PROVED. -/
theorem centralKMIdentOf_u₀ (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentOf G hfinite H Z).u₀ = 1 := rfl

/-- **G3 for the genuine identification**: `central (a b u₀) = a₀ b₀` exactly (unit `1`).
Kind: PROVED. -/
theorem centralKMIdentOf_core (Z : CentralClassFunctional G hfinite H) :
    central ((centralKMIdentOf G hfinite H Z).a * (centralKMIdentOf G hfinite H Z).b *
      (centralKMIdentOf G hfinite H Z).u₀) =
      ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) *
        ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) :=
  centralKMIdentModelOf_core Z

/-- **The coordinate of the genuine identification is that of the model identification.**
Kind: PROVED. -/
theorem centralKMIdentOf_coord (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentOf G hfinite H Z).coord = (centralKMIdentModelOf G hfinite H Z).coord := rfl

/-- The coordinate of the general genuine identification. Kind: PROVED. -/
theorem centralKMIdent_coord (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdent G hfinite H a b).coord = centralKMCoord G hfinite a b := rfl

/-- **The functional of the pinned identification is `λ₀ ⊗ ℚ₂[[t]]`.** Kind: PROVED. -/
theorem centralKMIdentOf_lamSel (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentOf G hfinite H Z).lamSel = centralKMLam G hfinite Z.lam0 := rfl

/-- **The class of the pinned identification is the class of `z₀ ⊗ 1`**: its component in the
target differs from `1 ⊗ z₀` by a coboundary (`retained_cycle_coboundary`). Kind: PROVED. -/
theorem centralKMIdentOf_class (Z : CentralClassFunctional G hfinite H) :
    ∃ w : (scalarChangedComplex constQt (retainedCentralComplex G hfinite)).X 0,
      ((scalarChangedComplex constQt (retainedCentralComplex G hfinite)).d 0 1).hom w =
        bcTmul constQt _ 1 1 Z.z0 -
          (modelProj (centralKMTarget G hfinite)).f 1 1 rfl
            (centralKMIdentOf G hfinite H Z).zSel := by
  obtain ⟨w, hw⟩ := retained_cycle_coboundary G hfinite H constQt
    (isUnit_constQt_det G hfinite 1) (isUnit_constQt_det G hfinite 2) Z.z0 Z.hz0
  refine ⟨w, hw.trans ?_⟩
  congr 1
  refine Eq.symm ((retainedKMMap_one G hfinite H constQt _ _ _ _).trans ?_)
  congr 1
  change ((Z.aUnit : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) * 1 = _
  rw [mul_one]
  rfl

end ZInQ.Manuscript.RC.Wiring.KmIdent
