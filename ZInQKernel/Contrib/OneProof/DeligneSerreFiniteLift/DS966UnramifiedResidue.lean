import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Existence
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Henselian
import Mathlib.FieldTheory.Finite.GaloisField
import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966Adic

/-! # Realize a prescribed finite residue extension by an unramified local extension -/

noncomputable section

namespace DS966Small

open TauCeti ValuativeRel

universe u

/-- Every finite extension of the residue field of a nonarchimedean local field
is realized by a finite unramified extension, with the residue isomorphism
linear over the original residue field. Kind: PROVED. -/
theorem exists_unramified_residue_equiv (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (C : Type*) [Field C] [Algebra 𝓀[K] C] [Finite C] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : ValuativeExtension K L), IsUnramified K L ∧ Nonempty (𝓀[L] ≃ₐ[𝓀[K]] C) := by
  have : Module.Finite 𝓀[K] C := Module.Finite.of_finite
  let d := Module.finrank 𝓀[K] C
  have hd : d ≠ 0 := (Module.finrank_pos (R := 𝓀[K]) (M := C)).ne'
  let Ω := SeparableClosure K
  let L := unramifiedExtension K Ω d
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have hL := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have hVal := finiteIntermediateField_valuativeExtension K Ω L
  have hUn : IsUnramified K L := isUnramified_unramifiedExtension hd
  have hr : Module.finrank 𝓀[K] 𝓀[L] = Module.finrank 𝓀[K] C :=
    (inertiaDegree_def (K := K) (L := L)).symm.trans
      (IsUnramified.inertiaDegree_eq_finrank.trans (finrank_unramifiedExtension hd))
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (dvd_of_eq hr)
  have : Module.Finite 𝓀[K] 𝓀[L] := Module.Finite.of_finite
  have hcard : Nat.card 𝓀[L] = Nat.card C := by
    rw [Module.natCard_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L]),
      Module.natCard_eq_pow_finrank (K := 𝓀[K]) (V := C), hr]
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hL, hVal, hUn, ⟨AlgEquiv.ofBijective e
      ((Nat.bijective_iff_injective_and_card e).mpr ⟨e.injective, hcard⟩)⟩⟩

/-- A representation over the prescribed finite residue extension lifts on the
same group into the integers of an unramified extension. The map from its local
integers to `C` agrees with the fixed map on the base residue field. Kind: PROVED. -/
theorem lift_over_unramified_residue (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (C : Type*) [Field C] [Algebra 𝓀[K] C] [Finite C]
    {n H : Type*} [Fintype n] [DecidableEq n] [Group H] [Fintype H]
    (hcard : IsUnit (Fintype.card H : C)) (ρ : H →* GL n C) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : ValuativeExtension K L), IsUnramified K L ∧
        ∃ (e : 𝓀[L] ≃ₐ[𝓀[K]] C) (r : H →* GL n 𝒪[L]),
          (Matrix.GeneralLinearGroup.map
            (e.toRingEquiv.toRingHom.comp (IsLocalRing.residue 𝒪[L]))).comp r = ρ := by
  obtain ⟨L, _, _, _, _, _, _, _, hUn, ⟨e⟩⟩ := exists_unramified_residue_equiv K C
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  let _ := isUniformAddGroup_of_addCommGroup (G := L)
  let r := (Matrix.GeneralLinearGroup.map e.symm.toRingEquiv.toRingHom).comp ρ
  have hunit : IsUnit (Fintype.card H : 𝓀[L]) := by
    simpa only [map_natCast] using hcard.map e.symm.toRingEquiv.toRingHom
  obtain ⟨T, hT⟩ := DS966Lifting.lift_matrix_complete
    (IsLocalRing.maximalIdeal 𝒪[L]) hunit r
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hUn, e, T, ?_⟩
  refine MonoidHom.ext (fun g => Units.ext (Matrix.ext (fun i j => ?_)))
  have hentry := congrArg (fun f : H →* GL n 𝓀[L] => (↑(f g) : Matrix n n 𝓀[L]) i j) hT
  exact (congrArg e hentry).trans (e.apply_symm_apply ((ρ g : Matrix n n C) i j))

end DS966Small
