import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966UnramifiedResidue
import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966PrescribedResidue
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-! # Factor finite residual matrix data and lift over the prescribed local field -/

noncomputable section

namespace DS966Small

open TauCeti ValuativeRel NumberField IsDedekindDomain
open scoped NumberField

/-- The entries of a representation of a finite group in an algebraic extension
of a finite field lie in a common finite field, including the inverses.
Kind: PROVED. -/
theorem exists_finite_residual_factor {F k n H : Type*} [Field F] [Field k] [Algebra F k]
    [Finite F] [Algebra.IsAlgebraic F k] [Fintype n] [DecidableEq n] [Group H] [Fintype H]
    (ρ : H →* GL n k) : ∃ C : IntermediateField F k, Finite C ∧
      ∃ r : H →* GL n C, (Matrix.GeneralLinearGroup.map C.val.toRingHom).comp r = ρ := by
  let a (g : H × n × n) := (ρ g.1 : Matrix n n k) g.2.1 g.2.2
  let S := Set.range a
  let C := IntermediateField.adjoin F S
  have : Finite S := (Set.finite_range a).to_subtype
  have : FiniteDimensional F C := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hfin : Finite C := Module.finite_of_finite F
  let T (g : H) : Matrix n n C := Matrix.of fun i j =>
    ⟨(ρ g : Matrix n n k) i j, IntermediateField.subset_adjoin F S ⟨(g, i, j), rfl⟩⟩
  let m : Matrix n n C →+* Matrix n n k := C.val.toRingHom.mapMatrix
  have hm (g : H) : m (T g) = (ρ g : Matrix n n k) := by ext i j; rfl
  have hinj : Function.Injective m := by
    intro x y h
    apply Matrix.ext
    intro i j
    exact Subtype.ext (congrArg (fun A : Matrix n n k => A i j) h)
  let ψ : H →* Matrix n n C :=
    { toFun := T
      map_one' := hinj (by rw [hm, map_one, Units.val_one, map_one])
      map_mul' := fun x y => hinj (by rw [hm, map_mul m, hm, hm, map_mul, Units.val_mul]) }
  exact ⟨C, hfin, ψ.toHomUnits, MonoidHom.ext fun g => Units.ext (hm g)⟩

universe u

/-- The prescribed global reduction, read on the residue field of the canonical
valuative relation on the completion. Kind: definition. -/
def residueMapAtCompletion {K : Type u} {k : Type*} [Field K] [NumberField K] [Field k]
    (f : 𝓞 K →+* k) (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal = RingHom.ker f) :
    𝓀[v.adicCompletion K] →+* k :=
  (Ideal.Quotient.lift v.asIdeal f (fun _ ha => RingHom.mem_ker.mp (hv ▸ ha))).comp
    (v.residueFieldEquivAdicCompletion (K := K)).symm.toRingHom

/-- The global integer inclusion followed by residue and the completed residue
map is the original reduction, not a conjugate. Kind: PROVED. -/
theorem residueMapAtCompletion_apply {K : Type u} {k : Type*} [Field K] [NumberField K] [Field k]
    (f : 𝓞 K →+* k) (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal = RingHom.ker f) (a : 𝓞 K) :
    residueMapAtCompletion f v hv (IsLocalRing.residue _
      (⟨algebraMap (𝓞 K) (v.adicCompletion K) a,
        v.algebraMap_mem_integer_adicCompletion a⟩ : 𝒪[v.adicCompletion K])) = f a := by
  have he := v.residueFieldEquivAdicCompletion_apply_mk (K := K) a
  refine (congrArg (residueMapAtCompletion f v hv) he.symm).trans ?_
  unfold residueMapAtCompletion
  rw [RingHom.comp_apply]
  exact (congrArg (Ideal.Quotient.lift v.asIdeal f
      (fun _ ha => RingHom.mem_ker.mp (hv ▸ ha)))
    ((v.residueFieldEquivAdicCompletion (K := K)).symm_apply_apply
      (Ideal.Quotient.mk v.asIdeal a))).trans (Ideal.Quotient.lift_mk _ _ _)

/-- A finite-group representation over an algebraic extension of the prescribed
completion residue field lifts on the same group, over the integers of a finite
unramified extension of the completion. The full reduction on integers agrees
with `f`. Kind: PROVED. -/
theorem lift_with_global_reduction {K : Type u} {k n H : Type*}
    [Field K] [NumberField K] [Field k] [Fintype n] [DecidableEq n] [Group H] [Fintype H]
    (f : 𝓞 K →+* k) {ℓ : ℕ} [CharP k ℓ] (hℓ : ℓ ≠ 0)
    (hins : let v := placeOfReduction f hℓ
      let _ := (residueMapAtCompletion f v rfl).toAlgebra
      Algebra.IsAlgebraic 𝓀[v.adicCompletion K] k)
    (hcard : ¬ ℓ ∣ Fintype.card H) (ρ : H →* GL n k) :
    let v := placeOfReduction f hℓ
    let F := v.adicCompletion K
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : ValuativeExtension F L), IsUnramified F L ∧
        ∃ (red : 𝒪[L] →+* k) (r : H →* GL n 𝒪[L]),
          (Matrix.GeneralLinearGroup.map red).comp r = ρ ∧
          ∀ a : 𝓞 K, red (algebraMap 𝒪[F] 𝒪[L]
            ⟨algebraMap (𝓞 K) F a, v.algebraMap_mem_integer_adicCompletion a⟩) = f a := by
  let v := placeOfReduction f hℓ
  let F := v.adicCompletion K
  let g := residueMapAtCompletion f v rfl
  let _ := g.toAlgebra
  let _ : Algebra.IsAlgebraic 𝓀[F] k := hins
  obtain ⟨C, hC, r, hr⟩ := exists_finite_residual_factor (F := 𝓀[F]) ρ
  have huc : IsUnit (Fintype.card H : C) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have he : (Fintype.card H : k) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg C.val.toRingHom hz
    exact hcard ((CharP.cast_eq_zero_iff k ℓ _).mp he)
  obtain ⟨L, _, _, _, _, _, _, _, hUn, e, T, hT⟩ :=
    lift_over_unramified_residue F C huc r
  let red := C.val.toRingHom.comp
    (e.toRingEquiv.toRingHom.comp (IsLocalRing.residue 𝒪[L]))
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hUn, red, T, ?_, ?_⟩
  · rw [show red = _ from rfl, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_assoc, hT, hr]
  · intro a
    let aF : 𝒪[F] := ⟨algebraMap (𝓞 K) F a, v.algebraMap_mem_integer_adicCompletion a⟩
    change C.val (e (IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] aF))) = f a
    rw [← IsLocalRing.ResidueField.algebraMap_residue, e.commutes]
    exact residueMapAtCompletion_apply f v rfl a

/-- The algebraicity hypothesis of `lift_with_global_reduction` follows for the
algebraic closure of the prime field, for any chosen residue embedding.
Kind: PROVED. -/
theorem algebraic_of_embedding_into_algClosure_zmod (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type*} [Field F] (g : F →+* AlgebraicClosure (ZMod ℓ)) :
    let _ := g.toAlgebra
    Algebra.IsAlgebraic F (AlgebraicClosure (ZMod ℓ)) := by
  let k := AlgebraicClosure (ZMod ℓ)
  let _ := g.toAlgebra
  let hk : CharP k ℓ :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod ℓ) k) ℓ (Fact.out : ℓ.Prime).ne_zero
  let hF : CharP F ℓ := ⟨fun m => by
    have h := @CharP.cast_eq_zero_iff k _ ℓ hk m
    constructor
    · intro hm
      exact h.mp (by simpa only [map_natCast, map_zero] using congrArg g hm)
    · intro hm
      apply g.injective
      simpa only [map_natCast, map_zero] using h.mpr hm⟩
  let _ : Algebra (ZMod ℓ) F := @ZMod.algebra F _ ℓ hF
  have ht : IsScalarTower (ZMod ℓ) F k := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective (n := ℓ) x
    rw [map_intCast, map_intCast, map_intCast]
  exact Algebra.IsAlgebraic.tower_top (K := ZMod ℓ) (A := k) F

end DS966Small
