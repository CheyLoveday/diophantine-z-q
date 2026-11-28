import Mathlib

/-!
# Base change of exterior powers

For a commutative ring `A`, a commutative `A`-algebra `B` and an `A`-module `M`, we construct the
`B`-linear equivalence `⋀[B]^n (B ⊗[A] M) ≃ₗ[B] B ⊗[A] ⋀[A]^n M` sending
`ιMulti B n (fun i => 1 ⊗ₜ m i)` to `1 ⊗ₜ ιMulti A n m`.

The forward map is the degree-`n` part of `ExteriorAlgebra.baseChangeEquiv`, followed by the
base change of the graded projection onto degree `n`; the inverse comes from the universal property
of `⋀[A]^n M`.

As a consequence, the natural `A`-linear map `⋀[A]^n M → ⋀[B]^n (B ⊗[A] M)` is injective whenever
`⋀[A]^n M` is flat and `algebraMap A B` is injective; in particular for `M` free or projective
and `B` a nontrivial torsion-free `A`-algebra (for example a fraction field of a domain `A`).
-/

namespace ZInQ.HeightModelM5

open TensorProduct

section BaseChange

variable (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
  (n : ℕ)

/-- The `A`-linear projection of the exterior algebra onto its degree-`n` piece. -/
noncomputable def exteriorDegreeProj : ExteriorAlgebra A M →ₗ[A] ⋀[A]^n M :=
  DirectSum.component A ℕ (fun i => ⋀[A]^i M) n ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[A]^i M)).toLinearMap

theorem exteriorDegreeProj_ιMulti (m : Fin n → M) :
    exteriorDegreeProj A M n (ExteriorAlgebra.ιMulti A n m) = exteriorPower.ιMulti A n m := by
  apply Subtype.ext
  rw [exteriorPower.ιMulti_apply_coe]
  change ((DirectSum.decompose (fun i : ℕ => ⋀[A]^i M) (ExteriorAlgebra.ιMulti A n m)) n :
    ExteriorAlgebra A M) = _
  refine DirectSum.decompose_of_mem_same _ ?_
  rw [← exteriorPower.ιMulti_apply_coe]
  exact (exteriorPower.ιMulti A n m).2

theorem baseChangeEquiv_symm_ιMulti_one_tmul (m : Fin n → M) :
    (ExteriorAlgebra.baseChangeEquiv A M B).symm
        (ExteriorAlgebra.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] m i)) =
      (1 : B) ⊗ₜ[A] ExteriorAlgebra.ιMulti A n m := by
  rw [← Algebra.TensorProduct.includeRight_apply (R := A) (A := B), ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  congr 2
  funext i
  simp [ExteriorAlgebra.baseChangeEquiv_symm_apply]

/-- The forward map of the degree-`n` base change. -/
noncomputable def exteriorPowerBaseChangeFun : ⋀[B]^n (B ⊗[A] M) →ₗ[B] B ⊗[A] ⋀[A]^n M :=
  (exteriorDegreeProj A M n).baseChange B ∘ₗ
    (ExteriorAlgebra.baseChangeEquiv A M B).symm.toLinearMap ∘ₗ (⋀[B]^n (B ⊗[A] M)).subtype

theorem exteriorPowerBaseChangeFun_ιMulti (m : Fin n → M) :
    exteriorPowerBaseChangeFun A B M n
        (exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] m i)) =
      (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n m := by
  simp only [exteriorPowerBaseChangeFun, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, AlgEquiv.toLinearMap_apply, exteriorPower.ιMulti_apply_coe]
  rw [baseChangeEquiv_symm_ιMulti_one_tmul, LinearMap.baseChange_tmul, exteriorDegreeProj_ιMulti]

/-- The `A`-alternating map `m ↦ ιMulti B n (fun i => 1 ⊗ₜ m i)`. -/
noncomputable def toBaseChangeAlternating : M [⋀^Fin n]→ₗ[A] ⋀[B]^n (B ⊗[A] M) :=
  { ((exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A).compLinearMap
      (fun _ => TensorProduct.mk A B M 1) with
    map_eq_zero_of_eq' := fun m i j h hij =>
      (exteriorPower.ιMulti B n).map_eq_zero_of_eq (fun k => (1 : B) ⊗ₜ[A] m k)
        (by simp only [h]) hij }

theorem toBaseChangeAlternating_apply (m : Fin n → M) :
    toBaseChangeAlternating A B M n m = exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] m i) :=
  rfl

/-- The natural `A`-linear map `⋀[A]^n M → ⋀[B]^n (B ⊗[A] M)`. -/
noncomputable def exteriorPowerToBaseChange : ⋀[A]^n M →ₗ[A] ⋀[B]^n (B ⊗[A] M) :=
  exteriorPower.alternatingMapLinearEquiv (toBaseChangeAlternating A B M n)

theorem exteriorPowerToBaseChange_ιMulti (m : Fin n → M) :
    exteriorPowerToBaseChange A B M n (exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] m i) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- Two `B`-multilinear maps on `B ⊗[A] M` agreeing on tuples of pure tensors `1 ⊗ₜ m i` are
equal. -/
theorem multilinearMap_ext_one_tmul {N : Type*} [AddCommGroup N] [Module B N] (n : ℕ) :
    ∀ {f g : MultilinearMap B (fun _ : Fin n => B ⊗[A] M) N},
      (∀ m : Fin n → M, f (fun i => (1 : B) ⊗ₜ[A] m i) = g (fun i => (1 : B) ⊗ₜ[A] m i)) →
        f = g := by
  induction n with
  | zero =>
    intro f g h
    ext v
    rw [Subsingleton.elim v (fun i => (1 : B) ⊗ₜ[A] (Fin.elim0 i : M))]
    exact h _
  | succ n ih =>
    intro f g h
    have key : f.curryLeft = g.curryLeft := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul b m =>
        have hm : f.curryLeft ((1 : B) ⊗ₜ[A] m) = g.curryLeft ((1 : B) ⊗ₜ[A] m) := by
          refine ih fun m' => ?_
          rw [MultilinearMap.curryLeft_apply, MultilinearMap.curryLeft_apply]
          have e : (Fin.cons ((1 : B) ⊗ₜ[A] m) (fun i => (1 : B) ⊗ₜ[A] m' i) :
              Fin (n + 1) → B ⊗[A] M) =
              fun i => (1 : B) ⊗ₜ[A] (Fin.cons m m' : Fin (n + 1) → M) i := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          rw [e]
          exact h _
        have hb : b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A] m) := by
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [hb, map_smul, map_smul, hm]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    ext v
    rw [← Fin.cons_self_tail v, ← MultilinearMap.curryLeft_apply,
      ← MultilinearMap.curryLeft_apply, key]

/-- Two `B`-alternating maps on `B ⊗[A] M` agreeing on tuples of pure tensors `1 ⊗ₜ m i` are
equal. -/
theorem alternatingMap_ext_one_tmul {N : Type*} [AddCommGroup N] [Module B N]
    {f g : (B ⊗[A] M) [⋀^Fin n]→ₗ[B] N}
    (h : ∀ m : Fin n → M, f (fun i => (1 : B) ⊗ₜ[A] m i) = g (fun i => (1 : B) ⊗ₜ[A] m i)) :
    f = g :=
  AlternatingMap.coe_multilinearMap_injective (multilinearMap_ext_one_tmul A B M n h)

theorem exteriorPowerBaseChangeFun_toBaseChange (x : ⋀[A]^n M) :
    exteriorPowerBaseChangeFun A B M n (exteriorPowerToBaseChange A B M n x) =
      (1 : B) ⊗ₜ[A] x := by
  have hlin : ((exteriorPowerBaseChangeFun A B M n).restrictScalars A) ∘ₗ
      exteriorPowerToBaseChange A B M n = TensorProduct.mk A B (⋀[A]^n M) 1 := by
    apply exteriorPower.linearMap_ext
    ext m
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      LinearMap.comp_apply, exteriorPowerToBaseChange_ιMulti, LinearMap.restrictScalars_apply,
      exteriorPowerBaseChangeFun_ιMulti, TensorProduct.mk_apply]
  exact LinearMap.congr_fun hlin x

/-- Degree-`n` base change of exterior powers:
`⋀[B]^n (B ⊗[A] M) ≃ₗ[B] B ⊗[A] ⋀[A]^n M`. -/
noncomputable def exteriorPowerBaseChange : ⋀[B]^n (B ⊗[A] M) ≃ₗ[B] B ⊗[A] ⋀[A]^n M :=
  LinearEquiv.ofLinearMap (exteriorPowerBaseChangeFun A B M n)
    (LinearMap.liftBaseChange B (exteriorPowerToBaseChange A B M n))
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro b x
      rw [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, map_smul,
        exteriorPowerBaseChangeFun_toBaseChange, LinearMap.id_apply, smul_tmul', smul_eq_mul,
        mul_one])
    (by
      apply exteriorPower.linearMap_ext
      apply alternatingMap_ext_one_tmul
      intro m
      rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
        LinearMap.comp_apply, exteriorPowerBaseChangeFun_ιMulti, LinearMap.liftBaseChange_tmul,
        one_smul, exteriorPowerToBaseChange_ιMulti, LinearMap.id_apply])

theorem exteriorPowerBaseChange_ιMulti (m : Fin n → M) :
    exteriorPowerBaseChange A B M n (exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] m i)) =
      (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n m :=
  exteriorPowerBaseChangeFun_ιMulti A B M n m

theorem exteriorPowerBaseChange_ιMulti_tmul (b : Fin n → B) (m : Fin n → M) :
    exteriorPowerBaseChange A B M n (exteriorPower.ιMulti B n (fun i => b i ⊗ₜ[A] m i)) =
      (∏ i, b i) ⊗ₜ[A] exteriorPower.ιMulti A n m := by
  have hb : (fun i => b i ⊗ₜ[A] m i) = fun i => b i • ((1 : B) ⊗ₜ[A] m i) := by
    funext i
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hs : exteriorPower.ιMulti B n (fun i => b i • ((1 : B) ⊗ₜ[A] m i)) =
      (∏ i, b i) • exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] m i) :=
    (exteriorPower.ιMulti B n).toMultilinearMap.map_smul_univ b _
  rw [hb, hs, map_smul, exteriorPowerBaseChange_ιMulti, smul_tmul', smul_eq_mul, mul_one]

theorem exteriorPowerBaseChange_symm_tmul (b : B) (x : ⋀[A]^n M) :
    (exteriorPowerBaseChange A B M n).symm (b ⊗ₜ[A] x) =
      b • exteriorPowerToBaseChange A B M n x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

theorem exteriorPowerToBaseChange_eq (x : ⋀[A]^n M) :
    exteriorPowerToBaseChange A B M n x = (exteriorPowerBaseChange A B M n).symm (1 ⊗ₜ[A] x) := by
  rw [exteriorPowerBaseChange_symm_tmul, one_smul]

/-- If `⋀[A]^n M` is flat and `algebraMap A B` is injective, then
`exteriorPowerToBaseChange` is injective. -/
theorem exteriorPowerToBaseChange_injective_of_flat [Module.Flat A (⋀[A]^n M)]
    (hAB : Function.Injective (algebraMap A B)) :
    Function.Injective (exteriorPowerToBaseChange A B M n) := by
  have h1 : Function.Injective fun x : ⋀[A]^n M => (1 : B) ⊗ₜ[A] x := by
    have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := ⋀[A]^n M)
      (Algebra.linearMap A B) hAB
    have e : (fun x : ⋀[A]^n M => (1 : B) ⊗ₜ[A] x) =
        (LinearMap.rTensor (⋀[A]^n M) (Algebra.linearMap A B)) ∘
          (TensorProduct.lid A (⋀[A]^n M)).symm := by
      funext x
      simp
    rw [e]
    exact hr.comp (TensorProduct.lid A _).symm.injective
  intro x y hxy
  apply h1
  apply (exteriorPowerBaseChange A B M n).symm.injective
  rw [← exteriorPowerToBaseChange_eq, ← exteriorPowerToBaseChange_eq, hxy]

/-- Injectivity into the generic fibre, for `M` free. -/
theorem exteriorPowerToBaseChange_injective [IsDomain A] [Module.Free A M]
    [NoZeroSMulDivisors A B] [Nontrivial B] :
    Function.Injective (exteriorPowerToBaseChange A B M n) :=
  exteriorPowerToBaseChange_injective_of_flat A B M n (FaithfulSMul.algebraMap_injective A B)

/-- Exterior powers of a projective module are flat (as retracts of exterior powers of a free
module). -/
theorem exteriorPower_flat_of_projective [Module.Projective A M] : Module.Flat A (⋀[A]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A M)
  exact Module.Flat.of_retract (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination A id))
    (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])

/-- Injectivity into the generic fibre, for `M` projective. -/
theorem exteriorPowerToBaseChange_injective_of_projective [IsDomain A] [Module.Projective A M]
    [NoZeroSMulDivisors A B] [Nontrivial B] :
    Function.Injective (exteriorPowerToBaseChange A B M n) :=
  haveI := exteriorPower_flat_of_projective A M n
  exteriorPowerToBaseChange_injective_of_flat A B M n (FaithfulSMul.algebraMap_injective A B)

end BaseChange

end ZInQ.HeightModelM5
