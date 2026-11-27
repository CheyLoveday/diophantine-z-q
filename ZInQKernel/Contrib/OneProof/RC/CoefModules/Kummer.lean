import ZInQKernel.Contrib.OneProof.RC.CoefModules.CocycleCondition
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois

/-!
# Lane RC28: the finite-level local Kummer condition in genuine continuous cochains

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3468): "For the actual
local twist `B = E^{(h)}` over `F = K_v`, the condition `U_F = B(F)^∧_2[−1] → RΓ(F, T_2B)` includes
the finite two-primary torsion. Its reduction modulo `2^a` has `B(F)[2^a]` in degree zero and
`B(F)/2^aB(F)` in degree one. Its Kummer image is its exact local annihilator …"; and (tex
3430–3438) "derived coefficient extension defines the scalar `A_i` condition".

This file builds the finite-level object for `m = 2^a` (indeed for any `m ≥ 1`), over a field `F`
of characteristic zero (so that `F̄/F` is Galois), for an elliptic curve `B` over `F`, with
`G_F = Field.absoluteGaloisGroup F` (Mathlib, Krull topology) and the genuine continuous cochains
`C^•_cont(G_F, −)` of lane RC26:

* `PtAlg F B = B(F̄)` (points over `AlgebraicClosure F`), a discrete `G_F`-module
  (`PtAlg.instContinuousSMul`: stabilizers of points are open; the action is the other group's
  `pointGaloisAction`/`torsionGaloisAction`, `pointGaloisAction_eq_smul`,
  `torsionGaloisAction_eq_smul`); `TorsAlg F B m = B(F̄)[m]`, a finite discrete `G_F`-module;
  `basePt : B(F) → B(F̄)`, `exists_basePt_of_fixed` (Galois descent), `exists_nsmul_eq`
  (divisibility of `B(F̄)`).
* `kummerCocycle F B m P ∈ C¹_cont(G_F, B(F̄)[m])`, `σ ↦ σQ − Q` (`m • Q = P`): a cocycle
  (`kummerCocycle_isCocycle`), additive up to coboundaries (`kummerCocycle_add`), a coboundary iff
  `P ∈ m B(F)` (`kummerCocycle_mem_coboundaries_iff`); any other division point gives a cocycle
  differing by a coboundary (`kummerCocycleOf_sub_mem`, `kummerCocycleOf_mem_sup`).
* `kummerZ F B m` (the `ℤ`-span of the `κ_P`) and **the Kummer condition**
  `kummerCondition F B m = cocycleCondition (kummerZ F B m) _ : GCx ℤ`, with its inclusion
  `kummerConditionι` into `natCx (contCochains ℤ G_F B(F̄)[m])`, injective in every degree.
* Cohomology (Mathlib homology of `(kummerCondition F B m).toCC`):
  `kummerH0AddEquiv : B(F)[m] ≃+ H⁰` and `kummerH1AddEquiv : B(F) ⧸ m B(F) ≃+ H¹`
  (`P ↦ [κ_P]`; `kummerH1Hom_ker`, `kummerH1Hom_surjective`); `H⁰` is that of the local complex
  (`kummerCondition_isIso_homologyMap_zero`) and `H¹` injects into it, so the Kummer map
  `B(F) ⧸ m B(F) → H¹(C^•_cont(G_F, B(F̄)[m]))` is injective (`kummerMapH1_injective`) and sends
  `[P]` to the homology class of the cycle `κ_P` (`kummerMapH1_mk`).
* Coefficient extension (tex 3430–3438): for a discrete `k[G_F]`-module `M` and an equivariant
  additive `ι : B(F̄)[m] → M`, `kummerZ' k ι` (the `k`-span of `g ↦ a • ι(κ_P(g))`) and
  `kummerConditionIn k ι hι : GCx k` with its injective map into `natCx (contCochains k G_F M)`;
  `kummerZ'_id`, `kummerConditionIn_id` recover the scalar condition; `kummerLocalConditions` and
  `kummerGaloisLocalConditions` (at `K_v`, `v ∈ S`, for a number field `K`) package such conditions
  as genuine `LocalConditions` of `SelmerComplex/Selmer.lean`.
* Non-vacuity: `y² = x³ − x` over `ℚ`, `m = 2` (`curveY2X3mX`,
  `kummerCondition_curveY2X3mX_H0_nontrivial`).

DEPARTURE (form): the text's `U_F = B(F)^∧_2[−1]` and its derived reduction modulo `2^a` are
realized at finite level by the explicit subcomplex `U⁰ = C⁰_cont`, `U¹ = kummerZ ⊔ B¹_cont`,
`Uⁿ = 0` otherwise, of the genuine continuous cochains (see `CocycleCondition.lean`); its
cohomology is the prescribed one (`B(F)[m]` in degree zero, `B(F)/mB(F)` in degree one) and it maps
injectively into the local cochains. The hypothesis `(m : F) ≠ 0` of the text is automatic in
characteristic zero (`natCast_ne_zero_of_charZero`). The Kummer cocycles use chosen division points
(`Classical.choose`); the condition does not depend on these choices (`kummerCocycleOf_mem_sup`).
For comparison only: the other group's cohomology-level Kummer map over the separable closure
(`WeierstrassCurve.kummerMap`) is not used.

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open CategoryTheory WeierstrassCurve ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex NumberField
  IsDedekindDomain

/-! ### The Galois module `B(F̄)` and its `m`-torsion -/

section Points

variable (F : Type) [Field F] (B : WeierstrassCurve F)

/-- Definition (tex 3413–3416: the points of the local twist over `F̄`). The points `B(F̄)` of
`B` over the algebraic closure `F̄ = AlgebraicClosure F`, as a type synonym of the points of the
base change, carrying the discrete topology and the Galois action. -/
def PtAlg : Type := (B.baseChange (AlgebraicClosure F)).toAffine.Point

open scoped Classical in
/-- Definition (tex 3413–3416). The group law of `B(F̄)`. -/
instance PtAlg.instAddCommGroup : AddCommGroup (PtAlg F B) :=
  inferInstanceAs (AddCommGroup (B.baseChange (AlgebraicClosure F)).toAffine.Point)

/-- Definition (tex 3413–3416). `B(F̄)` carries the discrete topology. -/
instance PtAlg.instTopologicalSpace : TopologicalSpace (PtAlg F B) := ⊥

/-- PROVED (tex 3413–3416). The topology of `B(F̄)` is discrete. -/
instance PtAlg.instDiscreteTopology : DiscreteTopology (PtAlg F B) := ⟨rfl⟩

open scoped Classical in
/-- Definition (tex 3413–3416). The identification of `PtAlg F B` with the points of the base
change of `B` to `F̄`. -/
def ptEquiv : (B.baseChange (AlgebraicClosure F)).toAffine.Point ≃+ PtAlg F B :=
  AddEquiv.refl _

variable {F B}

open scoped Classical in
/-- Definition (tex 3413–3416). The absolute Galois group `G_F = Gal(F̄/F)` (Mathlib's
`Field.absoluteGaloisGroup F`) acts on `B(F̄)` through the coordinates (Mathlib's
`WeierstrassCurve.Affine.Point.map` along each automorphism). -/
instance PtAlg.instSMul : SMul (Field.absoluteGaloisGroup F) (PtAlg F B) where
  smul σ P := ptEquiv F B (Affine.Point.map (W' := B) σ.toAlgHom ((ptEquiv F B).symm P))

open scoped Classical in
/-- PROVED (tex 3413–3416). The Galois action on a point is the point map along the
automorphism. -/
theorem smul_ptEquiv (σ : Field.absoluteGaloisGroup F)
    (P : (B.baseChange (AlgebraicClosure F)).toAffine.Point) :
    σ • ptEquiv F B P = ptEquiv F B (Affine.Point.map (W' := B) σ.toAlgHom P) :=
  rfl

open scoped Classical in
/-- PROVED (tex 3413–3416). The Galois action is the action `WeierstrassCurve.pointGaloisAction`
of the other group. -/
theorem pointGaloisAction_eq_smul (σ : Field.absoluteGaloisGroup F)
    (P : (B.baseChange (AlgebraicClosure F)).toAffine.Point) :
    ptEquiv F B (Multiplicative.toAdd (B.pointGaloisAction σ) P) = σ • ptEquiv F B P :=
  congrArg (ptEquiv F B) (pointGaloisAction_apply B σ P)

open scoped Classical in
/-- PROVED (tex 3413–3416). `B(F̄)` is a `G_F`-module. -/
instance PtAlg.instDistribMulAction :
    DistribMulAction (Field.absoluteGaloisGroup F) (PtAlg F B) where
  one_smul P := by
    obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
    rw [smul_ptEquiv]
    congr 1
    rcases P with _ | ⟨x, y, h⟩ <;> rfl
  mul_smul σ τ P := by
    obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
    rw [smul_ptEquiv, smul_ptEquiv, smul_ptEquiv, Affine.Point.map_map]
    rfl
  smul_zero σ := by
    rw [← (ptEquiv F B).map_zero, smul_ptEquiv, map_zero]
  smul_add σ P Q := by
    obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
    obtain ⟨Q, rfl⟩ := (ptEquiv F B).surjective Q
    rw [← map_add, smul_ptEquiv, smul_ptEquiv, smul_ptEquiv, map_add, map_add]

/-- PROVED (tex 3413–3416). The stabilizer in `G_F` of an element of `F̄` is open (Krull
topology; `F̄/F` is algebraic). -/
theorem isOpen_fix (x : AlgebraicClosure F) :
    IsOpen {σ : Field.absoluteGaloisGroup F | σ.toAlgHom x = x} := by
  have h := stabilizer_isOpen_of_isIntegral (K := F) (L := AlgebraicClosure F) x
  have e : {σ : Field.absoluteGaloisGroup F | σ.toAlgHom x = x} =
      ((MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) x :
        Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) :
          Set (Field.absoluteGaloisGroup F)) := by
    ext σ
    exact Iff.rfl
  rw [e]
  exact h

open scoped Classical in
/-- PROVED (tex 3413–3416). **`B(F̄)` is a discrete `G_F`-module**: the stabilizer of a point
contains the (open) stabilizers of its coordinates. -/
instance PtAlg.instContinuousSMul : ContinuousSMul (Field.absoluteGaloisGroup F) (PtAlg F B) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun P => ?_
  obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
  rcases P with _ | ⟨x, y, h⟩
  · convert isOpen_univ
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    rw [← Affine.Point.zero_def, map_zero, smul_zero]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    refine Filter.mem_of_superset (((isOpen_fix x).inter (isOpen_fix y)).mem_nhds ⟨rfl, rfl⟩) ?_
    rintro σ ⟨hx, hy⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_ptEquiv, Affine.Point.map_some]
    congr 1
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

variable (F B) in
/-- Definition (tex 3415–3417: `B[2^a]`, here for any `m`). **The `G_F`-module `B(F̄)[m]`**: the
`m`-torsion subgroup `AddSubgroup.torsionBy (B(F̄)) m` of the points of `B` over `F̄`. It is a
discrete (`Subtype.discreteTopology`) `G_F`-module, finite for `B` elliptic and `m ≠ 0`. -/
abbrev TorsAlg (m : ℕ) : Type := AddSubgroup.torsionBy (PtAlg F B) (m : ℤ)

/-- PROVED (tex 3415–3417). The Galois action preserves `B(F̄)[m]`. -/
theorem smul_mem_torsAlg {m : ℕ} (σ : Field.absoluteGaloisGroup F) {P : PtAlg F B}
    (hP : P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ)) :
    σ • P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← smul_comm, hP, smul_zero]

/-- PROVED (tex 3415–3417). `B(F̄)[m]` is a `G_F`-module. -/
instance TorsAlg.instDistribMulAction (m : ℕ) :
    DistribMulAction (Field.absoluteGaloisGroup F) (TorsAlg F B m) where
  smul σ t := ⟨σ • (t : PtAlg F B), smul_mem_torsAlg σ t.2⟩
  one_smul t := Subtype.ext (one_smul _ (t : PtAlg F B))
  mul_smul σ τ t := Subtype.ext (mul_smul σ τ (t : PtAlg F B))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ s t := Subtype.ext (smul_add σ (s : PtAlg F B) t)

/-- PROVED (tex 3415–3417). The action on `B(F̄)[m]` is the action on `B(F̄)`. -/
@[simp]
theorem coe_smul_torsAlg {m : ℕ} (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m) :
    ((σ • t : TorsAlg F B m) : PtAlg F B) = σ • (t : PtAlg F B) :=
  rfl

open scoped Classical in
/-- PROVED (tex 3415–3417). The action on `B(F̄)[m]` is the action
`WeierstrassCurve.torsionGaloisAction` of the other group, read through `ptEquiv`. -/
theorem torsionGaloisAction_eq_smul {m : ℕ} (σ : Field.absoluteGaloisGroup F)
    (t : AddSubgroup.torsionBy (B.baseChange (AlgebraicClosure F)).toAffine.Point (m : ℤ)) :
    ptEquiv F B ((Multiplicative.toAdd (B.torsionGaloisAction (m : ℤ) σ) t :
      AddSubgroup.torsionBy (B.baseChange (AlgebraicClosure F)).toAffine.Point (m : ℤ)) :
        (B.baseChange (AlgebraicClosure F)).toAffine.Point) =
      σ • ptEquiv F B (t : (B.baseChange (AlgebraicClosure F)).toAffine.Point) :=
  (congrArg (ptEquiv F B) (torsionGaloisAction_apply_coe B (m : ℤ) σ t)).trans
    (pointGaloisAction_eq_smul (B := B) σ (t : (B.baseChange (AlgebraicClosure F)).toAffine.Point))

/-- PROVED (tex 3415–3417). **`B(F̄)[m]` is a discrete `G_F`-module.** -/
instance TorsAlg.instContinuousSMul (m : ℕ) :
    ContinuousSMul (Field.absoluteGaloisGroup F) (TorsAlg F B m) :=
  ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩

open scoped Classical in
/-- PROVED (tex 3415–3417). **`B(F̄)[m]` is finite** for `B` elliptic and `m ≠ 0` (the other
group's `WeierstrassCurve.finite_torsionBy`). -/
instance TorsAlg.instFinite [B.IsElliptic] (m : ℕ) [NeZero m] : Finite (TorsAlg F B m) :=
  WeierstrassCurve.finite_torsionBy (B.baseChange (AlgebraicClosure F)) (n := (m : ℤ))
    (Int.natCast_ne_zero.2 (NeZero.ne m))

variable [DecidableEq F]

variable (F B) in
open scoped Classical in
/-- Definition (tex 3413–3417). The inclusion `B(F) → B(F̄)`, induced by `F → F̄`. -/
def basePt : B.toAffine.Point →+ PtAlg F B :=
  (ptEquiv F B).toAddMonoidHom.comp <|
    (Affine.Point.map (W' := B.toAffine) (Algebra.ofId F (AlgebraicClosure F))).comp
      (Affine.Point.equivBaseChangeSelf B.toAffine).toAddMonoidHom

open scoped Classical in
/-- PROVED (tex 3413–3417). The inclusion `B(F) → B(F̄)` keeps the coordinates. -/
theorem basePt_some {x y : F} (h : B.toAffine.Nonsingular x y) :
    basePt F B (.some x y h) =
      ptEquiv F B (.some (algebraMap F (AlgebraicClosure F) x)
        (algebraMap F (AlgebraicClosure F) y)
        ((B.toAffine.baseChange_nonsingular (Algebra.ofId F (AlgebraicClosure F)).injective
          x y).2 h)) := by
  simp only [basePt, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Affine.Point.equivBaseChangeSelf_some, Affine.Point.map_some]
  rfl

/-- PROVED (tex 3413–3417). The inclusion `B(F) → B(F̄)` is injective. -/
theorem basePt_injective : Function.Injective (basePt F B) := by
  classical
  exact (ptEquiv F B).injective.comp <| (Affine.Point.map_injective _).comp
    (Affine.Point.equivBaseChangeSelf B.toAffine).injective

/-- PROVED (tex 3413–3417). The points of `B(F)` are fixed by `G_F`. -/
theorem smul_basePt (σ : Field.absoluteGaloisGroup F) (P : B.toAffine.Point) :
    σ • basePt F B P = basePt F B P := by
  classical
  rw [basePt, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, smul_ptEquiv,
    AddMonoidHom.comp_apply, Affine.Point.map_map]
  rw [Subsingleton.elim (σ.toAlgHom.comp (Algebra.ofId F (AlgebraicClosure F)))
    (Algebra.ofId F (AlgebraicClosure F))]

/-- PROVED (tex 3415–3417; Galois descent, `F` of characteristic zero so that `F̄/F` is Galois).
**A point of `B(F̄)` fixed by `G_F` comes from `B(F)`** (Mathlib's
`InfiniteGalois.mem_range_algebraMap_iff_fixed` applied to the coordinates). -/
theorem exists_basePt_of_fixed [CharZero F] {Q : PtAlg F B}
    (hQ : ∀ σ : Field.absoluteGaloisGroup F, σ • Q = Q) :
    ∃ P : B.toAffine.Point, basePt F B P = Q := by
  classical
  obtain ⟨Q, rfl⟩ := (ptEquiv F B).surjective Q
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, by rw [map_zero, ← Affine.Point.zero_def, map_zero]⟩
  · have hfix : ∀ σ : Field.absoluteGaloisGroup F, σ.toAlgHom x = x ∧ σ.toAlgHom y = y :=
      fun σ => by
        have h := hQ σ
        rw [smul_ptEquiv, Affine.Point.map_some] at h
        simpa only [Affine.Point.some.injEq] using (ptEquiv F B).injective h
    obtain ⟨x₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 fun σ => (hfix σ).1
    obtain ⟨y₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 fun σ => (hfix σ).2
    have h₀ : B.toAffine.Nonsingular x₀ y₀ :=
      (B.toAffine.baseChange_nonsingular (Algebra.ofId F (AlgebraicClosure F)).injective
        x₀ y₀).1 h
    exact ⟨.some x₀ y₀ h₀, by rw [basePt_some]⟩

omit [DecidableEq F] in
/-- PROVED (tex 3413–3417). **`B(F̄)` is `m`-divisible** for `B` elliptic, `m ≠ 0`, `F` of
characteristic zero (the other group's `WeierstrassCurve.Affine.nsmul_surjective`). -/
theorem exists_nsmul_eq [CharZero F] [B.IsElliptic] (m : ℕ) [NeZero m] (Q : PtAlg F B) :
    ∃ R : PtAlg F B, m • R = Q := by
  classical
  have hm : ((m : ℕ) : AlgebraicClosure F) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  obtain ⟨R, hR⟩ := Affine.nsmul_surjective (B.baseChange (AlgebraicClosure F)).toAffine hm
    ((ptEquiv F B).symm Q)
  refine ⟨ptEquiv F B R, ?_⟩
  rw [← map_nsmul]
  exact (congrArg (ptEquiv F B) hR).trans ((ptEquiv F B).apply_symm_apply Q)

variable (F B) in
/-- Definition (tex 3415–3417). The inclusion `B(F)[m] → B(F̄)[m]`. -/
def baseTors (m : ℕ) : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) →+ TorsAlg F B m :=
  ((basePt F B).comp (AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)).subtype).codRestrict _
    fun T => by
      rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul,
        AddSubgroup.coe_subtype, AddSubgroup.torsionBy.nsmul_iff.1 T.2, map_zero]

/-- PROVED (tex 3415–3417). The inclusion `B(F)[m] → B(F̄)[m]` on underlying points. -/
@[simp]
theorem coe_baseTors {m : ℕ} (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    (baseTors F B m T : PtAlg F B) = basePt F B T :=
  rfl

/-- PROVED (tex 3415–3417). The points of `B(F)[m]` are fixed by `G_F`. -/
theorem smul_baseTors {m : ℕ} (σ : Field.absoluteGaloisGroup F)
    (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    σ • baseTors F B m T = baseTors F B m T :=
  Subtype.ext (by rw [coe_smul_torsAlg, coe_baseTors, smul_basePt])

/-- PROVED (tex 3415–3417). The inclusion `B(F)[m] → B(F̄)[m]` is injective. -/
theorem baseTors_injective (m : ℕ) : Function.Injective (baseTors F B m) :=
  fun _ _ h => Subtype.ext (basePt_injective (congrArg Subtype.val h))

/-- PROVED (tex 3415–3417: "`B(F)[2^a]` in degree zero"). **The `G_F`-invariants of `B(F̄)[m]`
are the points of `B(F)[m]`.** -/
theorem exists_baseTors_of_fixed [CharZero F] {m : ℕ} {Q : TorsAlg F B m}
    (h : ∀ σ : Field.absoluteGaloisGroup F, σ • Q = Q) :
    ∃ T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ), baseTors F B m T = Q := by
  obtain ⟨T, hT⟩ := exists_basePt_of_fixed (B := B) (Q := (Q : PtAlg F B))
    fun σ => congrArg Subtype.val (h σ)
  refine ⟨⟨T, AddSubgroup.torsionBy.nsmul_iff.2 (basePt_injective ?_)⟩, Subtype.ext hT⟩
  rw [map_nsmul, hT, map_zero, AddSubgroup.torsionBy.nsmul_iff.1 Q.2]

end Points

/-! ### Kummer cocycles -/

section KummerCocycle

variable (F : Type) [Field F] [CharZero F] [DecidableEq F] (B : WeierstrassCurve F) [B.IsElliptic]
  (m : ℕ) [NeZero m]

omit [DecidableEq F] [B.IsElliptic] in
/-- PROVED (tex 3413–3417). The text's hypothesis `(m : F) ≠ 0` (`m = 2^a` invertible in `F`)
is automatic in characteristic zero. -/
theorem natCast_ne_zero_of_charZero : (m : F) ≠ 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne m)

/-- PROVED (tex 3413–3417). Every point of `B(F)` has an `m`-th division point in `B(F̄)`. -/
theorem exists_divPt (P : B.toAffine.Point) : ∃ Q : PtAlg F B, m • Q = basePt F B P :=
  exists_nsmul_eq m _

/-- Definition (tex 3413–3417). A chosen `m`-th division point `Q ∈ B(F̄)` of `P ∈ B(F)`,
`m • Q = P`. -/
def divPt (P : B.toAffine.Point) : PtAlg F B :=
  Classical.choose (exists_divPt F B m P)

/-- PROVED (tex 3413–3417). `m • divPt P = P`. -/
theorem nsmul_divPt (P : B.toAffine.Point) : m • divPt F B m P = basePt F B P :=
  Classical.choose_spec (exists_divPt F B m P)

/-- PROVED (tex 3413–3417). The Kummer difference `σ Q − Q` is `m`-torsion (`P` is fixed by
`G_F`). -/
theorem smul_sub_divPt_mem (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) :
    σ • divPt F B m P - divPt F B m P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, smul_comm, nsmul_divPt, smul_basePt, sub_self]

/-- Definition (tex 3417–3418, the Kummer map). The Kummer function `σ ↦ σ Q − Q ∈ B(F̄)[m]` of
`P ∈ B(F)`, for the chosen division point `Q = divPt P`. -/
def kummerFun (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) : TorsAlg F B m :=
  ⟨σ • divPt F B m P - divPt F B m P, smul_sub_divPt_mem F B m P σ⟩

/-- PROVED (tex 3417–3418). The value of the Kummer function. -/
@[simp]
theorem coe_kummerFun (P : B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) :
    (kummerFun F B m P σ : PtAlg F B) = σ • divPt F B m P - divPt F B m P :=
  rfl

/-- PROVED (tex 3417–3418). The Kummer function is continuous (locally constant). -/
theorem continuous_kummerFun (P : B.toAffine.Point) : Continuous (kummerFun F B m P) :=
  Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _

/-- PROVED (tex 3417–3418). The cocycle identity `κ(στ) = σ • κ(τ) + κ(σ)`. -/
theorem kummerFun_mul (P : B.toAffine.Point) (σ τ : Field.absoluteGaloisGroup F) :
    kummerFun F B m P (σ * τ) = σ • kummerFun F B m P τ + kummerFun F B m P σ := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, coe_smul_torsAlg, coe_kummerFun, mul_smul, smul_sub]
  abel

/-- Definition (tex 3417–3418). **The Kummer cocycle** `κ_P ∈ C¹_cont(G_F, B(F̄)[m])`,
`σ ↦ σ Q − Q` with `m • Q = P`, a genuine continuous inhomogeneous `1`-cochain. -/
def kummerCocycle (P : B.toAffine.Point) :
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 :=
  ⟨(fun g => kummerFun F B m P (g 0) :
      (Fin 1 → Field.absoluteGaloisGroup F) → TorsAlg F B m),
    (continuous_kummerFun F B m P).comp (continuous_apply 0)⟩

/-- PROVED (tex 3417–3418). The value of the Kummer cocycle. -/
@[simp]
theorem cfun_kummerCocycle (P : B.toAffine.Point) (g : Fin 1 → Field.absoluteGaloisGroup F) :
    cfun (kummerCocycle F B m P) g = kummerFun F B m P (g 0) :=
  rfl

/-- PROVED (tex 3417–3418). **The Kummer cocycle is a cocycle**: `d¹ κ_P = 0`. -/
theorem kummerCocycle_isCocycle (P : B.toAffine.Point) :
    contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 (kummerCocycle F B m P) = 0 := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) 1 (kummerCocycle F B m P) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • kummerFun F B m P (g 1) + ((-1 : ℤ) ^ ((0 : ℕ) + 1) •
    kummerFun F B m P (g 0 * g 1) + (-1 : ℤ) ^ ((1 : ℕ) + 1) • kummerFun F B m P (g 0)) = 0
  rw [kummerFun_mul]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- PROVED (tex 3417–3418). **The Kummer cocycle is additive up to a continuous coboundary**:
`κ_{P+P'} − κ_P − κ_{P'} = d⁰(T)` with `T = Q_{P+P'} − Q_P − Q_{P'} ∈ B(F̄)[m]`. -/
theorem kummerCocycle_add (P P' : B.toAffine.Point) :
    kummerCocycle F B m (P + P') - kummerCocycle F B m P - kummerCocycle F B m P' ∈
      contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  have hT : divPt F B m (P + P') - divPt F B m P - divPt F B m P' ∈
      AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_sub, nsmul_divPt, nsmul_divPt,
      nsmul_divPt, map_add, sub_sub, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (⟨_, hT⟩ : TorsAlg F B m), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) _ g).trans ?_
  change _ = kummerFun F B m (P + P') (g 0) - kummerFun F B m P (g 0) - kummerFun F B m P' (g 0)
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun, smul_sub]
  abel

/-- PROVED (tex 3417–3418: the kernel of the Kummer map). **`κ_P` is a continuous coboundary iff
`P ∈ m B(F)`.** -/
theorem kummerCocycle_mem_coboundaries_iff (P : B.toAffine.Point) :
    kummerCocycle F B m P ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) ↔
      ∃ P' : B.toAffine.Point, m • P' = P := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (mem_contB1_iff _).1 h
    have key : ∀ σ : Field.absoluteGaloisGroup F,
        σ • (divPt F B m P - ((cfun c default : TorsAlg F B m) : PtAlg F B)) =
          divPt F B m P - ((cfun c default : TorsAlg F B m) : PtAlg F B) := by
      intro σ
      have h1 : σ • (cfun c default : TorsAlg F B m) - cfun c default = kummerFun F B m P σ :=
        (contD_zero_apply (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B m) c
          (fun _ => σ)).symm.trans (congrArg (fun f => cfun f (fun _ => σ)) hc)
      have h2 := congrArg Subtype.val h1
      simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun] at h2
      rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
      exact h2.symm
    obtain ⟨P', hP'⟩ := exists_basePt_of_fixed key
    refine ⟨P', basePt_injective ?_⟩
    rw [map_nsmul, hP', nsmul_sub, nsmul_divPt,
      AddSubgroup.torsionBy.nsmul_iff.1 (cfun c default : TorsAlg F B m).2, sub_zero]
  · rintro ⟨P', rfl⟩
    have hT : divPt F B m (m • P') - basePt F B P' ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
      rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_divPt, map_nsmul, sub_self]
    refine (mem_contB1_iff _).2 ⟨constCochain (⟨_, hT⟩ : TorsAlg F B m), ?_⟩
    apply Subtype.ext
    funext g
    refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
      (M := TorsAlg F B m) _ g).trans ?_
    change _ = kummerFun F B m (m • P') (g 0)
    apply Subtype.ext
    simp only [AddSubgroup.coe_sub, coe_smul_torsAlg, coe_kummerFun, smul_sub, smul_basePt]
    abel

/-- PROVED (tex 3417–3418). The Kummer cocycle of a point of `m B(F)` (e.g. of `0`) is a
continuous coboundary. -/
theorem kummerCocycle_zero_mem :
    kummerCocycle F B m 0 ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) :=
  (kummerCocycle_mem_coboundaries_iff F B m 0).2 ⟨0, smul_zero _⟩

/-- Definition (tex 3417–3418). The Kummer map into `H¹`-level cochains,
`B(F) → C¹_cont(G_F, B(F̄)[m]) ⧸ B¹_cont`, `P ↦ [κ_P]`; additive by `kummerCocycle_add`. -/
def kummerToQuot :
    B.toAffine.Point →+
      (contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 ⧸
        contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (kummerCocycle F B m P)) fun P P' => by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, ← sub_sub]
    exact kummerCocycle_add F B m P P'

/-- PROVED (tex 3417–3418). The value of `kummerToQuot`. -/
@[simp]
theorem kummerToQuot_apply (P : B.toAffine.Point) :
    kummerToQuot F B m P = Submodule.Quotient.mk (kummerCocycle F B m P) :=
  rfl

/-! ### The Kummer condition -/

/-- Definition (tex 3417–3418: the Kummer image). **The Kummer submodule**
`kummerZ F B m ⊆ C¹_cont(G_F, B(F̄)[m])`, the `ℤ`-span of the Kummer cocycles `κ_P`, `P ∈ B(F)`. -/
abbrev kummerZ :=
  cochainSpan (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B m)
    (Set.range (kummerCocycle F B m))

/-- PROVED (tex 3417–3418). The Kummer submodule consists of cocycles. -/
theorem kummerZ_cocycle :
    ∀ z ∈ kummerZ F B m, contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 z = 0 :=
  cochainSpan_cocycle _ (by
    rintro _ ⟨P, rfl⟩
    exact kummerCocycle_isCocycle F B m P)

/-- PROVED (tex 3417–3418). Every element of the Kummer submodule is congruent modulo continuous
coboundaries to a single Kummer cocycle `κ_P`. -/
theorem exists_kummerToQuot_eq (z : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1)
    (hz : z ∈ kummerZ F B m) :
    ∃ P : B.toAffine.Point, kummerToQuot F B m P = Submodule.Quotient.mk z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, rfl⟩
  | zero => exact ⟨0, by rw [map_zero, Submodule.Quotient.mk_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨P', hP'⟩ := hy
    exact ⟨P + P', by rw [map_add, hP, hP', Submodule.Quotient.mk_add]⟩
  | smul a x _ hx =>
    obtain ⟨P, hP⟩ := hx
    refine ⟨a • P, ?_⟩
    rw [map_zsmul, hP, Submodule.Quotient.mk_smul]
    exact (int_smul_eq_zsmul _ a _).symm

/-- Definition (tex 3413–3418; DEPARTURE of form, see `CocycleCondition.lean`). **The finite-level
local Kummer condition** `U = [C⁰_cont(G_F, B(F̄)[m]) --d⁰--> kummerZ ⊔ B¹_cont]`, the cocycle
condition of the Kummer submodule, a relation-indexed complex `GCx ℤ`. -/
abbrev kummerCondition : GCx ℤ :=
  cocycleCondition (kummerZ F B m) (kummerZ_cocycle F B m)

/-- Definition (tex 3413–3418, the local map `U_F → RΓ(F, B[m])`). The inclusion of the Kummer
condition into the genuine local complex `C^•_cont(G_F, B(F̄)[m])`. -/
abbrev kummerConditionι :
    GHom (kummerCondition F B m)
      (natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))) :=
  cocycleConditionι (kummerZ F B m) (kummerZ_cocycle F B m)

/-- PROVED (tex 3413–3418). **The Kummer condition maps injectively into the local cochains**, in
every degree. -/
theorem kummerConditionι_injective (i : ℤ) :
    Function.Injective ((kummerConditionι F B m).f i i rfl) :=
  cocycleConditionι_injective _ _ i

/-- Definition (tex 3417–3418). The Kummer function `σ ↦ σ Q − Q` of an arbitrary `m`-th division
point `Q` of `P` (`m • Q = P`). -/
def kummerFunOf {P : B.toAffine.Point} {Q : PtAlg F B} (hQ : m • Q = basePt F B P)
    (σ : Field.absoluteGaloisGroup F) : TorsAlg F B m :=
  ⟨σ • Q - Q, by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, smul_comm, hQ, smul_basePt, sub_self]⟩

/-- Definition (tex 3417–3418). The Kummer cocycle `σ ↦ σ Q − Q` of an arbitrary `m`-th division
point `Q` of `P`, a continuous `1`-cochain. -/
def kummerCocycleOf {P : B.toAffine.Point} {Q : PtAlg F B} (hQ : m • Q = basePt F B P) :
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 :=
  ⟨(fun g => kummerFunOf F B m hQ (g 0) :
      (Fin 1 → Field.absoluteGaloisGroup F) → TorsAlg F B m),
    (Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _).comp
      (continuous_apply 0)⟩

/-- PROVED (tex 3417–3418). Two choices of division points give Kummer cocycles differing by a
continuous coboundary. -/
theorem kummerCocycleOf_sub_mem {P : B.toAffine.Point} {Q : PtAlg F B}
    (hQ : m • Q = basePt F B P) :
    kummerCocycleOf F B m hQ - kummerCocycle F B m P ∈
      contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  have hT : Q - divPt F B m P ∈ AddSubgroup.torsionBy (PtAlg F B) (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, hQ, nsmul_divPt, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (⟨_, hT⟩ : TorsAlg F B m), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) _ g).trans ?_
  change _ = kummerFunOf F B m hQ (g 0) - kummerFun F B m P (g 0)
  apply Subtype.ext
  change g 0 • (Q - divPt F B m P) - (Q - divPt F B m P) =
    (g 0 • Q - Q) - (g 0 • divPt F B m P - divPt F B m P)
  rw [smul_sub]
  abel

/-- PROVED (tex 3417–3418). **The Kummer condition does not depend on the chosen division
points**: the Kummer cocycle of any `m`-th division point of any `P ∈ B(F)` lies in
`U¹ = kummerZ ⊔ B¹_cont`. -/
theorem kummerCocycleOf_mem_sup {P : B.toAffine.Point} {Q : PtAlg F B}
    (hQ : m • Q = basePt F B P) :
    kummerCocycleOf F B m hQ ∈
      kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) := by
  have h := Submodule.add_mem_sup (Submodule.subset_span ⟨P, rfl⟩ : kummerCocycle F B m P ∈
    kummerZ F B m) (kummerCocycleOf_sub_mem F B m hQ)
  rwa [add_sub_cancel] at h

/-! ### First cohomology of the Kummer condition: `B(F) ⧸ m B(F)` -/

/-- PROVED (tex 3417–3418). The Kummer cocycle `κ_P` lies in `U¹ = kummerZ ⊔ B¹`. -/
theorem kummerCocycle_mem_sup (P : B.toAffine.Point) :
    kummerCocycle F B m P ∈
      kummerZ F B m ⊔ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨P, rfl⟩)

/-- Definition (tex 3417–3418). **The Kummer map into the first cohomology of the condition**,
`B(F) → U¹ ⧸ B¹`, `P ↦ [κ_P]`; additive by `kummerCocycle_add`. -/
def kummerH1Hom :
    B.toAffine.Point →+
      ((kummerCondition F B m).X 1 ⧸ condB1 (kummerZ F B m) (kummerZ_cocycle F B m)) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (ofCondOne (kummerZ F B m)
      (kummerZ_cocycle F B m) ⟨kummerCocycle F B m P, kummerCocycle_mem_sup F B m P⟩))
    fun P P' => by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      change kummerCocycle F B m (P + P') -
        (kummerCocycle F B m P + kummerCocycle F B m P') ∈
          contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)
      rw [← sub_sub]
      exact kummerCocycle_add F B m P P'

/-- PROVED (tex 3417–3418). The value of `kummerH1Hom`. -/
theorem kummerH1Hom_apply (P : B.toAffine.Point) :
    kummerH1Hom F B m P = Submodule.Quotient.mk (ofCondOne (kummerZ F B m)
      (kummerZ_cocycle F B m) ⟨kummerCocycle F B m P, kummerCocycle_mem_sup F B m P⟩) :=
  rfl

/-- PROVED (tex 3417–3418). **The kernel of the Kummer map is `m B(F)`** (pointwise form). -/
theorem kummerH1Hom_eq_zero_iff (P : B.toAffine.Point) :
    kummerH1Hom F B m P = 0 ↔ ∃ P' : B.toAffine.Point, m • P' = P := by
  rw [← kummerCocycle_mem_coboundaries_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- PROVED (tex 3417–3418). **The kernel of the Kummer map is `m B(F)`.** -/
theorem kummerH1Hom_ker :
    (kummerH1Hom F B m).ker = (nsmulAddMonoidHom (α := B.toAffine.Point) m).range := by
  ext P
  rw [AddMonoidHom.mem_ker, kummerH1Hom_eq_zero_iff, AddMonoidHom.mem_range]
  rfl

/-- PROVED (tex 3417–3418: the Kummer image fills the condition). **The Kummer map onto the first
cohomology of the condition is surjective.** -/
theorem kummerH1Hom_surjective : Function.Surjective (kummerH1Hom F B m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.1 (condOne (kummerZ F B m)
    (kummerZ_cocycle F B m) x).2
  obtain ⟨P, hP⟩ := exists_kummerToQuot_eq F B m z hz
  refine ⟨P, ?_⟩
  rw [kummerH1Hom_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change kummerCocycle F B m P - (condOne (kummerZ F B m) (kummerZ_cocycle F B m) x :
    contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1) ∈
      contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)
  rw [← hzb, ← sub_sub]
  exact sub_mem ((Submodule.Quotient.eq _).1 hP) hb

/-- PROVED (tex 3415–3417: "`B(F)/2^aB(F)` in degree one", for any `m`). **`B(F) ⧸ m B(F)` is
the first cohomology `U¹ ⧸ B¹` of the Kummer condition**, via `P ↦ [κ_P]`. -/
def kummerH1Equiv :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) ≃+
      ((kummerCondition F B m).X 1 ⧸ condB1 (kummerZ F B m) (kummerZ_cocycle F B m)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (kummerH1Hom_ker F B m).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (kummerH1Hom_surjective F B m))

/-- PROVED (tex 3417–3418). `kummerH1Equiv` sends the class of `P` to the class of `κ_P`. -/
theorem kummerH1Equiv_mk (P : B.toAffine.Point) :
    kummerH1Equiv F B m (QuotientAddGroup.mk P) = kummerH1Hom F B m P :=
  rfl

/-- PROVED (tex 3415–3417). **`H¹` of the Kummer condition is `B(F) ⧸ m B(F)`**: an isomorphism
between `B(F) ⧸ m B(F)` and Mathlib's homology `H¹((kummerCondition F B m).toCC)`. -/
def kummerH1AddEquiv :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) ≃+
      ((kummerCondition F B m).toCC.homology 1) :=
  (kummerH1Equiv F B m).trans
    (cocycleConditionH1Iso (kummerZ F B m) (kummerZ_cocycle F B m)).toLinearEquiv.toAddEquiv.symm

/-- PROVED (tex 3417–3418: the Kummer image inside the local cohomology). The first cohomology of
the Kummer condition injects into the first cohomology of the genuine local complex
`C^•_cont(G_F, B(F̄)[m])` (instance of `cocycleCondition_mono_homologyMap_one`). -/
theorem kummerCondition_mono_homologyMap_one :
    Mono (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionι F B m)) 1) :=
  cocycleCondition_mono_homologyMap_one (kummerZ F B m) (kummerZ_cocycle F B m)

/-- Definition (tex 3417–3418, 3442–3445: the Kummer map). **The Kummer map**
`B(F) ⧸ m B(F) → H¹(C^•_cont(G_F, B(F̄)[m]))` into the first cohomology of the genuine local
complex, `[P] ↦ [κ_P]`. -/
def kummerMapH1 :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) →+
      ((natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.homology 1) :=
  (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionι F B m)) 1).hom.toAddMonoidHom.comp
    (kummerH1AddEquiv F B m).toAddMonoidHom

/-- PROVED (tex 3417–3418). **The Kummer map `B(F) ⧸ m B(F) → H¹(G_F, B(F̄)[m])` is injective**
(genuine continuous cohomology). -/
theorem kummerMapH1_injective : Function.Injective (kummerMapH1 F B m) :=
  ((ModuleCat.mono_iff_injective _).1 (kummerCondition_mono_homologyMap_one F B m)).comp
    (kummerH1AddEquiv F B m).injective

/-- PROVED (tex 3417–3418, 3442–3445). **The Kummer map sends `[P]` to the cohomology class of the
Kummer cocycle**: `kummerMapH1 [P] = π(c)` for the `1`-cycle `c` of the genuine local complex
`C^•_cont(G_F, B(F̄)[m])` with underlying cochain `κ_P`. -/
theorem kummerMapH1_mk (P : B.toAffine.Point) :
    ∃ c : (natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.cycles 1,
      ((natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.iCycles 1).hom
          c = kummerCocycle F B m P ∧
      kummerMapH1 F B m (QuotientAddGroup.mk P) =
        ((natCx (contCochains ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))).toCC.homologyπ
          1).hom c :=
  cocycleCondition_homologyMap_inv_mk (kummerZ F B m) (kummerZ_cocycle F B m)
    (ofCondOne (kummerZ F B m) (kummerZ_cocycle F B m)
      ⟨kummerCocycle F B m P, kummerCocycle_mem_sup F B m P⟩)

/-! ### Zeroth cohomology of the Kummer condition: `B(F)[m]` -/

/-- PROVED (tex 3415–3417, degree zero). The Kummer condition has the `H⁰` of the genuine local
complex `C^•_cont(G_F, B(F̄)[m])` (instance of `cocycleCondition_isIso_homologyMap_zero`). -/
theorem kummerCondition_isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionι F B m)) 0) :=
  cocycleCondition_isIso_homologyMap_zero (kummerZ F B m) (kummerZ_cocycle F B m)

/-- PROVED (tex 3415–3417). The constant `0`-cochain at a point of `B(F)[m]` is a `0`-cocycle of
the Kummer condition. -/
theorem kummerH0_mem (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    ofCondZero (kummerZ F B m) (kummerZ_cocycle F B m) (constCochain (baseTors F B m T)) ∈
      LinearMap.ker ((kummerCondition F B m).toCC.sc' (-1) 0 1).g.hom := by
  change ((kummerCondition F B m).toCC.d 0 1).hom (ofCondZero (kummerZ F B m)
    (kummerZ_cocycle F B m) (constCochain (baseTors F B m T))) = 0
  refine (cocycleCondition_toCC_d₀_eq_zero_iff (kummerZ F B m) (kummerZ_cocycle F B m) _).2 ?_
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ) (G := Field.absoluteGaloisGroup F)
    (M := TorsAlg F B m) _ g).trans ?_
  rw [smul_baseTors, sub_self]
  rfl

/-- Definition (tex 3415–3417). The map `B(F)[m] → H⁰(U)` (the `0`-cocycles of the Kummer
condition), `T ↦` the constant `0`-cochain at `T`. -/
def kummerH0Hom : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) →+
    ↥(LinearMap.ker ((kummerCondition F B m).toCC.sc' (-1) 0 1).g.hom) :=
  AddMonoidHom.mk' (fun T => ⟨ofCondZero (kummerZ F B m) (kummerZ_cocycle F B m)
      (constCochain (baseTors F B m T)), kummerH0_mem F B m T⟩)
    fun T T' => by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact map_add (baseTors F B m) T T'

/-- PROVED (tex 3415–3417). The value of `kummerH0Hom` at the point of `G⁰`. -/
theorem kummerH0Hom_apply (T : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :
    cfun (condZero (kummerZ F B m) (kummerZ_cocycle F B m) (kummerH0Hom F B m T).1 :
      contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 0) default = baseTors F B m T :=
  rfl

/-- PROVED (tex 3415–3417). `kummerH0Hom` is injective. -/
theorem kummerH0Hom_injective : Function.Injective (kummerH0Hom F B m) := by
  intro T T' h
  apply baseTors_injective (F := F) (B := B) m
  rw [← kummerH0Hom_apply F B m T, ← kummerH0Hom_apply F B m T', h]

/-- PROVED (tex 3415–3417: the degree-zero torsion; Galois descent). `kummerH0Hom` is surjective:
every `0`-cocycle is the constant cochain at a `G_F`-invariant point of `B(F̄)[m]`, i.e. at a
point of `B(F)[m]`. -/
theorem kummerH0Hom_surjective : Function.Surjective (kummerH0Hom F B m) := by
  rintro ⟨x, hx⟩
  have hx' : ((kummerCondition F B m).toCC.d 0 1).hom x = 0 := hx
  have hc := (cocycleCondition_toCC_d₀_eq_zero_iff (kummerZ F B m) (kummerZ_cocycle F B m) x).1 hx'
  set c : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 0 :=
    (condZero (kummerZ F B m) (kummerZ_cocycle F B m) x).1 with hcdef
  have hfix : ∀ σ : Field.absoluteGaloisGroup F,
      σ • (cfun c default : TorsAlg F B m) = cfun c default := by
    intro σ
    have h1 := (contD_zero_apply (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B m) c
      (fun _ => σ)).symm.trans (congrArg (fun f => cfun f (fun _ => σ)) hc)
    exact sub_eq_zero.1 h1
  obtain ⟨T, hT⟩ := exists_baseTors_of_fixed hfix
  refine ⟨T, Subtype.ext ?_⟩
  change ofCondZero (kummerZ F B m) (kummerZ_cocycle F B m) (constCochain (baseTors F B m T)) = x
  rw [hT, ← eq_constCochain c]
  rfl

/-- PROVED (tex 3415–3417). `B(F)[m]` is the group of `0`-cocycles of the Kummer condition. -/
def kummerH0Equiv : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) ≃+
    ↥(LinearMap.ker ((kummerCondition F B m).toCC.sc' (-1) 0 1).g.hom) :=
  AddEquiv.ofBijective (kummerH0Hom F B m)
    ⟨kummerH0Hom_injective F B m, kummerH0Hom_surjective F B m⟩

/-- PROVED (tex 3415–3417: "`B(F)[2^a]` in degree zero", for any `m`). **`H⁰` of the Kummer
condition is `B(F)[m]`**: an isomorphism between `B(F)[m]` and Mathlib's homology
`H⁰((kummerCondition F B m).toCC)`. -/
def kummerH0AddEquiv : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) ≃+
    ((kummerCondition F B m).toCC.homology 0) :=
  (kummerH0Equiv F B m).trans
    (cocycleConditionH0Iso (kummerZ F B m) (kummerZ_cocycle F B m)).toLinearEquiv.toAddEquiv.symm

end KummerCocycle

/-! ### Coefficient extension -/

section CoefficientExtension

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (ι : TorsAlg F B m →+ M)

/-- Definition (tex 3430–3438: "derived coefficient extension defines the scalar `A_i`
condition"). The extended Kummer cochain `g ↦ a • ι(κ_P(g))` in `C¹_cont(G_F, M)`, for a scalar
`a : k` and an additive map `ι : B(F̄)[m] → M` into a discrete `k[G_F]`-module. -/
def kummerCocycleIn (a : k) (P : B.toAffine.Point) :
    contCochain k (Field.absoluteGaloisGroup F) M 1 :=
  ⟨(fun g => a • ι (kummerFun F B m P (g 0)) : (Fin 1 → Field.absoluteGaloisGroup F) → M),
    (continuous_of_discreteTopology (f := fun t : TorsAlg F B m => a • ι t)).comp
      ((continuous_kummerFun F B m P).comp (continuous_apply 0))⟩

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- PROVED (tex 3430–3438). The value of the extended Kummer cochain. -/
@[simp]
theorem cfun_kummerCocycleIn (a : k) (P : B.toAffine.Point)
    (g : Fin 1 → Field.absoluteGaloisGroup F) :
    cfun (kummerCocycleIn ι a P) g = a • ι (kummerFun F B m P (g 0)) :=
  rfl

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- PROVED (tex 3430–3438). `g ↦ a • ι(κ_P(g))` is `a` times `g ↦ ι(κ_P(g))`. -/
theorem kummerCocycleIn_eq_smul (a : k) (P : B.toAffine.Point) :
    kummerCocycleIn ι a P = a • kummerCocycleIn ι 1 P := by
  apply Subtype.ext
  funext g
  change a • ι (kummerFun F B m P (g 0)) = a • (1 : k) • ι (kummerFun F B m P (g 0))
  rw [one_smul]

/-- PROVED (tex 3430–3438). **The extended Kummer cochains are cocycles**, for `ι` equivariant
(`ι (σ • t) = σ • ι t`). -/
theorem kummerCocycleIn_isCocycle
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t)
    (a : k) (P : B.toAffine.Point) :
    contD k (Field.absoluteGaloisGroup F) M 1 (kummerCocycleIn ι a P) = 0 := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := Field.absoluteGaloisGroup F) (M := M) 1
    (kummerCocycleIn ι a P) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • (a • ι (kummerFun F B m P (g 1))) + ((-1 : k) ^ ((0 : ℕ) + 1) •
    (a • ι (kummerFun F B m P (g 0 * g 1))) + (-1 : k) ^ ((1 : ℕ) + 1) •
      (a • ι (kummerFun F B m P (g 0)))) = 0
  rw [kummerFun_mul, map_add, hι, smul_add, smul_comm (g 0) a]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

variable (k) in
/-- Definition (tex 3430–3438). **The extended Kummer submodule** `kummerZ' k ι ⊆ C¹_cont(G_F, M)`:
the `k`-span of the cocycles `g ↦ a • ι(κ_P(g))`, `a : k`, `P ∈ B(F)`. -/
abbrev kummerZ' : Submodule k (contCochain k (Field.absoluteGaloisGroup F) M 1) :=
  cochainSpan (Set.range fun p : k × B.toAffine.Point => kummerCocycleIn ι p.1 p.2)

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- PROVED (tex 3430–3438). The extended Kummer cochains lie in `kummerZ' k ι`. -/
theorem kummerCocycleIn_mem (a : k) (P : B.toAffine.Point) :
    kummerCocycleIn ι a P ∈ kummerZ' k ι :=
  Submodule.subset_span ⟨(a, P), rfl⟩

variable (k) in
/-- PROVED (tex 3430–3438). The extended Kummer submodule consists of cocycles. -/
theorem kummerZ'_cocycle
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    ∀ z ∈ kummerZ' k ι, contD k (Field.absoluteGaloisGroup F) M 1 z = 0 :=
  cochainSpan_cocycle _ (by
    rintro _ ⟨p, rfl⟩
    exact kummerCocycleIn_isCocycle ι hι p.1 p.2)

variable (k) in
/-- Definition (tex 3430–3438; DEPARTURE of form as in `CocycleCondition.lean`). **The Kummer
condition with coefficients extended along `ι`**:
`[C⁰_cont(G_F, M) --d⁰--> kummerZ' k ι ⊔ B¹_cont(G_F, M)]`, a relation-indexed complex `GCx k`. -/
abbrev kummerConditionIn
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) : GCx k :=
  cocycleCondition (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

variable (k) in
/-- Definition (tex 3430–3438). The inclusion of the extended Kummer condition into the genuine
local complex `natCx (contCochains k G_F M)`. -/
abbrev kummerConditionInι
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    GHom (kummerConditionIn k ι hι) (natCx (contCochains k (Field.absoluteGaloisGroup F) M)) :=
  cocycleConditionι (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

variable (k) in
/-- PROVED (tex 3430–3438). **The extended Kummer condition maps injectively into the local
cochains**, in every degree. -/
theorem kummerConditionInι_injective
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) (i : ℤ) :
    Function.Injective ((kummerConditionInι k ι hι).f i i rfl) :=
  cocycleConditionι_injective (kummerZ' k ι) (kummerZ'_cocycle k ι hι) i

variable (k) in
/-- PROVED (tex 3430–3438). `H¹` of the extended Kummer condition is `(kummerZ' k ι ⊔ B¹) ⧸ B¹`
(an instance of `cocycleConditionH1Iso`). -/
def kummerConditionInH1Iso
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    (kummerConditionIn k ι hι).toCC.homology 1 ≅
      ModuleCat.of k ((kummerConditionIn k ι hι).X 1 ⧸
        condB1 (kummerZ' k ι) (kummerZ'_cocycle k ι hι)) :=
  cocycleConditionH1Iso (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

variable (k) in
/-- PROVED (tex 3430–3438). The extended Kummer condition has the `H⁰` of the full local complex
(an instance of `cocycleCondition_isIso_homologyMap_zero`). -/
theorem kummerConditionIn_isIso_homologyMap_zero
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t) :
    IsIso (HomologicalComplex.homologyMap (GHom.toCC (kummerConditionInι k ι hι)) 0) :=
  cocycleCondition_isIso_homologyMap_zero (kummerZ' k ι) (kummerZ'_cocycle k ι hι)

end CoefficientExtension

/-! ### Genuine local conditions -/

/-- Definition (tex 3413–3468 with (4.3) at tex 3455–3463: "These are the local maps used in the
Selmer-cone duality above"). **Kummer local conditions** in the format `LocalConditions` of the
genuine Selmer data (`SelmerComplex/Selmer.lean`): for local fields `F_v` of characteristic zero
with elliptic curves `B_v`, the local groups `G_{F_v}` with continuous homomorphisms
`loc_v : G_{F_v} → G_S`, a discrete `k[G_S]`-module `M` and `G_{F_v}`-equivariant additive maps
`ι_v : B_v(F̄_v)[m] → M` (`M` with the action through `loc_v`, `ResMod (loc v) M`), the local
conditions are `U_v = kummerConditionIn k ι_v _` with their inclusions into the genuine local
complexes `C^•_cont(G_{F_v}, M)`. -/
def kummerLocalConditions {GS : Type} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
    {V : Type} (Fv : V → Type) [∀ v, Field (Fv v)] [∀ v, CharZero (Fv v)]
    [∀ v, DecidableEq (Fv v)] (Bv : ∀ v, WeierstrassCurve (Fv v)) [∀ v, (Bv v).IsElliptic]
    (m : ℕ) [NeZero m] (loc : ∀ v, Field.absoluteGaloisGroup (Fv v) →ₜ* GS)
    (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M]
    [SMulCommClass GS k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M]
    (ι : ∀ v, TorsAlg (Fv v) (Bv v) m →+ ResMod (loc v) M)
    (hι : ∀ v (σ : Field.absoluteGaloisGroup (Fv v)) (t : TorsAlg (Fv v) (Bv v) m),
      ι v (σ • t) = σ • ι v t) :
    LocalConditions k GS (fun v => Field.absoluteGaloisGroup (Fv v)) loc M :=
  ⟨fun v => kummerConditionIn k (ι v) (hι v), fun v => kummerConditionInι k (ι v) (hι v)⟩

/-- PROVED (tex 3413–3468). The local condition complexes of `kummerLocalConditions` are the
extended Kummer conditions. -/
theorem kummerLocalConditions_U {GS : Type} [Group GS] [TopologicalSpace GS]
    [IsTopologicalGroup GS] {V : Type} (Fv : V → Type) [∀ v, Field (Fv v)] [∀ v, CharZero (Fv v)]
    [∀ v, DecidableEq (Fv v)] (Bv : ∀ v, WeierstrassCurve (Fv v)) [∀ v, (Bv v).IsElliptic]
    (m : ℕ) [NeZero m] (loc : ∀ v, Field.absoluteGaloisGroup (Fv v) →ₜ* GS)
    (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M]
    [SMulCommClass GS k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M]
    (ι : ∀ v, TorsAlg (Fv v) (Bv v) m →+ ResMod (loc v) M)
    (hι : ∀ v (σ : Field.absoluteGaloisGroup (Fv v)) (t : TorsAlg (Fv v) (Bv v) m),
      ι v (σ • t) = σ • ι v t) (v : V) :
    (kummerLocalConditions Fv Bv m loc k M ι hι).U v = kummerConditionIn k (ι v) (hι v) :=
  rfl

/-- Definition (tex 3413–3468 with (4.3) at tex 3455–3463). **Kummer local conditions for the
genuine Galois Selmer data** of a number field `K` and a set `S` of finite primes: at `v ∈ S` the
local field `K_v = v.adicCompletion K` (characteristic zero), an elliptic curve `B_v` over `K_v`,
and a `G_{K_v}`-equivariant additive map `ι_v : B_v(K̄_v)[m] → M` into a discrete
`k[G_{K,S}]`-module `M` (with `G_{K_v}` acting through the localization `locMap K S v`); this
specializes `kummerLocalConditions` to lane RC26's `Gloc K v = G_{K_v}`. -/
def kummerGaloisLocalConditions (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m] (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) :
    GaloisLocalConditions K S k M :=
  kummerLocalConditions (fun v : Places K S => v.1.adicCompletion K) B m
    (fun v => locMap K S v.1) k M ι hι

/-- PROVED (tex 3413–3468). The Kummer local conditions of the genuine Galois Selmer data are
injective in every degree at every place. -/
theorem kummerGaloisLocalConditions_injective (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m] (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) (v : Places K S) (n : ℤ) :
    Function.Injective (((kummerGaloisLocalConditions K S B m k M ι hι).i v).f n n rfl) :=
  kummerConditionInι_injective k (ι v) (hι v) n

/-- PROVED (tex 3455–3463, (4.3)). The genuine Selmer data with the Kummer local conditions
(`galoisSelData` of lane RC26); its Selmer complex is `selCx` of these data. -/
example (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m] (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) : SelData k :=
  galoisSelData K S k M (kummerGaloisLocalConditions K S B m k M ι hι)

/-- PROVED (tex 3430–3438). For the identity coefficients (`k = ℤ`, `M = B(F̄)[m]`, `ι = id`,
`a = 1`) the extended Kummer cochain is the Kummer cocycle. -/
theorem kummerCocycleIn_id {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] (P : B.toAffine.Point) :
    kummerCocycleIn (AddMonoidHom.id (TorsAlg F B m)) (1 : ℤ) P = kummerCocycle F B m P := by
  apply Subtype.ext
  funext g
  exact one_smul ℤ (kummerFun F B m P (g 0))

/-- PROVED (tex 3430–3438). For the identity coefficients the extended Kummer submodule is the
Kummer submodule. -/
theorem kummerZ'_id {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] :
    kummerZ' ℤ (AddMonoidHom.id (TorsAlg F B m)) = kummerZ F B m := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, P⟩, rfl⟩
    change kummerCocycleIn (AddMonoidHom.id (TorsAlg F B m)) a P ∈ kummerZ F B m
    rw [kummerCocycleIn_eq_smul, kummerCocycleIn_id]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨P, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨P, rfl⟩
    rw [← kummerCocycleIn_id]
    exact kummerCocycleIn_mem _ 1 P

/-- PROVED (tex 3430–3438). For the identity coefficients the extended Kummer condition is the
Kummer condition. -/
theorem kummerConditionIn_id {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] :
    kummerConditionIn ℤ (AddMonoidHom.id (TorsAlg F B m)) (fun _ _ => rfl) =
      kummerCondition F B m := by
  unfold kummerConditionIn kummerCondition
  congr 1
  exact kummerZ'_id

/-! ### Non-vacuity: `y² = x³ − x` over `ℚ`, `m = 2` -/

section Example

/-- Definition (non-vacuity of the hypotheses of tex 3413–3468). The elliptic curve
`y² = x³ − x` over `ℚ`. -/
def curveY2X3mX : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `y² = x³ − x` is elliptic
(`Δ = 64`). -/
instance curveY2X3mX.instIsElliptic : curveY2X3mX.IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [curveY2X3mX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `(0, 0)` is a nonsingular point of
`y² = x³ − x`. -/
theorem curveY2X3mX_nonsingular : curveY2X3mX.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  norm_num [curveY2X3mX, WeierstrassCurve.Affine.equation_iff']

/-- Definition (non-vacuity of the hypotheses of tex 3413–3468). The rational `2`-torsion point
`(0, 0)` of `y² = x³ − x`. -/
def curveY2X3mXPt : AddSubgroup.torsionBy curveY2X3mX.toAffine.Point ((2 : ℕ) : ℤ) :=
  ⟨.some 0 0 curveY2X3mX_nonsingular, by
    rw [AddSubgroup.torsionBy.nsmul_iff, two_nsmul]
    exact Affine.Point.add_self_of_Y_eq (by
      norm_num [curveY2X3mX, WeierstrassCurve.Affine.negY])⟩

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). The Kummer condition of
`y² = x³ − x` over `ℚ` with `m = 2` (all hypotheses `CharZero ℚ`, `IsElliptic`, `NeZero 2` are
satisfied). -/
example : GCx ℤ := kummerCondition ℚ curveY2X3mX 2

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). Its injective map into
`C^•_cont(G_ℚ, B(ℚ̄)[2])`. -/
example : GHom (kummerCondition ℚ curveY2X3mX 2)
    (natCx (contCochains ℤ (Field.absoluteGaloisGroup ℚ) (TorsAlg ℚ curveY2X3mX 2))) :=
  kummerConditionι ℚ curveY2X3mX 2

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `H¹ ≅ B(ℚ)/2B(ℚ)` for
`y² = x³ − x`. -/
example : (curveY2X3mX.toAffine.Point ⧸
      (nsmulAddMonoidHom (α := curveY2X3mX.toAffine.Point) 2).range) ≃+
    ((kummerCondition ℚ curveY2X3mX 2).toCC.homology 1) :=
  kummerH1AddEquiv ℚ curveY2X3mX 2

/-- PROVED (non-vacuity of the hypotheses of tex 3413–3468). `H⁰` of the Kummer condition of
`y² = x³ − x`, `m = 2`, is nonzero: it contains the class of the rational `2`-torsion point
`(0, 0)`. -/
theorem kummerCondition_curveY2X3mX_H0_nontrivial :
    Nontrivial ((kummerCondition ℚ curveY2X3mX 2).toCC.homology 0) := by
  refine ⟨⟨kummerH0AddEquiv ℚ curveY2X3mX 2 curveY2X3mXPt, 0, fun h => ?_⟩⟩
  have h' := (kummerH0AddEquiv ℚ curveY2X3mX 2).injective
    (h.trans (map_zero (kummerH0AddEquiv ℚ curveY2X3mX 2)).symm)
  exact Affine.Point.some_ne_zero curveY2X3mX_nonsingular (congrArg Subtype.val h')

/-- PROVED (non-vacuity of the coefficient-extension hypotheses, tex 3430–3438). The identity
coefficients `ι = id : B(ℚ̄)[2] → B(ℚ̄)[2]` (over `k = ℤ`) satisfy the equivariance hypothesis,
giving an extended Kummer condition. -/
example : GCx ℤ :=
  kummerConditionIn ℤ (AddMonoidHom.id (TorsAlg ℚ curveY2X3mX 2)) (fun _ _ => rfl)

end Example

end ZInQ.Manuscript.RC.CoefModules
