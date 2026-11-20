import ZInQKernel.Contrib.RC53Assist.StagePrimes.Arithmetic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Detection of prescribed cohomology classes

The characteristic-zero kernel argument uses a central scalar, not residual
irreducibility. A cocycle vanishing on the kernel is a coboundary by the scalar
identity in lines 4768–4774 of the manuscript. The linear span of the action
then turns independence in first cohomology into a full joint evaluation span.
Polarization selects an actual kernel element, rather than a linear combination
of kernel elements. The square of a conjugation coset gives the finite evaluation
used in lines 4788–4830 and in equation (5.5b), lines 5087–5114.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Detection

open Filter Topology Module
open ZInQ.Contrib.RC53Assist.InnerLimitArith

section ScalarRestriction

variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]

/-- The linear action of a group element on the coefficient module. -/
def linearAction (k M : Type) [Field k] [AddCommGroup M] [Module k M]
    {G : Type} [Group G] [DistribMulAction G M] [SMulCommClass G k M]
    (g : G) : M →ₗ[k] M where
  toFun m := g • m
  map_add' := smul_add g
  map_smul' a m := smul_comm g a m

/-- The inverse identity for an additive one-cocycle. -/
theorem cocycle_inverse {c : G → M} (hc : groupCohomology.IsCocycle₁ c) (g : G) :
    g • c g⁻¹ + c g = 0 := by
  rw [← hc g g⁻¹, mul_inv_cancel]
  exact groupCohomology.map_one_of_isCocycle₁ hc

/-- Restriction to a subgroup acting trivially is an additive homomorphism. -/
theorem cocycle_kernel_mul {c : G → M} (hc : groupCohomology.IsCocycle₁ c)
    (H : Subgroup G) (htriv : ∀ h ∈ H, ∀ m : M, h • m = m) (g h : H) :
    c ((g : G) * h) = c g + c h := by
  rw [hc, htriv g g.property, add_comm]

/-- Equivariance of kernel restriction is a consequence of the cocycle identity. -/
theorem cocycle_kernel_conjugate {c : G → M} (hc : groupCohomology.IsCocycle₁ c)
    (H : Subgroup G) (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (g : G) {h : G} (hh : h ∈ H) : c (g * h * g⁻¹) = g • c h := by
  rw [hc, hc, mul_smul, htriv h hh]
  have hinv := cocycle_inverse hc g
  calc
    g • c g⁻¹ + (g • c h + c g) = g • c h + (g • c g⁻¹ + c g) := by abel
    _ = g • c h := by rw [hinv, add_zero]

/-- The scalar identity proves the vanishing of first cohomology of the image.
The centrality needed here is only centrality modulo the kernel. -/
theorem coboundary_of_scalar_commutators {c : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (H : Subgroup G)
    (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H)
    (hcH : ∀ h ∈ H, c h = 0) : groupCohomology.IsCoboundary₁ c := by
  have hid (g : G) : (a - 1) • c g = g • c z - c z := by
    let d := z * g * z⁻¹ * g⁻¹
    have hd : d ∈ H := hcomm g
    have hgroup : d * (g * z) = z * g := by simp [d, mul_assoc]
    have heq : c (z * g) = c (g * z) := by
      rw [← hgroup, hc, htriv d hd, hcH d hd, add_zero]
    rw [hc, hc, hz] at heq
    rw [sub_smul, one_smul]
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using heq)
  refine ⟨(a - 1)⁻¹ • c z, fun g => ?_⟩
  rw [smul_comm g (a - 1)⁻¹, ← smul_sub, ← hid g, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr ha), one_smul]

/-- Every prescribed nonzero cohomology class has a nonzero value on the kernel. -/
theorem exists_nonzero_kernel_value {c : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (H : Subgroup G)
    (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H)
    (hnc : ¬ groupCohomology.IsCoboundary₁ c) : ∃ h : H, c h ≠ 0 := by
  by_contra hno
  push Not at hno
  exact hnc (coboundary_of_scalar_commutators hc H htriv z a ha hz hcomm
    (fun h hh => hno ⟨h, hh⟩))

/-- A linear combination of cocycles is a cocycle. -/
theorem cocycle_linear_combination {c d : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (hd : groupCohomology.IsCocycle₁ d) (a b : k) :
    groupCohomology.IsCocycle₁ (fun g => a • c g + b • d g) := by
  intro g h
  change a • c (g * h) + b • d (g * h) = g • (a • c h + b • d h) + (a • c g + b • d g)
  rw [hc, hd]
  simp only [smul_add]
  rw [smul_comm g a, smul_comm g b]
  abel

/-- Diagonal application of an endomorphism to a joint value. -/
def diagonalApply (x : M × M) : (M →ₗ[k] M) →ₗ[k] M × M where
  toFun f := (f x.1, f x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Independence of two classes forces the full joint kernel-evaluation span.
The hypothesis on the action is the finite matrix-span witness of lines 4779–4785;
it implies absolute irreducibility and scalar endomorphisms. -/
theorem joint_span_of_independent {c d : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (hd : groupCohomology.IsCocycle₁ d)
    (H : Subgroup G) [H.Normal]
    (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H)
    (hact : Submodule.span k (Set.range (linearAction k M : G → M →ₗ[k] M)) = ⊤)
    (hind : ∀ r s : k, groupCohomology.IsCoboundary₁ (fun g => r • c g + s • d g) →
      r = 0 ∧ s = 0) :
    Submodule.span k (Set.range (fun h : H => (c h, d h))) = ⊤ := by
  let X := Submodule.span k (Set.range (fun h : H => (c h, d h)))
  have hstable (g : G) : X ≤ X.comap ((linearAction k M g).prodMap (linearAction k M g)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change (g • c h, g • d h) ∈ X
    rw [← cocycle_kernel_conjugate hc H htriv g h.property,
      ← cocycle_kernel_conjugate hd H htriv g h.property]
    exact Submodule.subset_span
      ⟨⟨g * h * g⁻¹, (inferInstance : H.Normal).conj_mem h h.property g⟩, rfl⟩
  have hendo (f : M →ₗ[k] M) {x : M × M} (hx : x ∈ X) : (f x.1, f x.2) ∈ X := by
    have hle : Submodule.span k (Set.range (linearAction k M : G → M →ₗ[k] M)) ≤
        X.comap (diagonalApply x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact hstable g hx
    rw [hact] at hle
    exact hle (Submodule.mem_top : f ∈ ⊤)
  by_contra hX
  obtain ⟨l, hl0, hl⟩ := X.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hX)
  obtain ⟨m, hm⟩ : ∃ m : M, l (m, 0) ≠ 0 ∨ l (0, m) ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hl0
    apply LinearMap.ext
    intro x
    have he : x = (x.1, (0 : M)) + (0, x.2) := by ext <;> simp
    rw [he, map_add, (hno x.1).1, (hno x.2).2, add_zero]
    rfl
  let r := l (m, 0)
  let s := l (0, m)
  have hzero (h : H) : r • c h + s • d h = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro p
    have hv := LinearMap.mem_ker.mp (hl (hendo (p.smulRight m)
      (Submodule.subset_span (Set.mem_range_self h))))
    have he : ((p.smulRight m) (c h), (p.smulRight m) (d h)) =
        p (c h) • (m, (0 : M)) + p (d h) • (0, m) := by
      ext <;> simp
    rw [he, map_add, map_smul, map_smul] at hv
    rw [map_add, map_smul, map_smul]
    simpa only [r, s, smul_eq_mul, mul_comm] using hv
  have hb := coboundary_of_scalar_commutators (cocycle_linear_combination hc hd r s)
    H htriv z a ha hz hcomm (fun h hh => hzero ⟨h, hh⟩)
  obtain ⟨hr, hs⟩ := hind r s hb
  exact hm.elim (fun h => h hr) (fun h => h hs)

end ScalarRestriction

open CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex

section ContinuousClasses

variable {k G M : Type} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- Evaluation presents a continuous cocycle as its ordinary cocycle function. -/
def cocycleFunction (c : Cocycles k G M) : G → M := fun g => evalOne k M g c

/-- The function of a continuous cocycle satisfies the cocycle identity. -/
theorem cocycleFunction_isCocycle (c : Cocycles k G M) :
    groupCohomology.IsCocycle₁ (cocycleFunction c) := evalOne_mul c

/-- Degree-one continuous cochains are determined by their evaluations. -/
theorem oneCochain_ext (c d : (contCochains k G M).X 1)
    (h : ∀ g : G, evalOne k M g c = evalOne k M g d) : c = d := by
  apply Subtype.ext
  funext q
  have hq : q = fun _ : Fin 1 => q 0 := by
    funext j
    fin_cases j
    rfl
  rw [hq]
  exact h (q 0)

/-- The continuous first cohomology quotient map. -/
def cocycleClass : Cocycles k G M →ₗ[k] ContH1 k G M :=
  (LinearMap.range (coboundary k G M)).mkQ

/-- Vanishing in continuous first cohomology is exactly being a principal cocycle. -/
theorem cocycleClass_eq_zero_iff (c : Cocycles k G M) :
    cocycleClass c = 0 ↔ groupCohomology.IsCoboundary₁ (cocycleFunction c) := by
  rw [cocycleClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨evalZero k M a, fun g => ?_⟩
    change g • evalZero k M a - evalZero k M a = evalOne k M g c
    rw [← ha]
    exact (evalOne_d_zero a g).symm
  · rintro ⟨x, hx⟩
    let a : (contCochains k G M).X 0 :=
      (contSubCx k G M).ofSub ⟨(fun _ => x), continuous_const⟩
    have hax : evalZero k M a = x := rfl
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply oneCochain_ext
    intro g
    change evalOne k M g (((contCochains k G M).d 0 1).hom a) = evalOne k M g c
    rw [evalOne_d_zero, hax]
    exact hx g

/-- Linear independence in cohomology gives the scalar relation criterion,
without any localization or determinant hypothesis. -/
theorem independent_cocycle_classes (c d : Cocycles k G M)
    (hind : LinearIndependent k ![cocycleClass c, cocycleClass d]) :
    ∀ r s : k, groupCohomology.IsCoboundary₁
      (fun g => r • cocycleFunction c g + s • cocycleFunction d g) → r = 0 ∧ s = 0 := by
  intro r s hcb
  have hc : cocycleClass (r • c + s • d) = 0 := by
    apply (cocycleClass_eq_zero_iff _).mpr
    convert hcb using 1
    funext g
    change evalOne k M g (r • (c : (contCochains k G M).X 1) +
      s • (d : (contCochains k G M).X 1)) = _
    rw [map_add, map_smul, map_smul]
    rfl
  rw [map_add, map_smul, map_smul] at hc
  have h := (Fintype.linearIndependent_iff.mp hind) ![r, s] (by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hc)
  exact ⟨h 0, h 1⟩

/-- Restriction of continuous cohomology to a trivially acting kernel. -/
def restrictionH1 (H : Subgroup G) (htriv : ∀ h ∈ H, ∀ m : M, h • m = m) :
    ContH1 k G M →ₗ[k] (H → M) :=
  (LinearMap.range (coboundary k G M)).liftQ
    { toFun c h := evalOne k M (h : G) c
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (by
      rintro _ ⟨a, rfl⟩
      apply LinearMap.mem_ker.mpr
      funext h
      change evalOne k M (h : G) (((contCochains k G M).d 0 1).hom a) = 0
      rw [evalOne_d_zero, htriv h h.property, sub_self])

/-- The scalar argument makes the genuine continuous restriction map injective. -/
theorem restrictionH1_injective (H : Subgroup G)
    (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H) :
    Function.Injective (restrictionH1 H htriv : ContH1 k G M → H → M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨c, rfl⟩ := (LinearMap.range (coboundary k G M)).mkQ_surjective x
  have hzero : ∀ h ∈ H, cocycleFunction c h = 0 := by
    intro h hh
    exact congrFun (LinearMap.mem_ker.mp hx) ⟨h, hh⟩
  change cocycleClass c = 0
  apply (cocycleClass_eq_zero_iff c).mpr
  exact coboundary_of_scalar_commutators (cocycleFunction_isCocycle c)
    H htriv z a ha hz hcomm hzero

end ContinuousClasses

section Polarization

variable {k : Type} [Field k]

/-- The determinant quadratic polynomial on a pair of finite coordinates. -/
def detectionDet (x : (Fin 2 → k) × (Fin 2 → k)) : k :=
  (Matrix.of ![x.1, x.2]).det

/-- The polar bilinear form of the determinant polynomial. -/
def detectionPolar : ((Fin 2 → k) × (Fin 2 → k)) →ₗ[k]
    ((Fin 2 → k) × (Fin 2 → k)) →ₗ[k] k :=
  LinearMap.mk₂ k
    (fun x y => x.1 0 * y.2 1 - x.1 1 * y.2 0 +
      y.1 0 * x.2 1 - y.1 1 * x.2 0)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)

/-- Polarization requires no division by two. -/
theorem detectionDet_add (x y : (Fin 2 → k) × (Fin 2 → k)) :
    detectionDet (x + y) = detectionDet x + detectionDet y + detectionPolar x y := by
  simp only [detectionDet, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    detectionPolar, LinearMap.mk₂_apply]
  ring

/-- The determinant polynomial is homogeneous of degree two. -/
theorem detectionDet_smul (r : k) (x : (Fin 2 → k) × (Fin 2 → k)) :
    detectionDet (r • x) = r ^ 2 * detectionDet x := by
  simp only [detectionDet, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring

/-- The polar form is symmetric. -/
theorem detectionPolar_symm (x y : (Fin 2 → k) × (Fin 2 → k)) :
    detectionPolar x y = detectionPolar y x := by
  simp only [detectionPolar, LinearMap.mk₂_apply]
  ring

/-- Vanishing on all actual additive evaluations implies vanishing on their linear span. -/
theorem detectionDet_zero_on_span {H : Type} [Group H]
    (c d : H → Fin 2 → k)
    (hc : ∀ g h, c (g * h) = c g + c h)
    (hd : ∀ g h, d (g * h) = d g + d h)
    (hzero : ∀ h, detectionDet (c h, d h) = 0) :
    ∀ x ∈ Submodule.span k (Set.range (fun h => (c h, d h))), detectionDet x = 0 := by
  let E := fun h => (c h, d h)
  let X := Submodule.span k (Set.range E)
  have hE (g h : H) : E (g * h) = E g + E h := Prod.ext (hc g h) (hd g h)
  have hp (g h : H) : detectionPolar (E g) (E h) = 0 := by
    have he := detectionDet_add (E g) (E h)
    rw [← hE, hzero (g * h), hzero g, hzero h, zero_add, zero_add] at he
    exact he.symm
  have hleft (g : H) : X ≤ LinearMap.ker (detectionPolar (E g)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    exact LinearMap.mem_ker.mpr (hp g h)
  have hboth {x y} (hx : x ∈ X) (hy : y ∈ X) : detectionPolar x y = 0 := by
    have hr : X ≤ LinearMap.ker (detectionPolar x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      apply LinearMap.mem_ker.mpr
      rw [detectionPolar_symm]
      exact LinearMap.mem_ker.mp (hleft g hx)
    exact LinearMap.mem_ker.mp (hr hy)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact hzero h
  | zero => simp [detectionDet, Matrix.det_fin_two]
  | add x y hx hy ihx ihy =>
      rw [detectionDet_add, ihx, ihy, hboth hx hy, add_zero, add_zero]
  | smul r x hx ih => rw [detectionDet_smul, ih, mul_zero]

/-- A full joint span contains a determinant-one pair; polarization therefore
selects one actual group element with a nonzero determinant. -/
theorem exists_detectionDet_ne_zero {H : Type} [Group H]
    (c d : H → Fin 2 → k)
    (hc : ∀ g h, c (g * h) = c g + c h)
    (hd : ∀ g h, d (g * h) = d g + d h)
    (hspan : Submodule.span k (Set.range (fun h => (c h, d h))) = ⊤) :
    ∃ h, (Matrix.of ![c h, d h]).det ≠ 0 := by
  by_contra hno
  push Not at hno
  have he := detectionDet_zero_on_span c d hc hd hno
    ((![1, 0] : Fin 2 → k), (![0, 1] : Fin 2 → k))
    (by rw [hspan]; exact Submodule.mem_top)
  simp [detectionDet, Matrix.det_fin_two] at he

/-- Surjective finite-coordinate projection preserves a full joint span. -/
theorem projected_joint_span {H M : Type} [Group H] [AddCommGroup M] [Module k M]
    (c d : H → M) (p : M →ₗ[k] (Fin 2 → k)) (hp : Function.Surjective p)
    (hspan : Submodule.span k (Set.range (fun h => (c h, d h))) = ⊤) :
    Submodule.span k (Set.range (fun h => (p (c h), p (d h)))) = ⊤ := by
  let f := p.prodMap p
  have he : Set.range (fun h => (p (c h), p (d h))) =
      f '' Set.range (fun h => (c h, d h)) := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨(c h, d h), ⟨h, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, rfl⟩
  rw [he, ← Submodule.map_span, hspan, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  rintro ⟨x, y⟩
  obtain ⟨u, hu⟩ := hp x
  obtain ⟨v, hv⟩ := hp y
  exact ⟨(u, v), Prod.ext hu hv⟩

end Polarization

section PrescribedCoset

variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]

/-- The finite-coordinate map for the square of a conjugation coset. -/
def cosetProjection (p : M →ₗ[k] (Fin 2 → k)) (τ : G) : M →ₗ[k] (Fin 2 → k) :=
  p.comp (LinearMap.id + linearAction k M τ)

/-- The cocycle identity evaluates the square of a conjugation coset on the
kernel. No sign or nonvanishing statement is assumed. -/
theorem cocycle_coset_square {c : G → M} (hc : groupCohomology.IsCocycle₁ c)
    (H : Subgroup G) [H.Normal] (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (τ : G) (hτ : τ * τ = 1) (h : H) :
    c ((τ * h) * (τ * h)) = c h + τ • c h := by
  have hi : τ⁻¹ = τ := by
    calc
      τ⁻¹ = τ⁻¹ * (τ * τ) := by rw [hτ, mul_one]
      _ = τ := by simp
  have he : (τ * h) * (τ * h) = (τ * h * τ⁻¹) * h := by rw [hi]; simp [mul_assoc]
  rw [he, hc, htriv _ ((inferInstance : H.Normal).conj_mem h h.property τ),
    cocycle_kernel_conjugate hc H htriv τ h.property, add_comm]

/-- A prescribed nonzero class spans the coefficient module by kernel values,
using the finite matrix-span witness. -/
theorem single_span_of_nonzero {c : G → M} (hc : groupCohomology.IsCocycle₁ c)
    (H : Subgroup G) [H.Normal] (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H)
    (hact : Submodule.span k (Set.range (linearAction k M : G → M →ₗ[k] M)) = ⊤)
    (hnc : ¬ groupCohomology.IsCoboundary₁ c) :
    Submodule.span k (Set.range (fun h : H => c h)) = ⊤ := by
  let X := Submodule.span k (Set.range (fun h : H => c h))
  have hstable (g : G) : X ≤ X.comap (linearAction k M g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change g • c h ∈ X
    rw [← cocycle_kernel_conjugate hc H htriv g h.property]
    exact Submodule.subset_span
      ⟨⟨g * h * g⁻¹, (inferInstance : H.Normal).conj_mem h h.property g⟩, rfl⟩
  have hendo (f : M →ₗ[k] M) {x : M} (hx : x ∈ X) : f x ∈ X := by
    let e : (M →ₗ[k] M) →ₗ[k] M :=
      { toFun f := f x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span k (Set.range (linearAction k M : G → M →ₗ[k] M)) ≤
        X.comap e := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact hstable g hx
    rw [hact] at hle
    exact hle (Submodule.mem_top : f ∈ ⊤)
  obtain ⟨h, hh⟩ := exists_nonzero_kernel_value hc H htriv z a ha hz hcomm hnc
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hh
  apply top_unique
  intro x _
  have hm := hendo (l.smulRight x) (Submodule.subset_span (Set.mem_range_self h))
  simpa only [LinearMap.smulRight_apply, hl, one_smul] using hm

/-- A nonzero projection cannot vanish on the whole kernel-value span. -/
theorem exists_projected_nonzero {H : Type} [Group H] (c : H → M)
    (hspan : Submodule.span k (Set.range c) = ⊤)
    (p : M →ₗ[k] (Fin 2 → k)) (hp : p ≠ 0) : ∃ h, p (c h) ≠ 0 := by
  by_contra hno
  push Not at hno
  have hle : Submodule.span k (Set.range c) ≤ LinearMap.ker p := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    exact LinearMap.mem_ker.mpr (hno h)
  rw [hspan] at hle
  apply hp
  apply LinearMap.ext
  intro x
  exact LinearMap.mem_ker.mp (hle Submodule.mem_top)

/-- Detection of one prescribed nonzero class at the square of a conjugation
coset. The only projection hypothesis is algebraic surjectivity. -/
theorem exists_prescribed_square_nonzero {c : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (H : Subgroup G) [H.Normal]
    (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H)
    (hact : Submodule.span k (Set.range (linearAction k M : G → M →ₗ[k] M)) = ⊤)
    (hnc : ¬ groupCohomology.IsCoboundary₁ c)
    (p : M →ₗ[k] (Fin 2 → k)) (τ : G) (hτ : τ * τ = 1)
    (hp : Function.Surjective (cosetProjection p τ)) :
    ∃ h : H, p (c ((τ * h) * (τ * h))) ≠ 0 := by
  have hp0 : cosetProjection p τ ≠ 0 := by
    intro hzero
    obtain ⟨m, hm⟩ := hp (![1, 0] : Fin 2 → k)
    rw [hzero, LinearMap.zero_apply] at hm
    have he := congrFun hm 0
    simp at he
  obtain ⟨h, hh⟩ := exists_projected_nonzero (fun h : H => c h)
    (single_span_of_nonzero hc H htriv z a ha hz hcomm hact hnc)
    (cosetProjection p τ) hp0
  refine ⟨h, ?_⟩
  rw [cocycle_coset_square hc H htriv τ hτ h]
  exact hh

/-- Detection of two prescribed independent classes. Restriction, the full
joint span, and polarization are all proved; no determinant condition is an input. -/
theorem exists_prescribed_square_det {c d : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (hd : groupCohomology.IsCocycle₁ d)
    (H : Subgroup G) [H.Normal]
    (htriv : ∀ h ∈ H, ∀ m : M, h • m = m)
    (z : G) (a : k) (ha : a ≠ 1) (hz : ∀ m : M, z • m = a • m)
    (hcomm : ∀ g : G, z * g * z⁻¹ * g⁻¹ ∈ H)
    (hact : Submodule.span k (Set.range (linearAction k M : G → M →ₗ[k] M)) = ⊤)
    (hind : ∀ r s : k, groupCohomology.IsCoboundary₁ (fun g => r • c g + s • d g) →
      r = 0 ∧ s = 0)
    (p : M →ₗ[k] (Fin 2 → k)) (τ : G) (hτ : τ * τ = 1)
    (hp : Function.Surjective (cosetProjection p τ)) :
    ∃ h : H, (Matrix.of ![p (c ((τ * h) * (τ * h))),
      p (d ((τ * h) * (τ * h)))]).det ≠ 0 := by
  let q := cosetProjection p τ
  have hspan := projected_joint_span (fun h : H => c h) (fun h : H => d h) q hp
    (joint_span_of_independent hc hd H htriv z a ha hz hcomm hact hind)
  obtain ⟨h, hh⟩ := exists_detectionDet_ne_zero
    (fun h : H => q (c h)) (fun h : H => q (d h))
    (fun g h => by rw [Subgroup.coe_mul, cocycle_kernel_mul hc H htriv, map_add])
    (fun g h => by rw [Subgroup.coe_mul, cocycle_kernel_mul hd H htriv, map_add]) hspan
  refine ⟨h, ?_⟩
  rw [cocycle_coset_square hc H htriv τ hτ h,
    cocycle_coset_square hd H htriv τ hτ h]
  exact hh

/-- For an induced rank-four coefficient module, the conjugation exchanges
summands. Its finite-coordinate projection is consequently onto. -/
theorem cosetProjection_fst_surjective {G : Type} [Group G]
    [DistribMulAction G ((Fin 2 → k) × (Fin 2 → k))]
    [SMulCommClass G k ((Fin 2 → k) × (Fin 2 → k))]
    (τ : G) (T : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hexchange : ∀ x y, τ • (x, y) = (T y, T x)) :
    Function.Surjective (cosetProjection (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)) τ) := by
  intro x
  refine ⟨(x, 0), ?_⟩
  simp [cosetProjection, linearAction, hexchange]

end PrescribedCoset

open NumberField IsDedekindDomain IntermediateField
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.KummerMaps (tateLevelAct)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.GlueSweep.Tate (torsField torsCoords coordSet)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Contrib.RC53Assist.FrobeniusMatch
open scoped WeierstrassCurve PowerSeries.WithPiTopology

section ArithmeticKernel

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

omit [E.IsElliptic] in
/-- The coordinates of torsion points are stable under rational Galois automorphisms. -/
theorem torsCoords_galois_stable (i : ℕ) (g : GalQ) {x : Qbar} (hx : x ∈ torsCoords E i) :
    g x ∈ torsCoords E i := by
  obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨tateLevelAct E i g P, ?_⟩
  change g x ∈ coordSet (WeierstrassCurve.Affine.Point.map g.toAlgHom (P : (E⁄Qbar).toAffine.Point))
  generalize hP0 : (P : (E⁄Qbar).toAffine.Point) = P0 at hP ⊢
  rcases P0 with _ | ⟨a, b, hab⟩
  · simp [coordSet] at hP
  · simp only [coordSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rw [WeierstrassCurve.Affine.Point.map_some]
    rcases hP with rfl | rfl <;> simp [coordSet]

/-- The finite torsion field is normal. -/
instance torsField_normal (i : ℕ) : Normal ℚ (torsField E i) := by
  apply normal_iff_forall_map_le'.mpr
  intro g
  rw [IntermediateField.map_le_iff_le_comap]
  unfold torsField
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  change g x ∈ IntermediateField.adjoin ℚ (torsCoords E i)
  exact IntermediateField.subset_adjoin ℚ _ (torsCoords_galois_stable E i g hx)

variable {K : Type} [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-- The actual finite derivative kernels are normal. -/
instance derivativeKernel_normal (i : ℕ) : (derivativeKernel S e α E i).Normal := by
  unfold derivativeKernel
  infer_instance

/-- The common arithmetic kernel of rational Galois sequences. This definition
records the exact finite-field constraints; its class-restriction property is
proved only when the common-kernel scalar and coefficient hypotheses hold. -/
def sequenceDerivativeKernel : Subgroup (ℕ → GalQ) :=
  Subgroup.pi Set.univ (fun i => derivativeKernel S e α E i)

instance sequenceDerivativeKernel_normal : (sequenceDerivativeKernel E S e α).Normal := by
  refine ⟨?_⟩
  intro h hh g
  rw [sequenceDerivativeKernel, Subgroup.mem_pi] at hh ⊢
  intro i hi
  change g i * h i * (g i)⁻¹ ∈ derivativeKernel S e α E i
  exact (inferInstance : (derivativeKernel S e α E i).Normal).conj_mem (h i) (hh i hi) (g i)

/-- A common-kernel element supplies a genuine finite-stage kernel representative
at every precision. -/
def sequenceKernelFamily (h : sequenceDerivativeKernel E S e α) :
    ∀ i, derivativeKernel S e α E i := fun i =>
  ⟨h.val i, (Subgroup.mem_pi Set.univ).mp h.property i (Set.mem_univ i)⟩

/-- The exact finite-stage constraints may additionally include specified
ring-class and quadratic fields. Cocycle evaluation fields are kept separately:
they are used to realize values, not required to be fixed by the representative. -/
def arithmeticSequenceKernel (B : ℕ → IntermediateField ℚ Qbar) : Subgroup (ℕ → GalQ) :=
  Subgroup.pi Set.univ (fun i => derivativeKernel S e α E i ⊓ (B i).fixingSubgroup)

instance arithmeticSequenceKernel_normal (B : ℕ → IntermediateField ℚ Qbar)
    [∀ i, Normal ℚ (B i)] : (arithmeticSequenceKernel E S e α B).Normal := by
  refine ⟨?_⟩
  intro h hh g
  rw [arithmeticSequenceKernel, Subgroup.mem_pi] at hh ⊢
  intro i hi
  change g i * h i * (g i)⁻¹ ∈ derivativeKernel S e α E i ⊓ (B i).fixingSubgroup
  exact (inferInstance : (derivativeKernel S e α E i ⊓ (B i).fixingSubgroup).Normal).conj_mem
    (h i) (hh i hi) (g i)

/-- Extraction of the actual finite-stage representatives from the common
kernel with all the specified arithmetic constraints. -/
def arithmeticKernelFamily {B : ℕ → IntermediateField ℚ Qbar}
    (h : arithmeticSequenceKernel E S e α B) : ∀ i, derivativeKernel S e α E i := fun i =>
  ⟨h.val i, ((Subgroup.mem_pi Set.univ).mp h.property i (Set.mem_univ i)).1⟩

/-- The extracted representatives also fix every prescribed kernel field. -/
theorem arithmeticKernelFamily_fixes {B : ℕ → IntermediateField ℚ Qbar}
    (h : arithmeticSequenceKernel E S e α B) (i : ℕ) (x : Qbar) (hx : x ∈ B i) :
    (arithmeticKernelFamily E S e α h i : GalQ) x = x :=
  ((Subgroup.mem_pi Set.univ).mp h.property i (Set.mem_univ i)).2 ⟨x, hx⟩

end ArithmeticKernel

open ZInQ.Manuscript.RC.Limits hiding Lambda evalOne evalZero evalTwo
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs)

section ArithmeticEvaluation

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
  {α : GKS K S →* Lambdaˣ} [IsContChar α]

/-- Conjugating a retained stage cocycle at a trivially acting element transports
its value by the conjugator, at the same coefficient precision. -/
theorem stageCocycle_conjugate_sub {i : ℕ}
    {c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1}
    (hc : IsStageCocycle W α i c) (g s : GKS K S)
    (hs : ∀ x : TLam K S W α, s • x - x ∈ tlamNbhd K S W α i) :
    evalOne Lambda (TLam K S W α) (g * s * g⁻¹) c -
      g • evalOne Lambda (TLam K S W α) s c ∈ tlamNbhd K S W α i := by
  let N := tlamNbhd K S W α i
  have h1 := hc (g * s) g⁻¹
  have h2 := hc g s
  have h3 := hc g g⁻¹
  have h4 := act_mem_tlamNbhd g i (hs (evalOne Lambda (TLam K S W α) g⁻¹ c))
  have h5 := hc.eval_one_mem
  rw [mul_inv_cancel] at h3
  have he := N.add_mem (N.sub_mem (N.add_mem (N.add_mem h1 h2) h4) h3) h5
  convert he using 1
  rw [mul_smul, smul_sub]
  abel

/-- Restriction from rational automorphisms fixing the number field preserves
multiplication. The proofs of fixing the number field are immaterial. -/
theorem gksOfQ_mul (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (g h : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (hh : ∀ x : K, h (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (hgh : ∀ x : K, (g * h) (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x)) :
    gksOfQ S e (g * h) hgh = gksOfQ S e g hg * gksOfQ S e h hh := by
  unfold gksOfQ
  change resAbs K S (galKOfQ e (g * h) hgh) =
    resAbs K S (galKOfQ e g hg) * resAbs K S (galKOfQ e h hh)
  rw [← map_mul]
  congr 1
  ext x
  simp only [galKOfQ_apply, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]

/-- A retained stage cocycle has a finite normal rational field on whose fixing
subgroup its evaluation vanishes at the retained precision. -/
theorem exists_cocycleField (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : IsStageCocycle W α i c) :
    ∃ F : IntermediateField ℚ Qbar, FiniteDimensional ℚ F ∧ Normal ℚ F ∧
      (∀ x : K, e (algebraMap K (AlgebraicClosure K) x) ∈ F) ∧
      ∀ (g : GalQ)
        (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
          e (algebraMap K (AlgebraicClosure K) x)),
        (∀ x ∈ F, g x = x) →
          evalOne Lambda (TLam K S W α) (gksOfQ S e g hg) c ∈ tlamNbhd K S W α i := by
  have hcont : Continuous (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
      evalOne Lambda (TLam K S W α) (resAbsCont K S g) c -
        evalOne Lambda (TLam K S W α) (1 : GKS K S) c) :=
    ((continuous_evalOne c).comp (resAbsCont K S).continuous).sub continuous_const
  have hOne : resAbsCont K S (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) =
      (1 : GKS K S) := map_one (resAbsCont K S)
  have ht := hcont.tendsto' 1 0 (by rw [hOne, sub_self])
  have hnb : (tlamNbhd K S W α i : Set _) ∈ 𝓝 (0 : TLam K S W α) :=
    tlam_hasBasis_nhds_zero.mem_iff.mpr ⟨i, trivial, Set.Subset.refl _⟩
  have hn := ht hnb
  obtain ⟨B, hB, hker⟩ :=
    (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) _).mp hn
  have : FiniteDimensional K B := hB
  have : FiniteDimensional ℚ B := Module.Finite.trans K B
  have : FiniteDimensional ℚ (B.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ B)
  let A := (B.restrictScalars ℚ).map e.toAlgHom
  have : FiniteDimensional ℚ A := LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (B.restrictScalars ℚ) e.toAlgHom).toLinearEquiv
  let F := IntermediateField.normalClosure ℚ A Qbar
  refine ⟨F, normalClosure.is_finiteDimensional ℚ A Qbar,
    normalClosure.normal ℚ A Qbar, ?_, ?_⟩
  · intro x
    apply A.le_normalClosure
    exact ⟨algebraMap K (AlgebraicClosure K) x, B.algebraMap_mem x, rfl⟩
  · intro g hg hfix
    have hgb : galKOfQ e g hg ∈ B.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      rw [galKOfQ_apply]
      have hxF : e x ∈ F := A.le_normalClosure ⟨x, hx, rfl⟩
      rw [hfix (e x) hxF, AlgEquiv.symm_apply_apply]
    have hd := hker hgb
    have he := (tlamNbhd K S W α i).add_mem hd hc.eval_one_mem
    convert he using 1
    simp only [gksOfQ, sub_add_cancel]

/-- A finite normal field retaining a stage cocycle. -/
def cocycleField (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : IsStageCocycle W α i c) : IntermediateField ℚ Qbar :=
  (exists_cocycleField e i c hc).choose

instance cocycleField_finite (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : IsStageCocycle W α i c) : FiniteDimensional ℚ (cocycleField e i c hc) :=
  (exists_cocycleField e i c hc).choose_spec.1

instance cocycleField_normal (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : IsStageCocycle W α i c) : Normal ℚ (cocycleField e i c hc) :=
  (exists_cocycleField e i c hc).choose_spec.2.1

/-- Agreement on the retained finite field gives agreement of cocycle values at
that precision, for rational automorphisms fixing the number field. -/
theorem cocycleField_eval_sub (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : IsStageCocycle W α i c) (g h : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (hh : ∀ x : K, h (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (hagree : ∀ x ∈ cocycleField e i c hc, g x = h x) :
    evalOne Lambda (TLam K S W α) (gksOfQ S e g hg) c -
      evalOne Lambda (TLam K S W α) (gksOfQ S e h hh) c ∈ tlamNbhd K S W α i := by
  let d := h⁻¹ * g
  have hd : ∀ x : K, d (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x) := by
    intro x
    change h.symm (g (e (algebraMap K (AlgebraicClosure K) x))) = _
    rw [hg]
    apply h.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (hh x).symm
  have hfix : ∀ x ∈ cocycleField e i c hc, d x = x := by
    intro x hx
    change h.symm (g x) = x
    rw [hagree x hx, AlgEquiv.symm_apply_apply]
  have hdv := (exists_cocycleField e i c hc).choose_spec.2.2.2 d hd hfix
  have hhd : ∀ x : K, (h * d) (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x) := by
    intro x
    rw [AlgEquiv.mul_apply, hd, hh]
  have he : gksOfQ S e h hh * gksOfQ S e d hd = gksOfQ S e g hg := by
    rw [← gksOfQ_mul e h d hh hd hhd]
    simp only [d, mul_inv_cancel_left]
  have hv := (tlamNbhd K S W α i).add_mem
    (hc (gksOfQ S e h hh) (gksOfQ S e d hd)) (act_mem_tlamNbhd (gksOfQ S e h hh) i hdv)
  rw [he] at hv
  convert hv using 1
  abel

/-- The original stage fields together with both prescribed cocycle fields,
closed normally so that agreement also retains square evaluations. -/
def detectionFields (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : ∀ i, IsStageCocycle W α i (c i)) (hd : ∀ i, IsStageCocycle W α i (d i))
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) : IntermediateField ℚ Qbar :=
  (IntermediateField.normalClosure ℚ (F i) Qbar ⊔ cocycleField e i (c i) (hc i)) ⊔
    cocycleField e i (d i) (hd i)

instance detectionFields_finite (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : ∀ i, IsStageCocycle W α i (c i)) (hd : ∀ i, IsStageCocycle W α i (d i))
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)] (i : ℕ) :
    FiniteDimensional ℚ (detectionFields e c d hc hd F i) := by
  unfold detectionFields
  infer_instance

instance detectionFields_normal (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : ∀ i, IsStageCocycle W α i (c i)) (hd : ∀ i, IsStageCocycle W α i (d i))
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) :
    Normal ℚ (detectionFields e c d hc hd F i) := by
  unfold detectionFields
  infer_instance

/-- No original stage-field information is discarded. -/
theorem detectionFields_contains_original (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : ∀ i, IsStageCocycle W α i (c i)) (hd : ∀ i, IsStageCocycle W α i (d i))
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) : F i ≤ detectionFields e c d hc hd F i :=
  (F i).le_normalClosure.trans (le_sup_left.trans le_sup_left)

/-- The first prescribed cocycle is retained. -/
theorem detectionFields_contains_left (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : ∀ i, IsStageCocycle W α i (c i)) (hd : ∀ i, IsStageCocycle W α i (d i))
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) :
    cocycleField e i (c i) (hc i) ≤ detectionFields e c d hc hd F i :=
  le_sup_right.trans le_sup_left

/-- The second prescribed cocycle is retained. -/
theorem detectionFields_contains_right (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hc : ∀ i, IsStageCocycle W α i (c i)) (hd : ∀ i, IsStageCocycle W α i (d i))
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) :
    cocycleField e i (d i) (hd i) ≤ detectionFields e c d hc hd F i := le_sup_right

end ArithmeticEvaluation

section ArithmeticSquares

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)

omit [E.IsElliptic] in
/-- A genuine kernel representative fixes the number field. -/
theorem derivativeKernel_fixesK (i : ℕ) (h : derivativeKernel S e α E i) (x : K) :
    (h : GalQ) (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x) :=
  derivativeKernel_fixes_characterField S e α E i h _ (characterField_containsK S e α i x)

omit [E.IsElliptic] in
/-- The square of the actual conjugation coset fixes the number field, because
the representative fixes the normal character field containing it. -/
theorem kernel_cosetSquare_fixesK (i : ℕ) (h : derivativeKernel S e α E i) (x : K) :
    ((ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * h) *
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * h))
      (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x) := by
  let τ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C
  let y := e (algebraMap K (AlgebraicClosure K) x)
  have hy : y ∈ characterField S e α i := characterField_containsK S e α i x
  have hτy : τ y ∈ characterField S e α i := by
    have hm := (τ.restrictNormal (characterField S e α i) ⟨y, hy⟩).property
    simpa only [AlgEquiv.restrictNormal_apply] using hm
  change τ ((h : GalQ) (τ ((h : GalQ) y))) = y
  rw [derivativeKernel_fixes_characterField S e α E i h y hy,
    derivativeKernel_fixes_characterField S e α E i h (τ y) hτy]
  change (τ * τ) y = y
  rw [ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self, AlgEquiv.one_apply]

/-- The genuine square representative in the global Galois group. -/
def kernelSquare (H : ∀ i, derivativeKernel S e α E i) (i : ℕ) : GKS K S :=
  gksOfQ S e ((ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i) *
    (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i))
    (kernel_cosetSquare_fixesK S e α E C i (H i))

/-- Finite normal-field agreement retains the squares of the selected rational
Frobenius and of the prescribed conjugation coset. -/
theorem derivativePrimes_square_agree {τ : GalQ} {h : ℕ → GalQ}
    {F : ℕ → IntermediateField ℚ Qbar} [∀ i, Normal ℚ (F i)] {excl : ℕ → Finset ℕ}
    (D : DerivativePrimes E τ h F excl) (i : ℕ) (x : Qbar) (hx : x ∈ F i) :
    (D.frob i * D.frob i) x = ((τ * h i) * (τ * h i)) x := by
  have hr : (D.frob i).restrictNormal (F i) = (τ * h i).restrictNormal (F i) := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    rw [AlgEquiv.restrictNormal_apply, AlgEquiv.restrictNormal_apply]
    exact D.agree i y y.property
  have hs : (D.frob i * D.frob i).restrictNormal (F i) =
      ((τ * h i) * (τ * h i)).restrictNormal (F i) := by
    change (AlgEquiv.restrictNormalHom (F i)) (D.frob i * D.frob i) =
      (AlgEquiv.restrictNormalHom (F i)) ((τ * h i) * (τ * h i))
    rw [map_mul, map_mul]
    exact congrArg (fun g => g * g) hr
  have he := congrArg (fun g : F i ≃ₐ[ℚ] F i => (g ⟨x, hx⟩ : Qbar)) hs
  simpa only [AlgEquiv.restrictNormal_apply] using he

/-- Finite evaluation fields turn the actual selected Frobenius square into the
prescribed square evaluation at each retained coefficient precision. -/
theorem ratSqFrob_eval_sub_of_containsField
    (H : ∀ i, derivativeKernel S e α E i)
    {F : ℕ → IntermediateField ℚ Qbar} [∀ i, Normal ℚ (F i)] {excl : ℕ → Finset ℕ}
    (D : DerivativePrimes E (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C) (fun i => H i) F excl)
    (hK : ∀ i (x : K), (D.frob i * D.frob i) (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x))
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (hz : ∀ i, IsStageCocycle (E⁄K) α i (z i))
    (hF : ∀ i, cocycleField e i (z i) (hz i) ≤ F i) (i : ℕ) :
    evalOne Lambda (TLam K S (E⁄K) α) (ratSqFrob E e C D hK i) (z i) -
      evalOne Lambda (TLam K S (E⁄K) α) (kernelSquare S e α E C H i) (z i) ∈
        tlamNbhd K S (E⁄K) α i :=
  cocycleField_eval_sub e i (z i) (hz i) (D.frob i * D.frob i)
    ((ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i) *
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i)) (hK i)
    (kernel_cosetSquare_fixesK S e α E C i (H i))
    (fun x hx => derivativePrimes_square_agree E D i x (hF i hx))

end ArithmeticSquares

open ZInQ.Manuscript.RC.Wiring (ResAt)
open scoped Matrix

section CoordinateAction

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] [HasFullTwoTorsion K S W]
  {α : GKS K S →* Lambdaˣ}

/-- The actual twisted action matrix in the retained coefficient basis. -/
def tlamActionMatrix (g : GKS K S) : Matrix (Fin 2) (Fin 2) Lambda :=
  LinearMap.toMatrix (tlamBasis (K := K) (S := S) (W := W) (α := α))
    (tlamBasis (K := K) (S := S) (W := W) (α := α)) (TLam.act (α := α) g)

/-- The action matrix computes the actual twisted action on coordinates. -/
theorem tlamActionMatrix_mulVec (g : GKS K S) (x : TLam K S W α) :
    tlamActionMatrix (W := W) (α := α) g *ᵥ
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α) x =
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α) (g • x) := by
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

/-- Actual twisted action matrices preserve multiplication. -/
theorem tlamActionMatrix_mul (g h : GKS K S) :
    tlamActionMatrix (W := W) (α := α) (g * h) =
      tlamActionMatrix (W := W) (α := α) g * tlamActionMatrix (W := W) (α := α) h := by
  have he : TLam.act (W := W) (α := α) (g * h) =
      (TLam.act (W := W) (α := α) g).comp (TLam.act (W := W) (α := α) h) := by
    ext x
    exact TLam.act_mul g h x
  unfold tlamActionMatrix
  rw [he, LinearMap.toMatrix_comp
    (tlamBasis (K := K) (S := S) (W := W) (α := α))
    (tlamBasis (K := K) (S := S) (W := W) (α := α))
    (tlamBasis (K := K) (S := S) (W := W) (α := α))]

/-- The identity action has the identity matrix. -/
theorem tlamActionMatrix_one :
    tlamActionMatrix (W := W) (α := α) (1 : GKS K S) = 1 := by
  have he : TLam.act (W := W) (α := α) (1 : GKS K S) = LinearMap.id := by
    ext x
    exact TLam.act_one x
  unfold tlamActionMatrix
  rw [he, LinearMap.toMatrix_id]

/-- The common transport matrix in the limit is invertible, without assuming a
determinant bound at the stages. -/
theorem tlamActionMatrix_limit_inverse (g : ℕ → GKS K S) (U : Ultrafilter ℕ) :
    ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i)) *
      ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i)⁻¹) = 1 := by
  rw [← ulimMat_mul]
  simp only [← tlamActionMatrix_mul, mul_inv_cancel, tlamActionMatrix_one, ulimMat_one]

/-- Specializing an invertible integral transport matrix gives an invertible
finite-coordinate transport matrix. -/
theorem tlamActionMatrix_limit_det_ne_zero (g : ℕ → GKS K S) (U : Ultrafilter ℕ)
    (P : Ideal Lambda) [P.IsPrime] :
    ((ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i))).map
      (algebraMap Lambda (ResAt P))).det ≠ 0 := by
  let A := (ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i))).map
    (algebraMap Lambda (ResAt P))
  let B := (ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i)⁻¹)).map
    (algebraMap Lambda (ResAt P))
  have he : A * B = 1 := by
    rw [← Matrix.map_mul, tlamActionMatrix_limit_inverse, Matrix.map_one _ (map_zero _) (map_one _)]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hzero
  rw [hzero, zero_mul] at hd
  exact zero_ne_one hd

/-- Common transport multiplies the detecting determinant by its own determinant. -/
theorem detectionDet_transport {k : Type} [Field k]
    (A : Matrix (Fin 2) (Fin 2) k) (u v : Fin 2 → k) :
    (Matrix.of ![A *ᵥ u, A *ᵥ v]).det = (Matrix.of ![u, v]).det * A.det := by
  have he : Matrix.of ![A *ᵥ u, A *ᵥ v] = Matrix.of ![u, v] * A.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [he, Matrix.det_mul, Matrix.det_transpose]

end CoordinateAction

section KernelAction

open ZInQ.Manuscript.RC.PrintsArith (tateRep TateMod)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix tateMatrix_one)
open ZInQ.Manuscript.RC.GlueSweep.Tate (tateMatrix_congr_of_eqOn_torsField)

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]

/-- Finite kernel membership proves the actual Tate congruence, rather than
assuming a trivial action on the coefficient module. -/
theorem derivativeKernel_tate_mod (i : ℕ) (h : derivativeKernel S e α E i) :
    (PadicInt.toZModPow i).mapMatrix (tateMatrix E (h : GalQ)) = 1 := by
  have he := tateMatrix_congr_of_eqOn_torsField E (h := (h : GalQ)) (σ := 1)
    (fun x hx => (derivativeKernel_fixes_torsField S e α E i h x hx).trans
      (AlgEquiv.one_apply x).symm)
  rw [tateMatrix_one, map_one] at he
  exact he

/-- A finite kernel element acts trivially on the actual Tate module modulo
the required two-power precision. -/
theorem derivativeKernel_tate_sub (i : ℕ) (h : derivativeKernel S e α E i)
    (P : TateS K S (E⁄K)) : ∃ Q : TateS K S (E⁄K),
    (2 : ℤ_[2]) ^ i • Q =
      gksOfQ S e (h : GalQ) (derivativeKernel_fixesK S e α E i h) • P - P := by
  obtain ⟨N, hN⟩ := exists_sub_one_eq_two_pow_smul (derivativeKernel_tate_mod S e α E i h)
  let b := ZInQ.Manuscript.RC.PrintsArith.tateBasis E
  have hf : LinearMap.toMatrix b b
      (tateRep E 2 (h : GalQ) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2) =
      (2 : ℤ_[2]) ^ i • N := by
    rw [map_sub, LinearMap.toMatrix_id, ← hN]
    rfl
  have hy : ∀ y : TateMod E 2,
      ((tateRep E 2 (h : GalQ) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2) y) =
      (2 : ℤ_[2]) ^ i • Matrix.toLin b b N y := by
    intro y
    rw [← Matrix.toLin_toMatrix b b
      (tateRep E 2 (h : GalQ) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2), hf,
      map_smul, LinearMap.smul_apply]
  refine ⟨(tateSEquiv S E e).symm (Matrix.toLin b b N (tateSEquiv S E e P)), ?_⟩
  apply (tateSEquiv S E e).injective
  rw [map_smul, LinearEquiv.apply_symm_apply, ← hy, map_sub, tateSEquiv_gksOfQ_smul]
  rfl

/-- Finite kernel membership also proves the twisted coefficient congruence,
including the character constraint. -/
theorem derivativeKernel_twisted_sub (i : ℕ) (h : derivativeKernel S e α E i)
    (x : TLam K S (E⁄K) α) :
    gksOfQ S e (h : GalQ) (derivativeKernel_fixesK S e α E i h) • x - x ∈
      tlamNbhd K S (E⁄K) α i := by
  have hchar := characterField_trivial S e α i (h : GalQ)
    (derivativeKernel_fixesK S e α E i h)
    (derivativeKernel_fixes_characterField S e α E i h)
  induction x using TLam.induction with
  | zero => rw [smul_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul l P => exact smul_tmul_sub_mem _ i l P hchar (derivativeKernel_tate_sub S e α E i h P)
  | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy

/-- Along an actual finite-kernel family, the integral twisted action matrix
has exact limit one. No characteristic-zero restriction-injectivity statement
is inferred from finite-stage membership alone. -/
theorem kernelFamily_action_limit (H : ∀ i, derivativeKernel S e α E i)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) :
    ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
      (gksOfQ S e (H i : GalQ) (derivativeKernel_fixesK S e α E i (H i)))) = 1 := by
  rw [← ulimMat_one (R := Lambda) U]
  apply ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU
  apply Eventually.of_forall
  intro i a b
  let B := tlamBasis (K := K) (S := S) (W := E⁄K) (α := α)
  have hm := derivativeKernel_twisted_sub S e α E i (H i) (B b)
  have hc := tlamHomeomorph_mem_stageIdeal hm a
  rw [tlamHomeomorph_apply, map_sub, Finsupp.sub_apply, Basis.repr_self] at hc
  change (tlamActionMatrix (W := E⁄K) (α := α) _ a b - (1 : Matrix (Fin 2) (Fin 2) Lambda) a b) ∈ _
  simpa only [tlamActionMatrix, LinearMap.toMatrix_apply, TLam.smul_def,
    Matrix.one_apply, Finsupp.single_apply, eq_comm] using hc

end KernelAction

section IntegralValues

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] [HasFullTwoTorsion K S W]
  {α : GKS K S →* Lambdaˣ} [IsContChar α]

/-- The integral inner limit of genuine retained cochain evaluations. -/
def integralTateValue (U : Ultrafilter ℕ) (s : ℕ → GKS K S)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) : Fin 2 → Lambda :=
  ulimVec U (fun i => tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
    (evalOne Lambda (TLam K S W α) (s i) (z i)))

/-- Specialization is applied only after the integral coordinate limit. -/
def specializeVec (P : Ideal Lambda) [P.IsPrime] (v : Fin 2 → Lambda) : Fin 2 → ResAt P :=
  fun j => algebraMap Lambda (ResAt P) (v j)

/-- The Frobenius-value consumer uses this same integral limit. -/
theorem limitFrobValue_eq_integral (P : Ideal Lambda) [P.IsPrime]
    (L : MovingLabel K S) (U : Ultrafilter ℕ)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) :
    limitFrobValue P L U z = specializeVec P (integralTateValue U L.frob z) := rfl

/-- Specialization commutes with finite matrix-vector multiplication. -/
theorem specializeVec_mulVec (P : Ideal Lambda) [P.IsPrime]
    (A : Matrix (Fin 2) (Fin 2) Lambda) (v : Fin 2 → Lambda) :
    specializeVec P (A *ᵥ v) = A.map (algebraMap Lambda (ResAt P)) *ᵥ specializeVec P v := by
  funext j
  simp only [specializeVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    map_add, map_mul, Matrix.map_apply]

/-- A common Galois transport gives an exact integral coordinate identity from
stage congruences. No equality of untransported representative values is used. -/
theorem integralTateValue_of_stage_sub
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (s t g : ℕ → GKS K S)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (h : ∀ i, evalOne Lambda (TLam K S W α) (s i) (z i) -
      g i • evalOne Lambda (TLam K S W α) (t i) (z i) ∈ tlamNbhd K S W α i) :
    integralTateValue U s z =
      ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i)) *ᵥ
        integralTateValue U t z := by
  unfold integralTateValue
  rw [← ulimVec_mulVec]
  apply ulimVec_eq_of_sub_mem stageIdeal_tendsToZero hU
  apply Eventually.of_forall
  intro i j
  rw [tlamActionMatrix_mulVec]
  have he := tlamHomeomorph_mem_stageIdeal (h i) j
  rw [tlamHomeomorph_apply, map_sub, Finsupp.sub_apply] at he
  exact he

/-- The determinant of the integral common transport is a unit. -/
theorem integralTransport_det_isUnit (g : ℕ → GKS K S) (U : Ultrafilter ℕ) :
    IsUnit (ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i))).det := by
  let A := ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i))
  let B := ulimMat U (fun i => tlamActionMatrix (W := W) (α := α) (g i)⁻¹)
  have he : A * B = 1 := tlamActionMatrix_limit_inverse (W := W) (α := α) g U
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one] at hd
  refine ⟨⟨A.det, B.det, hd, ?_⟩, rfl⟩
  rw [mul_comm]
  exact hd

end IntegralValues

section SelectedLabel

open ZInQ.Contrib.RC53Assist.StagePrimes

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (c d : ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (hc : ∀ i, IsStageCocycle (E⁄K) α i (c i))
    (hd : ∀ i, IsStageCocycle (E⁄K) α i (d i))
    (H : ∀ i, derivativeKernel S e α E i)
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2)

/-- The arithmetic label includes both prescribed evaluation fields and every
old stage field in its single finite Chebotarev selection. -/
def detectionArithmeticLabel : CompatibleArithmeticLabel E K S α :=
  compatibleArithmeticLabelFromImaginaryQuadraticKernel S hS e α E C H
    (detectionFields e c d hc hd F) excl hdegree

/-- The fixed-decomposition evaluations of both prescribed classes are the
prescribed square evaluations with one common integral Galois transport. Its
determinant is a unit. This supplies the conjugation transport required in (5.4). -/
theorem detectionArithmeticLabel_integral_values (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) :
    let X := detectionArithmeticLabel S hS e α E C c d hc hd H F excl hdegree
    ∃ A : Matrix (Fin 2) (Fin 2) Lambda, IsUnit A.det ∧
      integralTateValue U X.label.frob c = A *ᵥ integralTateValue U (kernelSquare S e α E C H) c ∧
      integralTateValue U X.label.frob d = A *ᵥ integralTateValue U (kernelSquare S e α E C H) d := by
  let X := detectionArithmeticLabel S hS e α E C c d hc hd H F excl hdegree
  choose g hg using X.frobMatch
  have hcr (i : ℕ) :
      evalOne Lambda (TLam K S (E⁄K) α) (ratSqFrob E e C X.primes X.hK i) (c i) -
        evalOne Lambda (TLam K S (E⁄K) α) (kernelSquare S e α E C H i) (c i) ∈
          tlamNbhd K S (E⁄K) α i :=
    ratSqFrob_eval_sub_of_containsField S e α E C H
      (F := detectionFields e c d hc hd F) X.primes X.hK c hc
      (detectionFields_contains_left e c d hc hd F) i
  have hdr (i : ℕ) :
      evalOne Lambda (TLam K S (E⁄K) α) (ratSqFrob E e C X.primes X.hK i) (d i) -
        evalOne Lambda (TLam K S (E⁄K) α) (kernelSquare S e α E C H i) (d i) ∈
          tlamNbhd K S (E⁄K) α i :=
    ratSqFrob_eval_sub_of_containsField S e α E C H
      (F := detectionFields e c d hc hd F) X.primes X.hK d hd
      (detectionFields_contains_right e c d hc hd F) i
  refine ⟨ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α) (g i)),
    integralTransport_det_isUnit (W := E⁄K) (α := α) g U, ?_, ?_⟩
  · apply integralTateValue_of_stage_sub hU X.label.frob (kernelSquare S e α E C H) g c
    intro i
    have hp := stageCocycle_conjugate_sub (hc i) (g i) (ratSqFrob E e C X.primes X.hK i)
      (twisted_congr_ratSqFrob E e C X.primes X.hK X.hh i (X.character i))
    have he := (tlamNbhd K S (E⁄K) α i).add_mem hp (act_mem_tlamNbhd (g i) i (hcr i))
    have hgi : X.label.frob i = g i * ratSqFrob E e C X.primes X.hK i * (g i)⁻¹ := hg i
    convert he using 1
    rw [hgi, smul_sub]
    abel
  · apply integralTateValue_of_stage_sub hU X.label.frob (kernelSquare S e α E C H) g d
    intro i
    have hp := stageCocycle_conjugate_sub (hd i) (g i) (ratSqFrob E e C X.primes X.hK i)
      (twisted_congr_ratSqFrob E e C X.primes X.hK X.hh i (X.character i))
    have he := (tlamNbhd K S (E⁄K) α i).add_mem hp (act_mem_tlamNbhd (g i) i (hdr i))
    have hgi : X.label.frob i = g i * ratSqFrob E e C X.primes X.hK i * (g i)⁻¹ := hg i
    convert he using 1
    rw [hgi, smul_sub]
    abel

/-- The integral transport gives simultaneous specialized value identities with
an invertible finite-coordinate matrix. -/
theorem detectionArithmeticLabel_values (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime] :
    let X := detectionArithmeticLabel S hS e α E C c d hc hd H F excl hdegree
    ∃ A : Matrix (Fin 2) (Fin 2) (ResAt P), A.det ≠ 0 ∧
      limitFrobValue P X.label U c =
        A *ᵥ specializeVec P (integralTateValue U (kernelSquare S e α E C H) c) ∧
      limitFrobValue P X.label U d =
        A *ᵥ specializeVec P (integralTateValue U (kernelSquare S e α E C H) d) := by
  let X := detectionArithmeticLabel S hS e α E C c d hc hd H F excl hdegree
  obtain ⟨A, hA, hcA, hdA⟩ := detectionArithmeticLabel_integral_values
    S hS e α E C c d hc hd H F excl hdegree U hU
  refine ⟨A.map (algebraMap Lambda (ResAt P)), ?_, ?_, ?_⟩
  · change ((algebraMap Lambda (ResAt P)).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    exact (hA.map (algebraMap Lambda (ResAt P))).ne_zero
  · rw [limitFrobValue_eq_integral, hcA, specializeVec_mulVec]
  · rw [limitFrobValue_eq_integral, hdA, specializeVec_mulVec]

end SelectedLabel

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

section PrescribedClasses

variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M]

/-- A cochain embedding which is onto in degree zero is injective on first
cohomology. This supplies a sufficient global comparison criterion. -/
theorem boundary_of_principal_under_embedding (Q : GCx k)
    (e0 : Q.X 0 →ₗ[k] M) (e1 : Q.X 1 →ₗ[k] (G → M))
    (hcomm : ∀ x g, e1 (Q.d 0 1 rfl x) g = g • e0 x - e0 x)
    (h0 : Function.Surjective e0) (h1 : Function.Injective e1)
    (x : Q.X 1) (hx : groupCohomology.IsCoboundary₁ (e1 x)) :
    x ∈ LinearMap.range (Q.d 0 1 rfl) := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨y, hy⟩ := h0 w
  refine ⟨y, h1 ?_⟩
  funext g
  rw [hcomm, hy]
  exact hw g

/-- A prescribed nonzero first-cohomology class has an independent cocycle
partner whenever first cohomology has dimension greater than one. -/
theorem exists_prescribed_cycle_partner (Q : GCx k)
    [FiniteDimensional k (Q.toCC.homology 1)] (a : LinearMap.ker (Q.d 1 2 rfl))
    (ha : clsAt Q 1 2 rfl a ≠ 0) (hdim : 1 < Module.finrank k (Q.toCC.homology 1)) :
    ∃ b : LinearMap.ker (Q.d 1 2 rfl),
      LinearIndependent k ![clsAt Q 1 2 rfl a, clsAt Q 1 2 rfl b] := by
  let v := clsAt Q 1 2 rfl a
  have hp : Submodule.span k {v} ≠ (⊤ : Submodule k (Q.toCC.homology 1)) := by
    intro htop
    have he : Module.finrank k (Submodule.span k {v}) = 1 := finrank_span_singleton ha
    rw [htop, finrank_top] at he
    omega
  obtain ⟨w, hw⟩ : ∃ w : Q.toCC.homology 1, w ∉ Submodule.span k {v} := by
    by_contra hno
    push Not at hno
    exact hp (top_unique (fun w _ => hno w))
  obtain ⟨b, hb⟩ := clsAt_surjective Q 1 2 rfl w
  refine ⟨b, ?_⟩
  rw [hb]
  apply Fintype.linearIndependent_iff.mpr
  intro f hf i
  rw [Fin.sum_univ_two] at hf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
  have h1 : f 1 = 0 := by
    by_contra hn
    have he := congrArg (fun x : Q.toCC.homology 1 => (f 1)⁻¹ • x) hf
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hn, one_smul, smul_zero] at he
    have hw' : w = -(((f 1)⁻¹ * f 0) • v) := by
      apply (eq_neg_iff_add_eq_zero).mpr
      simpa only [add_comm] using he
    apply hw
    rw [hw']
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v)))
  have h0 : f 0 = 0 := by
    rw [h1, zero_smul, add_zero] at hf
    exact (smul_eq_zero.mp hf).resolve_right ha
  fin_cases i
  · exact h0
  · exact h1

/-- Independence in prescribed fibre cohomology implies independence of its
evaluated cocycle functions when the global cohomology comparison is injective.
This criterion concerns global boundaries, not kernel restriction or detection. -/
theorem evaluated_classes_independent (Q : GCx k)
    (e1 : Q.X 1 →ₗ[k] (G → M))
    (hinj : ∀ x : Q.X 1, Q.d 1 2 rfl x = 0 →
      groupCohomology.IsCoboundary₁ (e1 x) → x ∈ LinearMap.range (Q.d 0 1 rfl))
    (a b : LinearMap.ker (Q.d 1 2 rfl))
    (hind : LinearIndependent k ![clsAt Q 1 2 rfl a, clsAt Q 1 2 rfl b]) :
    ∀ r s : k, groupCohomology.IsCoboundary₁
      (fun g => r • e1 a.val g + s • e1 b.val g) → r = 0 ∧ s = 0 := by
  intro r s hcb
  let c : LinearMap.ker (Q.d 1 2 rfl) := r • a + s • b
  have hc : groupCohomology.IsCoboundary₁ (e1 c.val) := by
    convert hcb using 1
    funext g
    change e1 (r • a.val + s • b.val) g = _
    rw [map_add, map_smul, map_smul]
    rfl
  obtain ⟨x, hx⟩ := hinj c.val c.property hc
  have hcz : clsAt Q 1 2 rfl c = 0 := by
    have he : c = ⟨Q.d 0 1 rfl x, LinearMap.mem_ker.mpr (Q.d_d 0 1 2 rfl rfl x)⟩ :=
      Subtype.ext hx.symm
    rw [he]
    exact clsAt_boundary Q 0 1 2 rfl rfl x
  change clsAt Q 1 2 rfl (r • a + s • b) = 0 at hcz
  rw [map_add, map_smul, map_smul] at hcz
  have he := (Fintype.linearIndependent_iff.mp hind) ![r, s] (by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hcz)
  exact ⟨he 0, he 1⟩

end PrescribedClasses

/-- The fixed scalar in the common-kernel argument. -/
def manuscriptScalar (P : Ideal Lambda) [P.IsPrime] (n : ℕ) : ResAt P :=
  algebraMap ℤ_[2] (ResAt P) ((1 + (2 : ℤ_[2]) ^ n) ^ 4)

/-- The scalar difference is nonzero on the characteristic-zero tests away
from two; vanishing of image cohomology is not assumed. -/
theorem manuscriptScalar_ne_one (P : Ideal Lambda) [P.IsPrime]
    (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) (n : ℕ) :
    manuscriptScalar P n ≠ 1 := by
  have : CharZero (ResAt P) := charZero_resAt hP hne
  have hn : (1 + 2 ^ n : ℕ) ^ 4 ≠ 1 := by
    have hbase : 2 ≤ 1 + 2 ^ n := by have := Nat.one_le_two_pow (n := n); omega
    have hp := Nat.pow_le_pow_left hbase 4
    norm_num at hp
    omega
  have he : manuscriptScalar P n = ((1 + 2 ^ n : ℕ) ^ 4 : ResAt P) := by
    simp only [manuscriptScalar, map_pow, map_add, map_one, map_ofNat,
      Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [he]
  exact_mod_cast hn

/-- Rational automorphisms which fix the given number field. -/
def rationalBaseGroup {K : Type} [Field K] [NumberField K]
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) : Subgroup GalQ where
  carrier := {g | ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
    e (algebraMap K (AlgebraicClosure K) x)}
  one_mem' := fun _ => rfl
  mul_mem' hg hh x := by rw [AlgEquiv.mul_apply, hh x, hg x]
  inv_mem' {g} hg x := by
    apply g.injective
    change g (g.symm (e (algebraMap K (AlgebraicClosure K) x))) =
      g (e (algebraMap K (AlgebraicClosure K) x))
    rw [AlgEquiv.apply_symm_apply]
    exact (hg x).symm

section BaseSequences

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- The genuine restriction homomorphism to the global unramified Galois group. -/
def baseRestriction : rationalBaseGroup e →* GKS K S where
  toFun g := gksOfQ S e g.val g.property
  map_one' := by
    change gksOfQ S e 1 _ = 1
    unfold gksOfQ
    have he : galKOfQ e 1 (fun _ => rfl) = 1 := by
      apply AlgEquiv.ext
      intro x
      change e.symm ((1 : GalQ) (e x)) = x
      rw [AlgEquiv.one_apply, AlgEquiv.symm_apply_apply]
    change resAbs K S (galKOfQ e 1 _) = 1
    rw [he, map_one]
  map_mul' g h := gksOfQ_mul e g.val h.val g.property h.property (g * h).property

/-- Every global Galois element has an actual rational lift fixing the number field. -/
theorem baseRestriction_surjective : Function.Surjective (baseRestriction S e) := by
  intro s
  obtain ⟨g, hg⟩ := ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_surjective K S s
  let q := ZInQ.Manuscript.RC.KummerMaps.tateGalToQ e g
  have hq : q ∈ rationalBaseGroup e := by
    intro x
    rw [ZInQ.Manuscript.RC.KummerMaps.tateGalToQ_apply,
      AlgEquiv.symm_apply_apply, AlgEquiv.commutes]
  refine ⟨⟨q, hq⟩, ?_⟩
  have he : galKOfQ e q hq = g := by
    apply AlgEquiv.ext
    intro x
    calc
      galKOfQ e q hq x = e.symm (q (e x)) := galKOfQ_apply e q hq x
      _ = e.symm (e (g (e.symm (e x)))) :=
        congrArg e.symm (ZInQ.Manuscript.RC.KummerMaps.tateGalToQ_apply e g (e x))
      _ = g x := by rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  change resAbs K S (galKOfQ e q hq) = s
  rw [he]
  exact hg

/-- A rational lift at the fixed embedding. -/
def baseLift (s : GKS K S) : rationalBaseGroup e :=
  (baseRestriction_surjective S e s).choose

theorem baseLift_spec (s : GKS K S) : baseRestriction S e (baseLift S e s) = s :=
  (baseRestriction_surjective S e s).choose_spec

/-- The pointwise inclusion of the number-field Galois sequences into rational sequences. -/
def baseSequenceInclusion : (ℕ → rationalBaseGroup e) →* (ℕ → GalQ) where
  toFun g i := (g i).val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Pointwise restriction of actual rational lifts. -/
def baseSequenceRestriction : (ℕ → rationalBaseGroup e) →* (ℕ → GKS K S) where
  toFun g i := baseRestriction S e (g i)
  map_one' := funext fun _ => map_one (baseRestriction S e)
  map_mul' _ _ := funext fun _ => map_mul (baseRestriction S e) _ _

end BaseSequences

/-- Rational Galois sequences. -/
abbrev RationalSequences := ℕ → GalQ

/-- Coordinates of the induced characteristic-zero coefficient module. -/
abbrev FibrePair (P : Ideal Lambda) [P.IsPrime] := (Fin 2 → ResAt P) × (Fin 2 → ResAt P)

/-- The simultaneous actual conjugation. -/
def sequenceConjugation {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S) : RationalSequences :=
  fun _ => ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C

theorem sequenceConjugation_sq {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S) :
    sequenceConjugation e C * sequenceConjugation e C = 1 :=
  funext fun _ => ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C

section CoefficientDictionary

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- The arithmetic identification of the induced coefficient action. In the
transversal coordinates at one and conjugation, conjugation exchanges summands.
Restriction to the number-field subgroup is the actual twisted Tate action.
These are coefficient identifications, independent of any cohomology class. -/
structure InducedCoefficientDictionary where
  conjugation : ∀ x y : Fin 2 → ResAt P, sequenceConjugation e C • (x, y) = (y, x)
  restriction : ∀ (g : ℕ → rationalBaseGroup e) (x : FibrePair P),
    (baseSequenceInclusion e g • x).1 =
      (ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
        (baseSequenceRestriction S e g i))).map (algebraMap Lambda (ResAt P)) *ᵥ x.1

/-- Actual finite kernel membership gives triviality on the induced coefficient
module in the limit, including all prescribed arithmetic kernel fields. -/
theorem InducedCoefficientDictionary.kernel_action
    (D : InducedCoefficientDictionary S e α E C U P)
    (hU : (U : Filter ℕ) ≤ cofinite)
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]
    (h : arithmeticSequenceKernel E S e α B) (x : FibrePair P) : (h : RationalSequences) • x = x := by
  have first (t : arithmeticSequenceKernel E S e α B) (y : FibrePair P) :
      ((t : RationalSequences) • y).1 = y.1 := by
    let H := arithmeticKernelFamily E S e α t
    let g : ℕ → rationalBaseGroup e := fun i =>
      ⟨H i, derivativeKernel_fixesK S e α E i (H i)⟩
    change (baseSequenceInclusion e g • y).1 = y.1
    rw [D.restriction]
    have hm := kernelFamily_action_limit S e α E H hU
    change (ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
      (gksOfQ S e (H i : GalQ) (derivativeKernel_fixesK S e α E i (H i))))).map
      (algebraMap Lambda (ResAt P)) *ᵥ y.1 = y.1
    rw [hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  let τ := sequenceConjugation e C
  let t : arithmeticSequenceKernel E S e α B :=
    ⟨τ * h * τ⁻¹, (inferInstance : (arithmeticSequenceKernel E S e α B).Normal).conj_mem
      h h.property τ⟩
  have he := first t (τ • x)
  have ht : (t : RationalSequences) • (τ • x) = τ • ((h : RationalSequences) • x) := by
    change (τ * h * τ⁻¹) • (τ • x) = τ • ((h : RationalSequences) • x)
    rw [← mul_smul, ← mul_smul]
    congr 1
    simp [mul_assoc]
  rw [ht] at he
  have e1 : (τ • ((h : RationalSequences) • x)).1 = ((h : RationalSequences) • x).2 :=
    congrArg Prod.fst (D.conjugation ((h : RationalSequences) • x).1
      ((h : RationalSequences) • x).2)
  have e2 : (τ • x).1 = x.2 := congrArg Prod.fst (D.conjugation x.1 x.2)
  exact Prod.ext (first h x) (e1.symm.trans (he.trans e2))

/-- The precise scalar input for the stated arithmetic sequence kernel. The
scalar action and centrality modulo this particular kernel are the hypotheses
of the manuscript, lines 4766–4774 and (H1). No cohomology or determinant
vanishing assertion occurs in this input. -/
structure ArithmeticCommonScalar (B : ℕ → IntermediateField ℚ Qbar) where
  n : ℕ
  two_le : 2 ≤ n
  element : RationalSequences
  action : ∀ x : FibrePair P, element • x = manuscriptScalar P n • x
  commutator : ∀ g : RationalSequences,
    element * g * element⁻¹ * g⁻¹ ∈ arithmeticSequenceKernel E S e α B

/-- A fixed finite matrix-span witness on the characteristic-zero induced
module. This is the image-algebra hypothesis in lines 4779–4785; it makes no
assertion about values of any class or about the residual representation. -/
structure CoefficientSpanWitness where
  size : ℕ
  elements : Fin size → RationalSequences
  spans : Submodule.span (ResAt P)
    (Set.range (fun i => linearAction (ResAt P) (FibrePair P) (elements i))) = ⊤

theorem CoefficientSpanWitness.full_span (D : CoefficientSpanWitness P) :
    Submodule.span (ResAt P)
      (Set.range (linearAction (ResAt P) (FibrePair P) : RationalSequences → _)) = ⊤ := by
  apply top_unique
  rw [← D.spans, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span (Set.mem_range_self (D.elements i))

end CoefficientDictionary

section NormalizedEvaluation

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ}
  [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
  {α : GKS K S →* Lambdaˣ} [IsContChar α]

/-- Original integral cochain evaluations are limited first. Localized fibre
coordinates, with any denominators in the minimal-model inclusion, are applied
only afterwards. -/
def basisValue {n : ℕ} (P : Ideal Lambda) [P.IsPrime] (U : Ultrafilter ℕ)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (s : ℕ → GKS K S) (w : Fin n → ResAt P) : Fin 2 → ResAt P :=
  ∑ j, w j • specializeVec P (integralTateValue U s (z j))

variable (S) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (α) (E)
    (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- The retained cochain comparison on the prescribed fibre. The original
integral basis cochains are not assumed to be cycles. Cochain identities imply
that fibre cycles give genuine crossed homomorphisms after specialization.
Boundary reflection is the global first-cohomology injection in lines 4651–4704;
it is not a localization or kernel-detection assumption. -/
structure RetainedEvaluation (n : ℕ) (Q : GCx (ResAt P)) where
  original : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1
  coordinates : Q.X 1 →ₗ[ResAt P] (Fin n → ResAt P)
  one : Q.X 1 →ₗ[ResAt P] (RationalSequences → FibrePair P)
  two : Q.X 2 →ₗ[ResAt P] (RationalSequences × RationalSequences → FibrePair P)
  cochain_identity : ∀ x g h, two (Q.d 1 2 rfl x) (g, h) =
    g • one x h - one x (g * h) + one x g
  principal_boundary : ∀ x : Q.X 1, Q.d 1 2 rfl x = 0 →
    groupCohomology.IsCoboundary₁ (one x) → x ∈ LinearMap.range (Q.d 0 1 rfl)
  projection : ∀ x (g : ℕ → rationalBaseGroup e),
    (one x (baseSequenceInclusion e g)).1 =
      basisValue P U original (baseSequenceRestriction S e g) (coordinates x)

/-- Crossed-homomorphism status is derived from the retained cochain identity. -/
theorem RetainedEvaluation.isCocycle {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) (a : LinearMap.ker (Q.d 1 2 rfl)) :
    groupCohomology.IsCocycle₁ (D.one a.val) := by
  intro g h
  have he : g • D.one a.val h - D.one a.val (g * h) + D.one a.val g = 0 := by
    rw [← D.cochain_identity, a.property, map_zero]
    rfl
  apply eq_of_sub_eq_zero
  calc
    D.one a.val (g * h) - (g • D.one a.val h + D.one a.val g) =
      -(g • D.one a.val h - D.one a.val (g * h) + D.one a.val g) := by abel
    _ = 0 := by rw [he, neg_zero]

end NormalizedEvaluation

section ProjectedConjugacy

variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
    [DistribMulAction G M] [SMulCommClass G k M]

/-- The projected cocycle transports under conjugation whenever the square acts
trivially on the projected coefficient module. This does not require integral
stage-cocycle lifts of the fibre class. -/
theorem projected_cocycle_conjugate {c : G → M}
    (hc : groupCohomology.IsCocycle₁ c) (p : M →ₗ[k] (Fin 2 → k))
    (g s : G) (A : Matrix (Fin 2) (Fin 2) k)
    (hg : ∀ m : M, p (g • m) = A *ᵥ p m)
    (hs : ∀ m : M, p (s • m) = p m) :
    p (c (g * s * g⁻¹)) = A *ᵥ p (c s) := by
  rw [hc, hc, mul_smul, map_add, map_add, hg, hs, hg]
  have hi := congrArg p (cocycle_inverse hc g)
  rw [map_add, hg, map_zero] at hi
  calc
    A *ᵥ p (c g⁻¹) + (A *ᵥ p (c s) + p (c g)) =
      A *ᵥ p (c s) + (A *ᵥ p (c g⁻¹) + p (c g)) := by abel
    _ = A *ᵥ p (c s) := by rw [hi, add_zero]

end ProjectedConjugacy

section KernelProducer

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]

include hU hP hne in
/-- The inner-limit kernel detection producer for a prescribed nonzero fibre
class. An independent partner is chosen in fibre cohomology. Restriction
injectivity, coefficient span, and polarization produce an actual arithmetic
kernel sequence. No detecting determinant is an input. -/
theorem produce_kernel_detection {n : ℕ} (Q : GCx (ResAt P))
    [FiniteDimensional (ResAt P) (Q.toCC.homology 1)]
    (coeff : InducedCoefficientDictionary S e α E C U P)
    (scalar : ArithmeticCommonScalar S e α E P B)
    (span : CoefficientSpanWitness P)
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) (Q.toCC.homology 1)) :
    ∃ b : LinearMap.ker (Q.d 1 2 rfl), ∃ h : arithmeticSequenceKernel E S e α B,
      LinearIndependent (ResAt P) ![clsAt Q 1 2 rfl a, clsAt Q 1 2 rfl b] ∧
      (Matrix.of ![(D.one a.val ((sequenceConjugation e C * h) *
        (sequenceConjugation e C * h))).1,
        (D.one b.val ((sequenceConjugation e C * h) *
        (sequenceConjugation e C * h))).1]).det ≠ 0 := by
  obtain ⟨b, hab⟩ := exists_prescribed_cycle_partner Q a ha hdim
  have htriv : ∀ h ∈ arithmeticSequenceKernel E S e α B,
      ∀ m : FibrePair P, h • m = m := fun h hh m =>
    InducedCoefficientDictionary.kernel_action (S := S) (e := e) (α := α) (E := E)
      (C := C) (U := U) (P := P) coeff hU B ⟨h, hh⟩ m
  have hind := evaluated_classes_independent Q D.one D.principal_boundary a b hab
  have hp := cosetProjection_fst_surjective (sequenceConjugation e C)
    (LinearMap.id : (Fin 2 → ResAt P) →ₗ[ResAt P] (Fin 2 → ResAt P)) coeff.conjugation
  have hca := RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
    (U := U) (P := P) D a
  have hcb := RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
    (U := U) (P := P) D b
  obtain ⟨h, hh⟩ := exists_prescribed_square_det hca hcb
    (arithmeticSequenceKernel E S e α B) htriv scalar.element (manuscriptScalar P scalar.n)
    (manuscriptScalar_ne_one P hP hne scalar.n) scalar.action scalar.commutator
    span.full_span hind (LinearMap.fst (ResAt P) (Fin 2 → ResAt P) (Fin 2 → ResAt P))
    (sequenceConjugation e C) (sequenceConjugation_sq e C) hp
  exact ⟨b, h, hab, hh⟩

end KernelProducer

section RetainedArithmeticHelpers

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)

/-- The prescribed square is an actual sequence in the number-field subgroup. -/
def kernelSquareBase (H : ∀ i, derivativeKernel S e α E i) : ℕ → rationalBaseGroup e := fun i =>
  ⟨(ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i) *
    (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i),
    kernel_cosetSquare_fixesK S e α E C i (H i)⟩

/-- An actual stage action congruence implies exact identity in the integral
matrix limit. -/
theorem actionMatrix_limit_one (s : ℕ → GKS K S) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite)
    (hs : ∀ i (x : TLam K S (E⁄K) α), s i • x - x ∈ tlamNbhd K S (E⁄K) α i) :
    ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α) (s i)) = 1 := by
  rw [← ulimMat_one (R := Lambda) U]
  apply ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU
  apply Eventually.of_forall
  intro i a b
  let B := tlamBasis (K := K) (S := S) (W := E⁄K) (α := α)
  have he := tlamHomeomorph_mem_stageIdeal (hs i (B b)) a
  rw [tlamHomeomorph_apply, map_sub, Finsupp.sub_apply, Basis.repr_self] at he
  change (tlamActionMatrix (W := E⁄K) (α := α) (s i) a b -
    (1 : Matrix (Fin 2) (Fin 2) Lambda) a b) ∈ stageIdeal i
  simpa only [tlamActionMatrix, LinearMap.toMatrix_apply, TLam.smul_def,
    Matrix.one_apply, Finsupp.single_apply, eq_comm] using he

/-- Original continuous cochain congruences give exact integral evaluation
identities. The cochains need not themselves be cocycles. -/
theorem integralTateValue_eq_of_sub (s t : ℕ → GKS K S) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (h : ∀ i, evalOne Lambda (TLam K S (E⁄K) α) (s i) (z i) -
      evalOne Lambda (TLam K S (E⁄K) α) (t i) (z i) ∈ tlamNbhd K S (E⁄K) α i) :
    integralTateValue U s z = integralTateValue U t z := by
  unfold integralTateValue
  apply ulimVec_eq_of_sub_mem stageIdeal_tendsToZero hU
  apply Eventually.of_forall
  intro i j
  have he := tlamHomeomorph_mem_stageIdeal (h i) j
  rw [tlamHomeomorph_apply, map_sub, Finsupp.sub_apply] at he
  exact he

/-- Eventual equality of group representatives preserves original-basis
integral evaluation matrices before localized coordinates are applied. -/
theorem basisValue_eq_of_eventual_eq {n : ℕ} (P : Ideal Lambda) [P.IsPrime]
    (U : Ultrafilter ℕ)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (s t : ℕ → GKS K S) (h : ∀ᶠ i in (U : Filter ℕ), s i = t i)
    (w : Fin n → ResAt P) : basisValue P U z s w = basisValue P U z t w := by
  have he (j : Fin n) : integralTateValue U s (z j) = integralTateValue U t (z j) := by
    funext a
    apply ulim_congr
    exact h.mono (fun i hi => by dsimp only; rw [hi])
  unfold basisValue
  apply Finset.sum_congr rfl
  intro j _
  rw [he j]

end RetainedArithmeticHelpers

section GeneralFields

variable {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
    {α : GKS K S →* Lambdaˣ} [IsContChar α]

/-- Every original continuous cochain factors at the retained precision through
a finite normal rational field. Original basis cochains need not be cocycles. -/
theorem exists_cochainField (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) :
    ∃ F : IntermediateField ℚ Qbar, FiniteDimensional ℚ F ∧ Normal ℚ F ∧
      (∀ x : K, e (algebraMap K (AlgebraicClosure K) x) ∈ F) ∧
      ∀ (g h : GalQ)
        (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
          e (algebraMap K (AlgebraicClosure K) x))
        (hh : ∀ x : K, h (e (algebraMap K (AlgebraicClosure K) x)) =
          e (algebraMap K (AlgebraicClosure K) x)),
        (∀ x ∈ F, g x = h x) →
          evalOne Lambda (TLam K S W α) (gksOfQ S e g hg) c -
            evalOne Lambda (TLam K S W α) (gksOfQ S e h hh) c ∈ tlamNbhd K S W α i := by
  classical
  let G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K
  let f : G → TLam K S W α := fun g => evalOne Lambda (TLam K S W α) (resAbsCont K S g) c
  have hf : Continuous f := (continuous_evalOne c).comp (resAbsCont K S).continuous
  have hnb : (tlamNbhd K S W α i : Set _) ∈ 𝓝 (0 : TLam K S W α) :=
    tlam_hasBasis_nhds_zero.mem_iff.mpr ⟨i, trivial, Set.Subset.refl _⟩
  have hlocal (g : G) : ∃ B : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K B ∧ ∀ u ∈ B.fixingSubgroup,
        f (g * u) - f g ∈ tlamNbhd K S W α i := by
    have hcont : Continuous (fun u : G => f (g * u) - f g) :=
      (hf.comp (continuous_const.mul continuous_id)).sub continuous_const
    have ht := hcont.tendsto' 1 0 (by rw [mul_one, sub_self])
    obtain ⟨B, hB, hker⟩ :=
      (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) _).mp (ht hnb)
    exact ⟨B, hB, fun u hu => hker hu⟩
  choose B hB hlocalB using hlocal
  let V : G → Set G := fun g => (fun x => g⁻¹ * x) ⁻¹' ((B g).fixingSubgroup : Set G)
  have hV : ∀ g, IsOpen (V g) := by
    intro g
    have : FiniteDimensional K (B g) := hB g
    exact (B g).fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_id)
  have hcover : Set.univ ⊆ ⋃ g, V g := by
    intro g _
    refine Set.mem_iUnion.mpr ⟨g, ?_⟩
    change g⁻¹ * g ∈ (B g).fixingSubgroup
    simp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  let T : IntermediateField K (AlgebraicClosure K) := t.sup B
  have hT : FiniteDimensional K T := by
    change FiniteDimensional K ↥(t.sup B : IntermediateField K (AlgebraicClosure K))
    clear ht T
    induction t using Finset.induction_on with
    | empty =>
        change FiniteDimensional K ↥(⊥ : IntermediateField K (AlgebraicClosure K))
        infer_instance
    | insert g t hgt ih =>
        rw [Finset.sup_insert]
        have : FiniteDimensional K (B g) := hB g
        have : FiniteDimensional K ↥(t.sup B : IntermediateField K (AlgebraicClosure K)) := ih
        infer_instance
  have := hT
  have : FiniteDimensional ℚ T := Module.Finite.trans K T
  have : FiniteDimensional ℚ (T.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ T)
  let A := (T.restrictScalars ℚ).map e.toAlgHom
  have : FiniteDimensional ℚ A := LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (T.restrictScalars ℚ) e.toAlgHom).toLinearEquiv
  let F := IntermediateField.normalClosure ℚ A Qbar
  refine ⟨F, normalClosure.is_finiteDimensional ℚ A Qbar,
    normalClosure.normal ℚ A Qbar, ?_, ?_⟩
  · intro x
    apply A.le_normalClosure
    exact ⟨algebraMap K (AlgebraicClosure K) x, T.algebraMap_mem x, rfl⟩
  · intro g h hg hh hagree
    let a : G := galKOfQ e g hg
    let b : G := galKOfQ e h hh
    let d : G := a⁻¹ * b
    have hd : d ∈ T.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      change a.symm (b x) = x
      apply a.injective
      rw [AlgEquiv.apply_symm_apply]
      change galKOfQ e h hh x = galKOfQ e g hg x
      rw [galKOfQ_apply, galKOfQ_apply]
      congr 1
      exact (hagree (e x) (A.le_normalClosure ⟨x, hx, rfl⟩)).symm
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ a))
    obtain ⟨hvt, hva⟩ := Set.mem_iUnion.mp hv
    let u : G := v⁻¹ * a
    have hu : u ∈ (B v).fixingSubgroup := hva
    have hdv : d ∈ (B v).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (show B v ≤ T from Finset.le_sup hvt) hd
    have huv := (B v).fixingSubgroup.mul_mem hu hdv
    have h1 := hlocalB v u hu
    have h2 := hlocalB v (u * d) huv
    have he1 : v * u = a := by simp [u]
    have he2 : v * (u * d) = b := by simp [u, d, mul_assoc]
    rw [he1] at h1
    rw [he2] at h2
    have he := (tlamNbhd K S W α i).sub_mem h1 h2
    change f a - f b ∈ tlamNbhd K S W α i
    convert he using 1
    abel

/-- A finite normal field retaining an arbitrary original basis cochain. -/
def cochainField (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) : IntermediateField ℚ Qbar :=
  (exists_cochainField e i c).choose

instance cochainField_finite (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) :
    FiniteDimensional ℚ (cochainField e i c) := (exists_cochainField e i c).choose_spec.1

instance cochainField_normal (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) :
    Normal ℚ (cochainField e i c) := (exists_cochainField e i c).choose_spec.2.1

theorem cochainField_eval_sub (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
    (c : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) (g h : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (hh : ∀ x : K, h (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (hagree : ∀ x ∈ cochainField e i c, g x = h x) :
    evalOne Lambda (TLam K S W α) (gksOfQ S e g hg) c -
      evalOne Lambda (TLam K S W α) (gksOfQ S e h hh) c ∈ tlamNbhd K S W α i :=
  (exists_cochainField e i c).choose_spec.2.2.2 g h hg hh hagree

end GeneralFields

section FiniteFieldSup

variable {F L ι : Type} [Field F] [Field L] [Algebra F L]

theorem finiteDimensional_field_finset_sup (A : ι → IntermediateField F L)
    (hA : ∀ i, FiniteDimensional F (A i)) (s : Finset ι) :
    FiniteDimensional F ↥(s.sup A : IntermediateField F L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change FiniteDimensional F ↥(⊥ : IntermediateField F L)
      infer_instance
  | insert i s his ih =>
      rw [Finset.sup_insert]
      have : FiniteDimensional F (A i) := hA i
      have : FiniteDimensional F ↥(s.sup A : IntermediateField F L) := ih
      infer_instance

end FiniteFieldSup

section BasisFields

variable {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}
    {α : GKS K S →* Lambdaˣ} [IsContChar α] {n : ℕ}

/-- One compositum retains every original basis cochain and every old stage
field, before any localized coordinate or minimal-model inclusion is applied. -/
def basisFields (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.normalClosure ℚ
    (F i ⊔ Finset.univ.sup (fun j => cochainField e i (z j i)) : IntermediateField ℚ Qbar) Qbar

instance basisFields_finite (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)] (i : ℕ) :
    FiniteDimensional ℚ (basisFields e z F i) := by
  have : FiniteDimensional ℚ ↥(Finset.univ.sup (fun j => cochainField e i (z j i)) :
      IntermediateField ℚ Qbar) :=
    finiteDimensional_field_finset_sup (fun j => cochainField e i (z j i))
      (fun _ => inferInstance) Finset.univ
  unfold basisFields
  exact normalClosure.is_finiteDimensional ℚ _ Qbar

instance basisFields_normal (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) : Normal ℚ (basisFields e z F i) := by
  unfold basisFields
  exact normalClosure.normal ℚ _ Qbar

theorem basisFields_contains_original (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) : F i ≤ basisFields e z F i := by
  unfold basisFields
  exact le_sup_left.trans (IntermediateField.le_normalClosure
    (F i ⊔ Finset.univ.sup (fun j => cochainField e i (z j i))))

theorem basisFields_contains_cochain (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (F : ℕ → IntermediateField ℚ Qbar) (i : ℕ) (j : Fin n) :
    cochainField e i (z j i) ≤ basisFields e z F i := by
  unfold basisFields
  exact (Finset.le_sup (Finset.mem_univ j)).trans
    (le_sup_right.trans (IntermediateField.le_normalClosure
      (F i ⊔ Finset.univ.sup (fun j => cochainField e i (z j i)))))

end BasisFields

section NormalizedLabel

open ZInQ.Contrib.RC53Assist.StagePrimes

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S) {n : ℕ}

/-- A genuine arithmetic label retaining all original integral basis cochains,
without postulating integral stage-cocycle lifts of fibre classes. -/
def basisArithmeticLabel
    (z : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (H : ∀ i, derivativeKernel S e α E i)
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2) : CompatibleArithmeticLabel E K S α :=
  compatibleArithmeticLabelFromImaginaryQuadraticKernel S hS e α E C H
    (basisFields e z F) excl hdegree

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

include hU in
/-- The fixed-decomposition values of every prescribed fibre cycle are its
square-coset values with one common invertible Galois transport. Finite field
matching is done on original integral basis columns; localized coordinates are
applied after the exact integral identities. -/
theorem RetainedEvaluation.label_transport (Q : GCx (ResAt P))
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (coeff : InducedCoefficientDictionary S e α E C U P)
    (H : ∀ i, derivativeKernel S e α E i)
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2) :
    let X := basisArithmeticLabel S hS e α E C D.original H F excl hdegree
    ∃ A : Matrix (Fin 2) (Fin 2) (ResAt P), A.det ≠ 0 ∧
      ∀ a : LinearMap.ker (Q.d 1 2 rfl),
        basisValue P U D.original X.label.frob (D.coordinates a.val) =
          A *ᵥ (D.one a.val (baseSequenceInclusion e (kernelSquareBase S e α E C H))).1 := by
  let X := basisArithmeticLabel S hS e α E C D.original H F excl hdegree
  choose g hg using X.frobMatch
  let γ : ℕ → rationalBaseGroup e := fun i => baseLift S e (g i)
  let σ : ℕ → rationalBaseGroup e := fun i => ⟨X.primes.frob i * X.primes.frob i, X.hK i⟩
  let r := kernelSquareBase S e α E C H
  have hγ : baseSequenceRestriction S e γ = g := funext (fun i => baseLift_spec S e (g i))
  have hσ : baseSequenceRestriction S e σ = ratSqFrob E e C X.primes X.hK := rfl
  have hr : baseSequenceRestriction S e r = kernelSquare S e α E C H := rfl
  have hconj : baseSequenceRestriction S e (γ * σ * γ⁻¹) = X.label.frob := by
    funext i
    change baseRestriction S e (γ i * σ i * (γ i)⁻¹) = X.label.frob i
    rw [map_mul, map_mul, map_inv]
    change baseRestriction S e (baseLift S e (g i)) *
      ratSqFrob E e C X.primes X.hK i * (baseRestriction S e (baseLift S e (g i)))⁻¹ = _
    rw [baseLift_spec]
    exact (hg i).symm
  have hAσ : ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
      (baseSequenceRestriction S e σ i)) = 1 :=
    actionMatrix_limit_one (S := S) (α := α) (E := E) (baseSequenceRestriction S e σ) hU
      (fun i x => twisted_congr_ratSqFrob E e C X.primes X.hK X.hh i (X.character i) x)
  have hsproj (x : FibrePair P) : (baseSequenceInclusion e σ • x).1 = x.1 := by
    rw [coeff.restriction, hAσ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hcol (j : Fin n) :
      integralTateValue U (baseSequenceRestriction S e σ) (D.original j) =
        integralTateValue U (baseSequenceRestriction S e r) (D.original j) := by
    apply integralTateValue_eq_of_sub (S := S) (α := α) (E := E)
      (baseSequenceRestriction S e σ) (baseSequenceRestriction S e r) hU (D.original j)
    intro i
    exact cochainField_eval_sub e i (D.original j i)
      (X.primes.frob i * X.primes.frob i)
      ((ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i) *
        (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i))
      (X.hK i) (kernel_cosetSquare_fixesK S e α E C i (H i))
      (fun x hx => derivativePrimes_square_agree E
        (F := basisFields e D.original F) X.primes i x
        (basisFields_contains_cochain e D.original F i j hx))
  have hvals (w : Fin n → ResAt P) :
      basisValue P U D.original (baseSequenceRestriction S e σ) w =
        basisValue P U D.original (baseSequenceRestriction S e r) w := by
    unfold basisValue
    apply Finset.sum_congr rfl
    intro j _
    rw [hcol j]
  let A := (ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
    (baseSequenceRestriction S e γ i))).map (algebraMap Lambda (ResAt P))
  have hγproj (x : FibrePair P) : (baseSequenceInclusion e γ • x).1 = A *ᵥ x.1 :=
    coeff.restriction γ x
  refine ⟨A, tlamActionMatrix_limit_det_ne_zero (W := E⁄K) (α := α)
    (baseSequenceRestriction S e γ) U P, ?_⟩
  intro a
  have hca := RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
    (U := U) (P := P) D a
  have he : (D.one a.val (baseSequenceInclusion e (γ * σ * γ⁻¹))).1 =
      A *ᵥ (D.one a.val (baseSequenceInclusion e σ)).1 := by
    rw [map_mul, map_mul, map_inv]
    exact projected_cocycle_conjugate hca
      (LinearMap.fst (ResAt P) (Fin 2 → ResAt P) (Fin 2 → ResAt P))
      (baseSequenceInclusion e γ) (baseSequenceInclusion e σ) A hγproj hsproj
  calc
    basisValue P U D.original X.label.frob (D.coordinates a.val) =
        (D.one a.val (baseSequenceInclusion e (γ * σ * γ⁻¹))).1 := by
      rw [D.projection, hconj]
    _ = A *ᵥ (D.one a.val (baseSequenceInclusion e σ)).1 := he
    _ = A *ᵥ basisValue P U D.original (baseSequenceRestriction S e σ) (D.coordinates a.val) := by
      rw [D.projection]
    _ = A *ᵥ basisValue P U D.original (baseSequenceRestriction S e r) (D.coordinates a.val) := by
      rw [hvals]
    _ = A *ᵥ (D.one a.val (baseSequenceInclusion e r)).1 := by rw [D.projection]

end NormalizedLabel

section ArithmeticProducer

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]
    [∀ i, FiniteDimensional ℚ (B i)]
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2)

include hU hP hne in
/-- The complete arithmetic detection producer on the retained route. It
chooses a partner through the prescribed nonzero fibre class, produces genuine
kernel representatives, constructs their actual inert prime label, and proves
its normalized detecting determinant. Representatives are nonidentity on an
ultrafilter-large set, as required for detection at the inner limit. -/
theorem produce_arithmetic_detection {n : ℕ} (Q : GCx (ResAt P))
    [FiniteDimensional (ResAt P) (Q.toCC.homology 1)]
    (coeff : InducedCoefficientDictionary S e α E C U P)
    (scalar : ArithmeticCommonScalar S e α E P B)
    (span : CoefficientSpanWitness P)
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) (Q.toCC.homology 1)) :
    ∃ b : LinearMap.ker (Q.d 1 2 rfl), ∃ h : arithmeticSequenceKernel E S e α B,
      LinearIndependent (ResAt P) ![clsAt Q 1 2 rfl a, clsAt Q 1 2 rfl b] ∧
      let H := arithmeticKernelFamily E S e α h
      let X := basisArithmeticLabel S hS e α E C D.original H (fun i => F i ⊔ B i) excl hdegree
      (∀ᶠ i in (U : Filter ℕ), (H i : GalQ) ≠ 1) ∧
      (Matrix.of ![basisValue P U D.original X.label.frob (D.coordinates a.val),
        basisValue P U D.original X.label.frob (D.coordinates b.val)]).det ≠ 0 := by
  obtain ⟨b, h, hab, hdet⟩ := produce_kernel_detection
    (S := S) (e := e) (α := α) (E := E) (C := C) (U := U) (hU := hU)
    (P := P) (hP := hP) (hne := hne) (B := B) Q coeff scalar span D a ha hdim
  let H := arithmeticKernelFamily E S e α h
  let r := kernelSquareBase S e α E C H
  let X := basisArithmeticLabel S hS e α E C D.original H (fun i => F i ⊔ B i) excl hdegree
  change (Matrix.of ![(D.one a.val (baseSequenceInclusion e r)).1,
    (D.one b.val (baseSequenceInclusion e r)).1]).det ≠ 0 at hdet
  have hca := RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
    (U := U) (P := P) D a
  have hnontriv : ∀ᶠ i in (U : Filter ℕ), (H i : GalQ) ≠ 1 := by
    rcases U.mem_or_compl_mem {i | (H i : GalQ) = 1} with hone | hnot
    · have hevent : ∀ᶠ i in (U : Filter ℕ), baseSequenceRestriction S e r i = 1 := by
        filter_upwards [hone] with i hi
        have hri : r i = (1 : rationalBaseGroup e) := by
          apply Subtype.ext
          change (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i) *
            (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C * H i) = 1
          rw [hi, mul_one, ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self]
        change baseRestriction S e (r i) = 1
        rw [hri, map_one]
      have hv := basisValue_eq_of_eventual_eq (S := S) (α := α) (E := E) P U D.original
        (baseSequenceRestriction S e r) (fun _ => 1) hevent (D.coordinates a.val)
      have hzero : basisValue P U D.original (fun _ => 1) (D.coordinates a.val) = 0 := by
        have hz := congrArg Prod.fst (groupCohomology.map_one_of_isCocycle₁ hca)
        have hp := D.projection a.val (1 : ℕ → rationalBaseGroup e)
        rw [map_one, map_one] at hp
        exact hp.symm.trans hz
      have ha0 : (D.one a.val (baseSequenceInclusion e r)).1 = 0 := by
        rw [D.projection, hv, hzero]
      rw [ha0] at hdet
      simp [Matrix.det_fin_two] at hdet
    · exact hnot
  obtain ⟨A, hA, ht⟩ := RetainedEvaluation.label_transport
    (S := S) (hS := hS) (e := e) (α := α) (E := E) (C := C) (U := U) (hU := hU)
    (P := P) (Q := Q) (D := D) (coeff := coeff) (H := H)
    (F := fun i => F i ⊔ B i) (excl := excl) (hdegree := hdegree)
  have hdetX : (Matrix.of ![basisValue P U D.original X.label.frob (D.coordinates a.val),
      basisValue P U D.original X.label.frob (D.coordinates b.val)]).det ≠ 0 := by
    rw [ht a, ht b, detectionDet_transport]
    exact mul_ne_zero hdet hA
  exact ⟨b, h, hab, hnontriv, hdetX⟩

/-- The derived arithmetic output. Its detection proof is an output of the
producer, not a hypothesis of that producer. -/
structure ArithmeticDetection {n : ℕ} (Q : GCx (ResAt P))
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (a : LinearMap.ker (Q.d 1 2 rfl)) where
  partner : LinearMap.ker (Q.d 1 2 rfl)
  kernel : arithmeticSequenceKernel E S e α B
  independent : LinearIndependent (ResAt P) ![clsAt Q 1 2 rfl a, clsAt Q 1 2 rfl partner]
  nontrivial : ∀ᶠ i in (U : Filter ℕ), (arithmeticKernelFamily E S e α kernel i : GalQ) ≠ 1
  detecting :
    let H := arithmeticKernelFamily E S e α kernel
    let X := basisArithmeticLabel S hS e α E C D.original H (fun i => F i ⊔ B i) excl hdegree
    (Matrix.of ![basisValue P U D.original X.label.frob (D.coordinates a.val),
      basisValue P U D.original X.label.frob (D.coordinates partner.val)]).det ≠ 0

include hU hP hne in
/-- Construction of the detecting arithmetic label and partner from the
prescribed fibre class and the named arithmetic and cochain-comparison inputs. -/
def makeArithmeticDetection {n : ℕ} (Q : GCx (ResAt P))
    [FiniteDimensional (ResAt P) (Q.toCC.homology 1)]
    (coeff : InducedCoefficientDictionary S e α E C U P)
    (scalar : ArithmeticCommonScalar S e α E P B)
    (span : CoefficientSpanWitness P)
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) (Q.toCC.homology 1)) :
    ArithmeticDetection S hS e α E C U P B F excl hdegree Q D a := by
  let hp := produce_arithmetic_detection
    (S := S) (hS := hS) (e := e) (α := α) (E := E) (C := C)
    (U := U) (hU := hU) (P := P) (hP := hP) (hne := hne) (B := B) (F := F)
    (excl := excl) (hdegree := hdegree) Q coeff scalar span D a ha hdim
  let b := hp.choose
  let h := hp.choose_spec.choose
  have ht := hp.choose_spec.choose_spec
  exact ⟨b, h, ht.1, ht.2.1, ht.2.2⟩

open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Wiring (resAt)

include hU hP hne in
/-- The retained nonquadratic consumer with its determinant assumption
discharged by the producer. The localization identity uses the original
integral basis and applies the minimal-model coordinates after the limit.
Duality and the side-to-stage comparisons remain the consumer's standard inputs. -/
def producedLimitNonquadStep {n : ℕ} (Q : GCx (ResAt P))
    [FiniteDimensional (ResAt P) (Q.toCC.homology 1)]
    (coeff : InducedCoefficientDictionary S e α E C U P)
    (scalar : ArithmeticCommonScalar S e α E P B)
    (span : CoefficientSpanWitness P)
    (D : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) (Q.toCC.homology 1)) :
    let r := makeArithmeticDetection S hS e α E C U hU P hP hne B F excl hdegree
      Q coeff scalar span D a ha hdim
    let H := arithmeticKernelFamily E S e α r.kernel
    let X := basisArithmeticLabel S hS e α E C D.original H (fun i => F i ⊔ B i) excl hdegree
    ∀ (res : GHom Q (splitLocalComplex (ResAt P)))
      (hloc : ∀ x : LinearMap.ker (Q.d 1 2 rfl),
        res.f 1 1 rfl x.val = (basisValue P U D.original X.label.frob (D.coordinates x.val), 0))
      {L : Type} [Field L] {ι : Localization.AtPrime P →+* L}
      (S₀ S₁ : TwoTermStage ι) (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P))
      (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
      (hdual : LimitSwitchDuality Q res ε σ J hε hσ hJ)
      (φ : (selCx (finiteLimitSide Q res).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₀)
      (φ' : (selCx (singularLimitSide Q res).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₁),
      QuasiNonquadStep (resAt P) S₀ S₁ := by
  dsimp only
  let r := makeArithmeticDetection S hS e α E C U hU P hP hne B F excl hdegree
    Q coeff scalar span D a ha hdim
  intro res hloc L _ ι S₀ S₁ ε σ J hε hσ hJ hdual φ φ'
  exact detectedLimitNonquadStep Q res (resAt P) S₀ S₁ ε σ J hε hσ hJ hdual
    a.property r.partner.property (hloc a) (hloc r.partner) r.detecting φ φ'

end ArithmeticProducer

end ZInQ.Contrib.RC53Assist.Detection
