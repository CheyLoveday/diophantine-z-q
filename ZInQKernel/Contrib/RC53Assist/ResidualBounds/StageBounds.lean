import ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidual
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith

/-!
# Cohomological ranges and residual ranks of finite Selmer complexes

The Selmer complex has terms `Gⁿ × Uⁿ × Lⁿ⁻¹`. Thus global and local
cohomological dimension two, together with conditions supported in degrees
zero through two, give a cohomological range of zero through three.

The residue field of every positive coefficient stage is the field with two
elements. Reduction of the coefficient module identifies it with the fixed
two-torsion representation; the scalar character disappears upon reduction.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidualBounds

open CategoryTheory IsLocalRing NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.ResidualFiniteness
open ZInQ.Manuscript.RC.Limits (subquotientOf residualCohomologyAt)
open scoped TensorProduct

local instance scalarEquiv_forward {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e

local instance scalarEquiv_backward {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := by
  simpa only [RingEquiv.symm_symm] using RingHomInvPair.of_ringEquiv e.symm

section Homology

variable {R : Type} [CommRing R]

/-- Cohomology is the quotient of cocycles by coboundaries. -/
def homologySubquotEquiv (C : GCx R) (n : ℤ) :
    C.toCC.homology n ≃ₗ[R]
      subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl) := by
  have hr : LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).moduleCatToCycles =
      (LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).f.hom).comap
        (LinearMap.ker (C.toCC.sc' (n - 1) n (n + 1)).g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  have e := ((C.toCC.homologyIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).toLinearEquiv.trans
    (C.toCC.sc' (n - 1) n (n + 1)).moduleCatHomologyIso.toLinearEquiv).trans
      (Submodule.quotEquivOfEq _ _ hr)
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) :=
    LinearMap.ext fun x => GCx.toCC_d_hom C (n - 1) n (by omega) x
  have hg : (C.toCC.sc' (n - 1) n (n + 1)).g.hom = C.d n (n + 1) rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom C n (n + 1) rfl x
  change C.toCC.homology n ≃ₗ[R]
    subquotientOf (C.toCC.sc' (n - 1) n (n + 1)).f.hom
      (C.toCC.sc' (n - 1) n (n + 1)).g.hom at e
  rw [hf, hg] at e
  exact e

/-- The residual cohomology used by the finite free model is the cohomology
of the residue-field base change. -/
def residualHomologyEquiv [IsLocalRing R] (C : GCx R) (n : ℤ) :
    (gcxBaseChange (ResidueField R) C).toCC.homology n ≃ₗ[ResidueField R]
      residualCohomologyAt C n :=
  homologySubquotEquiv (gcxBaseChange (ResidueField R) C) n

/-- A zero term has zero cohomology, over any coefficient ring. -/
theorem homology_subsingleton_of_term (C : GCx R) (n : ℤ)
    (h : Subsingleton (C.X n)) : Subsingleton (C.toCC.homology n) := by
  have := h
  have : Subsingleton
      (subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)) := inferInstance
  exact (homologySubquotEquiv C n).injective.subsingleton

/-- Vanishing of cohomology means that every cocycle is a coboundary. -/
theorem exists_primitive_of_subsingleton (C : GCx R) (n : ℤ)
    (h : Subsingleton (C.toCC.homology n)) (x : C.X n)
    (hx : C.d n (n + 1) rfl x = 0) :
    ∃ y : C.X (n - 1), C.d (n - 1) n (by omega) y = x := by
  have := h
  have : Subsingleton
      (subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)) :=
    (homologySubquotEquiv C n).symm.injective.subsingleton
  have hz : (Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker (C.d n (n + 1) rfl)) :
      subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)) = 0 :=
    Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).1 hz

/-- If all cocycles have primitives, cohomology vanishes. -/
theorem homology_subsingleton_of_primitives (C : GCx R) (n : ℤ)
    (h : ∀ x : C.X n, C.d n (n + 1) rfl x = 0 →
      ∃ y : C.X (n - 1), C.d (n - 1) n (by omega) y = x) :
    Subsingleton (C.toCC.homology n) := by
  let Q := subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)
  have hz : ∀ z : Q, z = 0 := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).2 (h x.1 x.2)
  have : Subsingleton Q := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact (homologySubquotEquiv C n).injective.subsingleton

/-- Exact sequences with zero outer terms have zero middle term. -/
theorem exact_subsingleton_middle {E : ShortComplex (ModuleCat.{0} R)} (hE : E.Exact)
    (h₁ : Subsingleton E.X₁) (h₃ : Subsingleton E.X₃) : Subsingleton E.X₂ := by
  have := h₁
  have := h₃
  rw [ShortComplex.moduleCat_exact_iff] at hE
  have hz : ∀ x : E.X₂, x = 0 := by
    intro x
    obtain ⟨y, hy⟩ := hE x (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Products preserve vanishing of cohomology. -/
theorem piCx_homology_subsingleton {ι : Type} (Cs : ι → GCx R) (n : ℤ)
    (h : ∀ v, Subsingleton ((Cs v).toCC.homology n)) :
    Subsingleton ((piCx Cs).toCC.homology n) := by
  apply homology_subsingleton_of_primitives
  intro x hx
  have hv : ∀ v, (Cs v).d n (n + 1) rfl (x v) = 0 := by
    intro v
    exact (congrFun hx v : (Cs v).d n (n + 1) rfl (x v) = 0)
  choose y hy using fun v => exists_primitive_of_subsingleton (Cs v) n (h v) (x v) (hv v)
  exact ⟨y, funext hy⟩

/-- A shift down by one raises the cohomological degree by one. -/
theorem shiftDown_homology_subsingleton (L : GCx R) (n : ℤ)
    (h : Subsingleton (L.toCC.homology (n - 1))) :
    Subsingleton ((shiftDown L).toCC.homology n) := by
  apply homology_subsingleton_of_primitives
  intro x hx
  have hx' : L.d (n - 1) (n - 1 + 1) rfl x = 0 := by
    change -(L.d (n - 1) (n + 1 - 1) (by omega) x) = 0 at hx
    have hneg := neg_eq_zero.mp hx
    have hker := ker_d_congr L (i := n - 1) (j := n + 1 - 1)
      (j' := n - 1 + 1) (by omega) rfl
    change x ∈ LinearMap.ker (L.d (n - 1) (n - 1 + 1) rfl)
    rw [← hker]
    exact hneg
  obtain ⟨y, hy⟩ := exists_primitive_of_subsingleton L (n - 1) h x hx'
  refine ⟨-y, ?_⟩
  change -(L.d (n - 1 - 1) (n - 1) (by omega) (-y)) = x
  rw [map_neg, neg_neg, hy]

/-- The Selmer cone vanishes whenever its global, condition, and shifted
local cohomology all vanish. -/
theorem selCx_homology_subsingleton (D : SelData R) (n : ℤ)
    (hG : Subsingleton (D.G.toCC.homology n))
    (hU : Subsingleton (D.U.toCC.homology n))
    (hL : Subsingleton (D.L.toCC.homology (n - 1))) :
    Subsingleton ((selCx D).toCC.homology n) := by
  have hC : Subsingleton ((locCx D).toCC.homology n) :=
    exact_subsingleton_middle ((coneSES_shortExact (negι D)).homology_exact₂ n)
      (shiftDown_homology_subsingleton D.L n hL) hU
  exact exact_subsingleton_middle ((sesTop_shortExact D).homology_exact₂ n) hC hG

/-- A Selmer datum with global and local range `[0,2]` and condition range
`[0,2]` has Selmer cohomology in `[0,3]`. -/
theorem selCx_homology_range (D : SelData R)
    (hG : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (D.G.toCC.homology n))
    (hL : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (D.L.toCC.homology n))
    (hU : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (D.U.toCC.homology n)) :
    ∀ n : ℤ, n < 0 ∨ 3 < n → Subsingleton ((selCx D).toCC.homology n) := by
  intro n hn
  apply selCx_homology_subsingleton D n
  · exact hG n (by omega)
  · exact hU n (by omega)
  · exact hL (n - 1) (by omega)

end Homology

section ResidueField

open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.GenuineInst (resEps)

/-- The coefficient residue map is onto the field with two elements. -/
theorem stageResidue_surjective (i : ℕ) [NeZero i] : Function.Surjective (resEps i) := by
  intro z
  rcases zmod_two_eq_zero_or_one z with rfl | rfl
  · exact ⟨0, map_zero _⟩
  · exact ⟨1, map_one _⟩

/-- The residue field of a positive stage is canonically the field with two elements. -/
def stageResidueFieldEquiv (i : ℕ) [NeZero i] : ResidueField (Acoef i) ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal (resEps i)
    (stageResidue_surjective i)).symm).trans
      ((resEps i).quotientKerEquivOfSurjective (stageResidue_surjective i))

/-- The residue-field identification commutes with the coefficient residue map. -/
theorem stageResidueFieldEquiv_residue (i : ℕ) [NeZero i] (a : Acoef i) :
    stageResidueFieldEquiv i (residue (Acoef i) a) = resEps i a := rfl

/-- There are only zero and one in the stage residue field. -/
theorem stageResidueField_zero_or_one (i : ℕ) [NeZero i] (c : ResidueField (Acoef i)) :
    c = 0 ∨ c = 1 := by
  rcases zmod_two_eq_zero_or_one (stageResidueFieldEquiv i c) with h | h
  · exact Or.inl ((stageResidueFieldEquiv i).injective (h.trans (map_zero _).symm))
  · exact Or.inr ((stageResidueFieldEquiv i).injective (h.trans (map_one _).symm))

end ResidueField

section Semilinear

variable {R S : Type} [CommRing R] [CommRing S]

/-- A scalar-compatible isomorphism of complexes over isomorphic coefficient rings. -/
structure ComplexScalarEquiv (e : R ≃+* S) (C : GCx R) (D : GCx S) where
  component : ∀ n : ℤ,
    LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S) (C.X n) (D.X n)
  comm : ∀ (a b : ℤ) (h : a + 1 = b) (x : C.X a),
    component b (C.d a b h x) = D.d a b h (component a x)

variable {e : R ≃+* S} {C : GCx R} {D : GCx S}

/-- The induced scalar-compatible isomorphism of cocycles. -/
def ComplexScalarEquiv.cycles (E : ComplexScalarEquiv e C D) (n : ℤ) :
    LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S)
      (LinearMap.ker (C.d n (n + 1) rfl))
      (LinearMap.ker (D.d n (n + 1) rfl)) where
  toFun x := ⟨E.component n x.1, by
    change D.d n (n + 1) rfl (E.component n x.1) = 0
    rw [← E.comm, x.2, map_zero]⟩
  invFun y := ⟨(E.component n).symm y.1, by
    apply (E.component (n + 1)).injective
    rw [map_zero, E.comm, LinearEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext ((E.component n).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((E.component n).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext ((E.component n).map_smulₛₗ c x.1)

/-- Cocycles modulo coboundaries are preserved by a scalar-compatible complex isomorphism. -/
theorem ComplexScalarEquiv.map_boundaries (E : ComplexScalarEquiv e C D) (n : ℤ) :
    ((LinearMap.range (C.d (n - 1) n (by omega))).comap
      (LinearMap.ker (C.d n (n + 1) rfl)).subtype).map (E.cycles n).toLinearMap =
    (LinearMap.range (D.d (n - 1) n (by omega))).comap
      (LinearMap.ker (D.d n (n + 1) rfl)).subtype := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, hy⟩, hxz⟩
    refine ⟨E.component (n - 1) y, ?_⟩
    rw [← E.comm, hy]
    exact congrArg Subtype.val hxz
  · rintro ⟨y, hy⟩
    refine ⟨(E.cycles n).symm z, ?_, (E.cycles n).apply_symm_apply z⟩
    refine ⟨(E.component (n - 1)).symm y, ?_⟩
    apply (E.component n).injective
    rw [E.comm, LinearEquiv.apply_symm_apply, hy]
    exact ((E.component n).apply_symm_apply z.1).symm

/-- The scalar-compatible cohomology isomorphism induced by a complex isomorphism. -/
def ComplexScalarEquiv.homology (E : ComplexScalarEquiv e C D) (n : ℤ) :
    LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S)
      (C.toCC.homology n) (D.toCC.homology n) :=
  (homologySubquotEquiv C n).trans
    ((Submodule.Quotient.equiv _ _ (E.cycles n) (E.map_boundaries n)).trans
      (homologySubquotEquiv D n).symm)

/-- Scalar-compatible cohomology isomorphisms preserve finite ranks. -/
theorem ComplexScalarEquiv.finrank_homology (E : ComplexScalarEquiv e C D) (n : ℤ) :
    Module.finrank R (C.toCC.homology n) = Module.finrank S (D.toCC.homology n) := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv e (E.homology n).toAddEquiv e.bijective
    (fun c x => (E.homology n).map_smulₛₗ c x)

/-- A scalar-compatible complex isomorphism transports vanishing. -/
theorem ComplexScalarEquiv.subsingleton_homology (E : ComplexScalarEquiv e C D) (n : ℤ)
    (h : Subsingleton (D.toCC.homology n)) : Subsingleton (C.toCC.homology n) := by
  have := h
  exact (E.homology n).injective.subsingleton

/-- Composing a scalar-compatible comparison with a chain isomorphism. -/
def ComplexScalarEquiv.precompose {C₀ : GCx R} (E : ComplexScalarEquiv e C D)
    (f : GHom C₀ C) (hf : ∀ n, Function.Bijective (f.f n n rfl)) :
    ComplexScalarEquiv e C₀ D where
  component n := (LinearEquiv.ofBijective (f.f n n rfl) (hf n)).trans (E.component n)
  comm a b h x := by
    change E.component b (f.f b b rfl (C₀.d a b h x)) = _
    rw [f.comm a b a b rfl h h rfl x]
    exact E.comm a b h _

end Semilinear

section NaturalDegrees

variable {R : Type} [CommRing R]

/-- The positive-degree short complexes of a complex and its extension by zero agree. -/
def natPositiveShortComplexIso (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (natCx C).toCC.sc' (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) ≅ C.sc' n (n + 1) (n + 2) :=
  ShortComplex.isoMk (Iso.refl (C.X n)) (Iso.refl (C.X (n + 1))) (Iso.refl (C.X (n + 2)))
    (by
      ext x
      exact (GCx.toCC_d_hom (natCx C) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega) x).symm)
    (by
      ext x
      exact (GCx.toCC_d_hom (natCx C) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)
        (by omega) x).symm)

/-- Extension by zero does not change positive-degree cohomology. -/
def natPositiveHomologyIso (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (natCx C).toCC.homology ((n + 1 : ℕ) : ℤ) ≅ C.homology (n + 1) :=
  (natCx C).toCC.homologyIsoSc' (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)
    (by simp) (by simp; omega) ≪≫
      ShortComplex.homologyMapIso (natPositiveShortComplexIso C n) ≪≫
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).symm

/-- The extension by zero has zero terms in negative degrees. -/
theorem natCx_term_subsingleton_neg (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℤ)
    (hn : n < 0) : Subsingleton ((natCx C).X n) := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast] at hn
    omega
  | negSucc m => exact inferInstanceAs (Subsingleton PUnit)

/-- Negative-degree cohomology of an extension by zero vanishes. -/
theorem natCx_homology_subsingleton_neg (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℤ)
    (hn : n < 0) : Subsingleton ((natCx C).toCC.homology n) :=
  homology_subsingleton_of_term _ n (natCx_term_subsingleton_neg C n hn)

end NaturalDegrees

section CoefficientScalars

variable {R S : Type} [CommRing R] [CommRing S] (eR : R ≃+* S)
  {X : Type} [TopologicalSpace X]
  {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (eM : LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S) M N)

/-- Scalar-compatible changes of coefficients act pointwise on locally constant functions. -/
def locallyConstantScalarEquiv :
    LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S)
      (LocallyConstant X M) (LocallyConstant X N) where
  toFun f := f.map eM
  invFun f := f.map eM.symm
  left_inv f := LocallyConstant.ext fun x => eM.symm_apply_apply (f x)
  right_inv f := LocallyConstant.ext fun x => eM.apply_symm_apply (f x)
  map_add' f g := LocallyConstant.ext fun x => map_add eM (f x) (g x)
  map_smul' c f := LocallyConstant.ext fun x => eM.map_smulₛₗ c (f x)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G M] [SMulCommClass G R M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- A scalar-compatible coefficient isomorphism induces the pointwise cochain isomorphism. -/
def cochainScalarEquiv (n : ℕ) :
    LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S)
      ((contCochains R G M).X n) ((contCochains S G N).X n) :=
  (contCochainLCEquiv R G M n).trans
    ((locallyConstantScalarEquiv (X := Fin n → G) eR eM).trans
      (contCochainLCEquiv S G N n).symm)

/-- The cochain comparison is pointwise application of the coefficient comparison. -/
theorem cochainScalarEquiv_apply (n : ℕ) (f : (contCochains R G M).X n) (x : Fin n → G) :
    cFun (cochainScalarEquiv (G := G) eR eM n f) x = eM (cFun f x) := rfl

variable (heM : ∀ (g : G) (m : M), eM (g • m) = g • eM m)

include heM in
/-- Equivariant changes of coefficients commute with the cochain differentials. -/
theorem cochainScalarEquiv_comm (n : ℕ) (f : (contCochains R G M).X n) :
    cochainScalarEquiv (G := G) eR eM (n + 1) (((contCochains R G M).d n (n + 1)).hom f) =
      ((contCochains S G N).d n (n + 1)).hom (cochainScalarEquiv (G := G) eR eM n f) := by
  apply Subtype.ext
  funext x
  change eM (asFun R G M ((contSubCx R G M).el
      (((contCochains R G M).d n (n + 1)).hom f)) x) =
    asFun S G N ((contSubCx S G N).el
      (((contCochains S G N).d n (n + 1)).hom (cochainScalarEquiv (G := G) eR eM n f))) x
  rw [contCochains_d_apply, contCochains_d_apply, map_add, map_sum]
  congr 1
  · exact heM (x 0) _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [eM.map_smulₛₗ, map_pow, map_neg, map_one]
    rfl

/-- The cochain comparison on complexes extended by zero. -/
def natCochainScalarComponent : ∀ n : ℤ,
    LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S)
      ((natCx (contCochains R G M)).X n) ((natCx (contCochains S G N)).X n)
  | Int.ofNat n => cochainScalarEquiv (G := G) eR eM n
  | Int.negSucc _ =>
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim (α := PUnit.{1}) _ _
      right_inv := fun _ => Subsingleton.elim (α := PUnit.{1}) _ _
      map_add' := fun _ _ => Subsingleton.elim (α := PUnit.{1}) _ _
      map_smul' := fun _ _ => Subsingleton.elim (α := PUnit.{1}) _ _ }

include heM in
/-- A coefficient isomorphism induces an isomorphism of the full integer-indexed complexes. -/
def natCochainScalarEquiv : ComplexScalarEquiv eR (natCx (contCochains R G M))
    (natCx (contCochains S G N)) where
  component := natCochainScalarComponent (G := G) eR eM
  comm a b h f := by
    cases a with
    | negSucc a =>
      change natCochainScalarComponent (G := G) eR eM b 0 = _
      rw [map_zero]
      rfl
    | ofNat a =>
      cases b with
      | negSucc b => exact False.elim (ofNat_add_one_ne_negSucc a b h)
      | ofNat b =>
        have hab : b = a + 1 := by
          simp only [Int.ofNat_eq_natCast] at h
          omega
        subst b
        exact cochainScalarEquiv_comm eR eM heM a f

end CoefficientScalars

section BaseChangedCochains

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
  {F : Type} [CommRing F] (eR : B ≃+* F)
  (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (M : Type) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  {N : Type} [AddCommGroup N] [Module F N] [DistribMulAction G N] [SMulCommClass G F N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]
  (eM : LinearEquiv (σ' := (eR.symm : F →+* B)) (eR : B →+* F) (BCoef A B M) N)
  (heM : ∀ (g : G) (x : BCoef A B M), eM (g • x) = g • eM x)

/-- Tensoring continuous cochains and identifying the residual coefficients is a complex isomorphism. -/
def baseChangedCochainsScalarEquiv :
    ComplexScalarEquiv eR (gcxBaseChange B (natCx (contCochains A G M)))
      (natCx (contCochains F G N)) :=
  (natCochainScalarEquiv (G := G) eR eM heM).precompose
    (natCochainsBaseChangeHom A B G M) (natCochainsBaseChangeHom_bijective A B G M)

/-- On pure tensors the cochain comparison applies the coefficient comparison pointwise. -/
theorem baseChangedCochainsScalarEquiv_tmul (n : ℕ) (b : B) (f : (contCochains A G M).X n)
    (x : Fin n → G) :
    cFun ((baseChangedCochainsScalarEquiv A B eR G M eM heM).component n (b ⊗ₜ[A] f)) x =
      eM (bcTmul A B M b (cFun f x)) := rfl

end BaseChangedCochains

section ScalarProducts

variable {R S : Type} [CommRing R] [CommRing S] (eR : R ≃+* S)

/-- Products of scalar-compatible module isomorphisms. -/
def scalarProdEquiv {M₁ M₂ N₁ N₂ : Type} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₁] [Module S N₁]
    [AddCommGroup N₂] [Module S N₂]
    (e₁ : LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S) M₁ N₁)
    (e₂ : LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S) M₂ N₂) :
    LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S) (M₁ × M₂) (N₁ × N₂) where
  toFun x := (e₁ x.1, e₂ x.2)
  invFun y := (e₁.symm y.1, e₂.symm y.2)
  left_inv x := Prod.ext (e₁.symm_apply_apply x.1) (e₂.symm_apply_apply x.2)
  right_inv y := Prod.ext (e₁.apply_symm_apply y.1) (e₂.apply_symm_apply y.2)
  map_add' x y := Prod.ext (map_add e₁ x.1 y.1) (map_add e₂ x.2 y.2)
  map_smul' c x := Prod.ext (e₁.map_smulₛₗ c x.1) (e₂.map_smulₛₗ c x.2)

/-- Products of scalar-compatible complex isomorphisms. -/
def piScalarEquiv {ι : Type} {Cs : ι → GCx R} {Ds : ι → GCx S}
    (E : ∀ v, ComplexScalarEquiv eR (Cs v) (Ds v)) :
    ComplexScalarEquiv eR (piCx Cs) (piCx Ds) where
  component n :=
    { toFun x := fun v => (E v).component n (x v)
      invFun y := fun v => ((E v).component n).symm (y v)
      left_inv x := funext fun v => ((E v).component n).symm_apply_apply (x v)
      right_inv y := funext fun v => ((E v).component n).apply_symm_apply (y v)
      map_add' x y := funext fun v => map_add ((E v).component n) (x v) (y v)
      map_smul' c x := funext fun v => ((E v).component n).map_smulₛₗ c (x v) }
  comm a b h x := funext fun v => (E v).comm a b h (x v)

/-- Isomorphisms of the three complexes and of their localization squares
induce an isomorphism of Selmer complexes. -/
def selmerScalarEquiv {D₁ : SelData R} {D₂ : SelData S}
    (EG : ComplexScalarEquiv eR D₁.G D₂.G) (EU : ComplexScalarEquiv eR D₁.U D₂.U)
    (EL : ComplexScalarEquiv eR D₁.L D₂.L)
    (hres : ∀ a b (h : a = b) (x : D₁.G.X a),
      EL.component b (D₁.res.f a b h x) = D₂.res.f a b h (EG.component a x))
    (hι : ∀ a b (h : a = b) (x : D₁.U.X a),
      EL.component b (D₁.ι.f a b h x) = D₂.ι.f a b h (EU.component a x)) :
    ComplexScalarEquiv eR (selCx D₁) (selCx D₂) where
  component n := scalarProdEquiv eR (EG.component n)
    (scalarProdEquiv eR (EU.component n) (EL.component (n - 1)))
  comm a b h x := by
    obtain ⟨g, u, l⟩ := x
    change (EG.component b (D₁.G.d a b h g), EU.component b (D₁.U.d a b h u),
      EL.component (b - 1) (D₁.res.f a (b - 1) (by omega) g -
        D₁.ι.f a (b - 1) (by omega) u - D₁.L.d (a - 1) (b - 1) (by omega) l)) =
      (D₂.G.d a b h (EG.component a g), D₂.U.d a b h (EU.component a u),
        D₂.res.f a (b - 1) (by omega) (EG.component a g) -
          D₂.ι.f a (b - 1) (by omega) (EU.component a u) -
          D₂.L.d (a - 1) (b - 1) (by omega) (EL.component (a - 1) l))
    refine Prod.ext (EG.comm a b h g) (Prod.ext (EU.comm a b h u) ?_)
    rw [map_sub, map_sub, hres a (b - 1) (by omega) g, hι a (b - 1) (by omega) u,
      EL.comm (a - 1) (b - 1) (by omega) l]

end ScalarProducts

section ActualResidualCoefficients

open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.GenuineInst

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K)

/-- The fixed residual coefficient module is the two-torsion representation. -/
def TwoTorsionResidual : Type := TorsS K S W (2 : ℤ)

instance : AddCommGroup (TwoTorsionResidual K S W) :=
  inferInstanceAs (AddCommGroup (TorsS K S W (2 : ℤ)))

instance : Module (ZMod 2) (TwoTorsionResidual K S W) :=
  AddSubgroup.torsionBy.zmodModule

instance : DistribMulAction (GKS K S) (TwoTorsionResidual K S W) :=
  inferInstanceAs (DistribMulAction (GKS K S) (TorsS K S W (2 : ℤ)))

instance : SMulCommClass (GKS K S) (ZMod 2) (TwoTorsionResidual K S W) where
  smul_comm g c x := ZMod.map_smul (DistribSMul.toAddMonoidHom
    (TwoTorsionResidual K S W) g) c x

instance : TopologicalSpace (TwoTorsionResidual K S W) := ⊥
instance : DiscreteTopology (TwoTorsionResidual K S W) := ⟨rfl⟩

instance : ContinuousSMul (GKS K S) (TwoTorsionResidual K S W) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun x => ?_
  exact isOpen_stabilizer_torsS (K := K) (S := S) (W := W) x

instance [W.IsElliptic] : Finite (TwoTorsionResidual K S W) :=
  finite_torsS (by norm_num)

variable {K S W}

/-- The residue-field isomorphism is linear over the stage coefficient ring. -/
def stageResidueLinearEquiv (i : ℕ) [NeZero i] :
    ResidueField (Acoef i) ≃ₗ[Acoef i] ZMod 2 where
  __ := (stageResidueFieldEquiv i).toAddEquiv
  map_smul' a c := by
    change stageResidueFieldEquiv i (algebraMap (Acoef i) _ a * c) =
      resEps i a * stageResidueFieldEquiv i c
    rw [map_mul, ResidueField.algebraMap_eq, stageResidueFieldEquiv_residue]

/-- Changing the residue-field presentation in a tensor product. -/
def stageResidueTensorEquiv (i : ℕ) [NeZero i] (N : Type) [AddCommGroup N] [Module (Acoef i) N] :
    (ResidueField (Acoef i) ⊗[Acoef i] N) ≃+ (ZMod 2 ⊗[Acoef i] N) :=
  (TensorProduct.congr (stageResidueLinearEquiv i) (LinearEquiv.refl (Acoef i) N)).toAddEquiv

/-- Evaluation of the tensor comparison on pure tensors. -/
theorem stageResidueTensorEquiv_tmul (i : ℕ) [NeZero i] (N : Type)
    [AddCommGroup N] [Module (Acoef i) N] (c : ResidueField (Acoef i)) (x : N) :
    stageResidueTensorEquiv i N (c ⊗ₜ[Acoef i] x) = stageResidueFieldEquiv i c ⊗ₜ[Acoef i] x :=
  rfl

variable (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ)
  (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
  (h2 : FullTorsion K S W 2)

/-- Reduction of the actual coefficient module identifies it with the fixed two-torsion module. -/
def stageCoefResidualAddEquiv :
    BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1))) (Mcoef K S W (j + 1) α) ≃+
      TwoTorsionResidual K S W :=
  (stageResidueTensorEquiv (j + 1) (Mcoef K S W (j + 1) α)).trans
    (residualEquiv j α hT hM h2)

/-- The coefficient reduction is semilinear for the canonical identification of residue fields. -/
def stageCoefResidualEquiv :
    LinearEquiv (σ' := ((stageResidueFieldEquiv (j + 1)).symm :
        ZMod 2 →+* ResidueField (Acoef (j + 1))))
      ((stageResidueFieldEquiv (j + 1)) : ResidueField (Acoef (j + 1)) →+* ZMod 2)
      (BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1))) (Mcoef K S W (j + 1) α))
      (TwoTorsionResidual K S W) where
  __ := stageCoefResidualAddEquiv j α hT hM h2
  map_smul' c x := by
    rcases stageResidueField_zero_or_one (j + 1) c with rfl | rfl
    · simp only [zero_smul, map_zero]
      exact (stageCoefResidualAddEquiv j α hT hM h2).map_zero
    · simp only [one_smul, map_one]

omit [NumberField K] in
/-- The reduction respects the Galois action; every scalar character has trivial residue. -/
theorem stageCoefResidualEquiv_smul (g : GKS K S)
    (x : BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1))) (Mcoef K S W (j + 1) α)) :
    stageCoefResidualEquiv j α hT hM h2 (g • x) = g • stageCoefResidualEquiv j α hT hM h2 x := by
  let E : BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1))) (Mcoef K S W (j + 1) α) ≃+
      (ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α) :=
    stageResidueTensorEquiv (j + 1) (Mcoef K S W (j + 1) α)
  have hc : E (g • x) = resAct (j + 1) α _ g (E x) := by
    refine BCoef.induction_on (Acoef (j + 1)) (ResidueField (Acoef (j + 1)))
      (Mcoef K S W (j + 1) α) x (fun c m => ?_) (fun x y hx hy => ?_)
    · rfl
    · rw [smul_add, map_add, map_add, hx, hy, map_add]
  change residualEquiv j α hT hM h2 (E (g • x)) = _
  rw [hc]
  exact residualEquiv_resAct j α hT hM h2 g _

variable [IsOpenKer α]

/-- Residual cochains of every positive stage are the cochains of one fixed residual representation. -/
def stageGlobalResidualEquiv :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (globalCx (Acoef (j + 1)) (GKS K S) (Mcoef K S W (j + 1) α)))
      (globalCx (ZMod 2) (GKS K S) (TwoTorsionResidual K S W)) where
  component n := (LinearEquiv.ofBijective
    ((natCochainsBaseChangeHom (Acoef (j + 1)) (ResidueField (Acoef (j + 1)))
      (GKS K S) (Mcoef K S W (j + 1) α)).f n n rfl)
    (natCochainsBaseChangeHom_bijective _ _ _ _ n)).trans
      ((natCochainScalarEquiv (G := GKS K S) (stageResidueFieldEquiv (j + 1))
        (stageCoefResidualEquiv j α hT hM h2) (stageCoefResidualEquiv_smul j α hT hM h2)).component n)
  comm a b h x := by
    change (natCochainScalarEquiv (G := GKS K S) (stageResidueFieldEquiv (j + 1))
      (stageCoefResidualEquiv j α hT hM h2) (stageCoefResidualEquiv_smul j α hT hM h2)).component b
      (((natCochainsBaseChangeHom _ _ _ _).f b b rfl)
        ((gcxBaseChange _ (globalCx _ _ _)).d a b h x)) = _
    rw [(natCochainsBaseChangeHom _ _ _ _).comm a b a b rfl h h rfl x]
    exact (natCochainScalarEquiv (G := GKS K S) (stageResidueFieldEquiv (j + 1))
      (stageCoefResidualEquiv j α hT hM h2) (stageCoefResidualEquiv_smul j α hT hM h2)).comm a b h _

end ActualResidualCoefficients

section RestrictedResidualCoefficients

open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ) [IsOpenKer α]
  (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
  (h2 : FullTorsion K S W 2)
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (φ : H →ₜ* GKS K S)

/-- The residual coefficient comparison commutes with restriction to a subgroup. -/
def stageRestrictedCoefResidualEquiv :
    LinearEquiv (σ' := ((stageResidueFieldEquiv (j + 1)).symm :
        ZMod 2 →+* ResidueField (Acoef (j + 1))))
      ((stageResidueFieldEquiv (j + 1)) : ResidueField (Acoef (j + 1)) →+* ZMod 2)
      (BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1))) (ResMod φ (Mcoef K S W (j + 1) α)))
      (ResMod φ (TwoTorsionResidual K S W)) := stageCoefResidualEquiv j α hT hM h2

omit [NumberField K] [IsOpenKer α] [IsTopologicalGroup H] in
/-- Equivariance of the restricted residual comparison. -/
theorem stageRestrictedCoefResidualEquiv_smul (g : H)
    (x : BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1))) (ResMod φ (Mcoef K S W (j + 1) α))) :
    stageRestrictedCoefResidualEquiv j α hT hM h2 φ (g • x) =
      g • stageRestrictedCoefResidualEquiv j α hT hM h2 φ x :=
  stageCoefResidualEquiv_smul j α hT hM h2 (φ g) x

variable [CompactSpace H]

/-- The residual cochain comparison is valid for every restricted local or global action. -/
def stageRestrictedCochainsResidualEquiv :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (natCx (contCochains (Acoef (j + 1)) H (ResMod φ (Mcoef K S W (j + 1) α)))))
      (natCx (contCochains (ZMod 2) H (ResMod φ (TwoTorsionResidual K S W)))) :=
  baseChangedCochainsScalarEquiv (Acoef (j + 1)) (ResidueField (Acoef (j + 1)))
    (stageResidueFieldEquiv (j + 1)) H (ResMod φ (Mcoef K S W (j + 1) α))
    (stageRestrictedCoefResidualEquiv j α hT hM h2 φ)
    (stageRestrictedCoefResidualEquiv_smul j α hT hM h2 φ)

/-- The local comparison of actual and fixed residual cochains. -/
def stageLocalResidualEquiv (v : Places K S) :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (locAt K S (Acoef (j + 1)) (Mcoef K S W (j + 1) α) v))
      (locAt K S (ZMod 2) (TwoTorsionResidual K S W) v) :=
  stageRestrictedCochainsResidualEquiv j α hT hM h2 (locMap K S v.1)

variable [Fintype (Places K S)] [DecidableEq (Places K S)]

/-- The comparison commutes with the finite direct sum of local complexes. -/
def stageLocalSumResidualEquiv :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (localSumCx (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (Mcoef K S W (j + 1) α)))
      (localSumCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (TwoTorsionResidual K S W)) :=
  (piScalarEquiv (stageResidueFieldEquiv (j + 1)) (stageLocalResidualEquiv j α hT hM h2)).precompose
    (piBaseChangeHom (ResidueField (Acoef (j + 1)))
      (locAt K S (Acoef (j + 1)) (Mcoef K S W (j + 1) α)))
    (piBaseChangeHom_bijective (ResidueField (Acoef (j + 1))) _)

/-- The residual global and local comparisons preserve the localization map. -/
theorem stageResidual_localization (a b : ℤ) (h : a = b)
    (x : (gcxBaseChange (ResidueField (Acoef (j + 1)))
      (globalCx (Acoef (j + 1)) (GKS K S) (Mcoef K S W (j + 1) α))).X a) :
    (stageLocalSumResidualEquiv j α hT hM h2).component b
      ((ghomBaseChange (ResidueField (Acoef (j + 1)))
        (resS (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (Mcoef K S W (j + 1) α))).f a b h x) =
    (resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (TwoTorsionResidual K S W)).f a b h
        ((stageGlobalResidualEquiv j α hT hM h2).component a x) := by
  subst b
  cases a with
  | ofNat n =>
    induction x using TensorProduct.inductionOn with
    | tmul c f =>
      funext v
      apply Subtype.ext
      funext t
      rfl
    | add x y hx hy =>
      let F := ((stageLocalSumResidualEquiv j α hT hM h2).component n).toAddMonoidHom.comp
        ((ghomBaseChange (ResidueField (Acoef (j + 1)))
          (resS (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) (Mcoef K S W (j + 1) α))).f n n rfl).toAddMonoidHom
      let G := ((resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (TwoTorsionResidual K S W)).f n n rfl).toAddMonoidHom.comp
          ((stageGlobalResidualEquiv j α hT hM h2).component n).toAddMonoidHom
      change F (x + y) = G (x + y)
      exact (F.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (G.map_add x y).symm)
  | negSucc n =>
    have : Subsingleton ((gcxBaseChange (ResidueField (Acoef (j + 1)))
        (globalCx (Acoef (j + 1)) (GKS K S) (Mcoef K S W (j + 1) α))).X (Int.negSucc n)) :=
      subsingleton_tensor_punit (Acoef (j + 1)) (ResidueField (Acoef (j + 1)))
    rw [Subsingleton.elim x 0, map_zero, map_zero, map_zero, map_zero]

end RestrictedResidualCoefficients

section ScalarRestriction

variable {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
  (M : Type) [AddCommGroup M] [Module R M]

/-- A coefficient module expressed over an isomorphic coefficient ring. -/
@[nolint unusedArguments]
def ScalarChangedModule (_e : R ≃+* S) (M : Type) [AddCommGroup M] [Module R M] : Type := M

instance : AddCommGroup (ScalarChangedModule e M) := inferInstanceAs (AddCommGroup M)
instance : Module S (ScalarChangedModule e M) := Module.compHom M (e.symm : S →+* R)
instance [TopologicalSpace M] : TopologicalSpace (ScalarChangedModule e M) :=
  inferInstanceAs (TopologicalSpace M)
instance [TopologicalSpace M] [DiscreteTopology M] : DiscreteTopology (ScalarChangedModule e M) :=
  inferInstanceAs (DiscreteTopology M)
instance [Finite M] : Finite (ScalarChangedModule e M) := inferInstanceAs (Finite M)

variable {G : Type} [Group G] [DistribMulAction G M] [SMulCommClass G R M]

instance : DistribMulAction G (ScalarChangedModule e M) := inferInstanceAs (DistribMulAction G M)
instance : SMulCommClass G S (ScalarChangedModule e M) where
  smul_comm g c x := smul_comm g (e.symm c) (show M from x)
instance [TopologicalSpace G] [TopologicalSpace M] [ContinuousSMul G M] :
    ContinuousSMul G (ScalarChangedModule e M) := inferInstanceAs (ContinuousSMul G M)

/-- Expressing coefficients over an isomorphic ring does not change the underlying additive group. -/
def scalarChangedEquiv : LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S) M
    (ScalarChangedModule e M) where
  __ := AddEquiv.refl M
  map_smul' c x := by
    change c • x = e.symm (e c) • x
    rw [e.symm_apply_apply]

omit [SMulCommClass G R M] in
/-- The scalar change preserves the group action. -/
theorem scalarChangedEquiv_smul (g : G) (x : M) :
    scalarChangedEquiv e M (g • x) = g • scalarChangedEquiv e M x := rfl

end ScalarRestriction

section PrintedDimension

open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.ContBridge

/-- Milne, Arithmetic Duality Theorems, second edition, I, Remark 1.12,
page 24: "Consequently scdₚ(G) = 2 in examples (1.6a,b,c,d) except
when p = 2 and K is a number field having a real prime."
Applied to the local class formation of I.1.6(b), this gives the following
vanishing for finite discrete modules over characteristic-zero local fields.
The local duality statement is I.2.3, page 28. -/
def MilneLocalDimensionTwo : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [DistribMulAction (Gloc K v) M] [SMulCommClass (Gloc K v) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K v) M],
    Finite M → ∀ n : ℤ, 2 < n →
      Subsingleton ((natCx (contCochains R (Gloc K v) M)).toCC.homology n)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [Finite M]

/-- Milne I.4.10(c), pages 56–57, gives global range `[0,2]` when there
are no real places; negative degrees vanish by extension by zero. -/
theorem globalBinary_homology_range (h410 : MilneADT_I_4_10_totallyComplex)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ n : ℤ, n < 0 ∨ 2 < n →
      Subsingleton ((globalCx (ZMod 2) (GKS K S) M).toCC.homology n) := by
  have : ContinuousSMul (ZMod 2) M := continuousSMul_of_discrete (ZMod 2) M
  intro n hn
  rcases hn with hn | hn
  · exact natCx_homology_subsingleton_neg _ n hn
  · cases n with
    | negSucc n => omega
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast] at hn
      cases n with
      | zero => norm_num at hn
      | succ n =>
        have hN : 2 < n + 1 := by omega
        have hH : Subsingleton (continuousCohomology (n + 1)
            (TauCeti.ofDiscreteModule (ZMod 2) (GKS K S) M)) :=
          h410 K hK S hS h2 (TauCeti.ofDiscreteModule (ZMod 2) (GKS K S) M)
            (inferInstanceAs (Finite M)) (inferInstanceAs (DiscreteTopology M))
            (hcontDisc (ZMod 2) (GKS K S) M) (n + 1) hN
        have : Subsingleton ((contCochains (ZMod 2) (GKS K S) M).homology (n + 1)) :=
          (contCohomologyLinearEquiv (ZMod 2) (GKS K S) M (n + 1)).symm.injective.subsingleton
        exact (natPositiveHomologyIso (contCochains (ZMod 2) (GKS K S) M) n).toLinearEquiv.injective.subsingleton

end PrintedDimension

section ResidualRanges

open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts

variable {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]

/-- Tensoring a zero module gives a zero module. -/
theorem tensor_subsingleton_right (M : Type) [AddCommGroup M] [Module A M]
    (hM : Subsingleton M) : Subsingleton (B ⊗[A] M) := by
  have hz : ∀ z : B ⊗[A] M, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Zero terms remain zero in residual cohomology. -/
theorem baseChange_homology_subsingleton_of_term (C : GCx A) (n : ℤ)
    (hC : Subsingleton (C.X n)) : Subsingleton ((gcxBaseChange B C).toCC.homology n) :=
  homology_subsingleton_of_term _ n (tensor_subsingleton_right B (C.X n) hC)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (i : ℕ) [NeZero i]

/-- Any finite discrete module over a stage residue field has global cohomological range `[0,2]`. -/
theorem globalStageField_homology_range (M : Type) [AddCommGroup M]
    [Module (ResidueField (Acoef i)) M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) (ResidueField (Acoef i)) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (h410 : MilneADT_I_4_10_totallyComplex) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ n : ℤ, n < 0 ∨ 2 < n →
      Subsingleton ((globalCx (ResidueField (Acoef i)) (GKS K S) M).toCC.homology n) := by
  let N := ScalarChangedModule (stageResidueFieldEquiv i) M
  let E := natCochainScalarEquiv (G := GKS K S) (stageResidueFieldEquiv i)
    (scalarChangedEquiv (stageResidueFieldEquiv i) M)
    (scalarChangedEquiv_smul (stageResidueFieldEquiv i) M)
  intro n hn
  exact E.subsingleton_homology n
    (globalBinary_homology_range K S N h410 hK hS h2 n hn)

variable (M : Type) [AddCommGroup M] [Module (Acoef i) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (Acoef i) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [Finite M]

/-- The residual global cochains of a positive stage have range `[0,2]`. -/
theorem stageGlobal_residual_range (h410 : MilneADT_I_4_10_totallyComplex)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton
      ((gcxBaseChange (ResidueField (Acoef i)) (globalCx (Acoef i) (GKS K S) M)).toCC.homology n) := by
  have : Finite (ResidueField (Acoef i)) := finite_residueField
  have : Finite (BCoef (Acoef i) (ResidueField (Acoef i)) M) := finite_bcoef _ _ _
  intro n hn
  have := globalStageField_homology_range K S i
    (BCoef (Acoef i) (ResidueField (Acoef i)) M) h410 hK hS h2 n hn
  exact (homologyIsoOfBijective
    (natCochainsBaseChangeHom (Acoef i) (ResidueField (Acoef i)) (GKS K S) M)
    (natCochainsBaseChangeHom_bijective _ _ _ _) n).toLinearEquiv.injective.subsingleton

/-- The residual local cochains have range `[0,2]`, by local cohomological dimension two. -/
theorem stageLocal_residual_range (hlcd : MilneLocalDimensionTwo) (v : Places K S) :
    ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton
      ((gcxBaseChange (ResidueField (Acoef i)) (locAt K S (Acoef i) M v)).toCC.homology n) := by
  have : Finite (ResidueField (Acoef i)) := finite_residueField
  have : Finite (BCoef (Acoef i) (ResidueField (Acoef i)) M) := finite_bcoef _ _ _
  have : Finite (ResMod (locMap K S v.1) (BCoef (Acoef i) (ResidueField (Acoef i)) M)) :=
    inferInstanceAs (Finite (BCoef (Acoef i) (ResidueField (Acoef i)) M))
  intro n hn
  have htarget : Subsingleton
      ((locAt K S (ResidueField (Acoef i)) (BCoef (Acoef i) (ResidueField (Acoef i)) M) v).toCC.homology n) := by
    rcases hn with hn | hn
    · exact natCx_homology_subsingleton_neg _ n hn
    · exact hlcd K v.1 (ResidueField (Acoef i))
        (ResMod (locMap K S v.1) (BCoef (Acoef i) (ResidueField (Acoef i)) M)) inferInstance n hn
  have := htarget
  exact (homologyIsoOfBijective (localBaseChangeHom (Acoef i) (ResidueField (Acoef i))
    (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v)
    (natCochainsBaseChangeHomOf_bijective (Acoef i) (ResidueField (Acoef i)) (Gloc K v.1)
      (ResMod (locMap K S v.1) M) _ _) n).toLinearEquiv.injective.subsingleton

/-- Full conditions or conditions with terms in `[0,2]` suffice for the actual residual
Selmer range. The condition assumption specifies its shape, not its cohomology. -/
theorem stageSelmer_residual_range (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S (Acoef i) M)
    (hΔ : ∀ v, Δ.U v = locAt K S (Acoef i) M v ∨
      ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton ((Δ.U v).X n)) :
    ∀ n : ℤ, n < 0 ∨ 3 < n →
      Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (galoisSelData K S (Acoef i) M Δ)) n) = 0 := by
  classical
  let : Fintype (Places K S) := hS.fintype
  have : Finite (ResidueField (Acoef i)) := finite_residueField
  have : Finite (BCoef (Acoef i) (ResidueField (Acoef i)) M) := finite_bcoef _ _ _
  let Δb := residualConditions (Acoef i) (ResidueField (Acoef i)) (GKS K S)
    (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M Δ
  let Db := galoisSelData K S (ResidueField (Acoef i))
    (BCoef (Acoef i) (ResidueField (Acoef i)) M) Δb
  have hG : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (Db.G.toCC.homology n) :=
    globalStageField_homology_range K S i (BCoef (Acoef i) (ResidueField (Acoef i)) M)
      h410 hK hS h2
  have hL : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (Db.L.toCC.homology n) := by
    intro n hn
    apply piCx_homology_subsingleton
    intro v
    have : Finite (ResMod (locMap K S v.1) (BCoef (Acoef i) (ResidueField (Acoef i)) M)) :=
      inferInstanceAs (Finite (BCoef (Acoef i) (ResidueField (Acoef i)) M))
    rcases hn with hn | hn
    · exact natCx_homology_subsingleton_neg _ n hn
    · exact hlcd K v.1 (ResidueField (Acoef i))
        (ResMod (locMap K S v.1) (BCoef (Acoef i) (ResidueField (Acoef i)) M)) inferInstance n hn
  have hU : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (Db.U.toCC.homology n) := by
    intro n hn
    apply piCx_homology_subsingleton
    intro v
    change Subsingleton ((gcxBaseChange (ResidueField (Acoef i)) (Δ.U v)).toCC.homology n)
    rcases hΔ v with h | h
    · rw [h]
      exact stageLocal_residual_range K S i M hlcd v n hn
    · exact baseChange_homology_subsingleton_of_term _ _ n (h n hn)
  intro n hn
  have ht := selCx_homology_range Db hG hL hU n hn
  have : Subsingleton ((gcxBaseChange (ResidueField (Acoef i))
      (selCx (galoisSelData K S (Acoef i) M Δ))).toCC.homology n) := by
    have := ht
    exact (HomologicalComplex.homologyMapIso
      (residualGaloisSelmerIso K S M (ResidueField (Acoef i)) Δ) n).toLinearEquiv.injective.subsingleton
  have : Subsingleton (residualCohomologyAt (selCx (galoisSelData K S (Acoef i) M Δ)) n) :=
    (residualHomologyEquiv _ n).symm.injective.subsingleton
  exact Module.finrank_zero_of_subsingleton

end ResidualRanges

section ActualAmplitude

open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts

/-- A cocycle condition has terms only in degrees zero and one. -/
theorem cocycleCondition_term_range {R G M : Type} [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [SMulCommClass G R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] (Z : Submodule R (contCochain R G M 1))
    (hZ : ∀ z ∈ Z, contD R G M 1 z = 0) (n : ℤ) (hn : n < 0 ∨ 1 < n) :
    Subsingleton ((cocycleCondition Z hZ).X n) := by
  cases n with
  | negSucc n => exact inferInstanceAs (Subsingleton PUnit)
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at hn
    rcases n with _ | _ | n
    · omega
    · omega
    · change Subsingleton ↥(⊥ : Submodule R (contCochain R G M (n + 2)))
      infer_instance

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S →* (Acoef i)ˣ)
  [IsOpenKer α]

/-- The strict actual stage complexes supply the producer's `hbdd` with `lo = 0`, `hi = 3`. -/
theorem stageStrictSelmer_hbdd (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ n : ℤ, n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
      (residualCohomologyAt (selCx (actualSelData_zero W i α)) n) = 0 :=
  stageSelmer_residual_range K S i (Mcoef K S W i α) h410 hlcd hK hS h2 _
    (fun _ => Or.inr (fun _ _ => inferInstanceAs (Subsingleton PUnit)))

/-- The relaxed actual stage complexes supply the same cohomological range. -/
theorem stageRelaxedSelmer_hbdd (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ n : ℤ, n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
      (residualCohomologyAt (selCx (actualSelData_full W i α)) n) = 0 :=
  stageSelmer_residual_range K S i (Mcoef K S W i α) h410 hlcd hK hS h2 _ (fun _ => Or.inl rfl)

/-- The actual Kummer stage complexes supply the same cohomological range. -/
theorem stageKummerSelmer_hbdd (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
    (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (Bv v).IsElliptic]
    (m : ℕ) [NeZero m]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (Bv v) m →+
      ResMod (locMap K S v.1) (Mcoef K S W i α))
    (hι : ∀ v (g : Gloc K v.1) t, ι v (g • t) = g • ι v t) :
    ∀ n : ℤ, n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
      (residualCohomologyAt (selCx (galoisSelData K S (Acoef i) (Mcoef K S W i α)
        (kummerGaloisLocalConditions K S Bv m (Acoef i) (Mcoef K S W i α) ι hι))) n) = 0 :=
  stageSelmer_residual_range K S i (Mcoef K S W i α) h410 hlcd hK hS h2 _ (fun v => Or.inr
    (fun n hn => cocycleCondition_term_range _ _ n (by omega)))

end ActualAmplitude

section RankEstimates

variable {R : Type} [Field R]

/-- Cohomology has dimension at most that of its term when the latter is finite dimensional. -/
theorem homology_finrank_le_term (C : GCx R) (n : ℤ) [Module.Finite R (C.X n)] :
    Module.finrank R (C.toCC.homology n) ≤ Module.finrank R (C.X n) := by
  rw [(homologySubquotEquiv C n).finrank_eq]
  exact (Submodule.finrank_quotient_le _).trans
    (LinearMap.finrank_le_finrank_of_injective (LinearMap.ker (C.d n (n + 1) rfl)).subtype_injective)

/-- Finite-dimensional outer terms of an exact sequence bound the dimension of the middle term. -/
theorem exact_finrank_middle_le {E : ShortComplex (ModuleCat.{0} R)} (hE : E.Exact)
    (h₁ : Module.Finite R E.X₁) (h₃ : Module.Finite R E.X₃) :
    Module.finrank R E.X₂ ≤ Module.finrank R E.X₁ + Module.finrank R E.X₃ := by
  have := h₁
  have := h₃
  have he : Function.Exact E.f.hom E.g.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact hE.moduleCat_range_eq_ker.symm
  have : Module.Finite R E.X₂ := Module.Finite.of_exact he
    (LinearMap.surjective_rangeRestrict E.g.hom)
  have hdim := LinearMap.finrank_range_add_finrank_ker E.g.hom
  have hf := LinearMap.finrank_range_le E.f.hom
  have hg : Module.finrank R E.g.hom.range ≤ Module.finrank R E.X₃ :=
    LinearMap.finrank_le_finrank_of_injective E.g.hom.range.subtype_injective
  rw [hE.moduleCat_range_eq_ker] at hf
  omega

/-- Finiteness of the middle term follows from finite-dimensional outer terms and exactness. -/
theorem exact_moduleFinite_middle {E : ShortComplex (ModuleCat.{0} R)} (hE : E.Exact)
    (h₁ : Module.Finite R E.X₁) (h₃ : Module.Finite R E.X₃) : Module.Finite R E.X₂ := by
  have := h₁
  have := h₃
  have he : Function.Exact E.f.hom E.g.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact hE.moduleCat_range_eq_ker.symm
  exact Module.Finite.of_exact he (LinearMap.surjective_rangeRestrict E.g.hom)

/-- Equal boundary and cycle submodules give isomorphic cohomology quotients. -/
def subquotEquivOfEq {X : Type} [AddCommGroup X] [Module R X]
    (B B' Z Z' : Submodule R X) (hB : B = B') (hZ : Z = Z') :
    (Z ⧸ B.comap Z.subtype) ≃ₗ[R] (Z' ⧸ B'.comap Z'.subtype) := by
  subst hB hZ
  exact LinearEquiv.refl R _

/-- The cohomology comparison for a shift down by one. -/
def shiftDownHomologyEquiv (C : GCx R) (n : ℤ) :
    (shiftDown C).toCC.homology n ≃ₗ[R] C.toCC.homology (n - 1) := by
  have hB : LinearMap.range ((shiftDown C).d (n - 1) n (by omega)) =
      LinearMap.range (C.d (n - 1 - 1) (n - 1) (by omega)) := LinearMap.range_neg _
  have hZ : LinearMap.ker ((shiftDown C).d n (n + 1) rfl) =
      LinearMap.ker (C.d (n - 1) (n - 1 + 1) rfl) := by
    change LinearMap.ker (-(C.d (n - 1) (n + 1 - 1) (by omega))) = _
    rw [LinearMap.ker_neg]
    exact ker_d_congr C _ _
  exact (homologySubquotEquiv (shiftDown C) n).trans
    ((subquotEquivOfEq _ _ _ _ hB hZ).trans (homologySubquotEquiv C (n - 1)).symm)

/-- The dimension estimate coming from the two exact sequences of a Selmer cone. -/
theorem selmer_finrank_le (D : SelData R) (n : ℤ)
    [Module.Finite R (D.G.toCC.homology n)] [Module.Finite R (D.U.toCC.homology n)]
    [Module.Finite R (D.L.toCC.homology (n - 1))] :
    Module.finrank R ((selCx D).toCC.homology n) ≤
      Module.finrank R (D.G.toCC.homology n) + Module.finrank R (D.U.toCC.homology n) +
        Module.finrank R (D.L.toCC.homology (n - 1)) := by
  have hShiftFinite : Module.Finite R ((shiftDown D.L).toCC.homology n) :=
    (Module.Finite.equiv_iff (shiftDownHomologyEquiv D.L n)).2 inferInstance
  have hU : Module.Finite R (D.U.toCC.homology n) := inferInstance
  have hG : Module.Finite R (D.G.toCC.homology n) := inferInstance
  have hLoc := (coneSES_shortExact (negι D)).homology_exact₂ n
  have hC : Module.Finite R ((locCx D).toCC.homology n) :=
    exact_moduleFinite_middle hLoc hShiftFinite hU
  have h₁ := exact_finrank_middle_le hLoc hShiftFinite hU
  have h₂ := exact_finrank_middle_le ((sesTop_shortExact D).homology_exact₂ n) hC hG
  change Module.finrank R ((locCx D).toCC.homology n) ≤
    Module.finrank R ((shiftDown D.L).toCC.homology n) + Module.finrank R (D.U.toCC.homology n) at h₁
  change Module.finrank R ((selCx D).toCC.homology n) ≤
    Module.finrank R ((locCx D).toCC.homology n) + Module.finrank R (D.G.toCC.homology n) at h₂
  rw [(shiftDownHomologyEquiv D.L n).finrank_eq] at h₁
  omega

/-- A degreewise bound on cohomology in a finite range gives a bound in every degree. -/
def finiteRangeRankBound (C : GCx R) (lo hi : ℤ) : ℕ :=
  (Finset.Icc lo hi).sup (fun n => Module.finrank R (C.toCC.homology n))

/-- The finite-range maximum bounds every cohomology rank of a bounded complex. -/
theorem finrank_le_finiteRangeRankBound (C : GCx R) (lo hi : ℤ)
    (hC : ∀ n : ℤ, n < lo ∨ hi < n → Subsingleton (C.toCC.homology n)) (n : ℤ) :
    Module.finrank R (C.toCC.homology n) ≤ finiteRangeRankBound C lo hi := by
  by_cases hn : n ∈ Finset.Icc lo hi
  · exact Finset.le_sup (f := fun a => Module.finrank R (C.toCC.homology a)) hn
  · have hzero := hC n (by simp only [Finset.mem_Icc] at hn; omega)
    have := hzero
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _

end RankEstimates

section FixedCohomology

open ZInQ.Contrib.CloudB3RC53.RankCounts

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] [Finite M]

/-- The one fixed global residual complex. -/
abbrev fixedGlobalCx : GCx (ZMod 2) := globalCx (ZMod 2) (GKS K S) M

/-- The one fixed finite direct sum of local residual complexes. -/
abbrev fixedLocalSumCx : GCx (ZMod 2) := localSumCx (ZMod 2) (GKS K S)
  (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M

/-- Milne I.4.15, page 62, supplies finiteness for the fixed binary global module.
The existing global finiteness leaf has the same statement. -/
theorem fixedGlobalCohomology_finite (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) (n : ℤ) :
    Finite ((fixedGlobalCx K S M).toCC.homology n) := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  rw [Nat.card_zmod] at hc
  apply hglob K S hS (ZMod 2) M inferInstance
  intro v hv
  rw [hc, Nat.cast_pow, Nat.cast_ofNat] at hv
  exact h2 v (v.isPrime.mem_of_pow_mem _ hv)

/-- Milne I.2.3 supplies finiteness of the fixed local residual complex. -/
theorem fixedLocalCohomology_finite (hloc : MilneLocalFiniteness) (hS : S.Finite) (n : ℤ) :
    Finite ((fixedLocalSumCx K S M).toCC.homology n) := by
  have : Finite (Places K S) := hS.to_subtype
  apply finite_homology_piCx
  intro v
  have : Finite (ResMod (locMap K S v.1) M) := inferInstanceAs (Finite M)
  exact hloc K v.1 (ZMod 2) (ResMod (locMap K S v.1) M) inferInstance n

/-- Local cohomological dimension two bounds the fixed direct sum of local complexes. -/
theorem fixedLocalCohomology_range (hlcd : MilneLocalDimensionTwo) :
    ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton ((fixedLocalSumCx K S M).toCC.homology n) := by
  intro n hn
  apply piCx_homology_subsingleton
  intro v
  have : Finite (ResMod (locMap K S v.1) M) := inferInstanceAs (Finite M)
  rcases hn with hn | hn
  · exact natCx_homology_subsingleton_neg _ n hn
  · exact hlcd K v.1 (ZMod 2) (ResMod (locMap K S v.1) M) inferInstance n hn

/-- A fixed global residual bound. -/
def fixedGlobalRankBound : ℕ := finiteRangeRankBound (fixedGlobalCx K S M) 0 2

/-- A fixed local residual bound. -/
def fixedLocalRankBound : ℕ := finiteRangeRankBound (fixedLocalSumCx K S M) 0 2

/-- A common bound for strict and relaxed Selmer complexes. -/
def strictRelaxedRankBound : ℕ := fixedGlobalRankBound K S M + 2 * fixedLocalRankBound K S M

end FixedCohomology

section ResidualConeRank

variable {A : Type} [CommRing A] [IsLocalRing A]

/-- The residual Selmer ranks are bounded by the residual global, condition, and shifted local ranks. -/
theorem residualSelmer_finrank_le (D : SelData A) (n : ℤ)
    [Module.Finite (ResidueField A) ((gcxBaseChange (ResidueField A) D.G).toCC.homology n)]
    [Module.Finite (ResidueField A) ((gcxBaseChange (ResidueField A) D.U).toCC.homology n)]
    [Module.Finite (ResidueField A) ((gcxBaseChange (ResidueField A) D.L).toCC.homology (n - 1))] :
    Module.finrank (ResidueField A) (residualCohomologyAt (selCx D) n) ≤
      Module.finrank (ResidueField A) ((gcxBaseChange (ResidueField A) D.G).toCC.homology n) +
      Module.finrank (ResidueField A) ((gcxBaseChange (ResidueField A) D.U).toCC.homology n) +
      Module.finrank (ResidueField A) ((gcxBaseChange (ResidueField A) D.L).toCC.homology (n - 1)) := by
  rw [← (residualHomologyEquiv (selCx D) n).finrank_eq,
    (homologyIsoOfBijective (selBaseChangeHom (ResidueField A) D)
      (selBaseChangeHom_bijective (ResidueField A) D) n).toLinearEquiv.finrank_eq]
  have hG : Module.Finite (ResidueField A)
      ((selDataBaseChange (ResidueField A) D).G.toCC.homology n) :=
    inferInstanceAs (Module.Finite (ResidueField A)
      ((gcxBaseChange (ResidueField A) D.G).toCC.homology n))
  have hU : Module.Finite (ResidueField A)
      ((selDataBaseChange (ResidueField A) D).U.toCC.homology n) :=
    inferInstanceAs (Module.Finite (ResidueField A)
      ((gcxBaseChange (ResidueField A) D.U).toCC.homology n))
  have hL : Module.Finite (ResidueField A)
      ((selDataBaseChange (ResidueField A) D).L.toCC.homology (n - 1)) :=
    inferInstanceAs (Module.Finite (ResidueField A)
      ((gcxBaseChange (ResidueField A) D.L).toCC.homology (n - 1)))
  exact selmer_finrank_le (selDataBaseChange (ResidueField A) D) n

end ResidualConeRank

section StrictRelaxedBounds

open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ)
  [IsOpenKer α] (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
  (hE2 : FullTorsion K S W 2)

include hT hM hE2 in
/-- A common residual bound for the actual strict and relaxed stage Selmer complexes,
independent of the stage and the scalar character. -/
theorem stageStrictRelaxedSelmer_hB (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) (n : ℤ) :
    Module.finrank (ResidueField (Acoef (j + 1)))
        (residualCohomologyAt (selCx (actualSelData_zero W (j + 1) α)) n) ≤
      strictRelaxedRankBound K S (TwoTorsionResidual K S W) ∧
    Module.finrank (ResidueField (Acoef (j + 1)))
        (residualCohomologyAt (selCx (actualSelData_full W (j + 1) α)) n) ≤
      strictRelaxedRankBound K S (TwoTorsionResidual K S W) := by
  classical
  let : Fintype (Places K S) := hS.fintype
  let G := globalCx (Acoef (j + 1)) (GKS K S) (Mcoef K S W (j + 1) α)
  let L := localSumCx (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (Mcoef K S W (j + 1) α)
  let k := ResidueField (Acoef (j + 1))
  let EG := stageGlobalResidualEquiv j α hT hM hE2
  let EL := stageLocalSumResidualEquiv j α hT hM hE2
  have hGF := fixedGlobalCohomology_finite K S (TwoTorsionResidual K S W) hglob hS h2 n
  have hLF : ∀ a, Finite ((fixedLocalSumCx K S (TwoTorsionResidual K S W)).toCC.homology a) :=
    fixedLocalCohomology_finite K S (TwoTorsionResidual K S W) hloc hS
  have : Finite ((gcxBaseChange k G).toCC.homology n) := Finite.of_injective _ (EG.homology n).injective
  have : Module.Finite k ((gcxBaseChange k G).toCC.homology n) := Module.Finite.of_finite
  have hLFin : ∀ a, Module.Finite k ((gcxBaseChange k L).toCC.homology a) := by
    intro a
    have := hLF a
    have : Finite ((gcxBaseChange k L).toCC.homology a) := Finite.of_injective _ (EL.homology a).injective
    exact Module.Finite.of_finite
  have hGb : Module.finrank k ((gcxBaseChange k G).toCC.homology n) ≤
      fixedGlobalRankBound K S (TwoTorsionResidual K S W) := by
    rw [EG.finrank_homology n]
    exact finrank_le_finiteRangeRankBound _ 0 2
      (globalBinary_homology_range K S (TwoTorsionResidual K S W) h410 hK hS h2) n
  have hLb : ∀ a, Module.finrank k ((gcxBaseChange k L).toCC.homology a) ≤
      fixedLocalRankBound K S (TwoTorsionResidual K S W) := by
    intro a
    rw [EL.finrank_homology a]
    exact finrank_le_finiteRangeRankBound _ 0 2
      (fixedLocalCohomology_range K S (TwoTorsionResidual K S W) hlcd) a
  have hUn : Subsingleton ((gcxBaseChange k (actualSelData_zero W (j + 1) α).U).toCC.homology n) :=
    baseChange_homology_subsingleton_of_term k _ n
      (inferInstanceAs (Subsingleton (Places K S → PUnit)))
  have := hUn
  have : Module.Finite k ((gcxBaseChange k (actualSelData_zero W (j + 1) α).U).toCC.homology n) :=
    Module.Finite.of_finite
  have := hLFin (n - 1)
  have hGz : Module.Finite k ((gcxBaseChange k (actualSelData_zero W (j + 1) α).G).toCC.homology n) :=
    inferInstanceAs (Module.Finite k ((gcxBaseChange k G).toCC.homology n))
  have hGf : Module.Finite k ((gcxBaseChange k (actualSelData_full W (j + 1) α).G).toCC.homology n) :=
    inferInstanceAs (Module.Finite k ((gcxBaseChange k G).toCC.homology n))
  have hLz : Module.Finite k ((gcxBaseChange k (actualSelData_zero W (j + 1) α).L).toCC.homology (n - 1)) :=
    hLFin (n - 1)
  have hLf : Module.Finite k ((gcxBaseChange k (actualSelData_full W (j + 1) α).L).toCC.homology (n - 1)) :=
    hLFin (n - 1)
  have hs := residualSelmer_finrank_le (actualSelData_zero W (j + 1) α) n
  have hr : Module.finrank k ((gcxBaseChange k (actualSelData_zero W (j + 1) α).U).toCC.homology n) = 0 :=
    Module.finrank_zero_of_subsingleton
  have := hLFin n
  have hUf : Module.Finite k ((gcxBaseChange k (actualSelData_full W (j + 1) α).U).toCC.homology n) :=
    hLFin n
  have hf := residualSelmer_finrank_le (actualSelData_full W (j + 1) α) n
  change _ ≤ _ + 2 * _ ∧ _ ≤ _ + 2 * _
  change _ ≤ Module.finrank k ((gcxBaseChange k G).toCC.homology n) +
    Module.finrank k ((gcxBaseChange k (actualSelData_zero W (j + 1) α).U).toCC.homology n) +
    Module.finrank k ((gcxBaseChange k L).toCC.homology (n - 1)) at hs
  change _ ≤ Module.finrank k ((gcxBaseChange k G).toCC.homology n) +
    Module.finrank k ((gcxBaseChange k L).toCC.homology n) +
    Module.finrank k ((gcxBaseChange k L).toCC.homology (n - 1)) at hf
  have hn := hLb n
  have hprev := hLb (n - 1)
  omega

end StrictRelaxedBounds

section KummerGenerators

open ZInQ.Manuscript.RC.CoefModules

variable {R S G M N : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- An additive change of coefficients acts pointwise on continuous cochains. -/
def cochainAddCoefficients (f : M →+ N) (n : ℕ) :
    contCochain R G M n →+ contCochain S G N n where
  toFun c := ⟨(fun x => f (cfun c x) : (Fin n → G) → N),
    (continuous_of_discreteTopology (f := f)).comp c.2⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero f)
  map_add' c d := Subtype.ext (funext fun x => map_add f (cfun c x) (cfun d x))

/-- The degree-zero differential commutes with an equivariant additive change of coefficients. -/
theorem cochainAddCoefficients_d_zero (f : M →+ N)
    (hf : ∀ (g : G) (x : M), f (g • x) = g • f x) (c : contCochain R G M 0) :
    cochainAddCoefficients (R := R) (S := S) (G := G) f 1 (contD R G M 0 c) =
      contD S G N 0 (cochainAddCoefficients (R := R) (S := S) (G := G) f 0 c) := by
  apply Subtype.ext
  funext g
  change f (cfun (contD R G M 0 c) g) =
    cfun (contD S G N 0 (cochainAddCoefficients (R := R) (S := S) (G := G) f 0 c)) g
  rw [contD_zero_apply, contD_zero_apply, map_sub, hf]
  rfl

/-- Continuous coboundaries remain coboundaries under an equivariant coefficient map. -/
theorem cochainAddCoefficients_mem_boundary (f : M →+ N)
    (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (c : contCochain R G M 1) (hc : c ∈ contB1 R G M) :
    cochainAddCoefficients (R := R) (S := S) (G := G) f 1 c ∈ contB1 S G N := by
  obtain ⟨d, rfl⟩ := (mem_contB1_iff c).1 hc
  refine ⟨cochainAddCoefficients (R := R) (S := S) (G := G) f 0 d, ?_⟩
  exact (cochainAddCoefficients_d_zero f hf d).symm

end KummerGenerators

section ExtendedKummerGenerators

open ZInQ.Manuscript.RC.CoefModules

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
  (E : WeierstrassCurve F) [E.IsElliptic] (m : ℕ) [NeZero m]
  (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M] [SMulCommClass (Field.absoluteGaloisGroup F) A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (ι : TorsAlg F E m →+ M)
  (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F E m), ι (g • t) = g • ι t)

/-- The first cohomology quotient of an extended Kummer condition. -/
abbrev extendedKummerQuot : Type := (kummerConditionIn A ι hι).X 1 ⧸
  condB1 (kummerZ' A ι) (kummerZ'_cocycle A ι hι)

/-- A local point determines a class in the extended Kummer condition. -/
def extendedKummerPointClass (P : E.toAffine.Point) : extendedKummerQuot E m A M ι hι :=
  Submodule.Quotient.mk (ofCondOne (kummerZ' A ι) (kummerZ'_cocycle A ι hι)
    ⟨kummerCocycleIn ι 1 P, Submodule.mem_sup_left (kummerCocycleIn_mem ι 1 P)⟩)

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- A pushed Kummer cocycle is the extended Kummer cocycle with scalar one. -/
theorem cochainAddCoefficients_kummer (P : E.toAffine.Point) :
    cochainAddCoefficients (R := ℤ) (S := A) ι 1 (kummerCocycle F E m P) =
      kummerCocycleIn ι 1 P := by
  apply Subtype.ext
  funext g
  exact (one_smul A (ι (kummerFun F E m P (g 0)))).symm

/-- The point-to-class map is additive, because Kummer cocycles are additive modulo coboundaries. -/
def extendedKummerPointHom : E.toAffine.Point →+ extendedKummerQuot E m A M ι hι :=
  AddMonoidHom.mk' (extendedKummerPointClass E m A M ι hι) (by
    intro P Q
    dsimp only [extendedKummerPointClass]
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    change kummerCocycleIn ι 1 (P + Q) -
      (kummerCocycleIn ι 1 P + kummerCocycleIn ι 1 Q) ∈ contB1 A (Field.absoluteGaloisGroup F) M
    have h := cochainAddCoefficients_mem_boundary (R := ℤ) (S := A) ι hι _
      (kummerCocycle_add F E m P Q)
    rw [map_sub, map_sub, cochainAddCoefficients_kummer E m A M ι P,
      cochainAddCoefficients_kummer E m A M ι Q,
      cochainAddCoefficients_kummer E m A M ι (P + Q)] at h
    simpa only [sub_add_eq_sub_sub] using h)

/-- All extended Kummer classes are generated by local points after scalar extension. -/
def extendedKummerEnvelope : (A ⊗[ℤ] E.toAffine.Point) →ₗ[A] extendedKummerQuot E m A M ι hι :=
  (extendedKummerPointHom E m A M ι hι).toIntLinearMap.liftBaseChange A

/-- Evaluation of the Kummer envelope on a pure tensor. -/
theorem extendedKummerEnvelope_tmul (a : A) (P : E.toAffine.Point) :
    extendedKummerEnvelope E m A M ι hι (a ⊗ₜ[ℤ] P) = a • extendedKummerPointClass E m A M ι hι P :=
  rfl

/-- The scalar-extended point module surjects onto the first Kummer cohomology quotient. -/
theorem extendedKummerEnvelope_surjective : Function.Surjective (extendedKummerEnvelope E m A M ι hι) := by
  let Z := kummerZ' A ι
  let hZ := kummerZ'_cocycle A ι hι
  let γ := extendedKummerEnvelope E m A M ι hι
  have hz : ∀ z (hz : z ∈ Z),
      (Submodule.Quotient.mk (ofCondOne Z hZ ⟨z, Submodule.mem_sup_left hz⟩) :
        extendedKummerQuot E m A M ι hι) ∈ LinearMap.range γ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨⟨a, P⟩, rfl⟩ := hc
      refine ⟨a ⊗ₜ[ℤ] P, ?_⟩
      rw [extendedKummerEnvelope_tmul]
      change Submodule.Quotient.mk
        (a • ofCondOne Z hZ ⟨kummerCocycleIn ι 1 P, Submodule.mem_sup_left (kummerCocycleIn_mem ι 1 P)⟩) = _
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (kummerCocycleIn_eq_smul ι a P).symm
    | zero =>
      exact ⟨0, map_zero γ⟩
    | add z z' hz hz' ih ih' =>
      exact (LinearMap.range γ).add_mem ih ih'
    | smul a z hz ih =>
      exact (LinearMap.range γ).smul_mem a ih
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨z, hz', b, hb, hzb⟩ := Submodule.mem_sup.1 (condOne Z hZ x).2
  let uz := ofCondOne Z hZ ⟨z, Submodule.mem_sup_left hz'⟩
  let ub := ofCondOne Z hZ ⟨b, Submodule.mem_sup_right hb⟩
  have hb0 : (Submodule.Quotient.mk ub : extendedKummerQuot E m A M ι hι) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hb
  have hx : x = uz + ub := Subtype.ext hzb.symm
  rw [hx, map_add]
  change ∃ a, γ a = (Submodule.Quotient.mk uz : extendedKummerQuot E m A M ι hι) +
    Submodule.Quotient.mk ub
  rw [hb0, add_zero]
  exact hz z hz'

end ExtendedKummerGenerators

section CokernelCohomology

variable {R : Type} [CommRing R]

/-- When the outgoing differential vanishes, cohomology is the cokernel of the incoming differential. -/
def homologyCokernelEquiv (C : GCx R) (n : ℤ) (hd : C.d n (n + 1) rfl = 0) :
    C.toCC.homology n ≃ₗ[R] (C.X n ⧸ LinearMap.range (C.d (n - 1) n (by omega))) := by
  have hk : LinearMap.ker (C.d n (n + 1) rfl) = ⊤ := LinearMap.ker_eq_top.2 hd
  let e := LinearEquiv.ofTop _ hk
  have hm : ((LinearMap.range (C.d (n - 1) n (by omega))).comap
      (LinearMap.ker (C.d n (n + 1) rfl)).subtype).map e.toLinearMap =
      LinearMap.range (C.d (n - 1) n (by omega)) := by
    change ((LinearMap.range (C.d (n - 1) n (by omega))).comap
      (LinearMap.ker (C.d n (n + 1) rfl)).subtype).map
      (LinearMap.ker (C.d n (n + 1) rfl)).subtype = _
    rw [Submodule.map_comap_eq, Submodule.range_subtype, hk, top_inf_eq]
  exact (homologySubquotEquiv C n).trans (Submodule.Quotient.equiv _ _ e hm)

end CokernelCohomology

section CocycleRightExact

open ZInQ.Manuscript.RC.CoefModules

variable {A G M : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (Z : Submodule A (contCochain A G M 1)) (hZ : ∀ z ∈ Z, contD A G M 1 z = 0)

/-- The degree-zero differential has precisely the continuous coboundaries as its image. -/
theorem cocycleCondition_range_d_zero :
    LinearMap.range ((cocycleCondition Z hZ).d 0 1 rfl) = condB1 Z hZ := by
  ext x
  rw [LinearMap.mem_range, mem_condB1]
  constructor
  · rintro ⟨y, rfl⟩
    exact (mem_contB1_iff _).2 ⟨(condZero Z hZ y : contCochain A G M 0),
      (cocycleCondition_d₀ Z hZ y).symm⟩
  · intro hx
    obtain ⟨c, hc⟩ := (mem_contB1_iff _).1 hx
    refine ⟨ofCondZero Z hZ c, ?_⟩
    apply Subtype.ext
    exact (cocycleCondition_d₀ Z hZ (ofCondZero Z hZ c)).trans hc

/-- Right exactness identifies residual first cohomology of a two-term cocycle condition
with the scalar extension of its first cohomology quotient. -/
def cocycleConditionBaseChangeH1Equiv (B : Type) [CommRing B] [Algebra A B] :
    (gcxBaseChange B (cocycleCondition Z hZ)).toCC.homology 1 ≃ₗ[B]
      (B ⊗[A] ((cocycleCondition Z hZ).X 1 ⧸ condB1 Z hZ)) := by
  let U := cocycleCondition Z hZ
  let f := U.d 0 1 rfl
  let q := (condB1 Z hZ).mkQ
  have hex : Function.Exact f q := by
    rw [LinearMap.exact_iff]
    dsimp only [q]
    rw [Submodule.ker_mkQ]
    exact (cocycleCondition_range_d_zero Z hZ).symm
  have hexB : Function.Exact (f.baseChange B) (q.baseChange B) :=
    lTensor_exact B hex (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker (q.baseChange B) = LinearMap.range (f.baseChange B) :=
    LinearMap.exact_iff.mp hexB
  have hd : U.d 1 2 rfl = 0 := LinearMap.ext (cocycleCondition_d₁ Z hZ)
  have hdB : (gcxBaseChange B U).d 1 2 rfl = 0 := by
    change (U.d 1 2 rfl).baseChange B = 0
    rw [hd, LinearMap.baseChange_zero]
  exact (homologyCokernelEquiv (gcxBaseChange B U) 1 hdB).trans
    ((Submodule.quotEquivOfEq _ _ hk.symm).trans
      ((q.baseChange B).quotKerEquivOfSurjective
        (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _))))

/-- Continuous zero-cochains are the coefficient module itself. -/
def continuousZeroCochainEquiv (R : Type) [CommRing R] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (N : Type) [AddCommGroup N] [Module R N]
    [DistribMulAction G N] [SMulCommClass G R N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul G N] : (contCochains R G N).X 0 ≃ₗ[R] N where
  toFun f := cFun f default
  invFun n := (contSubCx R G N).ofSub (constCochain (k := R) (G := G) n)
  left_inv f := Subtype.ext (funext fun _x => congrArg (cFun f) (Subsingleton.elim _ _))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reduction of the zeroth term of a cocycle condition is reduction of its coefficients. -/
def cocycleConditionBaseChangeZeroEquiv (B : Type) [CommRing B] [Algebra A B]
    [CompactSpace G] :
    (gcxBaseChange B (cocycleCondition Z hZ)).X 0 ≃ₗ[B] BCoef A B M :=
  (LinearEquiv.baseChange A B _ _ (LinearEquiv.ofTop (⊤ : Submodule A (contCochain A G M 0)) rfl)).trans
    ((cochainBaseChangeEquiv A B G M 0).trans (continuousZeroCochainEquiv B G (BCoef A B M)))

end CocycleRightExact

section BinaryPointTensors

open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra

/-- Re-expressing a point tensor over the canonical binary residue field. -/
def stagePointTensorEquiv (i : ℕ) [NeZero i] (P : Type) [AddCommGroup P] :
    LinearEquiv (σ' := ((stageResidueFieldEquiv i).symm : ZMod 2 →+* ResidueField (Acoef i)))
      (stageResidueFieldEquiv i : ResidueField (Acoef i) →+* ZMod 2)
      (ResidueField (Acoef i) ⊗[ℤ] P) (ZMod 2 ⊗[ℤ] P) := by
  let E := (TensorProduct.congr (stageResidueFieldEquiv i).toAddEquiv.toIntLinearEquiv
    (LinearEquiv.refl ℤ P)).toAddEquiv
  refine { E with map_smul' := ?_ }
  intro c x
  rcases stageResidueField_zero_or_one i c with rfl | rfl
  · simp only [zero_smul, map_zero]
    exact E.map_zero
  · simp only [one_smul, map_one]

/-- A finite local point quotient modulo two gives a finite binary point tensor. -/
theorem finite_point_tensor_of_mod_two (P : Type) [AddCommGroup P]
    (hP : Finite (P ⧸ (nsmulAddMonoidHom (α := P) 2).range)) : Finite (ZMod 2 ⊗[ℤ] P) := by
  let f := (TensorProduct.mk ℤ (ZMod 2) P 1).toAddMonoidHom
  have hker : (nsmulAddMonoidHom (α := P) 2).range ≤ f.ker := by
    rintro _ ⟨p, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change f (2 • p) = 0
    rw [map_nsmul]
    have hsmul : ((2 : ℕ) : ZMod 2) • f p = (2 : ℕ) • f p :=
      Nat.cast_smul_eq_nsmul (ZMod 2) _ _
    rw [← hsmul, show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_smul]
  let q := QuotientAddGroup.lift (nsmulAddMonoidHom (α := P) 2).range f hker
  have hf : Function.Surjective f :=
    TensorProduct.mk_surjective ℤ P (ZMod 2) (fun z => ⟨(z.val : ℤ), by simp⟩)
  have hq : Function.Surjective q := fun x => by
    obtain ⟨p, hp⟩ := hf x
    exact ⟨QuotientAddGroup.mk p, hp⟩
  have := hP
  exact Finite.of_surjective q hq

/-- The fixed binary point tensor of a local elliptic curve is finite by Kummer injection
and local Galois cohomology finiteness. -/
theorem localPointTensor_finite (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]
    (E : WeierstrassCurve (v.adicCompletion K)) [E.IsElliptic] (hloc : MilneLocalFiniteness) :
    Finite (ZMod 2 ⊗[ℤ] E.toAffine.Point) := by
  have hH := hloc K v ℤ (TorsAlg (v.adicCompletion K) E 2) inferInstance 1
  have hP : Finite (E.toAffine.Point ⧸ (nsmulAddMonoidHom (α := E.toAffine.Point) 2).range) :=
    Finite.of_injective _ (kummerMapH1_injective (v.adicCompletion K) E 2)
  exact finite_point_tensor_of_mod_two _ hP

end BinaryPointTensors

section ProductCohomologyRanks

variable {R : Type} [Field R] {ι : Type} [Fintype ι]

/-- The cohomology rank of a finite product is at most the sum of the cohomology ranks.
The comparison is the product of the maps on cocycles modulo coboundaries. -/
theorem piCx_finrank_homology_le (Cs : ι → GCx R) (n : ℤ)
    (hC : ∀ v, Module.Finite R ((Cs v).toCC.homology n)) :
    Module.finrank R ((piCx Cs).toCC.homology n) ≤
      ∑ v, Module.finrank R ((Cs v).toCC.homology n) := by
  let Kp := LinearMap.ker ((piCx Cs).d n (n + 1) rfl)
  let Bp := (LinearMap.range ((piCx Cs).d (n - 1) n (by omega))).comap Kp.subtype
  let Kv := fun v => LinearMap.ker ((Cs v).d n (n + 1) rfl)
  let Bv := fun v => (LinearMap.range ((Cs v).d (n - 1) n (by omega))).comap (Kv v).subtype
  let Qv := fun v => (Kv v ⧸ Bv v)
  let c : ∀ v, Kp →ₗ[R] Kv v := fun v => LinearMap.codRestrict _
    ((LinearMap.proj v).comp Kp.subtype) (fun x => (congrFun x.2 v))
  let Φ : Kp →ₗ[R] ∀ v, Qv v := LinearMap.pi fun v => (Bv v).mkQ.comp (c v)
  have hB : Bp ≤ LinearMap.ker Φ := by
    rintro x ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    funext v
    change (Bv v).mkQ (c v x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨y v, ?_⟩
    exact congrFun hy v
  have hker : LinearMap.ker Φ ≤ Bp := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hv : ∀ v, ∃ y : (Cs v).X (n - 1),
        (Cs v).d (n - 1) n (by omega) y = (x : (piCx Cs).X n) v := by
      intro v
      have hxv := congrFun hx v
      change (Bv v).mkQ (c v x) = 0 at hxv
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxv
      exact hxv
    choose y hy using hv
    exact ⟨y, funext hy⟩
  let q := Bp.liftQ Φ hB
  have hq : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hQ : ∀ v, Module.Finite R (Qv v) := fun v =>
    (Module.Finite.equiv_iff (homologySubquotEquiv (Cs v) n)).1 (hC v)
  have : Module.Finite R (∀ v, Qv v) := inferInstance
  let f := q.comp (homologySubquotEquiv (piCx Cs) n).toLinearMap
  have hf : Function.Injective f := hq.comp (homologySubquotEquiv (piCx Cs) n).injective
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  change Module.finrank R ((piCx Cs).toCC.homology n) ≤ Module.finrank R (∀ v, Qv v) at hd
  rw [Module.finrank_pi_fintype] at hd
  calc
    Module.finrank R ((piCx Cs).toCC.homology n) ≤ ∑ v, Module.finrank R (Qv v) := hd
    _ = ∑ v, Module.finrank R ((Cs v).toCC.homology n) :=
      Finset.sum_congr rfl fun v _ => (homologySubquotEquiv (Cs v) n).finrank_eq.symm

end ProductCohomologyRanks

section ScalarRanks

variable {R S M N : Type} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- A scalar-compatible module isomorphism preserves finite rank. -/
theorem scalar_finrank_eq (eR : R ≃+* S)
    (eM : LinearEquiv (σ' := (eR.symm : S →+* R)) (eR : R →+* S) M N) :
    Module.finrank R M = Module.finrank S N := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv eR eM.toAddEquiv eR.bijective (fun c x => eM.map_smulₛₗ c x)

end ScalarRanks

section ResiduePresentations

open ZInQ.Manuscript.RC.HeegnerAlgebra

/-- The two presentations of a stage residual tensor are scalar-compatibly isomorphic. -/
def stageTensorScalarEquiv (i : ℕ) [NeZero i] (N : Type) [AddCommGroup N] [Module (Acoef i) N] :
    LinearEquiv (σ' := ((stageResidueFieldEquiv i).symm : ZMod 2 →+* ResidueField (Acoef i)))
      (stageResidueFieldEquiv i : ResidueField (Acoef i) →+* ZMod 2)
      (ResidueField (Acoef i) ⊗[Acoef i] N) (ZMod 2 ⊗[Acoef i] N) := by
  let E := stageResidueTensorEquiv i N
  refine { E with map_smul' := ?_ }
  intro c x
  rcases stageResidueField_zero_or_one i c with rfl | rfl
  · simp only [zero_smul, map_zero]
    exact E.map_zero
  · simp only [one_smul, map_one]

/-- Changing the residue-field presentation commutes with every differential. -/
def stageResidualPresentationEquiv (i : ℕ) [NeZero i] (C : GCx (Acoef i)) :
    ComplexScalarEquiv (stageResidueFieldEquiv i)
      (gcxBaseChange (ResidueField (Acoef i)) C) (gcxBaseChange (ZMod 2) C) where
  component n := stageTensorScalarEquiv i (C.X n)
  comm a b h x := by
    let F := (stageTensorScalarEquiv i (C.X b)).toAddMonoidHom.comp
      ((C.d a b h).baseChange (ResidueField (Acoef i))).toAddMonoidHom
    let G := ((C.d a b h).baseChange (ZMod 2)).toAddMonoidHom.comp
      (stageTensorScalarEquiv i (C.X a)).toAddMonoidHom
    change F x = G x
    induction x using TensorProduct.inductionOn with
    | tmul c y => rfl
    | add x y hx hy =>
      exact (F.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (G.map_add x y).symm)

end ResiduePresentations

section KummerLocalRanks

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
  (E : WeierstrassCurve F) [E.IsElliptic] (m : ℕ) [NeZero m]
  (i : ℕ) [NeZero i] (M : Type) [AddCommGroup M] [Module (Acoef i) M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) (Acoef i) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (ι : TorsAlg F E m →+ M)
  (hι : ∀ (g : Field.absoluteGaloisGroup F) t, ι (g • t) = g • ι t)

/-- The residual first Kummer cohomology is bounded by one fixed binary local point module,
without any assumption that the residual local conditions themselves are constant. -/
theorem stageKummerLocal_finrank_one [Finite (ZMod 2 ⊗[ℤ] E.toAffine.Point)] :
    Module.finrank (ResidueField (Acoef i))
        ((gcxBaseChange (ResidueField (Acoef i)) (kummerConditionIn (Acoef i) ι hι)).toCC.homology 1) ≤
      Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point) := by
  let Q := extendedKummerQuot E m (Acoef i) M ι hι
  let U := kummerConditionIn (Acoef i) ι hι
  let ep := stageResidualPresentationEquiv i U
  let eH := cocycleConditionBaseChangeH1Equiv (kummerZ' (Acoef i) ι)
    (kummerZ'_cocycle (Acoef i) ι hι) (ZMod 2)
  let eC := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (Acoef i) (ZMod 2) (ZMod 2) E.toAffine.Point
  have : Finite (ZMod 2 ⊗[Acoef i] (Acoef i ⊗[ℤ] E.toAffine.Point)) :=
    Finite.of_injective _ eC.injective
  have : Module.Finite (ZMod 2) (ZMod 2 ⊗[Acoef i] (Acoef i ⊗[ℤ] E.toAffine.Point)) :=
    Module.Finite.of_finite
  have hγ := LinearMap.baseChange_surjective (ZMod 2)
    (extendedKummerEnvelope_surjective E m (Acoef i) M ι hι)
  have hr := LinearMap.finrank_le_finrank_of_surjective hγ
  calc
    Module.finrank (ResidueField (Acoef i))
        ((gcxBaseChange (ResidueField (Acoef i)) U).toCC.homology 1) =
        Module.finrank (ZMod 2) ((gcxBaseChange (ZMod 2) U).toCC.homology 1) := ep.finrank_homology 1
    _ = Module.finrank (ZMod 2) (ZMod 2 ⊗[Acoef i] Q) := eH.finrank_eq
    _ ≤ Module.finrank (ZMod 2) (ZMod 2 ⊗[Acoef i] (Acoef i ⊗[ℤ] E.toAffine.Point)) := hr
    _ = Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point) := eC.finrank_eq

omit [CharZero F] [DecidableEq F] in
/-- Zeroth residual cohomology of a cocycle condition is bounded by its residual coefficient module. -/
theorem stageCocycleLocal_finrank_zero [Finite M]
    (Z : Submodule (Acoef i) (contCochain (Acoef i) (Field.absoluteGaloisGroup F) M 1))
    (hZ : ∀ z ∈ Z, contD (Acoef i) (Field.absoluteGaloisGroup F) M 1 z = 0) :
    Module.finrank (ResidueField (Acoef i))
        ((gcxBaseChange (ResidueField (Acoef i)) (cocycleCondition Z hZ)).toCC.homology 0) ≤
      Module.finrank (ResidueField (Acoef i)) (BCoef (Acoef i) (ResidueField (Acoef i)) M) := by
  let k := ResidueField (Acoef i)
  have : Finite k := finite_residueField
  have : Finite (BCoef (Acoef i) k M) := finite_bcoef _ _ _
  let e := cocycleConditionBaseChangeZeroEquiv Z hZ k
  have : Finite ((gcxBaseChange k (cocycleCondition Z hZ)).X 0) := Finite.of_injective _ e.injective
  have : Module.Finite k ((gcxBaseChange k (cocycleCondition Z hZ)).X 0) := Module.Finite.of_finite
  exact (homology_finrank_le_term _ 0).trans_eq e.finrank_eq

/-- A uniform all-degree local bound for the actual extended Kummer condition. -/
theorem stageKummerLocal_finrank_le [Finite M] [Finite (ZMod 2 ⊗[ℤ] E.toAffine.Point)] (n : ℤ) :
    Module.finrank (ResidueField (Acoef i))
        ((gcxBaseChange (ResidueField (Acoef i)) (kummerConditionIn (Acoef i) ι hι)).toCC.homology n) ≤
      Module.finrank (ResidueField (Acoef i)) (BCoef (Acoef i) (ResidueField (Acoef i)) M) +
        Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point) := by
  by_cases h0 : n = 0
  · subst n
    exact (stageCocycleLocal_finrank_zero i M _ _).trans (Nat.le_add_right _ _)
  · by_cases h1 : n = 1
    · subst n
      exact (stageKummerLocal_finrank_one E m i M ι hι).trans (Nat.le_add_left _ _)
    · have hn : n < 0 ∨ 1 < n := by omega
      have : Subsingleton ((gcxBaseChange (ResidueField (Acoef i))
          (kummerConditionIn (Acoef i) ι hι)).toCC.homology n) :=
        baseChange_homology_subsingleton_of_term _ _ n (cocycleCondition_term_range _ _ n hn)
      rw [Module.finrank_zero_of_subsingleton]
      exact Nat.zero_le _

end KummerLocalRanks

section KummerSelmerBounds

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.RankCounts

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (Bv v).IsElliptic]

/-- The uniform Kummer bound uses only fixed global and local binary cohomology and
fixed local point modules modulo two. -/
def kummerSelmerRankBound (hS : S.Finite) : ℕ :=
  letI : Fintype (Places K S) := hS.fintype
  fixedGlobalRankBound K S (TwoTorsionResidual K S W) +
    fixedLocalRankBound K S (TwoTorsionResidual K S W) +
    ∑ v : Places K S, (Module.finrank (ZMod 2) (TwoTorsionResidual K S W) +
      Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point))

variable {K S W Bv}

/-- The actual Kummer stage Selmer complexes satisfy one stage-independent residual rank bound.
No residual-complex constancy or cohomology bound is assumed. -/
theorem stageKummerSelmer_hB (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ) [IsOpenKer α]
    (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (hE2 : FullTorsion K S W 2) (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (m : ℕ) [NeZero m]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (Bv v) m →+
      ResMod (locMap K S v.1) (Mcoef K S W (j + 1) α))
    (hι : ∀ v (g : Gloc K v.1) t, ι v (g • t) = g • ι v t) (n : ℤ) :
    Module.finrank (ResidueField (Acoef (j + 1)))
        (residualCohomologyAt (selCx (galoisSelData K S (Acoef (j + 1)) (Mcoef K S W (j + 1) α)
          (kummerGaloisLocalConditions K S Bv m (Acoef (j + 1)) (Mcoef K S W (j + 1) α) ι hι))) n) ≤
      kummerSelmerRankBound K S W Bv hS := by
  classical
  let : Fintype (Places K S) := hS.fintype
  let A := Acoef (j + 1)
  let k := ResidueField A
  let Mj := Mcoef K S W (j + 1) α
  let Δ := kummerGaloisLocalConditions K S Bv m A Mj ι hι
  let D := galoisSelData K S A Mj Δ
  let EG := stageGlobalResidualEquiv j α hT hM hE2
  let EL := stageLocalSumResidualEquiv j α hT hM hE2
  have : Finite k := finite_residueField
  have hGF := fixedGlobalCohomology_finite K S (TwoTorsionResidual K S W) hglob hS h2 n
  have hLF : ∀ a, Finite ((fixedLocalSumCx K S (TwoTorsionResidual K S W)).toCC.homology a) :=
    fixedLocalCohomology_finite K S (TwoTorsionResidual K S W) hloc hS
  have hDG : Module.Finite k ((gcxBaseChange k D.G).toCC.homology n) := by
    have : Finite ((gcxBaseChange k D.G).toCC.homology n) := Finite.of_injective _ (EG.homology n).injective
    exact Module.Finite.of_finite
  have hDL : Module.Finite k ((gcxBaseChange k D.L).toCC.homology (n - 1)) := by
    have := hLF (n - 1)
    have : Finite ((gcxBaseChange k D.L).toCC.homology (n - 1)) :=
      Finite.of_injective _ (EL.homology (n - 1)).injective
    exact Module.Finite.of_finite
  have hUV : ∀ v, Module.Finite k ((gcxBaseChange k (Δ.U v)).toCC.homology n) := by
    intro v
    have : Finite (ResMod (locMap K S v.1) Mj) := inferInstanceAs (Finite Mj)
    exact residualCohomologyFinite_cocycleCondition _ _
      (hloc K v.1 A (ResMod (locMap K S v.1) Mj) inferInstance 1) n
  have hUv : ∀ v, Module.finrank k ((gcxBaseChange k (Δ.U v)).toCC.homology n) ≤
      Module.finrank (ZMod 2) (TwoTorsionResidual K S W) +
        Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point) := by
    intro v
    have : Finite (ResMod (locMap K S v.1) Mj) := inferInstanceAs (Finite Mj)
    have : Finite (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point) := localPointTensor_finite K v.1 (Bv v) hloc
    have hr := stageKummerLocal_finrank_le (Bv v) m (j + 1)
      (ResMod (locMap K S v.1) Mj) (ι v) (hι v) n
    have he := scalar_finrank_eq (stageResidueFieldEquiv (j + 1))
      (stageRestrictedCoefResidualEquiv j α hT hM hE2 (locMap K S v.1))
    rw [he] at hr
    exact hr
  let eU := homologyIsoOfBijective (piBaseChangeHom k Δ.U) (piBaseChangeHom_bijective k Δ.U) n
  have hUF : Finite ((piCx fun v => gcxBaseChange k (Δ.U v)).toCC.homology n) :=
    finite_homology_piCx _ n (fun v => by
      have := hUV v
      exact Module.finite_of_finite k)
  have hDU : Module.Finite k ((gcxBaseChange k D.U).toCC.homology n) := by
    have : Finite ((gcxBaseChange k D.U).toCC.homology n) :=
      Finite.of_injective _ eU.toLinearEquiv.injective
    exact Module.Finite.of_finite
  have hUb : Module.finrank k ((gcxBaseChange k D.U).toCC.homology n) ≤
      ∑ v : Places K S, (Module.finrank (ZMod 2) (TwoTorsionResidual K S W) +
        Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point)) := by
    change Module.finrank k ((gcxBaseChange k (piCx Δ.U)).toCC.homology n) ≤ _
    rw [eU.toLinearEquiv.finrank_eq]
    exact (piCx_finrank_homology_le _ n hUV).trans (Finset.sum_le_sum fun v _ => hUv v)
  have hGb : Module.finrank k ((gcxBaseChange k D.G).toCC.homology n) ≤
      fixedGlobalRankBound K S (TwoTorsionResidual K S W) := by
    change Module.finrank (ResidueField (Acoef (j + 1)))
      ((gcxBaseChange (ResidueField (Acoef (j + 1)))
        (globalCx (Acoef (j + 1)) (GKS K S) (Mcoef K S W (j + 1) α))).toCC.homology n) ≤ _
    rw [EG.finrank_homology n]
    exact finrank_le_finiteRangeRankBound _ 0 2
      (globalBinary_homology_range K S (TwoTorsionResidual K S W) h410 hK hS h2) n
  have hLb : Module.finrank k ((gcxBaseChange k D.L).toCC.homology (n - 1)) ≤
      fixedLocalRankBound K S (TwoTorsionResidual K S W) := by
    change Module.finrank (ResidueField (Acoef (j + 1)))
      ((gcxBaseChange (ResidueField (Acoef (j + 1)))
        (localSumCx (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (Mcoef K S W (j + 1) α))).toCC.homology (n - 1)) ≤ _
    rw [EL.finrank_homology (n - 1)]
    exact finrank_le_finiteRangeRankBound _ 0 2
      (fixedLocalCohomology_range K S (TwoTorsionResidual K S W) hlcd) (n - 1)
  have hs := residualSelmer_finrank_le D n
  change Module.finrank k (residualCohomologyAt (selCx D) n) ≤
    fixedGlobalRankBound K S (TwoTorsionResidual K S W) +
    fixedLocalRankBound K S (TwoTorsionResidual K S W) +
    ∑ v : Places K S, (Module.finrank (ZMod 2) (TwoTorsionResidual K S W) +
      Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point))
  exact (hs.trans (Nat.add_le_add (Nat.add_le_add hGb hUb) hLb)).trans_eq (by omega)

end KummerSelmerBounds

section FamilyBounds

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ) [∀ i, IsOpenKer (α i)]
  (hTor : ∀ i : ℕ, FullTorsion K S W (2 ^ i))
  (h410 : MilneADT_I_4_10_totallyComplex) (hlcd : MilneLocalDimensionTwo)
  (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
  (hK : IsTotallyComplex K) (hS : S.Finite)
  (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hTor h410 hlcd hloc hglob hK hS h2 in
/-- The strict and relaxed actual stage families supply both boundedness hypotheses of
the retained producer, with `lo = 0`, `hi = 3`, and one uniform natural-number bound. -/
theorem strictRelaxed_producerBounds :
    ∃ B : ℕ,
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (actualSelData_zero W i (α i))) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (actualSelData_full W i (α i))) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (actualSelData_zero W i (α i))) n) ≤ B) ∧
      (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (actualSelData_full W i (α i))) n) ≤ B) := by
  have hE2 : FullTorsion K S W 2 := by simpa using hTor 1
  refine ⟨strictRelaxedRankBound K S (TwoTorsionResidual K S W), ?_, ?_, ?_, ?_⟩
  · intro i _ n hn
    exact stageStrictSelmer_hbdd W i (α i) h410 hlcd hK hS h2 n hn
  · intro i _ n hn
    exact stageRelaxedSelmer_hbdd W i (α i) h410 hlcd hK hS h2 n hn
  · intro i _ n
    cases i with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ j => exact (stageStrictRelaxedSelmer_hB W j (α (j + 1)) (hTor (j + 1)) (hTor j)
        hE2 h410 hlcd hloc hglob hK hS h2 n).1
  · intro i _ n
    cases i with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ j => exact (stageStrictRelaxedSelmer_hB W j (α (j + 1)) (hTor (j + 1)) (hTor j)
        hE2 h410 hlcd hloc hglob hK hS h2 n).2

variable [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (Bv v).IsElliptic]
  (m : ℕ → ℕ) [∀ i, NeZero (m i)]
  (ι : ∀ (i : ℕ) (v : Places K S), TorsAlg (v.1.adicCompletion K) (Bv v) (m i) →+
    ResMod (locMap K S v.1) (Mcoef K S W i (α i)))
  (hι : ∀ (i : ℕ) (v : Places K S) (g : Gloc K v.1) t, ι i v (g • t) = g • ι i v t)

include hTor h410 hlcd hloc hglob hK hS h2 in
/-- The actual Kummer stage family supplies both retained-producer hypotheses. The local
elliptic curves are fixed, while the torsion levels and coefficient maps may vary with the stage. -/
theorem kummer_producerBounds :
    ∃ B : ℕ,
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (galoisSelData K S (Acoef i) (Mcoef K S W i (α i))
          (kummerGaloisLocalConditions K S Bv (m i) (Acoef i) (Mcoef K S W i (α i)) (ι i) (hι i)))) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (galoisSelData K S (Acoef i) (Mcoef K S W i (α i))
          (kummerGaloisLocalConditions K S Bv (m i) (Acoef i) (Mcoef K S W i (α i)) (ι i) (hι i)))) n) ≤ B) := by
  have hE2 : FullTorsion K S W 2 := by simpa using hTor 1
  refine ⟨kummerSelmerRankBound K S W Bv hS, ?_, ?_⟩
  · intro i _ n hn
    exact stageKummerSelmer_hbdd W i (α i) h410 hlcd hK hS h2 Bv (m i) (ι i) (hι i) n hn
  · intro i _ n
    cases i with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ j =>
      exact stageKummerSelmer_hB (W := W) (Bv := Bv) j (α (j + 1))
        (hTor (j + 1)) (hTor j) hE2 h410 hlcd hloc hglob hK hS h2 (m (j + 1))
        (ι (j + 1)) (hι (j + 1)) n

end FamilyBounds

section TwoTermBounds

open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (rel01)

variable (i : ℕ) [NeZero i] (V : Type) [AddCommGroup V] [Module (Acoef i) V]
  (f : V →ₗ[Acoef i] V)

/-- The two-term complex of an endomorphism, in degrees zero and one. -/
abbrev endomorphismTwoTermCx : GCx (Acoef i) :=
  ofCC (HomologicalComplex.double (ModuleCat.ofHom f) rel01)

omit [NeZero i] in
/-- A two-term complex has zero terms outside degrees zero and one. -/
theorem endomorphismTwoTermCx_term_range (n : ℤ) (hn : n < 0 ∨ 1 < n) :
    Subsingleton ((endomorphismTwoTermCx i V f).X n) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (HomologicalComplex.isZero_double_X (ModuleCat.ofHom f) rel01 n (by omega) (by omega))

/-- Residual cohomology of a two-term endomorphism complex is bounded by its residual coefficient rank. -/
theorem endomorphismTwoTermCx_residual_rank [Finite V] (n : ℤ) :
    Module.finrank (ResidueField (Acoef i))
        ((gcxBaseChange (ResidueField (Acoef i)) (endomorphismTwoTermCx i V f)).toCC.homology n) ≤
      Module.finrank (ResidueField (Acoef i)) (BCoef (Acoef i) (ResidueField (Acoef i)) V) := by
  let k := ResidueField (Acoef i)
  have : Finite k := finite_residueField
  have : Finite (BCoef (Acoef i) k V) := finite_bcoef _ _ _
  by_cases h0 : n = 0
  · subst n
    let e : (gcxBaseChange k (endomorphismTwoTermCx i V f)).X 0 ≃ₗ[k] BCoef (Acoef i) k V :=
      LinearEquiv.baseChange (Acoef i) k _ _
        (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom f) rel01).toLinearEquiv
    have : Finite ((gcxBaseChange k (endomorphismTwoTermCx i V f)).X 0) := Finite.of_injective _ e.injective
    have : Module.Finite k ((gcxBaseChange k (endomorphismTwoTermCx i V f)).X 0) := Module.Finite.of_finite
    exact (homology_finrank_le_term _ 0).trans_eq e.finrank_eq
  · by_cases h1 : n = 1
    · subst n
      let e : (gcxBaseChange k (endomorphismTwoTermCx i V f)).X 1 ≃ₗ[k] BCoef (Acoef i) k V :=
        LinearEquiv.baseChange (Acoef i) k _ _
          (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom f) rel01 (by decide)).toLinearEquiv
      have : Finite ((gcxBaseChange k (endomorphismTwoTermCx i V f)).X 1) := Finite.of_injective _ e.injective
      have : Module.Finite k ((gcxBaseChange k (endomorphismTwoTermCx i V f)).X 1) := Module.Finite.of_finite
      exact (homology_finrank_le_term _ 1).trans_eq e.finrank_eq
    · have : Subsingleton ((gcxBaseChange k (endomorphismTwoTermCx i V f)).toCC.homology n) :=
        baseChange_homology_subsingleton_of_term _ _ n
          (endomorphismTwoTermCx_term_range i V f n (by omega))
      rw [Module.finrank_zero_of_subsingleton]
      exact Nat.zero_le _

end TwoTermBounds

section OldAmplitude

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (frob eUr)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (i : ℕ) [NeZero i] (M₀ : Type) [AddCommGroup M₀] [Module (Acoef i) M₀]
  [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) (Acoef i) M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]

/-- The unramified condition at a new place is a two-term complex. -/
theorem urAt_term_range (v : Places K S) (hv : v.1 ∉ S₀) (n : ℤ) (hn : n < 0 ∨ 1 < n) :
    Subsingleton ((urAt hS (Acoef i) M₀ v hv).U.X n) :=
  endomorphismTwoTermCx_term_range i (urRep (Acoef i) M₀ (newPlace v hv)).V
    (frob (eUr K v.1) (urRep (Acoef i) M₀ (newPlace v hv)) - 1) n hn

/-- The unramified residual cohomology rank is bounded by the residual coefficient rank. -/
theorem urAt_residual_rank (v : Places K S) (hv : v.1 ∉ S₀) (n : ℤ) :
    Module.finrank (ResidueField (Acoef i))
        ((gcxBaseChange (ResidueField (Acoef i)) (urAt hS (Acoef i) M₀ v hv).U).toCC.homology n) ≤
      Module.finrank (ResidueField (Acoef i)) (BCoef (Acoef i) (ResidueField (Acoef i)) M₀) :=
  endomorphismTwoTermCx_residual_rank i (urRep (Acoef i) M₀ (newPlace v hv)).V
    (frob (eUr K v.1) (urRep (Acoef i) M₀ (newPlace v hv)) - 1) n

variable (W : WeierstrassCurve K) [W.IsElliptic] (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

omit [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)] in
/-- Old conditions with full or two-term shape, together with unramified new conditions,
supply the producer's residual range. -/
theorem actualStageSelmer_hbdd (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v hv, (c v hv).U = locAt K S (Acoef i) (MinS hS W i α) v ∨
      ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton ((c v hv).U.X n)) :
    ∀ n : ℤ, n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
      (residualCohomologyAt (selCx (actualSelData hS W i α c)) n) = 0 := by
  letI : TopologicalSpace (Acoef i) := acoefTop i
  have : DiscreteTopology (Acoef i) := acoefTop_discrete i
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  apply stageSelmer_residual_range K S i (MinS hS W i α) h410 hlcd hK hSfin h2 _
  intro v
  change (urOutside hS (Acoef i) (Mcoef K S₀ W i α) c v).U =
      locAt K S (Acoef i) (MinS hS W i α) v ∨
    ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton
      ((urOutside hS (Acoef i) (Mcoef K S₀ W i α) c v).U.X n)
  unfold urOutside
  split_ifs with hv
  · exact hc v hv
  · exact Or.inr (fun n hn => urAt_term_range hS i (Mcoef K S₀ W i α) v hv n (by omega))

end OldAmplitude

section StandardConditions

open ZInQ.Manuscript.RC.CoefModules

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

/-- The usual old local conditions: zero, full, or a Kummer condition.
The labels zero and one select zero and full; every other label selects Kummer. -/
def standardOldAt (v : Places K S) [DecidableEq (v.1.adicCompletion K)] (label : ℕ)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) : CondAt K S A M v :=
  if label = 0 then zeroAt K S A M v else
  if label = 1 then fullAt K S A M v else
    ⟨kummerConditionIn A ι hι, kummerConditionInι A ι hι⟩

/-- Every standard old condition is full or has terms only in degrees zero and one. -/
theorem standardOldAt_amplitude (v : Places K S) [DecidableEq (v.1.adicCompletion K)] (label : ℕ)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) :
    (standardOldAt K S A M v label E m ι hι).U = locAt K S A M v ∨
      ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton ((standardOldAt K S A M v label E m ι hι).U.X n) := by
  unfold standardOldAt
  split_ifs
  · exact Or.inr (fun _ _ => inferInstanceAs (Subsingleton PUnit))
  · exact Or.inl rfl
  · exact Or.inr (fun n hn => cocycleCondition_term_range _ _ n (by omega))

end StandardConditions

section InflatedCoefficients

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]

/-- The fixed residual representation inflated from the coefficient support to the Selmer support. -/
abbrev inflatedResidualModule : Type := ResMod (inflMap K hS) (TwoTorsionResidual K S₀ W)

variable (j : ℕ) (α : GKS K S₀ →* (Acoef (j + 1))ˣ) [IsOpenKer α]
  (hT : FullTorsion K S₀ W (2 ^ (j + 1))) (hM : FullTorsion K S₀ W (2 ^ j))
  (hE2 : FullTorsion K S₀ W 2)

/-- The global residual cochains of the inflated actual coefficient module. -/
def inflatedGlobalResidualEquiv :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (globalCx (Acoef (j + 1)) (GKS K S) (MinS hS W (j + 1) α)))
      (fixedGlobalCx K S (inflatedResidualModule hS W)) :=
  stageRestrictedCochainsResidualEquiv (K := K) (S := S₀) (W := W) (H := GKS K S)
    j α hT hM hE2 (inflMap K hS)

/-- The local residual coefficient identification respects both restriction maps. -/
def inflatedLocalCoefResidualEquiv (v : Places K S) :
    LinearEquiv (σ' := ((stageResidueFieldEquiv (j + 1)).symm :
        ZMod 2 →+* ResidueField (Acoef (j + 1))))
      (stageResidueFieldEquiv (j + 1) : ResidueField (Acoef (j + 1)) →+* ZMod 2)
      (BCoef (Acoef (j + 1)) (ResidueField (Acoef (j + 1)))
        (ResMod (locMap K S v.1) (MinS hS W (j + 1) α)))
      (ResMod (locMap K S v.1) (inflatedResidualModule hS W)) where
  toFun x := stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2 x
  invFun y := (stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2).symm y
  left_inv x := (stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2).symm_apply_apply x
  right_inv y := (stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2).apply_symm_apply y
  map_add' x y := (stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2).map_add x y
  map_smul' c x := by
    rcases stageResidueField_zero_or_one (j + 1) c with rfl | rfl
    · simp only [zero_smul, map_zero]
      exact (stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2).map_zero
    · simp only [one_smul, map_one]
      exact (one_smul (ZMod 2)
        (stageCoefResidualAddEquiv (K := K) (S := S₀) (W := W) j α hT hM hE2 x)).symm

/-- The local residual cochain identification at the inflated actual module. -/
def inflatedLocalResidualEquiv (v : Places K S) :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (locAt K S (Acoef (j + 1)) (MinS hS W (j + 1) α) v))
      (locAt K S (ZMod 2) (inflatedResidualModule hS W) v) :=
  baseChangedCochainsScalarEquiv (Acoef (j + 1)) (ResidueField (Acoef (j + 1)))
    (stageResidueFieldEquiv (j + 1)) (Gloc K v.1)
    (ResMod (locMap K S v.1) (MinS hS W (j + 1) α))
    (inflatedLocalCoefResidualEquiv hS W j α hT hM hE2 v)
    (fun g x => stageCoefResidualEquiv_smul (K := K) (S := S₀) (W := W)
      j α hT hM hE2 (inflMap K hS (locMap K S v.1 g)) x)

variable [Fintype (Places K S)] [DecidableEq (Places K S)]

/-- The fixed finite direct sum of local complexes after inflation. -/
def inflatedLocalSumResidualEquiv :
    ComplexScalarEquiv (stageResidueFieldEquiv (j + 1))
      (gcxBaseChange (ResidueField (Acoef (j + 1)))
        (localSumCx (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (MinS hS W (j + 1) α)))
      (fixedLocalSumCx K S (inflatedResidualModule hS W)) :=
  (piScalarEquiv (stageResidueFieldEquiv (j + 1))
    (inflatedLocalResidualEquiv hS W j α hT hM hE2)).precompose
    (piBaseChangeHom (ResidueField (Acoef (j + 1)))
      (locAt K S (Acoef (j + 1)) (MinS hS W (j + 1) α)))
    (piBaseChangeHom_bijective (ResidueField (Acoef (j + 1))) _)

end InflatedCoefficients

section OldLocalBounds

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  (j : ℕ) (α : GKS K S₀ →* (Acoef (j + 1))ˣ) [IsOpenKer α]
  (hT : FullTorsion K S₀ W (2 ^ (j + 1))) (hM : FullTorsion K S₀ W (2 ^ j))
  (hE2 : FullTorsion K S₀ W 2)

/-- A fixed residual local maximum at an old or new place. -/
def oldLocalRankMaximum (v : Places K S) : ℕ :=
  finiteRangeRankBound (locAt K S (ZMod 2) (inflatedResidualModule hS W) v) 0 2

include hT hM hE2 in
/-- Finiteness and a uniform rank bound for each standard old condition. -/
theorem standardOldAt_residual_bound (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (label : ℕ) (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic]
    (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+ ResMod (locMap K S v.1) (MinS hS W (j + 1) α))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t)
    (hloc : MilneLocalFiniteness) (hlcd : MilneLocalDimensionTwo) (n : ℤ) :
    Module.Finite (ResidueField (Acoef (j + 1)))
        ((gcxBaseChange (ResidueField (Acoef (j + 1)))
          (standardOldAt K S (Acoef (j + 1)) (MinS hS W (j + 1) α) v label E m ι hι).U).toCC.homology n) ∧
    Module.finrank (ResidueField (Acoef (j + 1)))
        ((gcxBaseChange (ResidueField (Acoef (j + 1)))
          (standardOldAt K S (Acoef (j + 1)) (MinS hS W (j + 1) α) v label E m ι hι).U).toCC.homology n) ≤
      oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) (inflatedResidualModule hS W) +
        Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point) := by
  let k := ResidueField (Acoef (j + 1))
  let Mj := MinS hS W (j + 1) α
  let Mb := inflatedResidualModule hS W
  have : Finite k := finite_residueField
  have : Finite Mj := inferInstanceAs (Finite (Mcoef K S₀ W (j + 1) α))
  have : Finite (ResMod (locMap K S v.1) Mj) := inferInstanceAs (Finite Mj)
  have : Finite Mb := inferInstanceAs (Finite (TwoTorsionResidual K S₀ W))
  have : Finite (ResMod (locMap K S v.1) Mb) := inferInstanceAs (Finite Mb)
  rcases label with _ | _ | label
  · change Module.Finite k ((gcxBaseChange k (ZInQ.Manuscript.RC.SelmerComplex.zeroCx (Acoef (j + 1)))).toCC.homology n) ∧
      Module.finrank k ((gcxBaseChange k (ZInQ.Manuscript.RC.SelmerComplex.zeroCx (Acoef (j + 1)))).toCC.homology n) ≤ _
    have hF := residualCohomologyFinite_zeroCx (A := Acoef (j + 1)) n
    have hZ := baseChange_homology_subsingleton_of_term k
      (ZInQ.Manuscript.RC.SelmerComplex.zeroCx (Acoef (j + 1))) n
      (inferInstanceAs (Subsingleton PUnit))
    have := hZ
    exact ⟨hF, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  · change Module.Finite k ((gcxBaseChange k (locAt K S (Acoef (j + 1)) Mj v)).toCC.homology n) ∧
      Module.finrank k ((gcxBaseChange k (locAt K S (Acoef (j + 1)) Mj v)).toCC.homology n) ≤ _
    let e := inflatedLocalResidualEquiv hS W j α hT hM hE2 v
    have hF := hloc K v.1 (ZMod 2) (ResMod (locMap K S v.1) Mb) inferInstance n
    have hSrc : Finite ((gcxBaseChange k (locAt K S (Acoef (j + 1)) Mj v)).toCC.homology n) :=
      Finite.of_injective _ (e.homology n).injective
    have hRange : ∀ a : ℤ, a < 0 ∨ 2 < a → Subsingleton ((locAt K S (ZMod 2) Mb v).toCC.homology a) := by
      intro a ha
      rcases ha with ha | ha
      · exact natCx_homology_subsingleton_neg _ a ha
      · exact hlcd K v.1 (ZMod 2) (ResMod (locMap K S v.1) Mb) inferInstance a ha
    have hr := finrank_le_finiteRangeRankBound (locAt K S (ZMod 2) Mb v) 0 2 hRange n
    have he := e.finrank_homology n
    refine ⟨Module.Finite.of_finite, ?_⟩
    change Module.finrank k ((gcxBaseChange k (locAt K S (Acoef (j + 1)) Mj v)).toCC.homology n) ≤ _
    exact ((he.trans_le hr).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  · change Module.Finite k ((gcxBaseChange k (kummerConditionIn (Acoef (j + 1)) ι hι)).toCC.homology n) ∧
      Module.finrank k ((gcxBaseChange k (kummerConditionIn (Acoef (j + 1)) ι hι)).toCC.homology n) ≤ _
    have hF : Module.Finite k ((gcxBaseChange k (kummerConditionIn (Acoef (j + 1)) ι hι)).toCC.homology n) :=
      residualCohomologyFinite_cocycleCondition _ _
        (hloc K v.1 (Acoef (j + 1)) (ResMod (locMap K S v.1) Mj) inferInstance 1) n
    have : Finite (ZMod 2 ⊗[ℤ] E.toAffine.Point) := localPointTensor_finite K v.1 E hloc
    have hr := stageKummerLocal_finrank_le E m (j + 1) (ResMod (locMap K S v.1) Mj) ι hι n
    have he : Module.finrank k (BCoef (Acoef (j + 1)) k (ResMod (locMap K S v.1) Mj)) =
        Module.finrank (ZMod 2) Mb :=
      scalar_finrank_eq (stageResidueFieldEquiv (j + 1))
        (inflatedLocalCoefResidualEquiv hS W j α hT hM hE2 v)
    have hr' : Module.finrank k
        ((gcxBaseChange k (kummerConditionIn (Acoef (j + 1)) ι hι)).toCC.homology n) ≤
        Module.finrank (ZMod 2) Mb + Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point) :=
      hr.trans_eq (congrArg (fun b => b + Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point)) he)
    exact ⟨hF, hr'.trans (by
      change Module.finrank (ZMod 2) Mb + Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point) ≤
        oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) Mb +
          Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] E.toAffine.Point)
      exact Nat.add_le_add_right (Nat.le_add_left _ _) _)⟩

end OldLocalBounds

section OldBoundValue

open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (Bv v).IsElliptic]

/-- One bound for zero, full, or Kummer old conditions and unramified new conditions. -/
def oldSelmerRankBound (hSfin : S.Finite) : ℕ :=
  letI : Fintype (Places K S) := hSfin.fintype
  fixedGlobalRankBound K S (inflatedResidualModule hS W) +
    fixedLocalRankBound K S (inflatedResidualModule hS W) +
    ∑ v : Places K S, (oldLocalRankMaximum hS W v +
      Module.finrank (ZMod 2) (inflatedResidualModule hS W) +
      Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point))

end OldBoundValue

section OldSelmerBounds

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (Bv v).IsElliptic]

/-- Uniform bounded residual ranks for the actual old-support Selmer complexes, with
standard old conditions and unramified new conditions. -/
theorem actualStandardOldSelmer_hB (j : ℕ) (α : GKS K S₀ →* (Acoef (j + 1))ˣ) [IsOpenKer α]
    (hT : FullTorsion K S₀ W (2 ^ (j + 1))) (hM : FullTorsion K S₀ W (2 ^ j))
    (hE2 : FullTorsion K S₀ W 2) (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (label : Places K S → ℕ) (m : ℕ) [NeZero m]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (Bv v) m →+
      ResMod (locMap K S v.1) (MinS hS W (j + 1) α))
    (hι : ∀ v (g : Gloc K v.1) t, ι v (g • t) = g • ι v t) (n : ℤ) :
    Module.finrank (ResidueField (Acoef (j + 1)))
        (residualCohomologyAt (selCx (actualSelData hS W (j + 1) α
          (fun v _ => standardOldAt K S (Acoef (j + 1)) (MinS hS W (j + 1) α)
            v (label v) (Bv v) m (ι v) (hι v)))) n) ≤ oldSelmerRankBound hS W Bv hSfin := by
  classical
  let : Fintype (Places K S) := hSfin.fintype
  let A := Acoef (j + 1)
  letI : TopologicalSpace A := acoefTop (j + 1)
  have : DiscreteTopology A := acoefTop_discrete (j + 1)
  let k := ResidueField A
  let M₀ := Mcoef K S₀ W (j + 1) α
  let Mj := MinS hS W (j + 1) α
  let Mb := inflatedResidualModule hS W
  let c := fun (v : Places K S) (_ : v.1 ∈ S₀) =>
    standardOldAt K S A Mj v (label v) (Bv v) m (ι v) (hι v)
  let Δ := actualConditions hS W (j + 1) α c
  let D := galoisSelData K S A Mj Δ
  let EG := inflatedGlobalResidualEquiv hS W j α hT hM hE2
  let EL := inflatedLocalSumResidualEquiv hS W j α hT hM hE2
  have : Finite k := finite_residueField
  have : Finite Mj := inferInstanceAs (Finite M₀)
  have : Finite Mb := inferInstanceAs (Finite (TwoTorsionResidual K S₀ W))
  have hGF := fixedGlobalCohomology_finite K S Mb hglob hSfin h2 n
  have hLF : ∀ a, Finite ((fixedLocalSumCx K S Mb).toCC.homology a) :=
    fixedLocalCohomology_finite K S Mb hloc hSfin
  have hDG : Module.Finite k ((gcxBaseChange k D.G).toCC.homology n) := by
    have : Finite ((gcxBaseChange k D.G).toCC.homology n) := Finite.of_injective _ (EG.homology n).injective
    exact Module.Finite.of_finite
  have hDL : Module.Finite k ((gcxBaseChange k D.L).toCC.homology (n - 1)) := by
    have := hLF (n - 1)
    have : Finite ((gcxBaseChange k D.L).toCC.homology (n - 1)) :=
      Finite.of_injective _ (EL.homology (n - 1)).injective
    exact Module.Finite.of_finite
  have hV : ∀ v, Module.Finite k ((gcxBaseChange k (Δ.U v)).toCC.homology n) ∧
      Module.finrank k ((gcxBaseChange k (Δ.U v)).toCC.homology n) ≤
        oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) Mb +
          Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point) := by
    intro v
    let P : GCx A → Prop := fun C =>
      Module.Finite k ((gcxBaseChange k C).toCC.homology n) ∧
      Module.finrank k ((gcxBaseChange k C).toCC.homology n) ≤
        oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) Mb +
          Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point)
    change P (urOutside hS A M₀ c v).U
    by_cases hv : v.1 ∈ S₀
    · have heq : (urOutside hS A M₀ c v).U = (c v hv).U := by
        simp only [urOutside, dite_eq_left hv]
      have hp : P (c v hv).U :=
        standardOldAt_residual_bound hS W j α hT hM hE2 v (label v) (Bv v) m (ι v) (hι v) hloc hlcd n
      exact (congrArg P heq).mpr hp
    · have heq : (urOutside hS A M₀ c v).U = (urAt hS A M₀ v hv).U := by
        simp only [urOutside, dite_eq_right hv]
      have hF := urAt_residualCohomologyFinite (k := A) hS M₀ v hv n
      have hr := urAt_residual_rank hS (j + 1) M₀ v hv n
      have he : Module.finrank k (BCoef (Acoef (j + 1)) k M₀) = Module.finrank (ZMod 2) Mb :=
        scalar_finrank_eq (stageResidueFieldEquiv (j + 1))
          (stageCoefResidualEquiv j α hT hM hE2)
      have hr' : Module.finrank k ((gcxBaseChange k (urAt hS A M₀ v hv).U).toCC.homology n) ≤
          Module.finrank (ZMod 2) Mb := hr.trans_eq he
      have hp : P (urAt hS A M₀ v hv).U := ⟨hF, hr'.trans (by
        change Module.finrank (ZMod 2) Mb ≤ oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) Mb +
          Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point)
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))⟩
      exact (congrArg P heq).mpr hp
  let eU := homologyIsoOfBijective (piBaseChangeHom k Δ.U) (piBaseChangeHom_bijective k Δ.U) n
  have hUtarget : Finite ((piCx fun v => gcxBaseChange k (Δ.U v)).toCC.homology n) :=
    finite_homology_piCx _ n (fun v => by have := (hV v).1; exact Module.finite_of_finite k)
  have hDU : Module.Finite k ((gcxBaseChange k D.U).toCC.homology n) := by
    have : Finite ((gcxBaseChange k D.U).toCC.homology n) := Finite.of_injective _ eU.toLinearEquiv.injective
    exact Module.Finite.of_finite
  have hUb : Module.finrank k ((gcxBaseChange k D.U).toCC.homology n) ≤
      ∑ v : Places K S, (oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) Mb +
        Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point)) := by
    change Module.finrank k ((gcxBaseChange k (piCx Δ.U)).toCC.homology n) ≤ _
    rw [eU.toLinearEquiv.finrank_eq]
    exact (piCx_finrank_homology_le _ n (fun v => (hV v).1)).trans
      (Finset.sum_le_sum fun v _ => (hV v).2)
  have hGb : Module.finrank k ((gcxBaseChange k D.G).toCC.homology n) ≤ fixedGlobalRankBound K S Mb := by
    change Module.finrank (ResidueField (Acoef (j + 1)))
      ((gcxBaseChange (ResidueField (Acoef (j + 1)))
        (globalCx (Acoef (j + 1)) (GKS K S) (MinS hS W (j + 1) α))).toCC.homology n) ≤ _
    rw [EG.finrank_homology n]
    exact finrank_le_finiteRangeRankBound _ 0 2 (globalBinary_homology_range K S Mb h410 hK hSfin h2) n
  have hLb : Module.finrank k ((gcxBaseChange k D.L).toCC.homology (n - 1)) ≤ fixedLocalRankBound K S Mb := by
    change Module.finrank (ResidueField (Acoef (j + 1)))
      ((gcxBaseChange (ResidueField (Acoef (j + 1)))
        (localSumCx (Acoef (j + 1)) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (MinS hS W (j + 1) α))).toCC.homology (n - 1)) ≤ _
    rw [EL.finrank_homology (n - 1)]
    exact finrank_le_finiteRangeRankBound _ 0 2 (fixedLocalCohomology_range K S Mb hlcd) (n - 1)
  have hs := residualSelmer_finrank_le D n
  change Module.finrank k (residualCohomologyAt (selCx D) n) ≤
    fixedGlobalRankBound K S Mb + fixedLocalRankBound K S Mb +
    ∑ v : Places K S, (oldLocalRankMaximum hS W v + Module.finrank (ZMod 2) Mb +
      Module.finrank (ZMod 2) (ZMod 2 ⊗[ℤ] (Bv v).toAffine.Point))
  exact (hs.trans (Nat.add_le_add (Nat.add_le_add hGb hUb) hLb)).trans_eq (by omega)

end OldSelmerBounds

section OldFamilyBounds

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ) [∀ i, IsOpenKer (α i)]
  (hTor : ∀ i : ℕ, FullTorsion K S₀ W (2 ^ i))
  (h410 : MilneADT_I_4_10_totallyComplex) (hlcd : MilneLocalDimensionTwo)
  (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
  (hK : IsTotallyComplex K) (hSfin : S.Finite)
  (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (Bv v).IsElliptic]
  (label : ℕ → Places K S → ℕ) (m : ℕ → ℕ) [∀ i, NeZero (m i)]
  (ι : ∀ i (v : Places K S), TorsAlg (v.1.adicCompletion K) (Bv v) (m i) →+
    ResMod (locMap K S v.1) (MinS hS W i (α i)))
  (hι : ∀ i (v : Places K S) (g : Gloc K v.1) t, ι i v (g • t) = g • ι i v t)

include hTor h410 hlcd hloc hglob hK hSfin h2 in
/-- The actual old-support stage family supplies both retained-producer hypotheses.
Old zero, full, and Kummer conditions may be chosen independently at each stage;
all new places carry the actual unramified conditions. -/
theorem standardOld_producerBounds :
    ∃ B : ℕ,
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n → Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (actualSelData hS W i (α i)
          (fun v _ => standardOldAt K S (Acoef i) (MinS hS W i (α i))
            v (label i v) (Bv v) (m i) (ι i v) (hι i v)))) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (selCx (actualSelData hS W i (α i)
          (fun v _ => standardOldAt K S (Acoef i) (MinS hS W i (α i))
            v (label i v) (Bv v) (m i) (ι i v) (hι i v)))) n) ≤ B) := by
  have hE2 : FullTorsion K S₀ W 2 := by simpa using hTor 1
  refine ⟨oldSelmerRankBound hS W Bv hSfin, ?_, ?_⟩
  · intro i _ n hn
    letI : TopologicalSpace (Acoef i) := acoefTop i
    have : DiscreteTopology (Acoef i) := acoefTop_discrete i
    exact actualStageSelmer_hbdd hS i W (α i) h410 hlcd hK hSfin h2 _
      (fun v _ => standardOldAt_amplitude K S (Acoef i) (MinS hS W i (α i))
        v (label i v) (Bv v) (m i) (ι i v) (hι i v)) n hn
  · intro i _ n
    cases i with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ j =>
      exact actualStandardOldSelmer_hB hS W Bv j (α (j + 1)) (hTor (j + 1)) (hTor j)
        hE2 h410 hlcd hloc hglob hK hSfin h2 (label (j + 1)) (m (j + 1))
        (ι (j + 1)) (hι (j + 1)) n

end OldFamilyBounds

end ZInQ.Contrib.RC53Assist.ResidualBounds
