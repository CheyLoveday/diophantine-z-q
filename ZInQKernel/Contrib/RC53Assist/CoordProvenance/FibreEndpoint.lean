import ZInQKernel.Contrib.RC53Assist.CoordProvenance.BoundEndpoint
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionE1a
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.HomotopyComparison

/-!
# The selected endpoint bound to the actual finite clearing-field fibre

The preferred binding is in the clearing field.  It uses the fixed native
finite model, the actual class lifted through M.ψf, and the fixed pairedRow.
It retains the functional boundary in degree three.  It does not demand that
integral H0 or H3 torsion vanish, as an integral two-term model would.

The selected endpoint and all its coefficient readbacks remain parameters.
Constructing the actual field comparison is a structural finite-model
obligation, not an assumed coordinate equality or cone-normalization field.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint

open Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)
open ZInQ.Manuscript.RC.Determinant (OO Lam SignGroup evK sgnChar)
open ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull
open ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint
open ZInQ.Contrib.RC53Assist.CoordProvenance.Homotopy

abbrev K := FractionRing OO

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def finiteCore (D : Matrix ι ι K) : FourCx K Empty ι ι Empty where
  d0 := 0
  d1 := D
  d2 := 0
  d10 := Matrix.mul_zero _
  d21 := Matrix.zero_mul _

end Core

section NativeSource

variable {N : Type} [Field N] [NumberField N]
  {S S' : Set (HeightOneSpectrum (𝓞 N))} {hS : S ⊆ S'}
  [Fintype (NewPlaces N S S')] [DecidableEq (NewPlaces N S S')]
  {b dK hK cE tK : ℕ}
  (M : Identification3 N S S' hS b dK hK cE tK)
  (zActual : (familyCx M).X 1) (hzActual : (familyCx M).d 1 2 rfl zActual = 0)

/-- The lift is chosen from the actual family class through the native M.ψf,
not from a scalar that one wishes the endpoint to encode. -/
def actualClassRepresentative :
    (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b) :=
  (actual_class_lift M zActual hzActual).choose

theorem actualClassRepresentative_closed :
    (M.C.map (φO b)).toFour.d1 *ᵥ actualClassRepresentative M zActual hzActual = 0 :=
  (actual_class_lift M zActual hzActual).choose_spec.1

theorem actualClassRepresentative_readback :
    ∃ a : (familyCx M).X 0,
      modelMap1 M (actualClassRepresentative M zActual hzActual) - zActual =
        (familyCx M).d 0 1 rfl a :=
  (actual_class_lift M zActual hzActual).choose_spec.2

/-- This is the native finite fibre of the original actual family model. -/
abbrev sourceCx (x : ZInQ.Manuscript.RC.Addr b) :
    FourCx K (Fin M.C.m0) (M.C.D1 ⊕ M.C.N) (M.C.D2 ⊕ M.C.N) (Fin M.C.m2) :=
  (Cev3 (M.C.map (φO b)) x).toFour

abbrev sourceClass (x : ZInQ.Manuscript.RC.Addr b) : M.C.D1 ⊕ M.C.N → K :=
  evK (sgnChar x) ∘ actualClassRepresentative M zActual hzActual

theorem sourceClass_closed (x : ZInQ.Manuscript.RC.Addr b) :
    (sourceCx M x).d1 *ᵥ sourceClass M zActual hzActual x = 0 :=
  hzev3 (actualClassRepresentative_closed M zActual hzActual) x

end NativeSource

section Binding

variable {N : Type} [Field N] [NumberField N]
  {S S' : Set (HeightOneSpectrum (𝓞 N))} {hS : S ⊆ S'}
  [Fintype (NewPlaces N S S')] [DecidableEq (NewPlaces N S S')]
  {b dK hK cE tK : ℕ}
  {A R : Type} [CommRing A] [CommRing R]
  {F : Matrix (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : R →+* A) (g : R →+* K) (E : CommonLift s fScalar)
  (x : ZInQ.Manuscript.RC.Addr b)
  (M : Identification3 N S S' hS b dK hK cE tK)
  (zActual : (familyCx M).X 1) (hzActual : (familyCx M).d 1 2 rfl zActual = 0)
  {Dp : SelData (MonoidAlgebra OO (SignGroup b))} (P : SelPairData (familyData M) Dp)
  (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
  (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
  (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0)

abbrev targetMatrix : Matrix s.Index s.Index K := E.D.map g
abbrev targetClass : s.Index → K := g ∘ E.z
abbrev targetRow : s.Index → K := g ∘ E.w
abbrev sourceRow (x : ZInQ.Manuscript.RC.Addr b) : M.C.D2 ⊕ M.C.N → K :=
  evK (sgnChar x) ∘ pairedRow M P tr zc

include htr hzc in
theorem sourceRow_closed (x : ZInQ.Manuscript.RC.Addr b) : sourceRow M P tr zc x ᵥ* (sourceCx M x).d1 = 0 :=
  hlamev3 (pairedRow_closed M P tr htr zc hzc) x

/-- Preferred structural binding at the actual finite field fibre.  Its
source class and row are fixed by the genuine native M.ψf and pairedRow.
Its target is fixed by the selected step and coefficient readbacks. -/
structure FibreBinding
    (s : StepData F q qi a z zi uP uR eps unitR unitP)
    (fScalar : R →+* A) (g : R →+* K) (E : CommonLift s fScalar)
    (x : ZInQ.Manuscript.RC.Addr b)
    (M : Identification3 N S S' hS b dK hK cE tK)
    (zActual : (familyCx M).X 1) (hzActual : (familyCx M).d 1 2 rfl zActual = 0)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))} (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0) where
  scalar_injective : Function.Injective fScalar
  clearing_injective : Function.Injective g
  f : FourMap (sourceCx M x) (finiteCore (targetMatrix s fScalar g E))
  quasiIso : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap f))
  target_cycle : targetMatrix s fScalar g E *ᵥ targetClass s fScalar g E = 0
  target_closed : targetRow s fScalar g E ᵥ* targetMatrix s fScalar g E = 0
  class_map : f.f1 *ᵥ sourceClass M zActual hzActual x = targetClass s fScalar g E
  functionalPrimitive : Fin M.C.m2 → K
  functional_map : targetRow s fScalar g E ᵥ* f.f2 = sourceRow M P tr zc x +
    functionalPrimitive ᵥ* (sourceCx M x).d2

/-- The actual functional homotopy is retained in the comparison, including
when the original actual functional is a nonzero coboundary. -/
def FibreBinding.comparison (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) :
    HomotopyComparison (sourceCx M x) (finiteCore (targetMatrix s fScalar g E))
      (sourceClass M zActual hzActual x) (sourceRow M P tr zc x)
      (targetClass s fScalar g E) (targetRow s fScalar g E) where
  f := B.f
  classBoundary := 0
  functionalBoundary := B.functionalPrimitive
  class_map := by simpa [finiteCore] using B.class_map
  functional_map := B.functional_map

/-- The exported fibre binding keeps every original selected endpoint readback. -/
theorem FibreBinding.readback (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) :
    E.D.map fScalar = s.DR ∧ fScalar ∘ E.z = s.zR ∧ fScalar ∘ E.w = s.wR ∧
      B.f.f1 *ᵥ sourceClass M zActual hzActual x = targetClass s fScalar g E ∧
      targetRow s fScalar g E ᵥ* B.f.f2 = sourceRow M P tr zc x +
        B.functionalPrimitive ᵥ* (sourceCx M x).d2 :=
  ⟨E.matrix_readback, E.class_readback, E.functional_readback, B.class_map, B.functional_map⟩

/-- The fixed selected scalar has a common numerator and denominator on the
same bound target matrix and representatives.  No existential over replacement
endpoints is introduced. -/
theorem FibreBinding.fixed_fractional_coordinate [IsDomain A]
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc)
    (hlocal : (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F q z zi).det ≠ 0) :
    ∃ num den : R, den ≠ 0 ∧ fScalar den * uR = fScalar num ∧
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn (targetMatrix s fScalar g E)
        (targetClass s fScalar g E) (targetRow s fScalar g E) (g num / g den) := by
  have hadj : E.D.adjugate ≠ 0 := by
    intro hzero
    apply s.adjugate_ne_zero hlocal
    have hm := RingHom.map_adjugate fScalar E.D
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, E.matrix_readback] at hm
    rw [← hm, hzero, Matrix.map_zero _ (map_zero _)]
  exact E.common_fraction s fScalar B.scalar_injective g B.clearing_injective hadj

/-- A zero lifted endpoint vector forces the fixed native fibre class to be
a boundary.  No arbitrary scalar witness can alter that actual source class. -/
theorem FibreBinding.zero_class_forces_native_boundary
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) (hz : E.z = 0) :
    ∃ c : Fin M.C.m0 → K, sourceClass M zActual hzActual x = (sourceCx M x).d0 *ᵥ c := by
  let ψ := ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap B.f)
  let zs : (quadCx (sourceCx M x)).toCC.X 1 := sourceClass M zActual hzActual x
  let boundary : (quadCx (finiteCore (targetMatrix s fScalar g E))).toCC.X 0 := 0
  have hzero : targetClass s fScalar g E = 0 := by
    funext i
    rw [targetClass, hz]
    simp
  have hm : (ψ.f 1).hom zs - (ψ.f 1).hom 0 =
      ((quadCx (finiteCore (targetMatrix s fScalar g E))).toCC.d 0 1).hom boundary := by
    change B.f.f1 *ᵥ sourceClass M zActual hzActual x - B.f.f1 *ᵥ 0 = _
    rw [B.class_map, hzero, mulVec_zero, sub_self]
    exact (map_zero _).symm
  obtain ⟨c, hc⟩ := ZInQ.Contrib.RC53Assist.CoordProvenance.lifts_differ_by_boundary
    ψ B.quasiIso 1 zs 0 (sourceClass_closed M zActual hzActual x) (map_zero _) boundary hm
  refine ⟨c, ?_⟩
  change sourceClass M zActual hzActual x - 0 = (sourceCx M x).d0 *ᵥ c at hc
  simpa only [sub_zero] using hc

/-- Nonzero actual fibre cohomology excludes a zero bound endpoint class. -/
theorem FibreBinding.class_not_zero
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc)
    (hne : ∀ c : Fin M.C.m0 → K, sourceClass M zActual hzActual x ≠ (sourceCx M x).d0 *ᵥ c) :
    E.z ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := B.zero_class_forces_native_boundary s fScalar g E x M zActual hzActual P tr htr zc hzc hz
  exact hne c hc

/-- A zero endpoint row can occur only when the same actual paired functional
class vanishes on the fixed native fibre cycles. -/
theorem FibreBinding.zero_row_kills_native_cycles
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) (hw : E.w = 0)
    (v : M.C.D2 ⊕ M.C.N → K) (hv : (sourceCx M x).d2 *ᵥ v = 0) :
    sourceRow M P tr zc x ⬝ᵥ v = 0 := by
  have h := (B.comparison s fScalar g E x M zActual hzActual P tr htr zc hzc).functional_on_cycles v hv
  have hzero : targetRow s fScalar g E = 0 := by
    funext i
    rw [targetRow, hw]
    simp
  have ht : targetRow s fScalar g E ⬝ᵥ (B.f.f2 *ᵥ v) = sourceRow M P tr zc x ⬝ᵥ v := h
  exact ht.symm.trans ((congrArg (· ⬝ᵥ (B.f.f2 *ᵥ v)) hzero).trans (zero_dotProduct _))

/-- At a boundary of the fixed actual native fibre class, the same selected
regular scalar is zero.  This uses the fixed map and coefficient injections,
not a casewise coordinate-identity assumption or a normalization leaf. -/
theorem FibreBinding.scalar_zero_of_native_boundary [IsDomain A]
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc)
    (c : Fin M.C.m0 → K)
    (hc : sourceClass M zActual hzActual x = (sourceCx M x).d0 *ᵥ c)
    (hlocal : (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F q z zi).det ≠ 0) : uR = 0 := by
  have hmap : B.f.f1 *ᵥ ((sourceCx M x).d0 *ᵥ c) = 0 := by
    rw [mulVec_mulVec, ← B.f.c0]
    change ((0 : Matrix s.Index Empty K) * B.f.f0) *ᵥ c = 0
    rw [Matrix.zero_mul, zero_mulVec]
  have ht : targetClass s fScalar g E = 0 :=
    B.class_map.symm.trans ((congrArg (B.f.f1 *ᵥ ·) hc).trans hmap)
  have hz : E.z = 0 := by
    funext i
    apply B.clearing_injective
    exact (congrFun ht i).trans (map_zero g).symm
  have hs : s.zR = 0 := by
    rw [← E.class_readback, hz]
    exact funext fun i => map_zero _
  obtain ⟨i, j, hij⟩ : ∃ i j, s.DR.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact (s.adjugate_ne_zero hlocal) (Matrix.ext h)
  have h := congrFun (congrFun s.endpoint_coordinate i) j
  simp only [Matrix.vecMulVec_apply, hs, Pi.zero_apply, zero_mul, Matrix.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_right hij

end Binding

end ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint
