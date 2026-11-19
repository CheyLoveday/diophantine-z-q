import ZInQKernel.Contrib.RC53Assist.CoordProvenance.ActualFullModel
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.StoredRegularity
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.ExistingScalar
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.CoefficientRealization

/-!
# Selected endpoints with actual model and representative readbacks

The selected step remains a parameter of every endpoint realization.  Its
matrix, class vector and functional row are not replaced by a free existential.
The actual model binding is a quasi-isomorphism to the same native family
Selmer complex, with the given actual class and PD(-, conjugate class).
No determinant-normalization or coordinate-equality field is present.

The original weak step proposition alone does not construct the actual model
binding.  This file makes the precise structural evidence explicit and proves
that all-zero witnesses cannot meet it for nonzero actual cohomology classes.
The locators are TeX 3837–3862 and 4159–4194.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint

open Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Central (pointFactor IsClassFunctionalCoord)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK)
open ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull

section Selection

variable {A : Type} [CommRing A]

/-- Full selected matrix data of the stored step, including its original
bases and representatives.  This is not yet an actual Selmer model binding. -/
structure StepData (F : Matrix (Fin 2) (Fin 2) A) (q qi a z zi uP uR eps : A)
    (unitR unitP : A → Prop) where
  n : ℕ
  DP : Matrix (Fin n) (Fin n) A
  PP : Matrix (Fin n) (Fin n) A
  QP : Matrix (Fin n) (Fin n) A
  DR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) A
  PR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) A
  QR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) A
  X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) A
  zP : Fin n → A
  wP : Fin n → A
  zR : Fin n ⊕ (Fin 2 ⊕ Fin 2) → A
  wR : Fin n ⊕ (Fin 2 ⊕ Fin 2) → A
  hPP : IsUnit PP.det
  hQP : IsUnit QP.det
  hPR : IsUnit PR.det
  hQR : IsUnit QR.det
  matrix_step : PR * DR * QR = fromBlocks (PP * DP * QP) X 0 (twoPlaceBlock F q z zi)
  class_step : ∀ i, (QR⁻¹ *ᵥ zR) (Sum.inl i) = pointFactor a z zi * (QP⁻¹ *ᵥ zP) i
  functional_step : ∀ i, (wR ᵥ* PR⁻¹) (Sum.inl i) = pointFactor a z zi * (wP ᵥ* PP⁻¹) i
  endpoint_coordinate : IsCoordOn DR zR wR uR
  primitive_coordinate : IsClassFunctionalCoord DP zP wP uP
  primitive_adjugate : (PP * DP * QP).adjugate ≠ 0
  retained_unit_R : unitR (PR.det * QR.det)
  retained_unit_P : unitP (PP.det * QP.det)
  step_unit : eps = qi ^ 4 * (PR.det * QR.det) * Ring.inverse (PP.det * QP.det)

abbrev StepData.Index {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
    {unitR unitP : A → Prop} (s : StepData F q qi a z zi uP uR eps unitR unitP) :=
  Fin s.n ⊕ (Fin 2 ⊕ Fin 2)

/-- The selected record reads back to the original complete step proposition. -/
theorem StepData.toActualStep {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
    {unitR unitP : A → Prop} (s : StepData F q qi a z zi uP uR eps unitR unitP) :
    ActualStep F q qi a z zi uP uR eps unitR unitP :=
  ⟨s.n, s.DP, s.PP, s.QP, s.DR, s.PR, s.QR, s.X, s.zP, s.wP, s.zR, s.wR,
    s.hPP, s.hQP, s.hPR, s.hQR, s.matrix_step, s.class_step, s.functional_step,
    s.endpoint_coordinate, s.primitive_coordinate, s.primitive_adjugate,
    s.retained_unit_R, s.retained_unit_P, s.step_unit⟩

theorem selected_data_exists {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
    {unitR unitP : A → Prop} (h : ActualStep F q qi a z zi uP uR eps unitR unitP) :
    Nonempty (StepData F q qi a z zi uP uR eps unitR unitP) := by
  obtain ⟨n, DP, PP, QP, DR, PR, QR, X, zP, wP, zR, wR,
    hPP, hQP, hPR, hQR, hm, hz, hw, hc, hp, ha, huR, huP, he⟩ := h
  exact ⟨⟨n, DP, PP, QP, DR, PR, QR, X, zP, wP, zR, wR,
    hPP, hQP, hPR, hQR, hm, hz, hw, hc, hp, ha, huR, huP, he⟩⟩

/-- Select the full datum, not just an unbound coordinate witness. -/
def selected {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
    {unitR unitP : A → Prop} (h : ActualStep F q qi a z zi uP uR eps unitR unitP) :
    StepData F q qi a z zi uP uR eps unitR unitP :=
  Classical.choice (selected_data_exists h)

/-- Regularity belongs to the same selected endpoint, not to a replacement
matrix chosen to encode the scalar. -/
theorem StepData.adjugate_ne_zero [IsDomain A]
    {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
    (s : StepData F q qi a z zi uP uR eps unitR unitP)
    (hB : (twoPlaceBlock F q z zi).det ≠ 0) : s.DR.adjugate ≠ 0 :=
  ZInQ.Contrib.RC53Assist.CoordProvenance.StoredRegularity.original_adjugate_ne_zero
    s.DR s.PR s.QR (s.PP * s.DP * s.QP) s.X _ s.matrix_step s.primitive_adjugate hB

section Realization

variable {R : Type} [CommRing R] {F : Matrix (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : StepData F q qi a z zi uP uR eps unitR unitP) (f : R →+* A)

/-- A common-coefficient realization is indexed by the same selected step;
all three original-basis readbacks are fields of the exported type. -/
structure CommonLift where
  D : Matrix s.Index s.Index R
  z : s.Index → R
  w : s.Index → R
  matrix_readback : D.map f = s.DR
  class_readback : f ∘ z = s.zR
  functional_readback : f ∘ w = s.wR

/-- Read back the existing scalar identity on these fixed lifted matrices and vectors. -/
theorem CommonLift.stored_coordinate (E : CommonLift s f) :
    IsCoordOn (E.D.map f) (f ∘ E.z) (f ∘ E.w) uR := by
  rw [E.matrix_readback, E.class_readback, E.functional_readback]
  exact s.endpoint_coordinate

/-- Relabelling carries the same readbacks, not arbitrary replacement endpoint data. -/
theorem CommonLift.relabel_readback {κ : Type} (e : κ ≃ s.Index) (E : CommonLift s f) :
    (E.D.submatrix e e).map f = s.DR.submatrix e e ∧
      f ∘ (E.z ∘ e) = s.zR ∘ e ∧ f ∘ (E.w ∘ e) = s.wR ∘ e := by
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.ext fun i j => congrFun (congrFun E.matrix_readback (e i)) (e j)
  · exact funext fun i => congrFun E.class_readback (e i)
  · exact funext fun i => congrFun E.functional_readback (e i)

/-- Common fractional transport preserves the fixed endpoint fields in the conclusion. -/
theorem CommonLift.common_fraction {K : Type} [Field K] (hf : Function.Injective f)
    (g : R →+* K) (hg : Function.Injective g) (E : CommonLift s f)
    (hadj : E.D.adjugate ≠ 0) :
    ∃ num den : R, den ≠ 0 ∧ f den * uR = f num ∧
      IsCoordOn (E.D.map g) (g ∘ E.z) (g ∘ E.w) (g num / g den) :=
  ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_common_fraction
    f hf g hg E.D E.z E.w uR E.stored_coordinate hadj

end Realization
end Selection

section ActualModel

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev coreX (R : Type) [CommRing R] (ι : Type) : ℤ → ModuleCat R
  | 1 => ModuleCat.of R (ι → R)
  | 2 => ModuleCat.of R (ι → R)
  | _ => ModuleCat.of R PUnit

def coreD (D : Matrix ι ι R) : (i : ℤ) → coreX R ι i →ₗ[R] coreX R ι (i + 1)
  | 1 => D.mulVecLin
  | _ => 0

omit [DecidableEq ι] in
theorem coreD_square (D : Matrix ι ι R) (i : ℤ) (v : coreX R ι i) :
    coreD D (i + 1) (coreD D i v) = 0 := by
  match i with
  | 0 => exact map_zero _
  | 1 => rfl
  | Int.ofNat (n + 2) => rfl
  | Int.negSucc n =>
    change coreD D (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- The fixed lifted endpoint complex; no scalar is used to define its differential. -/
def coreCx (D : Matrix ι ι R) : GCx R where
  X := coreX R ι
  d i j h := by subst h; exact coreD D i
  d_d i j k hij hjk v := by subst hij hjk; exact coreD_square D i v

variable {N : Type} [Field N] [NumberField N]
  {S S' : Set (HeightOneSpectrum (𝓞 N))} {hS : S ⊆ S'}
  [Fintype (NewPlaces N S S')] [DecidableEq (NewPlaces N S S')]
  {b dK hK cE tK : ℕ}

/-- The original integral-to-scalar realization at the fixed sign character. -/
abbrev scalarAt (χ : SignGroup b →* ℤˣ) :
    MonoidAlgebra Lam (SignGroup b) →+* PowerSeries ℚ_[2] :=
  ZInQ.Contrib.CloudB3RC53.CoordLink.ιQ.comp
    (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom

variable {F : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])}
  {q qi a z zi uP uR eps : PowerSeries ℚ_[2]}
  {unitR unitP : PowerSeries ℚ_[2] → Prop}
  (s : StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : SignGroup b →* ℤˣ) (E : CommonLift s (scalarAt χ))
  (M : Identification3 N S S' hS b dK hK cE tK)
  (zActual : (familyCx M).X 1) (hzActual : (familyCx M).d 1 2 rfl zActual = 0)
  {Dp : SelData (MonoidAlgebra OO (SignGroup b))} (P : SelPairData (familyData M) Dp)
  (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
  (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
  (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0)

/-- Actual structural model evidence for the same selected endpoint and same
actual class and pairing.  Neither cone torsion nor coordinate equality is a field.
This evidence is not constructed by a weak ActualStep proposition alone. -/
structure SelmerBinding
    (s : StepData F q qi a z zi uP uR eps unitR unitP)
    (χ : SignGroup b →* ℤˣ) (E : CommonLift s (scalarAt χ))
    (M : Identification3 N S S' hS b dK hK cE tK)
    (zActual : (familyCx M).X 1) (hzActual : (familyCx M).d 1 2 rfl zActual = 0)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))} (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0) where
  ψ : (coreCx (E.D.map (φO b))).toCC ⟶ (familyCx M).toCC
  quasiIso : QuasiIso ψ
  cycle : E.D.map (φO b) *ᵥ (φO b ∘ E.z) = 0
  boundary : (familyCx M).X 0
  same_class : (show (s.Index → MonoidAlgebra OO (SignGroup b)) →ₗ[MonoidAlgebra OO (SignGroup b)]
      (familyCx M).X 1 from (ψ.f 1).hom) (φO b ∘ E.z) - zActual =
    (familyCx M).d 0 1 rfl boundary
  same_functional : ∀ v : s.Index → MonoidAlgebra OO (SignGroup b),
    (φO b ∘ E.w) ⬝ᵥ v = rightFunctional P tr zc
      ((show (s.Index → MonoidAlgebra OO (SignGroup b)) →ₗ[MonoidAlgebra OO (SignGroup b)]
        (familyCx M).X 2 from (ψ.f 2).hom) v)

abbrev SelmerBinding.classMap (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    (s.Index → MonoidAlgebra OO (SignGroup b)) →ₗ[MonoidAlgebra OO (SignGroup b)] (familyCx M).X 1 :=
  (B.ψ.f 1).hom

abbrev SelmerBinding.functionalMap (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    (s.Index → MonoidAlgebra OO (SignGroup b)) →ₗ[MonoidAlgebra OO (SignGroup b)] (familyCx M).X 2 :=
  (B.ψ.f 2).hom

/-- Readbacks and actual provenance are retained together in the exported conclusion. -/
theorem SelmerBinding.readback (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    E.D.map (scalarAt χ) = s.DR ∧ scalarAt χ ∘ E.z = s.zR ∧ scalarAt χ ∘ E.w = s.wR ∧
    B.classMap s χ E M zActual hzActual P tr htr zc hzc (φO b ∘ E.z) - zActual =
      (familyCx M).d 0 1 rfl B.boundary ∧
    ∀ v, (φO b ∘ E.w) ⬝ᵥ v = rightFunctional P tr zc
      (B.functionalMap s χ E M zActual hzActual P tr htr zc hzc v) :=
  ⟨E.matrix_readback, E.class_readback, E.functional_readback, B.same_class, B.same_functional⟩

/-- All-zero endpoint vectors are excluded when the fixed actual class is nonzero in cohomology. -/
theorem SelmerBinding.class_not_zero
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (hnonboundary : ∀ c : (familyCx M).X 0, zActual ≠ (familyCx M).d 0 1 rfl c) :
    E.z ≠ 0 := by
  intro hzero
  have hz : (φO b ∘ E.z) = 0 := by funext i; rw [hzero]; exact map_zero _
  have h := B.same_class
  rw [hz, map_zero, zero_sub] at h
  apply hnonboundary (-B.boundary)
  erw [map_neg]
  exact neg_eq_iff_eq_neg.mp h

/-- A zero bound row forces the same actual pairing to vanish on every actual
cohomology two-cycle, so it is not a freely chosen zero-functional witness. -/
theorem SelmerBinding.zero_row_kills_actual_cycles
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) (hw : E.w = 0)
    (v : (familyCx M).X 2) (hv : (familyCx M).d 2 3 rfl v = 0) :
    rightFunctional P tr zc v = 0 := by
  obtain ⟨vm, hvm, a, ha⟩ :=
    ZInQ.Contrib.RC53Assist.CoordProvenance.exists_lift_with_boundary B.ψ B.quasiIso 2 v hv
  let vm' : s.Index → MonoidAlgebra OO (SignGroup b) := vm
  let a' : (familyCx M).X 1 := a
  have hvalue := B.same_functional vm'
  have hrow : (φO b ∘ E.w) = 0 := by funext i; rw [hw]; exact map_zero _
  rw [hrow, zero_dotProduct] at hvalue
  have hd := rightFunctional_closed P tr htr zc hzc a'
  have ha' : (B.functionalMap s χ E M zActual hzActual P tr htr zc hzc) vm' - v =
      (familyCx M).d 1 2 rfl a' := ha
  have he := congrArg (rightFunctional P tr zc) ha'
  erw [map_sub] at he
  rw [← hvalue, hd, zero_sub] at he
  exact neg_eq_zero.mp he

section FixedCharacterRealizations

open ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients

/-- The common-field matrix has an exact readback to the same selected
Laurent endpoint.  No new endpoint matrix is existentially chosen. -/
theorem CommonLift.laurent_matrix_readback :
    (E.D.map (signToCommon χ)).map toLaurent = s.DR.map powerSeriesToLaurent := by
  exact Matrix.ext fun i j => (sign_toLaurent χ (E.D i j)).trans
    (congrArg powerSeriesToLaurent (congrFun (congrFun E.matrix_readback i) j))

/-- Both actual representatives retain their selected-step readbacks in the Laurent carrier. -/
theorem CommonLift.laurent_vector_readbacks :
    toLaurent ∘ (signToCommon χ ∘ E.z) = powerSeriesToLaurent ∘ s.zR ∧
      toLaurent ∘ (signToCommon χ ∘ E.w) = powerSeriesToLaurent ∘ s.wR := by
  constructor
  · exact funext fun i => (sign_toLaurent χ (E.z i)).trans
      (congrArg powerSeriesToLaurent (congrFun E.class_readback i))
  · exact funext fun i => (sign_toLaurent χ (E.w i)).trans
      (congrArg powerSeriesToLaurent (congrFun E.functional_readback i))

/-- The clearing matrix and vectors are the images of those same lifted fields. -/
theorem CommonLift.clearing_readbacks :
    (E.D.map (signToCommon χ)).map toClearing = (E.D.map (φO b)).map (evK χ) ∧
      toClearing ∘ (signToCommon χ ∘ E.z) = evK χ ∘ (φO b ∘ E.z) ∧
      toClearing ∘ (signToCommon χ ∘ E.w) = evK χ ∘ (φO b ∘ E.w) :=
  ⟨matrix_toClearing χ E.D, vector_toClearing χ E.z, vector_toClearing χ E.w⟩

/-- Transport the stored coordinate on the fixed lifted fields; the returned
statement keeps their actual matrix and representative readbacks. -/
theorem CommonLift.fixed_laurent_coordinate :
    IsCoordOn ((E.D.map (signToCommon χ)).map toLaurent)
      (toLaurent ∘ (signToCommon χ ∘ E.z)) (toLaurent ∘ (signToCommon χ ∘ E.w))
      (powerSeriesToLaurent uR) := by
  rw [CommonLift.laurent_matrix_readback s χ E, (CommonLift.laurent_vector_readbacks s χ E).1,
    (CommonLift.laurent_vector_readbacks s χ E).2]
  exact ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_map
    powerSeriesToLaurent s.DR s.zR s.wR uR s.endpoint_coordinate

end FixedCharacterRealizations

/-- A verified comparison to the native finite model binds the selected
endpoint through M.ψf and the actual pairedRow; no freely chosen target trace
or scalar normalization is introduced.  Constructing J is the structural
finite-model matching obligation, not a coordinate-identity leaf. -/
def bindingOfNativeComparison
    (J : (coreCx (E.D.map (φO b))).toCC ⟶ (modelCx M).toCC) (hJ : QuasiIso J)
    (hcycle : E.D.map (φO b) *ᵥ (φO b ∘ E.z) = 0)
    (a : (familyCx M).X 0)
    (hclass : modelMap1 M
      ((show (s.Index → MonoidAlgebra OO (SignGroup b)) →ₗ[MonoidAlgebra OO (SignGroup b)]
        (modelCx M).X 1 from (J.f 1).hom) (φO b ∘ E.z)) - zActual =
        (familyCx M).d 0 1 rfl a)
    (hrow : ∀ v : s.Index → MonoidAlgebra OO (SignGroup b),
      (φO b ∘ E.w) ⬝ᵥ v = pairedRow M P tr zc ⬝ᵥ
        ((show (s.Index → MonoidAlgebra OO (SignGroup b)) →ₗ[MonoidAlgebra OO (SignGroup b)]
          (modelCx M).X 2 from (J.f 2).hom) v)) :
    SelmerBinding s χ E M zActual hzActual P tr htr zc hzc where
  ψ := J ≫ M.ψf
  quasiIso := by
    have := hJ
    have := M.qisf
    infer_instance
  cycle := hcycle
  boundary := a
  same_class := hclass
  same_functional v := (hrow v).trans (pairedRow_value M P tr zc ((J.f 2).hom v))

/-- A bound row cannot be zero on a nonzero actual functional class. -/
theorem SelmerBinding.functional_not_zero
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (v : (familyCx M).X 2) (hv : (familyCx M).d 2 3 rfl v = 0)
    (hne : rightFunctional P tr zc v ≠ 0) : E.w ≠ 0 := by
  intro hw
  exact hne (B.zero_row_kills_actual_cycles s χ E M zActual hzActual P tr htr zc hzc hw v hv)

/-- The actual integral-to-completed coefficient map is injective. -/
theorem integralCompletion_injective : Function.Injective (φO b) := by
  intro x y h
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  apply ZInQ.Manuscript.RC.Determinant.lamToO_injective
  exact congrArg (fun a : MonoidAlgebra OO (SignGroup b) => a.coeff g) h

/-- The selected completed row is closed because it is the same actual paired
functional on the actual endpoint model map. -/
theorem SelmerBinding.completed_row_closed
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    (φO b ∘ E.w) ᵥ* E.D.map (φO b) = 0 := by
  funext j
  let v : s.Index → MonoidAlgebra OO (SignGroup b) := Pi.single j 1
  have hc := congrArg (fun f => f.hom v) (B.ψ.comm 1 2)
  simp only [ModuleCat.hom_comp] at hc
  have he : (familyCx M).d 1 2 rfl
      (B.classMap s χ E M zActual hzActual P tr htr zc hzc v) =
    B.functionalMap s χ E M zActual hzActual P tr htr zc hzc (E.D.map (φO b) *ᵥ v) := hc
  have hvalue := B.same_functional (E.D.map (φO b) *ᵥ v)
  have hzero := rightFunctional_closed P tr htr zc hzc
    (B.classMap s χ E M zActual hzActual P tr htr zc hzc v)
  have hv0 : (φO b ∘ E.w) ⬝ᵥ (E.D.map (φO b) *ᵥ v) = 0 :=
    hvalue.trans ((congrArg (rightFunctional P tr zc) he).symm.trans hzero)
  rw [dotProduct_mulVec] at hv0
  simpa [v, dotProduct, Pi.single_apply] using hv0

/-- Closure is reflected before completion, not asserted for freely chosen
vectors encoding the scalar. -/
theorem SelmerBinding.integral_closed
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    E.D *ᵥ E.z = 0 ∧ E.w ᵥ* E.D = 0 := by
  constructor
  · funext i
    apply integralCompletion_injective
    have h := congrFun B.cycle i
    rw [← RingHom.map_mulVec] at h
    exact h.trans (map_zero (φO b)).symm
  · funext i
    apply integralCompletion_injective
    have h := congrFun (B.completed_row_closed s χ E M zActual hzActual P tr htr zc hzc) i
    rw [← RingHom.map_vecMul] at h
    exact h.trans (map_zero (φO b)).symm

/-- The same selected stored step vectors are closed, derived from the actual
model binding and its readbacks.  No independent zero-vector witness is chosen. -/
theorem SelmerBinding.stored_closed
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    s.DR *ᵥ s.zR = 0 ∧ s.wR ᵥ* s.DR = 0 := by
  have hc := B.integral_closed s χ E M zActual hzActual P tr htr zc hzc
  have hz : E.D.map (scalarAt χ) *ᵥ (scalarAt χ ∘ E.z) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hc.1]
    exact map_zero _
  have hw : (scalarAt χ ∘ E.w) ᵥ* E.D.map (scalarAt χ) = 0 := by
    funext i
    rw [← RingHom.map_vecMul, hc.2]
    exact map_zero _
  rw [E.matrix_readback, E.class_readback] at hz
  rw [E.matrix_readback, E.functional_readback] at hw
  exact ⟨hz, hw⟩

/-- The fixed endpoint two-term model has no degree-zero boundaries.  Thus
an actual boundary class forces its bound original vector to be literally
zero; it is not a discretionary zero witness. -/
theorem SelmerBinding.actual_boundary_forces_class_zero
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (c : (familyCx M).X 0) (hc : zActual = (familyCx M).d 0 1 rfl c) : E.z = 0 := by
  have hb : B.classMap s χ E M zActual hzActual P tr htr zc hzc (φO b ∘ E.z) -
      B.classMap s χ E M zActual hzActual P tr htr zc hzc 0 =
      (familyCx M).d 0 1 rfl (B.boundary + c) := by
    rw [map_zero, sub_zero]
    have hh := eq_add_of_sub_eq B.same_class
    exact hh.trans ((congrArg ((familyCx M).d 0 1 rfl B.boundary + ·) hc).trans
      (map_add ((familyCx M).d 0 1 rfl) B.boundary c).symm)
  let zg : (coreCx (E.D.map (φO b))).toCC.X 1 := φO b ∘ E.z
  let targetBoundary : (familyCx M).toCC.X 0 := B.boundary + c
  obtain ⟨v, hv⟩ := ZInQ.Contrib.RC53Assist.CoordProvenance.lifts_differ_by_boundary
    B.ψ B.quasiIso 1 zg 0 B.cycle (map_zero _) targetBoundary hb
  have hz : (φO b ∘ E.z) - 0 = 0 := hv
  rw [sub_zero] at hz
  funext i
  apply integralCompletion_injective
  exact (congrFun hz i).trans (map_zero (φO b)).symm

/-- At an actual zero class the same regular stored scalar is zero, derived
from the bound model and fixed adjugate identity, without a normalization leaf. -/
theorem SelmerBinding.stored_scalar_zero_of_actual_boundary
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (c : (familyCx M).X 0) (hc : zActual = (familyCx M).d 0 1 rfl c)
    (hlocal : (twoPlaceBlock F q z zi).det ≠ 0) : uR = 0 := by
  have hz := B.actual_boundary_forces_class_zero s χ E M zActual hzActual P tr htr zc hzc c hc
  have hs : s.zR = 0 := by
    rw [← E.class_readback, hz]
    exact funext fun i => map_zero _
  obtain ⟨i, j, hij⟩ : ∃ i j, s.DR.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact (s.adjugate_ne_zero hlocal) (Matrix.ext h)
  have h := congrFun (congrFun s.endpoint_coordinate i) j
  simp only [vecMulVec_apply, hs, Pi.zero_apply, zero_mul, Matrix.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_right hij

/-- Scope obstruction for the integral two-term variant: it would force every
actual degree-three cycle to be a boundary.  It must not be imposed when the
actual integral Selmer complex retains H3 torsion. -/
theorem SelmerBinding.integral_h3_cycles_are_boundaries
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (v : (familyCx M).X 3) (hv : (familyCx M).d 3 4 rfl v = 0) :
    ∃ a : (familyCx M).X 2, v = (familyCx M).d 2 3 rfl a := by
  obtain ⟨vm, hvm, a, ha⟩ :=
    ZInQ.Contrib.RC53Assist.CoordProvenance.exists_lift_with_boundary B.ψ B.quasiIso 3 v hv
  let vm' : PUnit := vm
  let f3 : PUnit →ₗ[MonoidAlgebra OO (SignGroup b)] (familyCx M).X 3 := (B.ψ.f 3).hom
  let a' : (familyCx M).X 2 := a
  have hzero : vm' = 0 := Subsingleton.elim _ _
  have he : f3 vm' - v = (familyCx M).d 2 3 rfl a' := ha
  rw [hzero, map_zero, zero_sub] at he
  refine ⟨-a', ?_⟩
  erw [map_neg]
  exact neg_eq_iff_eq_neg.mp he

/-- Nonzero integral H3 excludes the optional integral two-term binding;
the clearing-field fibre binding is the intended alternative. -/
theorem no_integral_twoTerm_binding_of_nonzero_h3
    (v : (familyCx M).X 3) (hv : (familyCx M).d 3 4 rfl v = 0)
    (hn : ∀ a : (familyCx M).X 2, v ≠ (familyCx M).d 2 3 rfl a) :
    ¬ Nonempty (SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) := by
  rintro ⟨B⟩
  obtain ⟨a, ha⟩ := B.integral_h3_cycles_are_boundaries s χ E M zActual hzActual P tr htr zc hzc v hv
  exact hn a ha

end ActualModel

end ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint
