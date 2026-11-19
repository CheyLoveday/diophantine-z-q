import ZInQKernel.Contrib.RC53Assist.Detection.Producer

/-!
# Arithmetic inputs for prescribed-class detection

Genuine coinduction, finite matrix spans, norm scalars, and retained cochain
comparisons supply the coefficient inputs of the prescribed-class producer.
The remaining arithmetic and retained-comparison conditions are explicit.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct

namespace ZInQ.Contrib.RC53Assist.Detection.Inputs

open CategoryTheory Filter Topology Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.FrobeniusMatch
open ZInQ.Manuscript.RC.Limits hiding Lambda evalOne evalZero evalTwo
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Contrib.RC53Assist.Detection
open scoped WeierstrassCurve Matrix PowerSeries.WithPiTopology

section TwoCosets

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (H : Subgroup G) (τ : G) (hτ : τ * τ = 1) (hτH : τ ∉ H)
    (hcoset : ∀ g : G, g ∈ H ∨ g * τ ∈ H)
    (ρ : Representation R H M)

/-- Evaluation at the two coset representatives of the genuine coinduced module. -/
def coindPair : Representation.coindV H.subtype ρ →ₗ[R] M × M where
  toFun f := (f.val 1, f.val τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A vector in each coset determines a coinduced function. -/
def pairCoind (x : M × M) : Representation.coindV H.subtype ρ := by
  classical
  let f : G → M := fun g => if hg : g ∈ H then ρ ⟨g, hg⟩ x.1 else
    ρ ⟨g * τ, (hcoset g).resolve_left hg⟩ x.2
  refine ⟨f, ?_⟩
  intro h g
  change f ((h : G) * g) = ρ h (f g)
  have hm : (h : G) * g ∈ H ↔ g ∈ H := by
    constructor
    · intro hh
      have he := H.mul_mem (H.inv_mem h.property) hh
      simpa using he
    · exact H.mul_mem h.property
  by_cases hg : g ∈ H
  · simp only [f, dite_eq_left hg, dite_eq_left (hm.mpr hg)]
    have he : (⟨(h : G) * g, hm.mpr hg⟩ : H) = h * ⟨g, hg⟩ := rfl
    rw [he, map_mul, Module.End.mul_apply]
  · simp only [f, dite_eq_right hg, dite_eq_right (fun h => hg (hm.mp h))]
    have he : (⟨((h : G) * g) * τ, (hcoset _).resolve_left (fun h => hg (hm.mp h))⟩ : H) =
        h * ⟨g * τ, (hcoset g).resolve_left hg⟩ := Subtype.ext (mul_assoc _ _ _)
    rw [he, map_mul, Module.End.mul_apply]

/-- The actual coinduced module has the two transversal coordinates. -/
def coindPairEquiv : Representation.coindV H.subtype ρ ≃ₗ[R] M × M where
  toLinearMap := coindPair H τ ρ
  invFun := pairCoind H τ hcoset ρ
  left_inv f := by
    apply Subtype.ext
    funext g
    classical
    by_cases hg : g ∈ H
    · change (if h : g ∈ H then ρ ⟨g, h⟩ (f.val 1) else
        ρ ⟨g * τ, (hcoset g).resolve_left h⟩ (f.val τ)) = f.val g
      rw [dite_eq_left hg]
      have he := f.property ⟨g, hg⟩ 1
      simpa only [Subgroup.subtype_apply, mul_one] using he.symm
    · change (if h : g ∈ H then ρ ⟨g, h⟩ (f.val 1) else
        ρ ⟨g * τ, (hcoset g).resolve_left h⟩ (f.val τ)) = f.val g
      rw [dite_eq_right hg]
      have he := f.property ⟨g * τ, (hcoset g).resolve_left hg⟩ τ
      rw [Subgroup.subtype_apply, mul_assoc, hτ, mul_one] at he
      exact he.symm
  right_inv x := by
    classical
    apply Prod.ext
    · change (if h : (1 : G) ∈ H then ρ ⟨1, h⟩ x.1 else
        ρ ⟨1 * τ, (hcoset 1).resolve_left h⟩ x.2) = x.1
      rw [dite_eq_left H.one_mem]
      change ρ 1 x.1 = x.1
      rw [map_one, Module.End.one_apply]
    · change (if h : τ ∈ H then ρ ⟨τ, h⟩ x.1 else
        ρ ⟨τ * τ, (hcoset τ).resolve_left h⟩ x.2) = x.2
      rw [dite_eq_right hτH]
      have he : (⟨τ * τ, (hcoset τ).resolve_left hτH⟩ : H) = 1 := Subtype.ext hτ
      rw [he, map_one, Module.End.one_apply]

/-- The induced representation in the actual transversal coordinates. -/
def inducedPair : Representation R G (M × M) where
  toFun g := (coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ)).toLinearMap ∘ₗ
    Representation.coind H.subtype ρ g ∘ₗ
      (coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ)).symm.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change (coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ))
      (Representation.coind H.subtype ρ 1
        ((coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ)).symm x)) = x
    rw [map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The actual involution exchanges the two coset coordinates. -/
theorem inducedPair_conjugation (x : M × M) :
    inducedPair H τ hτ hτH hcoset ρ τ x = (x.2, x.1) := by
  apply Prod.ext
  · change (pairCoind H τ hcoset ρ x).val (1 * τ) = x.2
    rw [one_mul]
    have he := congrArg Prod.snd ((coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ)).apply_symm_apply x)
    exact he
  · change (pairCoind H τ hcoset ρ x).val (τ * τ) = x.1
    rw [hτ]
    have he := congrArg Prod.fst ((coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ)).apply_symm_apply x)
    exact he

/-- Restriction in the first coset coordinate is precisely the original action. -/
theorem inducedPair_restriction (h : H) (x : M × M) :
    (inducedPair H τ hτ hτH hcoset ρ (h : G) x).1 = ρ h x.1 := by
  change (pairCoind H τ hcoset ρ x).val (1 * h) = _
  rw [one_mul]
  have he := (pairCoind H τ hcoset ρ x).property h 1
  rw [Subgroup.subtype_apply, mul_one] at he
  have hx := congrArg Prod.fst ((coindPairEquiv (H := H) (τ := τ) (hτ := hτ) (hτH := hτH) (hcoset := hcoset) (ρ := ρ)).apply_symm_apply x)
  exact he.trans (congrArg (ρ h) hx)

end TwoCosets


section RationalCosets

variable {K : Type} [Field K] [NumberField K]
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- The rational embedding of the number field in its identified closure. -/
def rationalEmbedding : K →ₐ[ℚ] Qbar :=
  e.toAlgHom.comp (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure K))

/-- The genuine quadratic fixing subgroup has index two. -/
theorem rationalBaseGroup_index_two (hdegree : Module.finrank ℚ K = 2) :
    (rationalBaseGroup e).index = 2 := by
  let F := (rationalEmbedding e).fieldRange
  have he : rationalBaseGroup e = F.fixingSubgroup := by
    ext g
    constructor
    · intro hg
      intro x
      obtain ⟨a, ha⟩ : ∃ a : K, rationalEmbedding e a = (x : Qbar) := x.property
      change g (x : Qbar) = x
      rw [← ha]
      exact hg a
    · intro hg
      intro a
      exact hg ⟨rationalEmbedding e a, ⟨a, rfl⟩⟩
  have hf : Module.finrank ℚ F = 2 :=
    (AlgHom.equivFieldRange (rationalEmbedding e)).toLinearEquiv.finrank_eq.symm.trans hdegree
  rw [he, ← IntermediateField.finrank_eq_fixingSubgroup_index Qbar F, hf]

/-- The actual imaginary quadratic conjugation is outside the fixing subgroup. -/
theorem tateConjugation_not_mem [IsTotallyComplex K]
    {S : Set (HeightOneSpectrum (𝓞 K))}
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S) :
    ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C ∉ rationalBaseGroup e := by
  intro h
  apply ZInQ.Manuscript.RC.CoefModules.complexConj_restrict_ne_refl K C.ι C.τ C.hι C.κ C.hτ
  apply RingEquiv.ext
  intro x
  apply (algebraMap K (AlgebraicClosure K)).injective
  apply e.injective
  calc
    e (algebraMap K (AlgebraicClosure K) (C.κ x)) =
        ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C (e (algebraMap K (AlgebraicClosure K) x)) := by
      rw [ZInQ.Manuscript.RC.KummerMaps.tateConjQ_apply_e, C.hτ]
    _ = e (algebraMap K (AlgebraicClosure K) x) := h x

/-- Either coset of an index-two subgroup is represented by the actual
involution. No choice of an unrelated involution is made. -/
theorem two_coset_cover {G : Type} [Group G] (H : Subgroup G) (hindex : H.index = 2)
    (τ : G) (hτ : τ * τ = 1) (hτH : τ ∉ H) : ∀ g : G, g ∈ H ∨ g * τ ∈ H := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hindex
  have ht : τ * a ∈ H := by
    rcases ha τ with h | h
    · exact h.1
    · exact False.elim (hτH h.1)
  have hτinv : τ⁻¹ = τ := by
    calc
      τ⁻¹ = τ⁻¹ * (τ * τ) := by rw [hτ, mul_one]
      _ = τ := by simp
  intro g
  by_cases hg : g ∈ H
  · exact Or.inl hg
  · right
    have hga : g * a ∈ H := by
      rcases ha g with h | h
      · exact h.1
      · exact False.elim (hg h.1)
    have hat : a⁻¹ * τ ∈ H := by
      simpa only [mul_inv_rev, hτinv] using H.inv_mem ht
    have hm := H.mul_mem hga hat
    simpa only [mul_assoc, mul_inv_cancel_left] using hm

end RationalCosets

section CoordinateRepresentations

/-- Coordinates of the two coefficient summands, without any scalar conjugation. -/
def pairCoordinates (R : Type) [CommRing R] :
    ((Fin 2 → R) × (Fin 2 → R)) ≃ₗ[R] ((Fin 2 ⊕ Fin 2) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) R R).symm

theorem pairCoordinates_left (R : Type) [CommRing R] (x : (Fin 2 → R) × (Fin 2 → R))
    (j : Fin 2) : pairCoordinates R x (Sum.inl j) = x.1 j := rfl

theorem pairCoordinates_right (R : Type) [CommRing R] (x : (Fin 2 → R) × (Fin 2 → R))
    (j : Fin 2) : pairCoordinates R x (Sum.inr j) = x.2 j := rfl

/-- Scalar identity matrices commute with change of coefficient ring. -/
theorem matrix_map_scalar_one {R A n : Type} [CommRing R] [CommRing A] [DecidableEq n]
    (f : R →+* A) (a : R) : (a • (1 : Matrix n n R)).map f = f a • (1 : Matrix n n A) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, h]

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hdegree : Module.finrank ℚ K = 2)

/-- The actual twisted Tate representation of the quadratic subgroup, in the
coefficient basis already used by the inner limit. -/
def baseCoordinateRepresentation : Representation Lambda (rationalBaseGroup e) (Fin 2 → Lambda) where
  toFun g := Matrix.toLin' (tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e g))
  map_one' := by rw [map_one, tlamActionMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, tlamActionMatrix_mul, Matrix.toLin'_mul]; rfl

/-- Coinduction from the genuine quadratic subgroup. -/
def rationalInducedRepresentation : Representation Lambda GalQ ((Fin 2 → Lambda) × (Fin 2 → Lambda)) :=
  inducedPair (H := rationalBaseGroup e)
    (τ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
    (hτ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C)
    (hτH := tateConjugation_not_mem e C)
    (hcoset := two_coset_cover (rationalBaseGroup e) (rationalBaseGroup_index_two e hdegree)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C) (tateConjugation_not_mem e C))
    (ρ := baseCoordinateRepresentation S e α E)

/-- The actual induced matrix in transversal coordinates. -/
def rationalInducedMatrix (g : GalQ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Lambda :=
  LinearMap.toMatrix' ((pairCoordinates Lambda).toLinearMap ∘ₗ
    rationalInducedRepresentation S e α E C hdegree g ∘ₗ (pairCoordinates Lambda).symm.toLinearMap)

/-- The matrices multiply because they come from the genuine coinduced action. -/
theorem rationalInducedMatrix_mul (g h : GalQ) :
    rationalInducedMatrix S e α E C hdegree (g * h) =
      rationalInducedMatrix S e α E C hdegree g * rationalInducedMatrix S e α E C hdegree h := by
  have he : (pairCoordinates Lambda).toLinearMap ∘ₗ
      rationalInducedRepresentation S e α E C hdegree (g * h) ∘ₗ (pairCoordinates Lambda).symm.toLinearMap =
      ((pairCoordinates Lambda).toLinearMap ∘ₗ rationalInducedRepresentation S e α E C hdegree g ∘ₗ
        (pairCoordinates Lambda).symm.toLinearMap).comp
      ((pairCoordinates Lambda).toLinearMap ∘ₗ rationalInducedRepresentation S e α E C hdegree h ∘ₗ
        (pairCoordinates Lambda).symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  unfold rationalInducedMatrix
  rw [he, LinearMap.toMatrix'_comp]

theorem rationalInducedMatrix_one : rationalInducedMatrix S e α E C hdegree 1 = 1 := by
  have he : (pairCoordinates Lambda).toLinearMap ∘ₗ
      rationalInducedRepresentation S e α E C hdegree 1 ∘ₗ (pairCoordinates Lambda).symm.toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [map_one]
    simp
  unfold rationalInducedMatrix
  rw [he, LinearMap.toMatrix'_id]

/-- Restriction in transversal coordinates is the actual twisted Tate action. -/
theorem rationalInducedRepresentation_first (g : rationalBaseGroup e)
    (x : (Fin 2 → Lambda) × (Fin 2 → Lambda)) :
    (rationalInducedRepresentation S e α E C hdegree (g : GalQ) x).1 =
      tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e g) *ᵥ x.1 := by
  exact inducedPair_restriction (H := rationalBaseGroup e)
    (τ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
    (hτ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C)
    (hτH := tateConjugation_not_mem e C)
    (hcoset := two_coset_cover (rationalBaseGroup e) (rationalBaseGroup_index_two e hdegree)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C) (tateConjugation_not_mem e C))
    (ρ := baseCoordinateRepresentation S e α E) g x

/-- The actual conjugation exchanges the two transversal coordinates. -/
theorem rationalInducedRepresentation_swap (x : (Fin 2 → Lambda) × (Fin 2 → Lambda)) :
    rationalInducedRepresentation S e α E C hdegree
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C) x = (x.2, x.1) := by
  exact inducedPair_conjugation (H := rationalBaseGroup e)
    (τ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
    (hτ := ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C)
    (hτH := tateConjugation_not_mem e C)
    (hcoset := two_coset_cover (rationalBaseGroup e) (rationalBaseGroup_index_two e hdegree)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ_mul_self e C) (tateConjugation_not_mem e C))
    (ρ := baseCoordinateRepresentation S e α E) x

/-- The first block row of the genuine induced matrix on the quadratic subgroup. -/
theorem rationalInducedMatrix_first (g : rationalBaseGroup e) (j : Fin 2)
    (l : Fin 2 ⊕ Fin 2) : rationalInducedMatrix S e α E C hdegree g (Sum.inl j) l =
    Sum.elim (fun k => tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e g) j k)
      (fun _ => 0) l := by
  rw [rationalInducedMatrix, LinearMap.toMatrix'_apply]
  change (rationalInducedRepresentation S e α E C hdegree g
    ((pairCoordinates Lambda).symm (Pi.single l 1))).1 j = _
  rw [rationalInducedRepresentation_first]
  rcases l with k | k
  · simp [pairCoordinates, Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [pairCoordinates, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The matrix of actual conjugation is the exchange matrix. -/
theorem rationalInducedMatrix_swap (a b : Fin 2 ⊕ Fin 2) :
    rationalInducedMatrix S e α E C hdegree (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C) a b =
    if a = Sum.swap b then 1 else 0 := by
  rw [rationalInducedMatrix, LinearMap.toMatrix'_apply]
  change pairCoordinates Lambda
    (rationalInducedRepresentation S e α E C hdegree
      (ZInQ.Manuscript.RC.KummerMaps.tateConjQ e C)
      ((pairCoordinates Lambda).symm (Pi.single b 1))) a = _
  rw [rationalInducedRepresentation_swap]
  rcases a with a | a <;> rcases b with b | b <;> simp [pairCoordinates, Pi.single_apply, eq_comm]

end CoordinateRepresentations

section SequenceCoefficientAction

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hdegree : Module.finrank ℚ K = 2) (U : Ultrafilter ℕ)
    (P : Ideal Lambda) [P.IsPrime]

/-- The coefficient action is limited integrally and then specialized. -/
def inducedSequenceMatrix (g : RationalSequences) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZInQ.Manuscript.RC.Wiring.ResAt P) :=
  (ulimMat U (fun i => rationalInducedMatrix S e α E C hdegree (g i))).map
    (algebraMap Lambda (ZInQ.Manuscript.RC.Wiring.ResAt P))

theorem inducedSequenceMatrix_one : inducedSequenceMatrix S e α E C hdegree U P 1 = 1 := by
  unfold inducedSequenceMatrix
  simp only [Pi.one_apply, rationalInducedMatrix_one, ulimMat_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inducedSequenceMatrix_mul (g h : RationalSequences) :
    inducedSequenceMatrix S e α E C hdegree U P (g * h) =
      inducedSequenceMatrix S e α E C hdegree U P g * inducedSequenceMatrix S e α E C hdegree U P h := by
  unfold inducedSequenceMatrix
  simp only [Pi.mul_apply, rationalInducedMatrix_mul, ulimMat_mul, Matrix.map_mul]

/-- The genuine induced coefficient representation of rational Galois sequences. -/
def inducedSequenceRepresentation : Representation (ZInQ.Manuscript.RC.Wiring.ResAt P)
    RationalSequences (FibrePair P) where
  toFun g := (pairCoordinates (ZInQ.Manuscript.RC.Wiring.ResAt P)).symm.toLinearMap ∘ₗ
    Matrix.toLin' (inducedSequenceMatrix S e α E C hdegree U P g) ∘ₗ
      (pairCoordinates (ZInQ.Manuscript.RC.Wiring.ResAt P)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    rw [inducedSequenceMatrix_one, Matrix.toLin'_one]
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    rw [inducedSequenceMatrix_mul, Matrix.toLin'_mul]
    simp

/-- The linear Galois action carried by the constructed induced representation. -/
@[instance_reducible]
def inducedSequenceAction : DistribMulAction RationalSequences (FibrePair P) where
  smul g x := inducedSequenceRepresentation S e α E C hdegree U P g x
  one_smul x := by
    change inducedSequenceRepresentation S e α E C hdegree U P 1 x = x
    rw [map_one, Module.End.one_apply]
  mul_smul g h x := by
    change inducedSequenceRepresentation S e α E C hdegree U P (g * h) x =
      inducedSequenceRepresentation S e α E C hdegree U P g
        (inducedSequenceRepresentation S e α E C hdegree U P h x)
    rw [map_mul, Module.End.mul_apply]
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

/-- The coefficient scalar action commutes with the genuine induced action. -/
theorem inducedSequenceScalarComm :
    letI := inducedSequenceAction S e α E C hdegree U P
    SMulCommClass RationalSequences (ZInQ.Manuscript.RC.Wiring.ResAt P) (FibrePair P) := by
  letI := inducedSequenceAction S e α E C hdegree U P
  refine ⟨?_⟩
  intro g a x
  exact (inducedSequenceRepresentation S e α E C hdegree U P g).map_smul a x

/-- The coefficient dictionary is constructed from genuine coinduction and the
Tate coefficient basis. Neither of its two identities is an input. -/
def genuineCoefficientDictionary :
    letI := inducedSequenceAction S e α E C hdegree U P
    letI := inducedSequenceScalarComm S e α E C hdegree U P
    InducedCoefficientDictionary S e α E C U P := by
  letI := inducedSequenceAction S e α E C hdegree U P
  letI := inducedSequenceScalarComm S e α E C hdegree U P
  refine ⟨?_, ?_⟩
  · intro x y
    apply (pairCoordinates (ZInQ.Manuscript.RC.Wiring.ResAt P)).injective
    change pairCoordinates (ZInQ.Manuscript.RC.Wiring.ResAt P)
      (inducedSequenceRepresentation S e α E C hdegree U P (sequenceConjugation e C) (x, y)) =
        pairCoordinates (ZInQ.Manuscript.RC.Wiring.ResAt P) (y, x)
    simp only [inducedSequenceRepresentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    funext a
    rcases a with j | j <;>
      simp [inducedSequenceMatrix, sequenceConjugation, rationalInducedMatrix_swap,
        pairCoordinates, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, ulimMat_apply, ulim_const]
  · intro g x
    funext j
    change (inducedSequenceRepresentation S e α E C hdegree U P (baseSequenceInclusion e g) x).1 j = _
    simp only [inducedSequenceRepresentation, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (inducedSequenceMatrix S e α E C hdegree U P (baseSequenceInclusion e g) *ᵥ
      pairCoordinates (ZInQ.Manuscript.RC.Wiring.ResAt P) x) (Sum.inl j) = _
    simp [inducedSequenceMatrix, baseSequenceInclusion, baseSequenceRestriction,
      rationalInducedMatrix_first, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      pairCoordinates_left, pairCoordinates_right, ulimMat_apply, ulim_zero]

end SequenceCoefficientAction

section BlockSpan

variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
    (ρ : Representation k G (M × M))

/-- The image of a representation spans a subalgebra of endomorphisms. -/
theorem image_span_mul {a b : Module.End k (M × M)}
    (ha : a ∈ Submodule.span k (Set.range ρ))
    (hb : b ∈ Submodule.span k (Set.range ρ)) :
    a * b ∈ Submodule.span k (Set.range ρ) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨h, rfl⟩ := hb
          rw [← map_mul]
          exact Submodule.subset_span (Set.mem_range_self _)
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
      | smul r b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hb
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [add_mul]; exact Submodule.add_mem _ ha hc
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

/-- The four coordinate blocks of a pair-module endomorphism. -/
def block11 (T : Module.End k M) : Module.End k (M × M) :=
  (LinearMap.inl k M M).comp (T.comp (LinearMap.fst k M M))

def block12 (T : Module.End k M) : Module.End k (M × M) :=
  (LinearMap.inl k M M).comp (T.comp (LinearMap.snd k M M))

def block21 (T : Module.End k M) : Module.End k (M × M) :=
  (LinearMap.inr k M M).comp (T.comp (LinearMap.fst k M M))

def block22 (T : Module.End k M) : Module.End k (M × M) :=
  (LinearMap.inr k M M).comp (T.comp (LinearMap.snd k M M))

def block11Linear : Module.End k M →ₗ[k] Module.End k (M × M) where
  toFun := block11
  map_add' a b := by ext x <;> simp [block11]
  map_smul' r a := by ext x <;> simp [block11]

/-- Distinct scalar characters separate the two coefficient summands. Together
with a spanning rank-two action and the actual exchange, they span every
endomorphism of the induced rank-four coefficient module. -/
theorem full_span_of_scalar_separation {H : Type} [Group H]
    (ι : H →* G) (r : Representation k H M)
    (hr : Submodule.span k (Set.range r) = ⊤)
    (hfirst : ∀ h (x : M × M), (ρ (ι h) x).1 = r h x.1)
    (τ : G) (hτ : ∀ x : M × M, ρ τ x = (x.2, x.1))
    (s : G) (a b : k) (hab : a ≠ b)
    (hs : ∀ x : M × M, ρ s x = (a • x.1, b • x.2)) :
    Submodule.span k (Set.range ρ) = ⊤ := by
  let X := Submodule.span k (Set.range ρ)
  have hid : (1 : Module.End k (M × M)) ∈ X := by
    rw [← map_one ρ]
    exact Submodule.subset_span (Set.mem_range_self _)
  have hτmem : ρ τ ∈ X := Submodule.subset_span (Set.mem_range_self τ)
  have hp : block11 (LinearMap.id : Module.End k M) ∈ X := by
    have he : block11 (LinearMap.id : Module.End k M) =
        (a - b)⁻¹ • (ρ s - b • (1 : Module.End k (M × M))) := by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · simp only [block11, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.id_apply,
          LinearMap.inl_apply, LinearMap.smul_apply, LinearMap.sub_apply, hs, Module.End.one_apply,
          Prod.smul_fst, Prod.fst_sub, ← sub_smul, smul_smul,
          inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul]
      · simp [block11, hs]
    rw [he]
    exact X.smul_mem _ (X.sub_mem (Submodule.subset_span (Set.mem_range_self s)) (X.smul_mem b hid))
  have h11gen (h : H) : block11 (r h) ∈ X := by
    have he : block11 (r h) = block11 (LinearMap.id : Module.End k M) * ρ (ι h) *
        block11 (LinearMap.id : Module.End k M) := by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · simp only [block11, Module.End.mul_apply, LinearMap.comp_apply, LinearMap.inl_apply,
          LinearMap.fst_apply, LinearMap.id_apply, hfirst]
      · simp [block11]
    rw [he]
    exact image_span_mul ρ (image_span_mul ρ hp
      (Submodule.subset_span (Set.mem_range_self (ι h)))) hp
  have h11 (T : Module.End k M) : block11 T ∈ X := by
    have he : Submodule.span k (Set.range r) ≤ X.comap block11Linear := by
      apply Submodule.span_le.mpr
      rintro _ ⟨h, rfl⟩
      exact h11gen h
    rw [hr] at he
    exact he Submodule.mem_top
  have h12 (T : Module.End k M) : block12 T ∈ X := by
    have he : block12 T = block11 T * ρ τ := by
      apply LinearMap.ext
      intro x
      simp [block11, block12, Module.End.mul_apply, hτ]
    rw [he]
    exact image_span_mul ρ (h11 T) hτmem
  have h21 (T : Module.End k M) : block21 T ∈ X := by
    have he : block21 T = ρ τ * block11 T := by
      apply LinearMap.ext
      intro x
      simp [block11, block21, Module.End.mul_apply, hτ]
    rw [he]
    exact image_span_mul ρ hτmem (h11 T)
  have h22 (T : Module.End k M) : block22 T ∈ X := by
    have he : block22 T = ρ τ * block11 T * ρ τ := by
      apply LinearMap.ext
      intro x
      simp [block11, block22, Module.End.mul_apply, hτ]
    rw [he]
    exact image_span_mul ρ (image_span_mul ρ hτmem (h11 T)) hτmem
  apply top_unique
  intro T _
  let T11 := (LinearMap.fst k M M).comp (T.comp (LinearMap.inl k M M))
  let T12 := (LinearMap.fst k M M).comp (T.comp (LinearMap.inr k M M))
  let T21 := (LinearMap.snd k M M).comp (T.comp (LinearMap.inl k M M))
  let T22 := (LinearMap.snd k M M).comp (T.comp (LinearMap.inr k M M))
  have he : T = block11 T11 + block12 T12 + block21 T21 + block22 T22 := by
    apply LinearMap.ext
    intro x
    have hx : x = (x.1, (0 : M)) + (0, x.2) := by ext <;> simp
    have ht := T.map_add (x.1, (0 : M)) (0, x.2)
    rw [← hx] at ht
    apply Prod.ext <;>
      simp [T11, T12, T21, T22, block11, block12, block21, block22, ht]
  rw [he]
  exact X.add_mem (X.add_mem (X.add_mem (h11 T11) (h12 T12)) (h21 T21)) (h22 T22)

end BlockSpan

section FiniteSpanWitness

open ZInQ.Manuscript.RC.Wiring (ResAt)

variable (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- A full coefficient image span has a finite witness consisting of actual
rational sequences, not arbitrary endomorphisms. -/
def coefficientSpanWitness_of_full
    (hfull : Submodule.span (ResAt P)
      (Set.range (linearAction (ResAt P) (FibrePair P) : RationalSequences → _)) = ⊤) :
    CoefficientSpanWitness P := by
  classical
  apply Classical.choice
  have hfg : (Submodule.span (ResAt P)
      (Set.range (linearAction (ResAt P) (FibrePair P) : RationalSequences → _))).FG := by
    rw [hfull]
    exact Module.Finite.fg_top
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  let f : Fin t.card ≃ {x // x ∈ t} := t.equivFin.symm
  let g : Fin t.card → RationalSequences := fun i => (ht (f i).property).choose
  have hg (i : Fin t.card) : linearAction (ResAt P) (FibrePair P) (g i) = (f i).val :=
    (ht (f i).property).choose_spec
  have he : Set.range (fun i => linearAction (ResAt P) (FibrePair P) (g i)) = (t : Set _) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change linearAction (ResAt P) (FibrePair P) (g i) ∈ (t : Set _)
      rw [hg]
      exact (f i).property
    · intro hx
      obtain ⟨i, hi⟩ := f.surjective ⟨x, hx⟩
      exact ⟨i, (hg i).trans (congrArg Subtype.val hi)⟩
  refine ⟨⟨t.card, g, ?_⟩⟩
  rw [he, ← hspan, hfull]

/-- The rank-four span input is constructed from a rank-two coefficient image
span and one arithmetic scalar separator. This isolates the nonquadratic
moving-inertia requirement; it contains no cohomology or determinant condition. -/
def coefficientSpanWitness_of_separation {H : Type} [Group H]
    (ι : H →* RationalSequences) (r : Representation (ResAt P) H (Fin 2 → ResAt P))
    (hr : Submodule.span (ResAt P) (Set.range r) = ⊤)
    (hfirst : ∀ h (x : FibrePair P), (ι h • x).1 = r h x.1)
    (τ : RationalSequences) (hτ : ∀ x : FibrePair P, τ • x = (x.2, x.1))
    (s : RationalSequences) (a b : ResAt P) (hab : a ≠ b)
    (hs : ∀ x : FibrePair P, s • x = (a • x.1, b • x.2)) : CoefficientSpanWitness P := by
  let ρ := Representation.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P)
  have hf := full_span_of_scalar_separation ρ ι r hr hfirst τ hτ s a b hab hs
  have he : (linearAction (ResAt P) (FibrePair P) : RationalSequences → _) = ρ := by
    funext g
    apply LinearMap.ext
    intro x
    rfl
  apply coefficientSpanWitness_of_full P
  rw [he]
  exact hf

end FiniteSpanWitness

section ArithmeticScalarFields

open ZInQ.Manuscript.RC.PrintsArith (TateMod tateRep SerreThm3 HasNoCM serre_scalar)
open ZInQ.Manuscript.RC.KummerMaps (tateConjQ tateConjQ_mul_self)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix)
open ZInQ.Manuscript.RC.GlueSweep.Tate (torsField torsCoords coordSet)

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- Triviality on the genuine Tate module fixes each finite torsion field. -/
theorem fixes_torsionField_of_tate_trivial (g : GalQ)
    (hg : ∀ x : TateMod E 2, tateRep E 2 g x = x) (i : ℕ) :
    ∀ x ∈ torsField E i, g x = x := by
  have hpoint (P : TauCeti.TateModuleLevel 2 (E.baseChange Qbar).toAffine.Point i) :
      WeierstrassCurve.Affine.Point.map g.toAlgHom (P : (E.baseChange Qbar).toAffine.Point) = P := by
    have hcard : ∀ n : ℕ, Nat.card (TauCeti.TateModuleLevel 2 (E.baseChange Qbar).toAffine.Point n) =
        (2 ^ n) ^ 2 := fun n => by
      convert (E.baseChange Qbar).natCard_tateModuleLevel
        ZInQ.Manuscript.RC.PrintsArith.two_ne_zero_qbar n
    obtain ⟨x, hx⟩ := TauCeti.TateModule.proj_surjective
      (TauCeti.TateModule.tateModuleTransition_surjective_of_natCard Nat.prime_two.ne_zero hcard) i P
    have he := congrArg (fun y : TateMod E 2 => ZInQ.Manuscript.RC.KummerMaps.tateProj E i y) (hg x)
    rw [ZInQ.Manuscript.RC.KummerMaps.tateProj_tateRep] at he
    have hep := congrArg (fun y : ZInQ.Manuscript.RC.KummerMaps.TateLevel E i =>
      (y : (E.baseChange Qbar).toAffine.Point)) he
    change WeierstrassCurve.Affine.Point.map g.toAlgHom
      (TauCeti.TateModule.proj i x : (E.baseChange Qbar).toAffine.Point) =
        (TauCeti.TateModule.proj i x : (E.baseChange Qbar).toAffine.Point) at hep
    rw [hx] at hep
    exact hep
  have hgen : ∀ x ∈ torsCoords E i, g x = x := by
    intro x hx
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hx
    have he := hpoint P
    generalize hP0 : (P : (E.baseChange Qbar).toAffine.Point) = P0 at hP he
    rcases P0 with _ | ⟨a, b, hab⟩
    · simp [coordSet] at hP
    · rw [WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq] at he
      simp only [coordSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with rfl | rfl
      · exact he.1
      · exact he.2
  have hfix : g ∈ (IntermediateField.adjoin ℚ (torsCoords E i)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    have heq : IntermediateField.adjoin ℚ (torsCoords E i) ≤
        IntermediateField.fixedField (Subgroup.zpowers g) := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change ∀ h : Subgroup.zpowers g, h.val x = x
      have hs : Subgroup.zpowers g ≤ MulAction.stabilizer GalQ x := by
        rw [Subgroup.zpowers_le]
        exact hgen x hx
      intro h
      exact hs h.property
    intro x hx
    exact heq hx ⟨g, Subgroup.mem_zpowers g⟩
  intro x hx
  exact hfix ⟨x, hx⟩

/-- The actual Tate action of the fixed norm scalar. -/
theorem tate_norm_scalar (g τ : GalQ) (u : ℤ_[2])
    (hg : ∀ x : TateMod E 2, tateRep E 2 g x = u • x) :
    ∀ x : TateMod E 2, tateRep E 2 (g ^ 2 * τ * g ^ 2 * τ⁻¹) x = u ^ 4 • x := by
  intro x
  have hτ : tateRep E 2 τ (tateRep E 2 τ⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simp only [pow_two, map_mul, Module.End.mul_apply, hg, map_smul, hτ, smul_smul]
  congr 1
  ring

/-- A scalar Tate action has trivial commutators on the full Tate module. -/
theorem tate_scalar_commutator (z : GalQ) (u : ℤ_[2])
    (hz : ∀ x : TateMod E 2, tateRep E 2 z x = u • x) (g : GalQ) :
    ∀ x : TateMod E 2, tateRep E 2 (z * g * z⁻¹ * g⁻¹) x = x := by
  have hc : Commute (tateRep E 2 z) (tateRep E 2 g) := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, hz, map_smul]
  have he : tateRep E 2 (z * g * z⁻¹ * g⁻¹) = 1 := by
    calc
      tateRep E 2 (z * g * z⁻¹ * g⁻¹) =
        tateRep E 2 g * (tateRep E 2 z * tateRep E 2 z⁻¹) * tateRep E 2 g⁻¹ := by
          rw [map_mul, map_mul, map_mul, hc.eq]
          simp only [mul_assoc]
      _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one, mul_one,
        ← map_mul, mul_inv_cancel, map_one]
  intro x
  rw [he, Module.End.one_apply]

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]

/-- The exact field property used from ring-class theory: conjugation acts by
inversion on the quadratic-subgroup automorphisms of the kernel fields. This
is a condition on fields and automorphisms, not on cohomology classes. -/
def DihedralKernelFields : Prop :=
  ∀ i (g : rationalBaseGroup e) (x : Qbar), x ∈ characterField S e α i ⊔ B i →
    (tateConjQ e C * (g : GalQ) * (tateConjQ e C)⁻¹) x = (g : GalQ)⁻¹ x

include C in
/-- A square fixes the quadratic number field. -/
theorem square_mem_quadratic (hdegree : Module.finrank ℚ K = 2) (g : GalQ) :
    g ^ 2 ∈ rationalBaseGroup e := by
  let H := rationalBaseGroup e
  let τ := tateConjQ e C
  have hn : H.Normal := Subgroup.normal_of_index_eq_two (rationalBaseGroup_index_two e hdegree)
  have hτ : τ * τ = 1 := tateConjQ_mul_self e C
  have cover := two_coset_cover H (rationalBaseGroup_index_two e hdegree) τ hτ
    (tateConjugation_not_mem e C)
  rcases cover g with hg | hg
  · exact H.pow_mem hg 2
  · let h : H := ⟨g * τ, hg⟩
    have he : g = (h : GalQ) * τ := by simp [h, mul_assoc, hτ]
    have hτinv : τ⁻¹ = τ := by
      calc
        τ⁻¹ = τ⁻¹ * (τ * τ) := by rw [hτ, mul_one]
        _ = τ := by simp
    have hcon := hn.conj_mem h h.property τ
    have hp := H.mul_mem h.property hcon
    rw [he, pow_two]
    simpa only [mul_assoc, hτinv] using hp

/-- The manuscript's norm scalar fixes every specified dihedral kernel field. -/
theorem norm_scalar_fixes_fields (hdegree : Module.finrank ℚ K = 2)
    (hB : DihedralKernelFields S e α C B) (g : GalQ) (i : ℕ) :
    ∀ x ∈ characterField S e α i ⊔ B i,
      (g ^ 2 * tateConjQ e C * g ^ 2 * (tateConjQ e C)⁻¹) x = x := by
  intro x hx
  have he := hB i ⟨g ^ 2, square_mem_quadratic (S := S) (e := e) (C := C) hdegree g⟩ x hx
  change (g ^ 2) ((tateConjQ e C * g ^ 2 * (tateConjQ e C)⁻¹) x) = x
  rw [he]
  change (g ^ 2) ((g ^ 2).symm x) = x
  exact AlgEquiv.apply_symm_apply _ x

/-- Field fixing is enough to make the common scalar's commutators satisfy
all character and specified arithmetic field constraints. -/
theorem field_commutator_mem (F : IntermediateField ℚ Qbar) [Normal ℚ F]
    (z : GalQ) (hz : ∀ x ∈ F, z x = x) (g : GalQ) : z * g * z⁻¹ * g⁻¹ ∈ F.fixingSubgroup := by
  have hzf : z ∈ F.fixingSubgroup := fun x => hz x x.property
  have hc := (inferInstance : F.fixingSubgroup.Normal).conj_mem z⁻¹
    (F.fixingSubgroup.inv_mem hzf) g
  simpa only [mul_assoc] using F.fixingSubgroup.mul_mem hzf hc

/-- Serre's non-CM theorem supplies the fixed scalar and its exact arithmetic
commutator condition when the specified fields satisfy ring-class inversion. -/
theorem exists_arithmetic_scalar_element (hSerre : SerreThm3) (hE : HasNoCM E)
    (hdegree : Module.finrank ℚ K = 2) (hB : DihedralKernelFields S e α C B) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ z : GalQ,
      (∀ x : TateMod E 2, tateRep E 2 z x = (1 + (2 : ℤ_[2]) ^ n) ^ 4 • x) ∧
      (∀ i, ∀ x ∈ characterField S e α i ⊔ B i, z x = x) ∧
      ∀ (g : GalQ) (i : ℕ), z * g * z⁻¹ * g⁻¹ ∈ derivativeKernel S e α E i ⊓ (B i).fixingSubgroup := by
  obtain ⟨n, hn, g, hg⟩ := serre_scalar hSerre E hE
  let z := g ^ 2 * tateConjQ e C * g ^ 2 * (tateConjQ e C)⁻¹
  have hzT := tate_norm_scalar E g (tateConjQ e C) (1 + (2 : ℤ_[2]) ^ n) hg
  have hzF := norm_scalar_fixes_fields S e α C B hdegree hB g
  refine ⟨n, hn, z, hzT, hzF, ?_⟩
  intro h i
  have hfields := field_commutator_mem (characterField S e α i ⊔ B i) z (hzF i) h
  have htor := fixes_torsionField_of_tate_trivial E (z * h * z⁻¹ * h⁻¹)
    (tate_scalar_commutator E z _ hzT h) i
  refine ⟨?_, ?_⟩
  · change z * h * z⁻¹ * h⁻¹ ∈ (torsField E i ⊔ characterField S e α i).fixingSubgroup
    have hchar : z * h * z⁻¹ * h⁻¹ ∈ (characterField S e α i).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le le_sup_left hfields
    have ht : z * h * z⁻¹ * h⁻¹ ∈ (torsField E i).fixingSubgroup := fun x => htor x x.property
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨ht, hchar⟩
  · exact IntermediateField.fixingSubgroup_le le_sup_right hfields

end ArithmeticScalarFields

section ScalarCoefficientAction

open ZInQ.Manuscript.RC.PrintsArith (TateMod tateRep SerreThm3 HasNoCM)
open ZInQ.Manuscript.RC.KummerMaps (tateConjQ)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)

/-- A genuine Tate scalar which fixes the finite character fields acts by that
scalar on the twisted coefficients at every retained precision. -/
theorem tlam_scalar_stage (z : GalQ)
    (hK : ∀ x : K, z (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (μ : ℤ_[2]) (hz : ∀ x : TateMod E 2, tateRep E 2 z x = μ • x)
    (hchar : ∀ i, ∀ x ∈ characterField S e α i, z x = x)
    (i : ℕ) (x : TLam K S (E⁄K) α) :
    gksOfQ S e z hK • x - algebraMap ℤ_[2] Lambda μ • x ∈ tlamNbhd K S (E⁄K) α i := by
  let s := gksOfQ S e z hK
  have hP (P : TateS K S (E⁄K)) : s • P = μ • P := by
    apply (tateSEquiv S E e).injective
    rw [tateSEquiv_gksOfQ_smul, hz, map_smul]
  have ha := characterField_trivial S e α i z hK (hchar i)
  induction x using TLam.induction with
  | zero => rw [smul_zero, smul_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul l P =>
      have he : s • (show TLam K S (E⁄K) α from l ⊗ₜ P) =
          ((α s : Lambdaˣ) : Lambda) •
            (algebraMap ℤ_[2] Lambda μ • (show TLam K S (E⁄K) α from l ⊗ₜ P)) := by
        rw [TLam.smul_tmul, hP]
        change (((α s : Lambdaˣ) : Lambda) * l) ⊗ₜ[ℤ_[2]] (μ • P) =
          ((α s : Lambdaˣ) : Lambda) • (algebraMap ℤ_[2] Lambda μ • (l ⊗ₜ[ℤ_[2]] P))
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def]
        simp only [smul_eq_mul]
        congr 1
        ring
      rw [he]
      have he' : ((α s : Lambdaˣ) : Lambda) •
          (algebraMap ℤ_[2] Lambda μ • (show TLam K S (E⁄K) α from l ⊗ₜ P)) -
          algebraMap ℤ_[2] Lambda μ • (show TLam K S (E⁄K) α from l ⊗ₜ P) =
          (((α s : Lambdaˣ) : Lambda) - 1) •
            (algebraMap ℤ_[2] Lambda μ • (show TLam K S (E⁄K) α from l ⊗ₜ P)) := by
        rw [sub_smul, one_smul]
      rw [he']
      exact Submodule.smul_mem_smul ha Submodule.mem_top
  | add x y hx hy =>
      rw [smul_add, smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy

/-- The exact scalar action matrix after taking the integral limit. -/
theorem tlam_scalar_matrix_limit (z : GalQ)
    (hK : ∀ x : K, z (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (μ : ℤ_[2]) (hz : ∀ x : TateMod E 2, tateRep E 2 z x = μ • x)
    (hchar : ∀ i, ∀ x ∈ characterField S e α i, z x = x)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    ulimMat U (fun _ : ℕ => tlamActionMatrix (W := E⁄K) (α := α) (gksOfQ S e z hK)) =
      algebraMap ℤ_[2] Lambda μ • (1 : Matrix (Fin 2) (Fin 2) Lambda) := by
  rw [← ulimMat_const U (algebraMap ℤ_[2] Lambda μ • (1 : Matrix (Fin 2) (Fin 2) Lambda))]
  apply ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU
  apply Eventually.of_forall
  intro i a b
  let B := tlamBasis (K := K) (S := S) (W := E⁄K) (α := α)
  have he := tlamHomeomorph_mem_stageIdeal (tlam_scalar_stage S e α E z hK μ hz hchar i (B b)) a
  rw [tlamHomeomorph_apply, map_sub, Finsupp.sub_apply] at he
  have hr : B.repr (algebraMap ℤ_[2] Lambda μ • B b) a =
      algebraMap ℤ_[2] Lambda μ • (if b = a then 1 else 0) := by
    rw [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply]
  rw [hr] at he
  change (tlamActionMatrix (W := E⁄K) (α := α) _ a b -
    (algebraMap ℤ_[2] Lambda μ • (1 : Matrix (Fin 2) (Fin 2) Lambda)) a b) ∈ stageIdeal i
  simpa only [tlamActionMatrix, LinearMap.toMatrix_apply, TLam.smul_def,
    Matrix.smul_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm] using he

/-- Tate conjugation preserves an exact scalar. -/
theorem tate_scalar_conjugate (z τ : GalQ) (μ : ℤ_[2])
    (hz : ∀ x : TateMod E 2, tateRep E 2 z x = μ • x) :
    ∀ x : TateMod E 2, tateRep E 2 (τ * z * τ⁻¹) x = μ • x := by
  intro x
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz, map_smul]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

include hU in
/-- The arithmetic common scalar is constructed from Serre's theorem and the
ring-class inversion property of the actual specified kernel fields. -/
def arithmeticCommonScalar_of_dihedral
    (D : InducedCoefficientDictionary S e α E C U P)
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]
    (hSerre : SerreThm3) (hE : HasNoCM E) (hdegree : Module.finrank ℚ K = 2)
    (hB : DihedralKernelFields S e α C B) : ArithmeticCommonScalar S e α E P B := by
  let h := exists_arithmetic_scalar_element E S e α C B hSerre hE hdegree hB
  let n := h.choose
  let z := h.choose_spec.2.choose
  have hn : 2 ≤ n := h.choose_spec.1
  have hz := h.choose_spec.2.choose_spec
  have hzK : z ∈ rationalBaseGroup e := by
    intro x
    exact hz.2.1 0 _ (le_sup_left (a := characterField S e α 0) (b := B 0)
      (characterField_containsK S e α 0 x))
  let τ := tateConjQ e C
  let y := τ * z * τ⁻¹
  have hchar : ∀ i, ∀ x ∈ characterField S e α i, z x = x :=
    fun i x hx => hz.2.1 i x (le_sup_left (a := characterField S e α i) (b := B i) hx)
  have hychar : ∀ i, ∀ x ∈ characterField S e α i, y x = x := by
    intro i x hx
    have hzf : z ∈ (characterField S e α i).fixingSubgroup := fun t => hchar i t t.property
    exact (inferInstance : (characterField S e α i).fixingSubgroup.Normal).conj_mem z hzf τ ⟨x, hx⟩
  have hyK : y ∈ rationalBaseGroup e := by
    intro x
    exact hychar 0 _ (characterField_containsK S e α 0 x)
  have hyT := tate_scalar_conjugate (E := E) z τ _ hz.1
  let ξ : ℕ → rationalBaseGroup e := fun _ => ⟨z, hzK⟩
  let η : ℕ → rationalBaseGroup e := fun _ => ⟨y, hyK⟩
  have hzFirst (x : FibrePair P) : (baseSequenceInclusion e ξ • x).1 = manuscriptScalar P n • x.1 := by
    rw [D.restriction]
    have hm := tlam_scalar_matrix_limit S e α E z hzK _ hz.1 hchar U hU
    change ((ulimMat U (fun _ : ℕ => tlamActionMatrix (W := E⁄K) (α := α)
      (gksOfQ S e z hzK))).map (algebraMap Lambda (ResAt P))) *ᵥ x.1 = _
    have hval : algebraMap Lambda (ResAt P)
        (algebraMap ℤ_[2] Lambda ((1 + (2 : ℤ_[2]) ^ n) ^ 4)) = manuscriptScalar P n :=
      (IsScalarTower.algebraMap_apply ℤ_[2] Lambda (ResAt P) _).symm
    rw [hm, matrix_map_scalar_one, hval, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hyFirst (x : FibrePair P) : (baseSequenceInclusion e η • x).1 = manuscriptScalar P n • x.1 := by
    rw [D.restriction]
    have hm := tlam_scalar_matrix_limit S e α E y hyK _ hyT hychar U hU
    change ((ulimMat U (fun _ : ℕ => tlamActionMatrix (W := E⁄K) (α := α)
      (gksOfQ S e y hyK))).map (algebraMap Lambda (ResAt P))) *ᵥ x.1 = _
    have hval : algebraMap Lambda (ResAt P)
        (algebraMap ℤ_[2] Lambda ((1 + (2 : ℤ_[2]) ^ n) ^ 4)) = manuscriptScalar P n :=
      (IsScalarTower.algebraMap_apply ℤ_[2] Lambda (ResAt P) _).symm
    rw [hm, matrix_map_scalar_one, hval, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨n, hn, (fun _ => z), ?_, ?_⟩
  · intro x
    have he := hyFirst (sequenceConjugation e C • x)
    have ht : baseSequenceInclusion e η • (sequenceConjugation e C • x) =
        sequenceConjugation e C • (baseSequenceInclusion e ξ • x) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      funext i
      change (τ * z * τ⁻¹) * τ = τ * z
      simp [mul_assoc]
    rw [ht, D.conjugation, D.conjugation] at he
    apply Prod.ext
    · exact hzFirst x
    · exact he
  · intro g
    rw [arithmeticSequenceKernel, Subgroup.mem_pi]
    intro i _
    exact hz.2.2 (g i) i

end ScalarCoefficientAction

section TateImageSpan

open ZInQ.Manuscript.RC.PrintsArith (TateMod tateRep SerreThm3 HasNoCM serre_two_adic)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix autOfMatrix autOfMatrix_apply toLin_one_add_smul
  toMatrix_autOfMatrix tateMatrix_mul)
open ZInQ.Manuscript.RC.Moving (isUnit_of_two_dvd_sub_one)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The non-CM open image supplies actual preimages of every small matrix. -/
theorem serre_small_matrices (hSerre : SerreThm3) (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ X : Matrix (Fin 2) (Fin 2) ℤ_[2],
      ∃ g : GalQ, tateMatrix E g = 1 + (2 : ℤ_[2]) ^ n • X := by
  obtain ⟨n, hn, h⟩ := serre_two_adic hSerre E hE
  have hu (X : Matrix (Fin 2) (Fin 2) ℤ_[2]) : IsUnit (1 + (2 : ℤ_[2]) ^ n • X).det := by
    apply isUnit_of_two_dvd_sub_one
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk, Matrix.det_fin_two, Matrix.one_fin_two]
    refine ⟨2 ^ k * (X 0 0 + X 1 1) + 2 ^ (2 * k + 1) * (X 0 0 * X 1 1 - X 0 1 * X 1 0), ?_⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    ring
  refine ⟨n, hn, fun X => ?_⟩
  obtain ⟨g, hg⟩ := h (autOfMatrix E _ _ (Matrix.mul_nonsing_inv _ (hu X))
    (Matrix.nonsing_inv_mul _ (hu X)))
    (fun x => ⟨Matrix.toLin (ZInQ.Manuscript.RC.PrintsArith.tateBasis E)
      (ZInQ.Manuscript.RC.PrintsArith.tateBasis E) X x, by rw [autOfMatrix_apply, toLin_one_add_smul]⟩)
  refine ⟨g, ?_⟩
  rw [tateMatrix, hg, toMatrix_autOfMatrix]

/-- The elementary matrices used by the fixed finite image witness. -/
def elementaryMatrix (k : Type) [CommRing k] (i j : Fin 2) : Matrix (Fin 2) (Fin 2) k :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- Squaring the three open-image matrices puts them in every quadratic subgroup. -/
theorem elementary_square00 {k : Type} [CommRing k] (u : k) :
    (1 + u • elementaryMatrix k 0 0) ^ 2 = 1 + (2 * u + u ^ 2) • elementaryMatrix k 0 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem elementary_square01 {k : Type} [CommRing k] (u : k) :
    (1 + u • elementaryMatrix k 0 1) ^ 2 = 1 + (2 * u) • elementaryMatrix k 0 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem elementary_square10 {k : Type} [CommRing k] (u : k) :
    (1 + u • elementaryMatrix k 1 0) ^ 2 = 1 + (2 * u) • elementaryMatrix k 1 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

/-- The four small square matrices span the full rank-two endomorphism algebra
over every characteristic-zero coefficient field. -/
theorem four_small_squares_span {k : Type} [Field k] [CharZero k] (n : ℕ) :
    Submodule.span k (Set.range (fun j : Fin 4 =>
      ![(1 : Matrix (Fin 2) (Fin 2) k),
        (1 + (2 : k) ^ n • elementaryMatrix k 0 0) ^ 2,
        (1 + (2 : k) ^ n • elementaryMatrix k 0 1) ^ 2,
        (1 + (2 : k) ^ n • elementaryMatrix k 1 0) ^ 2] j)) = ⊤ := by
  let X := Submodule.span k (Set.range (fun j : Fin 4 =>
    ![(1 : Matrix (Fin 2) (Fin 2) k),
      (1 + (2 : k) ^ n • elementaryMatrix k 0 0) ^ 2,
      (1 + (2 : k) ^ n • elementaryMatrix k 0 1) ^ 2,
      (1 + (2 : k) ^ n • elementaryMatrix k 1 0) ^ 2] j))
  have hI : (1 : Matrix (Fin 2) (Fin 2) k) ∈ X := Submodule.subset_span ⟨0, rfl⟩
  have h00s : (1 + (2 : k) ^ n • elementaryMatrix k 0 0) ^ 2 ∈ X :=
    Submodule.subset_span ⟨1, rfl⟩
  have h01s : (1 + (2 : k) ^ n • elementaryMatrix k 0 1) ^ 2 ∈ X :=
    Submodule.subset_span ⟨2, rfl⟩
  have h10s : (1 + (2 : k) ^ n • elementaryMatrix k 1 0) ^ 2 ∈ X :=
    Submodule.subset_span ⟨3, rfl⟩
  have ha : 2 * (2 : k) ^ n + ((2 : k) ^ n) ^ 2 ≠ 0 := by
    have hnat : (2 * 2 ^ n + (2 ^ n) ^ 2 : ℕ) ≠ 0 := by positivity
    exact_mod_cast hnat
  have hb : 2 * (2 : k) ^ n ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ two_ne_zero)
  have h00 : elementaryMatrix k 0 0 ∈ X := by
    rw [elementary_square00] at h00s
    have he := X.smul_mem (2 * (2 : k) ^ n + ((2 : k) ^ n) ^ 2)⁻¹ (X.sub_mem h00s hI)
    simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha, one_smul] using he
  have h01 : elementaryMatrix k 0 1 ∈ X := by
    rw [elementary_square01] at h01s
    have he := X.smul_mem (2 * (2 : k) ^ n)⁻¹ (X.sub_mem h01s hI)
    simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul] using he
  have h10 : elementaryMatrix k 1 0 ∈ X := by
    rw [elementary_square10] at h10s
    have he := X.smul_mem (2 * (2 : k) ^ n)⁻¹ (X.sub_mem h10s hI)
    simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul] using he
  have h11 : elementaryMatrix k 1 1 ∈ X := by
    have he : elementaryMatrix k 1 1 = 1 - elementaryMatrix k 0 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [elementaryMatrix, Matrix.one_apply]
    rw [he]
    exact X.sub_mem hI h00
  apply top_unique
  intro A _
  have he : A = A 0 0 • elementaryMatrix k 0 0 + A 0 1 • elementaryMatrix k 0 1 +
      A 1 0 • elementaryMatrix k 1 0 + A 1 1 • elementaryMatrix k 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [elementaryMatrix]
  rw [he]
  exact X.add_mem (X.add_mem (X.add_mem (X.smul_mem _ h00) (X.smul_mem _ h01))
    (X.smul_mem _ h10)) (X.smul_mem _ h11)

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)

include S C in
/-- Four actual rational Galois automorphisms in the quadratic subgroup span
the full rational Tate matrix algebra at every characteristic-zero fibre. -/
theorem exists_four_quadratic_tate_span (hSerre : SerreThm3) (hE : HasNoCM E)
    (hdegree : Module.finrank ℚ K = 2) (P : Ideal Lambda) [P.IsPrime]
    (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    ∃ f : Fin 4 → rationalBaseGroup e,
      Submodule.span (ResAt P) (Set.range (fun j =>
        (tateMatrix E (f j : GalQ)).map (algebraMap ℤ_[2] (ResAt P)))) = ⊤ := by
  have : CharZero (ResAt P) := charZero_resAt hP hne
  obtain ⟨n, hn, h⟩ := serre_small_matrices E hSerre hE
  obtain ⟨g00, hg00⟩ := h (elementaryMatrix ℤ_[2] 0 0)
  obtain ⟨g01, hg01⟩ := h (elementaryMatrix ℤ_[2] 0 1)
  obtain ⟨g10, hg10⟩ := h (elementaryMatrix ℤ_[2] 1 0)
  let f : Fin 4 → rationalBaseGroup e :=
    ![1, ⟨g00 ^ 2, square_mem_quadratic (S := S) (e := e) (C := C) hdegree g00⟩,
      ⟨g01 ^ 2, square_mem_quadratic (S := S) (e := e) (C := C) hdegree g01⟩,
      ⟨g10 ^ 2, square_mem_quadratic (S := S) (e := e) (C := C) hdegree g10⟩]
  have hcast (g : GalQ) (i j : Fin 2)
      (hg : tateMatrix E g = 1 + (2 : ℤ_[2]) ^ n • elementaryMatrix ℤ_[2] i j) :
      (tateMatrix E (g ^ 2)).map (algebraMap ℤ_[2] (ResAt P)) =
        (1 + (2 : ResAt P) ^ n • elementaryMatrix (ResAt P) i j) ^ 2 := by
    rw [pow_two, tateMatrix_mul, hg]
    apply Matrix.ext
    intro a b
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, elementaryMatrix,
        Matrix.one_apply, map_add, map_mul, map_pow, map_ofNat, pow_two] <;> ring
  have he : (fun j => (tateMatrix E (f j : GalQ)).map (algebraMap ℤ_[2] (ResAt P))) =
      (fun j : Fin 4 => ![(1 : Matrix (Fin 2) (Fin 2) (ResAt P)),
        (1 + (2 : ResAt P) ^ n • elementaryMatrix (ResAt P) 0 0) ^ 2,
        (1 + (2 : ResAt P) ^ n • elementaryMatrix (ResAt P) 0 1) ^ 2,
        (1 + (2 : ResAt P) ^ n • elementaryMatrix (ResAt P) 1 0) ^ 2] j) := by
    funext j
    fin_cases j
    · change (tateMatrix E 1).map (algebraMap ℤ_[2] (ResAt P)) = 1
      rw [ZInQ.Manuscript.RC.TateWiring.tateMatrix_one, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hcast g00 0 0 hg00
    · exact hcast g01 0 1 hg01
    · exact hcast g10 1 0 hg10
  refine ⟨f, ?_⟩
  rw [he]
  exact four_small_squares_span n

end TateImageSpan

section TwistedTateSpan

open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 HasNoCM)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)

/-- In the coefficient basis, the twisted action is the scalar character times
the genuine transported Tate matrix. -/
theorem tlamActionMatrix_character (g : rationalBaseGroup e) :
    tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e g) =
      ((α (baseRestriction S e g) : Lambdaˣ) : Lambda) •
        (rhoKMatrix S E e (g : GalQ)).map (algebraMap ℤ_[2] Lambda) := by
  apply Matrix.ext
  intro a b
  rw [tlamActionMatrix, LinearMap.toMatrix_apply, Matrix.smul_apply, Matrix.map_apply]
  have hb : (tlamBasis (K := K) (S := S) (W := E⁄K) (α := α) b : TLam K S (E⁄K) α) =
      (show TLam K S (E⁄K) α from (1 : Lambda) ⊗ₜ (basisK S E b)) := tlamBasis_apply b
  have hgT : baseRestriction S e g • (basisK S E b) = rhoK S E e (g : GalQ) (basisK S E b) :=
    gksOfQ_smul_eq_rhoK (S := S) (e := e) (E := E) (g : GalQ) g.property (basisK S E b)
  have ha : TLam.act (α := α) (baseRestriction S e g)
      (tlamBasis (K := K) (S := S) (W := E⁄K) (α := α) b) =
      (show TLam K S (E⁄K) α from ((α (baseRestriction S e g) : Lambdaˣ) : Lambda) ⊗ₜ
        (rhoK S E e (g : GalQ) (basisK S E b))) := by
    calc
      TLam.act (α := α) (baseRestriction S e g)
          (tlamBasis (K := K) (S := S) (W := E⁄K) (α := α) b) =
          (show TLam K S (E⁄K) α from (((α (baseRestriction S e g) : Lambdaˣ) : Lambda) * 1) ⊗ₜ
            (baseRestriction S e g • (basisK S E b))) := by
        rw [hb, ← TLam.smul_def, TLam.smul_tmul]
      _ = _ := by
        simpa only [mul_one] using congrArg
          (fun P : TateS K S (E⁄K) => show TLam K S (E⁄K) α from
            ((α (baseRestriction S e g) : Lambdaˣ) : Lambda) ⊗ₜ P) hgT
  rw [ha, tlamBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  change (Algebra.TensorProduct.basis Lambda (basisK S E)).repr
    (((α (baseRestriction S e g) : Lambdaˣ) : Lambda) ⊗ₜ[ℤ_[2]]
      (rhoK S E e (g : GalQ) (basisK S E b))) a = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    rhoKMatrix, LinearMap.toMatrix_apply]

/-- Unit rescaling does not change the linear span of a finite image family. -/
theorem span_unit_rescaling {k V I : Type} [Field k] [AddCommGroup V] [Module k V]
    (f : I → V) (a : I → k) (ha : ∀ i, a i ≠ 0) :
    Submodule.span k (Set.range (fun i => a i • f i)) = Submodule.span k (Set.range f) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f i ∈ Submodule.span k (Set.range (fun i => a i • f i))
    have hm := Submodule.smul_mem (Submodule.span k (Set.range (fun i => a i • f i))) (a i)⁻¹
      (Submodule.subset_span (Set.mem_range_self i))
    simpa only [smul_smul, inv_mul_cancel₀ (ha i), one_smul] using hm

/-- A genuine invertible change of coefficient basis preserves a full matrix span. -/
theorem span_matrix_conjugation {k I : Type} [Field k]
    (A B : Matrix (Fin 2) (Fin 2) k) (hAB : A * B = 1) (hBA : B * A = 1)
    (f : I → Matrix (Fin 2) (Fin 2) k)
    (hf : Submodule.span k (Set.range f) = ⊤) :
    Submodule.span k (Set.range (fun i => A * f i * B)) = ⊤ := by
  let T : Module.End k (Matrix (Fin 2) (Fin 2) k) :=
    { toFun M := A * M * B
      map_add' M N := by simp [mul_add, add_mul]
      map_smul' r M := by simp [mul_smul_comm, smul_mul_assoc] }
  have hs : Function.Surjective T := by
    intro M
    refine ⟨B * M * A, ?_⟩
    change A * (B * M * A) * B = M
    simp only [← mul_assoc, hAB, one_mul]
    rw [mul_assoc, hAB, mul_one]
  have he : Set.range (fun i => A * f i * B) = T '' Set.range f := by
    ext M
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, Set.mem_range_self i, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [he, ← Submodule.map_span, hf, Submodule.map_top, LinearMap.range_eq_top.mpr hs]

include C in
/-- Four actual quadratic-subgroup elements span the twisted rank-two
coefficient action. The proof uses Serre, a genuine basis change, and unit
character values; no irreducibility of the residual representation is assumed. -/
theorem exists_four_twisted_span (hSerre : SerreThm3) (hE : HasNoCM E)
    (hdegree : Module.finrank ℚ K = 2) (P : Ideal Lambda) [P.IsPrime]
    (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    ∃ f : Fin 4 → rationalBaseGroup e,
      Submodule.span (ResAt P) (Set.range (fun j =>
        (tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e (f j))).map
          (algebraMap Lambda (ResAt P)))) = ⊤ := by
  obtain ⟨f, hf⟩ := exists_four_quadratic_tate_span (S := S) (e := e) (C := C)
    E hSerre hE hdegree P hP hne
  let bQ := basisQ S E e
  let b := ZInQ.Manuscript.RC.PrintsArith.tateBasis E
  let A := (bQ.toMatrix b).map (algebraMap ℤ_[2] (ResAt P))
  let B := (b.toMatrix bQ).map (algebraMap ℤ_[2] (ResAt P))
  have hAB0 : bQ.toMatrix b * b.toMatrix bQ = 1 := bQ.toMatrix_mul_toMatrix_flip b
  have hBA0 : b.toMatrix bQ * bQ.toMatrix b = 1 := b.toMatrix_mul_toMatrix_flip bQ
  have hAB : A * B = 1 := by
    rw [← Matrix.map_mul, hAB0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    rw [← Matrix.map_mul, hBA0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcon := span_matrix_conjugation A B hAB hBA
    (fun j => (tateMatrix E (f j : GalQ)).map (algebraMap ℤ_[2] (ResAt P))) hf
  let μ : Fin 4 → ResAt P := fun j => algebraMap Lambda (ResAt P)
    ((α (baseRestriction S e (f j)) : Lambdaˣ) : Lambda)
  have hμ (j : Fin 4) : μ j ≠ 0 :=
    ((α (baseRestriction S e (f j))).isUnit.map (algebraMap Lambda (ResAt P))).ne_zero
  have map_map (M : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
      (M.map (algebraMap ℤ_[2] Lambda)).map (algebraMap Lambda (ResAt P)) =
        M.map (algebraMap ℤ_[2] (ResAt P)) := by
    apply Matrix.ext
    intro a b
    exact (IsScalarTower.algebraMap_apply ℤ_[2] Lambda (ResAt P) (M a b)).symm
  have hrho (j : Fin 4) :
      ((rhoKMatrix S E e (f j : GalQ)).map (algebraMap ℤ_[2] Lambda)).map
        (algebraMap Lambda (ResAt P)) =
        A * (tateMatrix E (f j : GalQ)).map (algebraMap ℤ_[2] (ResAt P)) * B := by
    rw [rhoKMatrix_eq, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      map_map, map_map, map_map]
  have he : (fun j => (tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e (f j))).map
      (algebraMap Lambda (ResAt P))) = fun j =>
      μ j • (A * (tateMatrix E (f j : GalQ)).map (algebraMap ℤ_[2] (ResAt P)) * B) := by
    funext j
    apply Matrix.ext
    intro a b
    simp only [tlamActionMatrix_character, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    change μ j * algebraMap Lambda (ResAt P)
      (algebraMap ℤ_[2] Lambda (rhoKMatrix S E e (f j : GalQ) a b)) =
        μ j * (A * (tateMatrix E (f j : GalQ)).map (algebraMap ℤ_[2] (ResAt P)) * B) a b
    congr 1
    exact congrFun (congrFun (hrho j) a) b
  refine ⟨f, ?_⟩
  rw [he, span_unit_rescaling _ μ hμ]
  exact hcon

end TwistedTateSpan

section BaseSequenceSpan

open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 HasNoCM)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]

/-- The first coefficient summand under actual sequences fixing the number field. -/
def baseSequenceRepresentation : Representation (ResAt P) (ℕ → rationalBaseGroup e) (Fin 2 → ResAt P) where
  toFun g := Matrix.toLin' ((ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
    (baseSequenceRestriction S e g i))).map (algebraMap Lambda (ResAt P)))
  map_one' := by
    have he : ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
        (baseSequenceRestriction S e 1 i)) = 1 := by
      simp only [map_one, Pi.one_apply, tlamActionMatrix_one, ulimMat_one]
    rw [he, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    have he : ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
        (baseSequenceRestriction S e (g * h) i)) =
        ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
          (baseSequenceRestriction S e g i)) *
        ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
          (baseSequenceRestriction S e h i)) := by
      simp only [map_mul, Pi.mul_apply, tlamActionMatrix_mul, ulimMat_mul]
    rw [he, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

include C in
/-- Serre's four genuine quadratic-subgroup elements already span the first
coefficient summand of the sequence representation. -/
theorem baseSequenceRepresentation_span (hSerre : SerreThm3) (hE : HasNoCM E)
    (hdegree : Module.finrank ℚ K = 2) (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    Submodule.span (ResAt P) (Set.range (baseSequenceRepresentation S e α E U P)) = ⊤ := by
  obtain ⟨f, hf⟩ := exists_four_twisted_span S e α E C hSerre hE hdegree P hP hne
  let M := fun j => (tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e (f j))).map
    (algebraMap Lambda (ResAt P))
  have hc (j : Fin 4) : baseSequenceRepresentation S e α E U P (fun _ => f j) = Matrix.toLin' (M j) := by
    change Matrix.toLin' ((ulimMat U (fun _ : ℕ => tlamActionMatrix (W := E⁄K) (α := α)
      (baseRestriction S e (f j)))).map (algebraMap Lambda (ResAt P))) = _
    rw [ulimMat_const]
  have hle : (Submodule.span (ResAt P) (Set.range M)).map Matrix.toLin'.toLinearMap ≤
      Submodule.span (ResAt P) (Set.range (baseSequenceRepresentation S e α E U P)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change Matrix.toLin' (M j) ∈ Submodule.span (ResAt P)
      (Set.range (baseSequenceRepresentation S e α E U P))
    exact Submodule.subset_span ⟨(fun _ => f j), hc j⟩
  rw [hf, Submodule.map_top, LinearEquiv.range] at hle
  exact top_unique hle

end BaseSequenceSpan

section NonquadraticCoefficientInput

open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 HasNoCM)
open ZInQ.Manuscript.RC.KummerMaps (tateConjQ)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix tateMatrix_one)
open ZInQ.Manuscript.RC.GlueSweep.Tate (torsField tateMatrix_congr_of_eqOn_torsField)

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hdegree : Module.finrank ℚ K = 2) (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]

/-- The actual conjugation on the quadratic fixing subgroup. -/
def baseConjugate (g : rationalBaseGroup e) : rationalBaseGroup e :=
  ⟨tateConjQ e C * g * (tateConjQ e C)⁻¹,
    (Subgroup.normal_of_index_eq_two (rationalBaseGroup_index_two e hdegree)).conj_mem
      g g.property (tateConjQ e C)⟩

/-- The exact arithmetic export needed from moving inertia. It fixes the Tate
precision and has opposite scalar characters under actual conjugation. The
specialized character is nonquadratic. No class evaluation occurs in this type. -/
structure NonquadraticInertiaInput where
  element : ℕ → rationalBaseGroup e
  torsion : ∀ i, ∀ x ∈ torsField E i, (element i : GalQ) x = x
  inverse : ∀ i, α (baseRestriction S e (baseConjugate (S := S) (e := e) (C := C) (hdegree := hdegree) (element i))) =
    (α (baseRestriction S e (element i)))⁻¹
  nonquadratic : (algebraMap Lambda (ResAt P) (ulim U
    (fun i => ((α (baseRestriction S e (element i)) : Lambdaˣ) : Lambda)))) ^ 2 ≠ 1

/-- Tate-precision fixing alone gives the character scalar as the limiting
rank-two coefficient matrix. No character-triviality input is used. -/
theorem tate_precision_character_limit (g : ℕ → rationalBaseGroup e)
    (htor : ∀ i, ∀ x ∈ torsField E i, (g i : GalQ) x = x)
    (hU : (U : Filter ℕ) ≤ cofinite) :
    ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e (g i))) =
      ulim U (fun i => ((α (baseRestriction S e (g i)) : Lambdaˣ) : Lambda)) •
        (1 : Matrix (Fin 2) (Fin 2) Lambda) := by
  let c := fun i => ((α (baseRestriction S e (g i)) : Lambdaˣ) : Lambda)
  have hstage (i : ℕ) (a b : Fin 2) :
      (tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e (g i)) - c i • 1) a b ∈ stageIdeal i := by
    have hq := tateMatrix_congr_of_eqOn_torsField E (h := (g i : GalQ)) (σ := 1)
      (fun x hx => (htor i x hx).trans (AlgEquiv.one_apply x).symm)
    have hk := rhoKMatrix_congr S E e hq
    have hentry := congrFun (congrFun hk a) b
    have hd : PadicInt.toZModPow i (rhoKMatrix S E e (g i : GalQ) a b -
        (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) a b) = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, rhoKMatrix_one] using hentry
    have hi := algebraMap_mem_stageIdeal hd
    have hδ : algebraMap ℤ_[2] Lambda ((1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) a b) =
        (1 : Matrix (Fin 2) (Fin 2) Lambda) a b := by simp [Matrix.one_apply]
    rw [map_sub, hδ] at hi
    simp only [tlamActionMatrix_character, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul]
    rw [← mul_sub]
    exact (stageIdeal i).mul_mem_left (c i) hi
  have he : ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α) (baseRestriction S e (g i))) =
      ulimMat U (fun i => c i • (1 : Matrix (Fin 2) (Fin 2) Lambda)) :=
    ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU (Eventually.of_forall hstage)
  rw [he]
  apply Matrix.ext
  intro a b
  change ulim U (fun i => c i * (1 : Matrix (Fin 2) (Fin 2) Lambda) a b) =
    ulim U c * (1 : Matrix (Fin 2) (Fin 2) Lambda) a b
  rw [ulim_mul, ulim_const]

/-- A nonquadratic moving-inertia export and Serre's theorem construct the
entire finite rank-four coefficient-span witness for the genuine action. -/
def genuineCoefficientSpanWitness
    (hU : (U : Filter ℕ) ≤ cofinite) (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (hSerre : SerreThm3) (hE : HasNoCM E)
    (I : NonquadraticInertiaInput (S := S) (e := e) (α := α) (E := E) (C := C)
      (hdegree := hdegree) (U := U) (P := P)) :
    letI := inducedSequenceAction S e α E C hdegree U P
    letI := inducedSequenceScalarComm S e α E C hdegree U P
    CoefficientSpanWitness P := by
  letI := inducedSequenceAction S e α E C hdegree U P
  letI := inducedSequenceScalarComm S e α E C hdegree U P
  let D := genuineCoefficientDictionary S e α E C hdegree U P
  let γ := I.element
  let η := fun i => baseConjugate (S := S) (e := e) (C := C) (hdegree := hdegree) (γ i)
  let c := fun i => ((α (baseRestriction S e (γ i)) : Lambdaˣ) : Lambda)
  let d := fun i => ((α (baseRestriction S e (η i)) : Lambdaˣ) : Lambda)
  let a := algebraMap Lambda (ResAt P) (ulim U c)
  let b := algebraMap Lambda (ResAt P) (ulim U d)
  have hd (i : ℕ) : c i * d i = 1 := by
    have hi := I.inverse i
    change ((α (baseRestriction S e (γ i)) : Lambdaˣ) : Lambda) *
      ((α (baseRestriction S e (baseConjugate (S := S) (e := e) (C := C) (hdegree := hdegree) (γ i))) : Lambdaˣ) : Lambda) = 1
    rw [hi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hab1 : a * b = 1 := by
    change algebraMap Lambda (ResAt P) (ulim U c) * algebraMap Lambda (ResAt P) (ulim U d) = 1
    rw [← map_mul, ← ulim_mul]
    have he : (fun i => c i * d i) = fun _ => (1 : Lambda) := funext hd
    rw [he, ulim_const, map_one]
  have hab : a ≠ b := by
    intro heq
    apply I.nonquadratic
    change a ^ 2 = 1
    calc
      a ^ 2 = a * b := by rw [pow_two, heq]
      _ = 1 := hab1
  have ηtor : ∀ i, ∀ x ∈ torsField E i, (η i : GalQ) x = x := by
    intro i x hx
    have hg : (γ i : GalQ) ∈ (torsField E i).fixingSubgroup := fun y => I.torsion i y y.property
    exact (inferInstance : (torsField E i).fixingSubgroup.Normal).conj_mem
      (γ i : GalQ) hg (tateConjQ e C) ⟨x, hx⟩
  have haFirst (x : FibrePair P) : (baseSequenceInclusion e γ • x).1 = a • x.1 := by
    rw [D.restriction]
    have hm := tate_precision_character_limit S e α E U γ I.torsion hU
    change (ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
      (baseRestriction S e (γ i)))).map (algebraMap Lambda (ResAt P)) *ᵥ x.1 = a • x.1
    rw [hm, matrix_map_scalar_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hbFirst (x : FibrePair P) : (baseSequenceInclusion e η • x).1 = b • x.1 := by
    rw [D.restriction]
    have hm := tate_precision_character_limit S e α E U η ηtor hU
    change (ulimMat U (fun i => tlamActionMatrix (W := E⁄K) (α := α)
      (baseRestriction S e (η i)))).map (algebraMap Lambda (ResAt P)) *ᵥ x.1 = b • x.1
    rw [hm, matrix_map_scalar_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hscalar (x : FibrePair P) : baseSequenceInclusion e γ • x = (a • x.1, b • x.2) := by
    have he := hbFirst (sequenceConjugation e C • x)
    have ht : baseSequenceInclusion e η • (sequenceConjugation e C • x) =
        sequenceConjugation e C • (baseSequenceInclusion e γ • x) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      funext i
      change (tateConjQ e C * γ i * (tateConjQ e C)⁻¹) * tateConjQ e C =
        tateConjQ e C * γ i
      simp [mul_assoc]
    rw [ht, D.conjugation, D.conjugation] at he
    exact Prod.ext (haFirst x) he
  apply coefficientSpanWitness_of_separation P (baseSequenceInclusion e)
    (baseSequenceRepresentation S e α E U P)
    (baseSequenceRepresentation_span (S := S) (e := e) (α := α) (E := E) (C := C)
      (U := U) (P := P) hSerre hE hdegree hP hne)
    (fun g x => D.restriction g x) (sequenceConjugation e C)
    (fun x => D.conjugation x.1 x.2) (baseSequenceInclusion e γ) a b hab hscalar

end NonquadraticCoefficientInput

section RetainedComparisonExports

open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx)

variable {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime]
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- Sufficient retained cochain exports for the global evaluation comparison.
These are degree-zero, degree-one, and degree-two maps, their two differential
identities, and a cochain embedding. No localization or kernel-detection
condition is part of the exports. -/
structure RetainedCochainEmbedding (n : ℕ) (Q : GCx (ResAt P)) where
  original : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1
  coordinates : Q.X 1 →ₗ[ResAt P] (Fin n → ResAt P)
  zero : Q.X 0 →ₗ[ResAt P] FibrePair P
  one : Q.X 1 →ₗ[ResAt P] (RationalSequences → FibrePair P)
  two : Q.X 2 →ₗ[ResAt P] (RationalSequences × RationalSequences → FibrePair P)
  differential_zero : ∀ x g, one (Q.d 0 1 rfl x) g = g • zero x - zero x
  differential_one : ∀ x g h, two (Q.d 1 2 rfl x) (g, h) =
    g • one x h - one x (g * h) + one x g
  zero_surjective : Function.Surjective zero
  one_injective : Function.Injective one
  original_projection : ∀ x (g : ℕ → rationalBaseGroup e),
    (one x (baseSequenceInclusion e g)).1 =
      basisValue P U original (baseSequenceRestriction S e g) (coordinates x)

/-- Boundary reflection is proved from the cochain embedding rather than
postulated as a separate cohomology or kernel-restriction assertion. -/
def retainedEvaluation_of_embedding {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedCochainEmbedding (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) :
    RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q where
  original := D.original
  coordinates := D.coordinates
  one := D.one
  two := D.two
  cochain_identity := D.differential_one
  principal_boundary x _ hx := boundary_of_principal_under_embedding Q D.zero D.one
    D.differential_zero D.zero_surjective D.one_injective x hx
  projection := D.original_projection

/-- The cochain embedding supplies a well-defined injective map from the
retained model's first cohomology to the first cohomology of the genuine
induced sequence representation. The degree-zero identity is used here;
boundary reflection alone would not define this map. -/
theorem exists_injective_actual_h1_map {n : ℕ} {Q : GCx (ResAt P)}
    (D : RetainedCochainEmbedding (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q) :
    ∃ F : Q.toCC.homology 1 →ₗ[ResAt P]
      groupCohomology.H1 (Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P)),
      Function.Injective F ∧
      ∀ a : LinearMap.ker (Q.d 1 2 rfl),
        F (clsAt Q 1 2 rfl a) = groupCohomology.H1π
          (Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P))
          (groupCohomology.cocyclesOfIsCocycle₁
            (RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
              (U := U) (P := P) (retainedEvaluation_of_embedding S e α E U P D) a)) := by
  let A := Rep.ofDistribMulAction (ResAt P) RationalSequences (FibrePair P)
  let V := retainedEvaluation_of_embedding S e α E U P D
  let f : LinearMap.ker (Q.d 1 2 rfl) →ₗ[ResAt P] groupCohomology.cocycles₁ A :=
    { toFun a := groupCohomology.cocyclesOfIsCocycle₁
        (RetainedEvaluation.isCocycle (S := S) (e := e) (α := α) (E := E)
          (U := U) (P := P) V a)
      map_add' a b := Subtype.ext (D.one.map_add a.val b.val)
      map_smul' r a := Subtype.ext (D.one.map_smul r a.val) }
  let v := (groupCohomology.H1π A).hom.comp f
  have hb (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a = 0) : v a = 0 := by
    obtain ⟨y, hy⟩ := clsAt_eq_zero Q 0 1 2 rfl rfl a ha
    change groupCohomology.H1π A (f a) = 0
    rw [groupCohomology.H1π_eq_zero_iff]
    refine ⟨D.zero y, ?_⟩
    funext g
    change g • D.zero y - D.zero y = D.one a.val g
    rw [← hy, D.differential_zero]
  obtain ⟨F, hF⟩ := exists_factor_of_surjective (clsAt Q 1 2 rfl)
    (clsAt_surjective Q 1 2 rfl) v hb
  refine ⟨F, ?_, hF⟩
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro w hw
  change w = 0
  obtain ⟨a, rfl⟩ := clsAt_surjective Q 1 2 rfl w
  have hva : v a = 0 := (hF a).symm.trans (LinearMap.mem_ker.mp hw)
  change groupCohomology.H1π A (f a) = 0 at hva
  rw [groupCohomology.H1π_eq_zero_iff] at hva
  obtain ⟨m, hm⟩ := hva
  have hprincipal : groupCohomology.IsCoboundary₁ (D.one a.val) := by
    refine ⟨m, fun g => ?_⟩
    exact congrFun hm g
  obtain ⟨y, hy⟩ := V.principal_boundary a.val a.property hprincipal
  have he : a = ⟨Q.d 0 1 rfl y, LinearMap.mem_ker.mpr (Q.d_d 0 1 2 rfl rfl y)⟩ :=
    Subtype.ext hy.symm
  rw [he]
  exact clsAt_boundary Q 0 1 2 rfl rfl y

/-- The exact global boundary-reflection export when the retained comparison
is not a cochain embedding, as may happen for the original Selmer cone. -/
def RetainedBoundaryReflection {Q : GCx (ResAt P)}
    (one : Q.X 1 →ₗ[ResAt P] (RationalSequences → FibrePair P)) : Prop :=
  ∀ x : Q.X 1, Q.d 1 2 rfl x = 0 →
    groupCohomology.IsCoboundary₁ (one x) → x ∈ LinearMap.range (Q.d 0 1 rfl)

/-- The retained producer can alternatively export a verified global
first-cohomology comparison. The construction consumes precisely its cochain
identities and original-basis normalization, not any local determinant. -/
def retainedEvaluation_of_boundary_reflection {n : ℕ} (Q : GCx (ResAt P))
    (original : Fin n → ℕ → (contCochains Lambda (GKS K S) (TLam K S (E⁄K) α)).X 1)
    (coordinates : Q.X 1 →ₗ[ResAt P] (Fin n → ResAt P))
    (one : Q.X 1 →ₗ[ResAt P] (RationalSequences → FibrePair P))
    (two : Q.X 2 →ₗ[ResAt P] (RationalSequences × RationalSequences → FibrePair P))
    (hchain : ∀ x g h, two (Q.d 1 2 rfl x) (g, h) =
      g • one x h - one x (g * h) + one x g)
    (hboundary : RetainedBoundaryReflection (P := P) one)
    (hprojection : ∀ x (g : ℕ → rationalBaseGroup e),
      (one x (baseSequenceInclusion e g)).1 =
        basisValue P U original (baseSequenceRestriction S e g) (coordinates x)) :
    RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q :=
  ⟨original, coordinates, one, two, hchain, hboundary, hprojection⟩

end RetainedComparisonExports

section ConstructedDetection

open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 HasNoCM)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx)

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hdegree : Module.finrank ℚ K = 2)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (hSerre : SerreThm3) (hE : HasNoCM E)
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]
    [∀ i, FiniteDimensional ℚ (B i)] (hB : DihedralKernelFields S e α C B)
    (I : NonquadraticInertiaInput (S := S) (e := e) (α := α) (E := E) (C := C)
      (hdegree := hdegree) (U := U) (P := P))
    (F : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F i)]
    (excl : ℕ → Finset ℕ)

include hS hU hP hne hSerre hE hB I in
/-- Detection with its coefficient dictionary, full coefficient span, and
common scalar constructed from genuine coefficient objects and the explicitly
stated arithmetic field and moving-inertia inputs. The retained cochain
embedding supplies the global first-cohomology comparison. -/
def detection_with_constructed_inputs :
    letI := inducedSequenceAction S e α E C hdegree U P
    letI := inducedSequenceScalarComm S e α E C hdegree U P
    ∀ {n : ℕ} (Q : GCx (ResAt P)) [FiniteDimensional (ResAt P) (Q.toCC.homology 1)]
      (D : RetainedCochainEmbedding (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
      (a : LinearMap.ker (Q.d 1 2 rfl)) (ha : clsAt Q 1 2 rfl a ≠ 0)
      (hdim : 1 < Module.finrank (ResAt P) (Q.toCC.homology 1)),
      ArithmeticDetection S hS e α E C U P B F excl hdegree Q
        (retainedEvaluation_of_embedding S e α E U P D) a := by
  letI := inducedSequenceAction S e α E C hdegree U P
  letI := inducedSequenceScalarComm S e α E C hdegree U P
  intro n Q _ D a ha hdim
  let coeff := genuineCoefficientDictionary S e α E C hdegree U P
  let scalar := arithmeticCommonScalar_of_dihedral (S := S) (e := e) (α := α) (E := E)
    (C := C) (U := U) (hU := hU) (P := P) (D := coeff) (B := B)
    (hSerre := hSerre) (hE := hE) (hdegree := hdegree) (hB := hB)
  let span := genuineCoefficientSpanWitness S e α E C hdegree U P hU hP hne hSerre hE I
  exact makeArithmeticDetection S hS e α E C U hU P hP hne B F excl hdegree
    Q coeff scalar span (retainedEvaluation_of_embedding S e α E U P D) a ha hdim

end ConstructedDetection

end ZInQ.Contrib.RC53Assist.Detection.Inputs
