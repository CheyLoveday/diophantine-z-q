import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology

namespace ZInQ.Manuscript.RC.HCMV21

open WeierstrassCurve

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Good reduction after extension to a subfield of `Ω`, at the restriction of the
same chosen valuation. The integral Weierstrass equation has unit discriminant. -/
def HasGoodModelAt (B : ValuationSubring Ω) (L : IntermediateField K Ω)
    (W : WeierstrassCurve K) : Prop :=
  ∃ W₀ : WeierstrassCurve (B.comap L.val.toRingHom), W₀.IsElliptic ∧
    ∃ C : VariableChange L,
      C • W.baseChange L = W₀.map (B.comap L.val.toRingHom).subtype

/-- Candidate printed input (one direction), UNVERIFIED locator: Silverman,
*The Arithmetic of Elliptic Curves*, VII.5.5. A curve with integral `j` over a
complete discretely valued field has good reduction after finite extension. The
extensions are realized in one chosen algebraic closure over that place. -/
def IntegralJHasPotentiallyGoodReduction : Prop :=
  ∀ (K Γ₀ : Type) [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [CompleteSpace K] [IsDiscreteValuationRing (Valued.v (R := K)).valuationSubring]
    (B : ValuationSubring (AlgebraicClosure K)),
    B.comap (algebraMap K (AlgebraicClosure K)) = (Valued.v (R := K)).valuationSubring →
    ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j ∈ (Valued.v (R := K)).valuationSubring →
      ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧ HasGoodModelAt B L W

/-- Good reduction persists over a larger subextension at the same place. -/
theorem hasGoodModelAt_mono (B : ValuationSubring Ω) {L M : IntermediateField K Ω} (h : L ≤ M)
    {W : WeierstrassCurve K} (hw : HasGoodModelAt B L W) : HasGoodModelAt B M W := by
  obtain ⟨W₀, hW₀, C, hC⟩ := hw
  let j := IntermediateField.inclusion h
  let BL := B.comap L.val.toRingHom
  let BM := B.comap M.val.toRingHom
  let j₀ : BL →+* BM := (j.toRingHom.comp BL.subtype).codRestrict BM.toSubring (fun x => x.2)
  refine ⟨W₀.map j₀, inferInstance, C.map j.toRingHom, ?_⟩
  have hbase : (W.baseChange L).map j.toRingHom = W.baseChange M := by
    exact (W.map_map _ _).trans (congrArg W.map j.comp_algebraMap)
  rw [← hbase, map_variableChange, hC, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  rfl

/-- A finite collection of good models can be placed over one finite extension at
a single place. The auxiliary finite extension `F` can contain the defining data
of a finite diagram of morphisms and order generators. -/
theorem simultaneous_good_models {ι : Type*} [Finite ι] (B : ValuationSubring Ω)
    (W : ι → WeierstrassCurve K) (F : IntermediateField K Ω) [FiniteDimensional K F]
    (h : ∀ i, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ HasGoodModelAt B L (W i)) :
    ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧ F ≤ M ∧
      ∀ i, HasGoodModelAt B M (W i) := by
  classical
  choose L hL hgood using h
  let (i : ι) : FiniteDimensional K (L i) := hL i
  let M := F ⊔ ⨆ i, L i
  exact ⟨M, inferInstance, le_sup_left,
    fun i => hasGoodModelAt_mono B ((le_iSup L i).trans le_sup_right) (hgood i)⟩

/-- The single-curve integral-`j` criterion supplies a common good field for a
finite collection, retaining the chosen place and the auxiliary field. -/
theorem simultaneous_good_models_of_integral_j {K Γ₀ ι : Type} [Field K] [CharZero K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    [IsDiscreteValuationRing (Valued.v (R := K)).valuationSubring] [Finite ι]
    (hgood : IntegralJHasPotentiallyGoodReduction)
    (B : ValuationSubring (AlgebraicClosure K))
    (hB : B.comap (algebraMap K (AlgebraicClosure K)) = (Valued.v (R := K)).valuationSubring)
    (W : ι → WeierstrassCurve K) [∀ i, (W i).IsElliptic]
    (hW : ∀ i, IsIntegral ℤ (W i).j)
    (F : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K F] :
    ∃ M : IntermediateField K (AlgebraicClosure K), FiniteDimensional K M ∧ F ≤ M ∧
      ∀ i, HasGoodModelAt B M (W i) :=
  simultaneous_good_models B W F fun i => by
    apply hgood K Γ₀ B hB (W i)
    let O := (Valued.v (R := K)).valuationSubring
    have hi : IsIntegral O (W i).j := (hW i).tower_top
    obtain ⟨j₀, hj₀⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    exact hj₀ ▸ j₀.property

end ZInQ.Manuscript.RC.HCMV21
