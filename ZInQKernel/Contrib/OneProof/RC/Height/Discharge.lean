import ZInQKernel.Contrib.OneProof.RC.Height.BaseZeroCST
import ZInQKernel.Contrib.OneProof.RC.Height.SumDifference
import ZInQKernel.Contrib.OneProof.RC.Central.Nodes
import ZInQKernel.Contrib.OneProof.RC.Central.Calibration

/-!
# Lane RC19 (height): discharging lane RC15's height inputs

Lane RC15 (`RC/Central/`) leaves two height facts as hypotheses:

1. **The height adjunction** behind `Reg_B / Reg_A = 2/I²` (tex 4082–4091; RC15's
   `Calibration.regulator_ratio` takes it as `hadj : α Reg_B = β Reg_A`, and `calibration_46` takes
   the result as `hReg : v₂(Reg_B / Reg_A) = ±1`; RC15 marks the adjunction GLUE).
2. **`hheight`** in `Nodes.baseZero_node` (tex 4345–4346: "the conductor-one height formula makes
   the specified point torsion").

This file discharges both from this lane's results:

* `regulator_inputs_sumDiff`: for the sum/difference isogenies between `A(ℚ) = E^{(h)}(K)` and
  `B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)` with rank-one free generators, the integers `α, β` of RC15's
  `regulator_ratio`, with `αβ = 2` (RC15's `h`), `α Reg_B = β Reg_A` (RC15's `hadj`), the indices
  `IJ = 2` (RC15's `isogenyIndex_mul`), `Reg_B = ρ Reg_A` with `ρ = 2/α² ∈ ℚ` (the shape RC15's
  `milne_valuation_form` consumes), `v₂ ρ = ±1` (RC15's `padicValRat_regulator_ratio`, the input
  `hReg` of `calibration_46`) and `Reg_A > 0` (input `hRegA` of `milne_valuation_form`).
* `baseZero_node_of_CST`: RC15's `baseZero_node` with `CSTThm11 := CSTThm11Split` and `hheight`
  supplied by `hheight_of_CST`; what remains are RC15's own inputs, the Heegner data, the trace
  identity `hP` and the GLUE `L`-factorization.

Every theorem in this file is PROVED (from the stated inputs).
-/

noncomputable section

open Height NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  Matrix

/-! ### The regulator inputs of the calibration (4.6) -/

section Regulator

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]
  (E : WeierstrassCurve ℚ) (h k : ℚ) (D : QuadData K k)
  [(qtwist E h).IsElliptic] [(qtwist E (h * k)).IsElliptic]

/-- **RC15's regulator inputs from the adjunction** (tex 4082–4091). With rank-one free generators
`g_A` of `A(ℚ) = E^{(h)}(K)` and `g_B` of `B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)` and `Reg_A = ĥ_A(g_A)`,
`Reg_B = ĥ_B(g_B)`: there are integers `α, β` with `φ g_A ≡ α g_B` and `ψ g_B ≡ β g_A` modulo
torsion such that
* `α β = 2` and `α Reg_B = β Reg_A` (the hypotheses `h`, `hadj` of RC15's `regulator_ratio`);
* `I J = 2` for `I = |α|`, `J = |β|` (RC15's `isogenyIndex_mul`);
* `Reg_B = ρ Reg_A` with `ρ = 2/α²` rational (the form of RC15's `milne_valuation_form`), and
  `v₂ ρ = ±1` (RC15's `padicValRat_regulator_ratio`; the input `hReg` of `calibration_46`);
* `Reg_A > 0` (`g_A` is not torsion; RC15's `hRegA`).
PROVED. -/
theorem regulator_inputs_sumDiff (gA : ((qtwist E h).baseChange K).toAffine.Point)
    (gB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator gA) (hB : IsFreeGenerator gB) :
    ∃ α β : ℤ, IsOfFinAddOrder (diffMap E h k D gA - α • gB) ∧
      IsOfFinAddOrder (sumMap E h k D gB - β • gA) ∧ α * β = 2 ∧
      (α : ℝ) * heightB E h k gB = β * gA.canonicalHeight ∧
      α.natAbs * β.natAbs = 2 ∧
      heightB E h k gB = ((2 / (α : ℚ) ^ 2 : ℚ) : ℝ) * gA.canonicalHeight ∧
      (padicValRat 2 (2 / (α : ℚ) ^ 2) = 1 ∨ padicValRat 2 (2 / (α : ℚ) ^ 2) = -1) ∧
      0 < gA.canonicalHeight := by
  obtain ⟨α, β, hα, hβ, hαβ, hadj, hreg⟩ := regulator_ratio_sumDiff E h k D gA gB hA hB
  have hα0 : (α : ℝ) ≠ 0 := by
    have : α ≠ 0 := by rintro rfl; simp at hαβ
    exact_mod_cast this
  refine ⟨α, β, hα, hβ, hαβ, hadj, ZInQ.Manuscript.RC.Central.isogenyIndex_mul hαβ, ?_,
    ZInQ.Manuscript.RC.Central.padicValRat_regulator_ratio hαβ,
    (canonicalHeight_pos_iff ((qtwist E h).baseChange K) gA).mpr hA.1⟩
  push_cast
  field_simp
  linear_combination hreg

end Regulator

/-! ### The base-zero node with `hheight` discharged -/

open Classical in
/-- **RC15's `baseZero_node` with `hheight` discharged** (tex 4319–4373). RC15's node is applied
with `CSTThm11 := CSTThm11Split` and `hheight := hheight_of_CST …`; the remaining hypotheses are
RC15's inputs (`hcentral`, `hu`, `h45`, `h47`, `hcoef`, with RC15's kinds), the conductor-one
Heegner data of the print, the trace identity `hP` ("the specified point") and the GLUE
factorization `LFactorizationConductorOne E K k`. PROVED. -/
theorem baseZero_node_of_CST {E : WeierstrassCurve ℚ} [E.IsElliptic] {k : ℚ} {b : ℕ}
    (C : CoordData b)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hL : LFactorizationConductorOne E K k) (hCST : CSTThm11Split)
    {A F : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F]
    [Algebra A F] [IsFractionRing A F] (ρ : A →+* ℚ_[2])
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {m : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (Dm.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : Dm *ᵥ z = 0) (uprim : F)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord (Dm.map (algebraMap A F))
      (fun i => algebraMap A F (z i)) (fun i => algebraMap A F (w i)) uprim)
    (kum : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => ρ (z i)) = (Lm : ℚ_[2]) • kum P)
    (ε₀ : A) (utilde0 : F) (h47 : utilde0 = algebraMap A F ε₀ * uprim)
    (hcoef : ∀ a : A, algebraMap A F a = utilde0 → ρ a = C.u 0 0) :
    BaseZero E k C :=
  ZInQ.Manuscript.RC.Central.baseZero_node C K P CSTThm11Split hCST
    (hheight_of_CST E k f hf Lat hLat hnCM scale hscale K hK2 hKc hD3 hD4 hsplit a₀ b₀ c₀ hH ι y
      hy P hP hL)
    ρ hρ Dm hcentral z w hz uprim hu kum Lm h45 ε₀ utilde0 h47 hcoef

end ZInQ.Manuscript.RC.Height
