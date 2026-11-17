import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq

noncomputable section

open Complex Topology Filter
open scoped PeriodPair

namespace ZInQ.Contrib.HCMDict

open WeierstrassCurve.Affine (Point)

/-! ## §1. Definitions -/

/-- `P ↦ P^σ` on the points of a Weierstrass curve over `ℂ`: `(x, y) ↦ (σx, σy)`, `O ↦ O`. -/
def conjPt (σ : ℂ →+* ℂ) {W : WeierstrassCurve ℂ} : W.toAffine.Point → (W.map σ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (σ x) (σ y) ((W.toAffine.map_nonsingular σ.injective x y).2 h)

/-- **Analytic isomorphism `ℂ/Λ → E(ℂ)`**, read as a map `ξ : ℂ → E(ℂ)`: a group homomorphism, onto,
with kernel exactly `Λ` (so `ξ` induces a group isomorphism `ℂ/Λ ≅ E(ℂ)`), and holomorphic in the affine
coordinates at every point not sent to `O`. -/
def IsAnalyticUnif (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z w, ξ (z + w) = ξ z + ξ w) ∧ Function.Surjective ξ ∧ (∀ z, ξ z = 0 ↔ z ∈ Λ) ∧
    ∀ z₀, ξ z₀ ≠ 0 → ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, ∃ h : W.toAffine.Nonsingular (X z) (Y z), ξ z = .some (X z) (Y z) h

/-! ## §2. The Weierstrass uniformization is an analytic isomorphism -/

theorem toPoint_isAnalyticUnif (L : PeriodPair) :
    IsAnalyticUnif L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) := by
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  refine ⟨hU.1, hU.2.1, fun z => ⟨hU.2.2 z, fun hz => L.toPoint_of_mem _ hz⟩, fun z₀ hz₀ => ?_⟩
  have hz₀' : z₀ ∉ L.lattice := fun h => hz₀ (L.toPoint_of_mem _ h)
  refine ⟨(L.lattice : Set ℂ)ᶜ, L.isClosed_lattice.isOpen_compl, hz₀', ℘[L], fun z => ℘'[L] z / 2,
    L.analyticOnNhd_weierstrassP.differentiableOn,
    (L.analyticOnNhd_derivWeierstrassP.differentiableOn).div_const 2, fun z hz => ?_⟩
  exact ⟨_, L.toPoint_of_notMem _ hz⟩

/-! ## §3. Scaling lattices; every short Weierstrass model over `ℂ` is `L.weierstrassCurve` -/

theorem scale_isScale (L : PeriodPair) (α : ℂˣ) : T5Glue.IsScale (L.scale α) L α := by
  refine ⟨α.ne_zero, ?_⟩
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, PeriodPair.mem_lattice, PeriodPair.scale_ω₁,
    PeriodPair.scale_ω₂, smul_eq_mul]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m * L.ω₁ + n * L.ω₂, ⟨m, n, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

theorem exists_lattice_eq (W : WeierstrassCurve ℂ) [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) : ∃ L : PeriodPair, L.weierstrassCurve = W := by
  obtain ⟨L, C, hC⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq W
  have e₁ := congrArg WeierstrassCurve.a₁ hC
  have e₂ := congrArg WeierstrassCurve.a₂ hC
  have e₃ := congrArg WeierstrassCurve.a₃ hC
  have e₄ := congrArg WeierstrassCurve.a₄ hC
  have e₆ := congrArg WeierstrassCurve.a₆ hC
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, PeriodPair.weierstrassCurve_a₁,
    PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄,
    PeriodPair.weierstrassCurve_a₆, h₁, h₂, h₃] at e₁ e₂ e₃ e₄ e₆
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hs : C.s = 0 := by
    have := (mul_eq_zero.1 e₁).resolve_left hu; linear_combination this / 2
  have hr : C.r = 0 := by
    have := (mul_eq_zero.1 e₂).resolve_left (pow_ne_zero _ hu); rw [hs] at this
    linear_combination this / 3
  have ht : C.t = 0 := by
    have := (mul_eq_zero.1 e₃).resolve_left (pow_ne_zero _ hu); rw [hr] at this
    linear_combination this / 2
  simp only [hs, hr, ht] at e₄ e₆
  refine ⟨L.scale C.u, ?_⟩
  have hsc := scale_isScale L C.u
  ext
  · simp [h₁]
  · simp [h₂]
  · simp [h₃]
  · rw [PeriodPair.weierstrassCurve_a₄, hsc.g₂, ← e₄]
    simp only [Units.val_inv_eq_inv_val]; ring
  · rw [PeriodPair.weierstrassCurve_a₆, hsc.g₃, ← e₆]
    simp only [Units.val_inv_eq_inv_val]; ring

end ZInQ.Contrib.HCMDict
