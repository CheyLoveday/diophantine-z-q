import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Rings.HeightOne
import ZInQKernel.Contrib.OneProof.RC.Central.Nodes

/-!
# Lane RC20: the central DVR `A = Λ_(t)` of Lemma `ex:arith-base-zero`

Manuscript (`diophantine_zq.tex`, 11/5 version), proof of Lemma `ex:arith-base-zero`:
* tex 4342–4343: "Put `A = Λ_(t)`, with residue field `ℚ₂` and fraction field `F`";
* tex 4353: "Over the DVR `A` ...".

This file builds the genuine ring `A = Λ_(t)` (`LambdaT`, the Mathlib localization of
`Λ = ℤ₂[[t]]` at the prime `(t)`) and proves:

* `LambdaT` is a DVR with uniformizer `t` and maximal ideal `(t)`;
* the residue map `rhoT : Λ_(t) → ℚ₂` (`t ↦ 0`), surjective with kernel the maximal ideal, so the
  residue field is `ℚ₂` (`residueFieldEquiv`);
* the map `halfToT : Λ[1/2] → Λ_(t)` and its compatibility with the central specialization
  `Λ[1/2] → ℚ₂` (RC16) and with the fraction field `F = Frac Λ`;
* the identification `hcoef` of RC15's node `baseZero_node` for a corrected coordinate lying in
  `Λ[1/2]` (`rhoT_eq_centralSpecialization`), and the instantiated node `baseZero_node_genuine`.

Everything here is `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform PowerSeries

/-! ## 1. `A = Λ_(t)` is a DVR with uniformizer `t` -/

/-- **`A = Λ_(t)`** (tex 4342–4343): the localization of `Λ = ℤ₂[[t]]` at the prime `(t)`. -/
abbrev LambdaT : Type := Localization.AtPrime (Ideal.span {(PowerSeries.X : Lambda)})

/-- **Tex 4342–4343, 4353 ("Over the DVR `A`"), PROVED.** `Λ_(t)` is a discrete valuation ring:
the localization of the UFD `Λ` at the principal prime `(t)`. -/
instance isDiscreteValuationRing_lambdaT : IsDiscreteValuationRing LambdaT :=
  isDiscreteValuationRing_of_atPrime (p := (X : Lambda)) LambdaT X_ne_zero

/-- **Tex 4342–4343, PROVED.** `t` is a uniformizer (an irreducible element) of `Λ_(t)`. -/
theorem irreducible_t_lambdaT : Irreducible (algebraMap Lambda LambdaT X) :=
  irreducible_algebraMap_of_atPrime (p := (X : Lambda)) LambdaT X_ne_zero

/-- **Tex 4342–4343, PROVED.** The maximal ideal of `Λ_(t)` is `(t)`. -/
theorem maximalIdeal_lambdaT :
    IsLocalRing.maximalIdeal LambdaT = Ideal.span {algebraMap Lambda LambdaT X} :=
  irreducible_t_lambdaT.maximalIdeal_eq

/-! ## 2. The residue map `ρ : Λ_(t) → ℚ₂` -/

/-- **Tex 4342–4343, PROVED.** An element of `Λ` outside `(t)` has nonzero constant coefficient, so
`f(0)` is a unit of `ℚ₂`. -/
theorem isUnit_lambdaEvalZero_of_not_mem (y : (Ideal.span {(X : Lambda)}).primeCompl) :
    IsUnit (lambdaEvalZero (y : Lambda)) := by
  have hy := y.2
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, X_dvd_iff] at hy
  rw [isUnit_iff_ne_zero]
  simp only [lambdaEvalZero, RingHom.coe_comp, Function.comp_apply]
  exact fun h => hy (PadicInt.coe_eq_zero.mp h)

/-- **The residue map `ρ : A = Λ_(t) → ℚ₂`** (tex 4342–4343), `t ↦ 0`: `IsLocalization.lift` of
`f ↦ f(0)` (`Uniform.lambdaEvalZero`). -/
def rhoT : LambdaT →+* ℚ_[2] :=
  IsLocalization.lift (M := (Ideal.span {(X : Lambda)}).primeCompl) (S := LambdaT)
    isUnit_lambdaEvalZero_of_not_mem

/-- **Tex 4342–4343, PROVED.** On `Λ ⊂ Λ_(t)`, `ρ` is `f ↦ f(0)`. -/
@[simp]
theorem rhoT_algebraMap (f : Lambda) : rhoT (algebraMap Lambda LambdaT f) = lambdaEvalZero f :=
  IsLocalization.lift_eq _ f

/-- **Tex 4342–4343, PROVED.** `ρ(t) = 0`. -/
theorem rhoT_t : rhoT (algebraMap Lambda LambdaT X) = 0 := by
  rw [rhoT_algebraMap]
  simp [lambdaEvalZero]

/-- **Tex 4342–4343, PROVED.** `ρ` kills the maximal ideal of `Λ_(t)` (the hypothesis `hρ` of RC15's
`baseZero_core`/`baseZero_node`). -/
theorem rhoT_maximalIdeal : ∀ x ∈ IsLocalRing.maximalIdeal LambdaT, rhoT x = 0 := by
  intro x hx
  rw [maximalIdeal_lambdaT, Ideal.mem_span_singleton'] at hx
  obtain ⟨b, rfl⟩ := hx
  rw [map_mul, rhoT_t, mul_zero]

/-- **Tex 4342–4343 ("with residue field `ℚ₂`"), PROVED.** `ρ` is surjective: `a/b ∈ ℚ₂` with
`a, b ∈ ℤ₂`, `b ≠ 0`, is `ρ` of the fraction `a/b` of constant series. -/
theorem rhoT_surjective : Function.Surjective rhoT := by
  intro q
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[2]) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbX : (C b : Lambda) ∈ (Ideal.span {(X : Lambda)}).primeCompl := by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, X_dvd_iff, constantCoeff_C]
    exact hb0
  refine ⟨IsLocalization.mk' LambdaT (C a : Lambda) ⟨C b, hbX⟩, ?_⟩
  rw [rhoT, IsLocalization.lift_mk'_spec]
  simp only [lambdaEvalZero, RingHom.coe_comp, Function.comp_apply, constantCoeff_C]
  have hb' : ((b : ℤ_[2]) : ℚ_[2]) ≠ 0 := fun h => hb0 (PadicInt.coe_eq_zero.mp h)
  change ((a : ℤ_[2]) : ℚ_[2]) = (b : ℚ_[2]) * ((a : ℚ_[2]) / (b : ℚ_[2]))
  field_simp

/-- **Tex 4342–4343, PROVED.** The kernel of `ρ` is the maximal ideal `(t)` of `Λ_(t)`. -/
theorem ker_rhoT : RingHom.ker rhoT = IsLocalRing.maximalIdeal LambdaT := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    by_contra hxm
    have hu : IsUnit x := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hxm
    have := hu.map rhoT
    rw [hx] at this
    exact not_isUnit_zero this
  · exact rhoT_maximalIdeal x

/-- **The residue field of `A = Λ_(t)` is `ℚ₂`** (tex 4342–4343): induced by `ρ`. -/
def residueFieldEquiv : IsLocalRing.ResidueField LambdaT ≃+* ℚ_[2] :=
  (Ideal.quotEquivOfEq ker_rhoT.symm).trans (RingHom.quotientKerEquivOfSurjective rhoT_surjective)

/-- **Tex 4342–4343, PROVED.** The identification of the residue field with `ℚ₂` is induced by `ρ`. -/
theorem residueFieldEquiv_residue (x : LambdaT) :
    residueFieldEquiv (IsLocalRing.residue LambdaT x) = rhoT x :=
  rfl

/-! ## 3. `Λ[1/2] → Λ_(t)`, the central specialization and `F = Frac Λ` -/

/-- **Tex 4342–4343, 5196–5200, PROVED.** `2` is a unit of `Λ_(t)` (`2 ∉ (t)`). -/
theorem isUnit_two_lambdaT : IsUnit (algebraMap Lambda LambdaT 2) :=
  IsLocalization.map_units LambdaT
    (⟨2, two_not_mem_of_height_one _ height_span_X span_X_ne_span_two⟩ :
      (Ideal.span {(X : Lambda)}).primeCompl)

/-- **The inclusion `Λ[1/2] ⊂ Λ_(t)`** (tex 4342–4343 with tex 5196–5200): `2` is a unit at `(t)`. -/
def halfToT : LambdaHalf →+* LambdaT :=
  IsLocalization.Away.lift (2 : Lambda) isUnit_two_lambdaT

/-- **Tex 4342–4343, 5196–5200, PROVED.** `Λ[1/2] → Λ_(t)` restricts to the inclusion on `Λ`. -/
@[simp]
theorem halfToT_algebraMap (f : Lambda) :
    halfToT (algebraMap Lambda LambdaHalf f) = algebraMap Lambda LambdaT f :=
  IsLocalization.Away.lift_eq _ _ f

/-- **Tex 4342–4343, 4914–4920, PROVED.** The residue map of `Λ_(t)` restricts on `Λ[1/2]` to the
central specialization `u ↦ u(0)` of RC16. -/
theorem rhoT_comp_halfToT : rhoT.comp halfToT = centralSpecialization := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (2 : Lambda)) ?_
  ext f
  simp only [RingHom.coe_comp, Function.comp_apply, halfToT_algebraMap, rhoT_algebraMap,
    centralSpecialization_algebraMap]
  rfl

/-- **Tex 4342–4343, 4914–4920, PROVED.** Elementwise form of `rhoT_comp_halfToT`. -/
theorem rhoT_halfToT (u : LambdaHalf) : rhoT (halfToT u) = centralSpecialization u := by
  rw [← rhoT_comp_halfToT, RingHom.comp_apply]

/-- **Tex 4342–4343 ("fraction field `F`"), 5196–5200, PROVED.** The inclusions `Λ[1/2] ⊂ Λ_(t) ⊂ F`
and `Λ[1/2] ⊂ F` (RC16's `lambdaHalfToFrac`) agree, `F = Frac Λ = Frac Λ_(t)`. -/
theorem algebraMap_halfToT (u : LambdaHalf) :
    algebraMap LambdaT (FractionRing Lambda) (halfToT u) = lambdaHalfToFrac u := by
  have h : (algebraMap LambdaT (FractionRing Lambda)).comp halfToT =
      (lambdaHalfToFrac : LambdaHalf →+* FractionRing Lambda) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (2 : Lambda)) ?_
    ext f
    simp only [RingHom.coe_comp, Function.comp_apply, halfToT_algebraMap, RingHom.coe_coe,
      AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply Lambda LambdaT (FractionRing Lambda) f).symm
  exact congrArg (fun φ : LambdaHalf →+* FractionRing Lambda => φ u) h

/-! ## 4. The identification `hcoef` of `baseZero_node` -/

/-- **Tex 4342–4343, 4365–4373, 5196–5200, 5703, PROVED (discharges the GLUE `hcoef` of RC15's
`baseZero_node`).** If the corrected coordinate `ũ₀ ∈ F = Frac Λ` lies in `Λ[1/2]`, `ũ₀ = w`
(what height-one regularity gives, tex 5196–5200 and 5703: "Both `ũ_x` and `ũ₀` lie in `Λ[1/2]`"),
then every integral representative `a ∈ Λ_(t)` of `ũ₀` has residue `ρ(a) = w(0)`, the central
specialization of `w`: `a` is the image of `w` because `Λ_(t) → F` is injective. -/
theorem rhoT_eq_centralSpecialization (w : LambdaHalf) (utilde0 : FractionRing Lambda)
    (hw : lambdaHalfToFrac w = utilde0) (a : LambdaT)
    (ha : algebraMap LambdaT (FractionRing Lambda) a = utilde0) :
    rhoT a = centralSpecialization w := by
  have h : a = halfToT w :=
    IsFractionRing.injective LambdaT (FractionRing Lambda)
      (by rw [ha, algebraMap_halfToT, hw])
  rw [h, rhoT_halfToT]

/-- **Tex 4342–4343, 4365–4373, 5196–5200, 5703, PROVED.** The hypothesis `hcoef` of RC15's
`baseZero_node` (with `A = Λ_(t)`, `F = Frac Λ`, `ρ = rhoT`) holds as soon as `ũ₀ = w ∈ Λ[1/2]` and
the package's datum is the central value of `w`: `C.u 0 0 = w(0)` (the top layer's
"`u x 0 = ũ_x(0)`"). -/
theorem hcoef_of_lambdaHalf {b : ℕ} (C : ZInQ.Contrib.CloudB3RC53.CoordData b) (w : LambdaHalf)
    (utilde0 : FractionRing Lambda) (hw : lambdaHalfToFrac w = utilde0)
    (hC : C.u 0 0 = centralSpecialization w) :
    ∀ a : LambdaT, algebraMap LambdaT (FractionRing Lambda) a = utilde0 → rhoT a = C.u 0 0 :=
  fun a ha => by rw [hC]; exact rhoT_eq_centralSpecialization w utilde0 hw a ha

/-- **Tex 4342–4343, 5196–5200, PROVED (non-vacuity of `rhoT_eq_centralSpecialization` and
`hcoef_of_lambdaHalf`).** For every
`w ∈ Λ[1/2]`, `ũ₀ := w ∈ F` has the integral representative `halfToT w ∈ Λ_(t)`. -/
theorem exists_representative (w : LambdaHalf) :
    ∃ a : LambdaT, algebraMap LambdaT (FractionRing Lambda) a = lambdaHalfToFrac w ∧
      rhoT a = centralSpecialization w :=
  ⟨halfToT w, algebraMap_halfToT w, rhoT_halfToT w⟩

/-! ## 5. `BaseZero` over the genuine `A = Λ_(t)` -/

open ZInQ.Contrib.CloudB3RC53 Matrix in
/-- **`BaseZero` from Lemma `ex:arith-base-zero` over the genuine `A = Λ_(t)`** (tex 4319–4373;
`A = Λ_(t)` with residue field `ℚ₂` and fraction field `F`: tex 4342–4343, 4353). PROVED.

RC15's `baseZero_node` instantiated with `A := LambdaT`, `F := FractionRing Lambda`
(`= Frac Λ = Frac Λ_(t)`), `ρ := rhoT`. Its hypothesis `hρ` is discharged (`rhoT_maximalIdeal`), and
its GLUE hypothesis `hcoef` is replaced by: the corrected coordinate lies in `Λ[1/2]`
(`w : Λ[1/2]`, `lambdaHalfToFrac w = utilde0`, from height-one regularity, tex 5196–5200, 5703) and
the package's datum is its central value (`C.u 0 0 = centralSpecialization w`, the top layer's
"`u x 0 = ũ_x(0)`"); see `hcoef_of_lambdaHalf`. All other hypotheses are RC15's, verbatim, with their
kinds as recorded there (`hCST`/`hheight` PRINT, `hcentral`, `h45`, `h47` ELLIOT, `hu` definition). -/
theorem baseZero_node_genuine {E : WeierstrassCurve ℚ} {k : ℚ} {b : ℕ} (C : CoordData b)
    (K : Type*) [Field K] [DecidableEq K] [Algebra ℚ K] (P : (E.baseChange K).toAffine.Point)
    (CSTThm11 : Prop) (hCST : CSTThm11)
    (hheight : CSTThm11 → ProductOrderGeTwo E k → IsOfFinAddOrder P) {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) LambdaT) (hcentral : (D.map rhoT).rank = m)
    (z w : Fin (m + 1) → LambdaT) (hz : D *ᵥ z = 0) (uprim : FractionRing Lambda)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
      (D.map (algebraMap LambdaT (FractionRing Lambda)))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim)
    (κ : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • κ P)
    (ε₀ : LambdaT) (utilde0 : FractionRing Lambda)
    (h47 : utilde0 = algebraMap LambdaT (FractionRing Lambda) ε₀ * uprim)
    (wHalf : LambdaHalf) (hwHalf : lambdaHalfToFrac wHalf = utilde0)
    (hC : C.u 0 0 = centralSpecialization wHalf) :
    BaseZero E k C :=
  ZInQ.Manuscript.RC.Central.baseZero_node C K P CSTThm11 hCST hheight rhoT rhoT_maximalIdeal D
    hcentral z w hz uprim hu κ Lm h45 ε₀ utilde0 h47
    (hcoef_of_lambdaHalf C wHalf utilde0 hwHalf hC)

end ZInQ.Manuscript.RC.Rings
