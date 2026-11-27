import ZInQKernel.Contrib.OneProof.RC.Limits.Ultralimit

/-!
# Lane RC30 (base zero, inner limit), part 1: the inner limit in the central fibre

Lemma `ex:arith-central-specialization` (`diophantine_zq.tex`, 11/5 version, tex 3895–3986)
proves the retained boundary (4.5) at every finite coefficient stage and then passes to the limit
(tex 3912–3921):

> The split norm relation gives an actual finite-stage boundary
> `z_i(0) − L m_i j_i(b_h) = d v_i`, `m_i = a_{r_i} − 2χ_h(r_i)` (4.5).
> The equality in global cohomology lifts to the Selmer cone because the local degree-zero maps
> are onto and the degree-one maps inject. Retain `v_i`. The uniform trace bound bounds `v₂(m_i)`
> and the local determinants by `c_E`; their adjugate identities multiplied by a fixed power of
> two survive the limit.

The limit is the inner limit of Lemma `ex:limits-inner-limit` (tex 4391–4451; tex 4444–4448: "Fix
one nonprincipal ultrafilter on coefficient stages. Bounded ranks can be fixed on a set in that
ultrafilter. Each finite tuple of matrix entries then has a compatible limit at every coefficient
precision, giving matrices over `Λ`. Every polynomial identity between the matrices survives."),
formalized by lane RC6 (`RC/Limits/Ultralimit.lean`: `ulim`, `ulimVec`, `ulimMat` along an
ultrafilter in a compact Hausdorff ring with ideals tending to zero).

The display (4.5) lives in the fibre `t = 0`: `z_i(0)` is the stage class specialized at `t = 0`,
with coefficients `A_i/(t) = ℤ/2^i` (tex 2725, `A_i = (ℤ/2^i)[t]/t^i`). This file supplies the
`t = 0` form of RC6's instance and two general facts used by the boundary file:

* `twoAdicStage i = (2^i) ⊂ ℤ₂`, the `t = 0` fibre of RC6's stage ideal `(2^i, t^i) ⊂ Λ`
  (`constantCoeff_mem_twoAdicStage`); these ideals are open and tend to zero in the compact ring
  `ℤ₂` (`twoAdicStage_isOpen`, `twoAdicStage_tendsToZero`), so RC6's survival theorems apply over
  `ℤ₂`;
* the inner limit commutes with continuous maps (`ulim_map`), in particular with `t ↦ 0`
  (`ulim_constantCoeff`): taking the inner limit over `Λ` and then specializing at `t = 0` is the
  same as taking the inner limit of the stage data at `t = 0`;
* a limit along a nonprincipal ultrafilter on the stages is attained along a strictly increasing
  sequence of stages (`exists_strictMono_tendsto_of_ultrafilter`), used to produce lane RC25's
  `atTop` form of the limit (`Boundary45Base.hlim`).

Every theorem in this file is `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open Filter Topology ZInQ.Manuscript.RC.Limits

/-! ## The stage ideals of the central fibre -/

/-- **The stage ideal `(2^i)` of the fibre `t = 0`** (tex 2725: `A_i/(t) = ℤ/2^i`): the kernel of
`ℤ₂ → ℤ/2^i`. It is the image of lane RC6's stage ideal `(2^i, t^i)` of `Λ` under `t ↦ 0`
(`constantCoeff_mem_twoAdicStage`). Kind: definition. -/
def twoAdicStage (i : ℕ) : Ideal ℤ_[2] :=
  Ideal.span {(2 : ℤ_[2]) ^ i}

/-- The stage ideals `(2^i)` are open in `ℤ₂` (lane RC6's `isOpen_span_two_pow`). PROVED. -/
theorem twoAdicStage_isOpen (i : ℕ) : IsOpen (twoAdicStage i : Set ℤ_[2]) :=
  isOpen_span_two_pow i

/-- The stage ideals decrease. PROVED. -/
theorem twoAdicStage_antitone : Antitone twoAdicStage := fun _ _ hmn =>
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow 2 hmn)

/-- **The stage ideals `(2^i)` tend to zero in `ℤ₂`** (the hypothesis `IdealsTendToZero` of lane
RC6's survival theorems, for the compact ring `ℤ₂`). PROVED from RC6's
`idealsTendToZero_of_antitone` and `eq_zero_of_forall_two_pow_dvd`. -/
theorem twoAdicStage_tendsToZero : IdealsTendToZero twoAdicStage :=
  idealsTendToZero_of_antitone twoAdicStage_antitone
    (fun n => AddSubgroup.isClosed_of_isOpen (twoAdicStage n).toAddSubgroup (twoAdicStage_isOpen n))
    (fun _ hr => eq_zero_of_forall_two_pow_dvd fun n => Ideal.mem_span_singleton.mp (hr n))

/-- Membership in `(2^i)` is divisibility by `2^i`. PROVED. -/
theorem mem_twoAdicStage_iff {i : ℕ} {x : ℤ_[2]} : x ∈ twoAdicStage i ↔ (2 : ℤ_[2]) ^ i ∣ x :=
  Ideal.mem_span_singleton

/-- **The fibre `t = 0` of RC6's stage ideal**: `t ↦ 0` maps `(2^i, t^i) ⊂ Λ` into `(2^i) ⊂ ℤ₂`.
PROVED (RC6's `mem_stageIdeal_iff`). -/
theorem constantCoeff_mem_twoAdicStage {i : ℕ} {f : Lambda} (hf : f ∈ stageIdeal i) :
    PowerSeries.constantCoeff f ∈ twoAdicStage i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [twoAdicStage]
  · rw [mem_twoAdicStage_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact mem_stageIdeal_iff.mp hf 0 hi

/-! ## The inner limit commutes with continuous maps -/

/-- **The inner limit commutes with a continuous map** between compact Hausdorff spaces: the
ultralimit of `g ∘ x` is `g` of the ultralimit of `x`. PROVED. -/
theorem ulim_map {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (U : Ultrafilter ℕ) {g : X → Y} (hg : Continuous g)
    (x : ℕ → X) : ulim U (fun i => g (x i)) = g (ulim U x) :=
  ulim_eq_of_tendsto ((hg.tendsto _).comp (tendsto_ulim U x))

open scoped PowerSeries.WithPiTopology in
/-- **The inner limit over `Λ` followed by `t ↦ 0` is the inner limit of the fibres at `t = 0`**
(tex 4444–4448 with tex 3912–3916): for lifts `x i ∈ Λ` of stage data, the ultralimit of the
constant coefficients is the constant coefficient of the ultralimit. PROVED (`ulim_map`, the
continuity of `constantCoeff` for the coefficientwise topology). -/
theorem ulim_constantCoeff (U : Ultrafilter ℕ) (x : ℕ → Lambda) :
    ulim U (fun i => PowerSeries.constantCoeff (x i)) = PowerSeries.constantCoeff (ulim U x) :=
  ulim_map U (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ_[2]) x

/-- The inclusion `ℤ₂ → ℚ₂` is continuous. PROVED. -/
theorem continuous_coe_padicInt : Continuous (fun x : ℤ_[2] => (x : ℚ_[2])) :=
  continuous_subtype_val

/-- The stage values converge to their ultralimit in `ℚ₂` along the ultrafilter. PROVED. -/
theorem tendsto_coe_ulim (U : Ultrafilter ℕ) (x : ℕ → ℤ_[2]) :
    Tendsto (fun i => (x i : ℚ_[2])) (U : Filter ℕ) (𝓝 ((ulim U x : ℤ_[2]) : ℚ_[2])) :=
  (continuous_coe_padicInt.tendsto _).comp (tendsto_ulim U x)

/-! ## A limit along the ultrafilter is attained along a sequence of stages -/

/-- **A limit along a nonprincipal ultrafilter on the stages is a limit along a strictly
increasing sequence of stages**, in a first countable space. Used to pass from the inner limit
(along the fixed ultrafilter, tex 4444) to lane RC25's form of the limit (along `atTop`), by
discarding stages (the stages are indexed by the precision, and the moving prime varies with the
precision, tex 2739–2740). PROVED (`Filter.extraction_forall_of_frequently`). -/
theorem exists_strictMono_tendsto_of_ultrafilter {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    {x : ℕ → X} {y : X} (h : Tendsto x (U : Filter ℕ) (𝓝 y)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => x (φ k)) atTop (𝓝 y) := by
  obtain ⟨B, hB⟩ := (𝓝 y).exists_antitone_basis
  have hUa : (U : Filter ℕ) ≤ atTop := by rwa [← Nat.cofinite_eq_atTop]
  have hfreq : ∀ n, ∃ᶠ k in atTop, x k ∈ B n := fun n =>
    (h.eventually (hB.mem n)).frequently.filter_mono hUa
  obtain ⟨φ, hφ, hφB⟩ := extraction_forall_of_frequently hfreq
  exact ⟨φ, hφ, hB.tendsto hφB⟩

end ZInQ.Manuscript.RC.BaseZeroLimit
