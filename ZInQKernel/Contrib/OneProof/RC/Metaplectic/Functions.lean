import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Integral
import Mathlib.Topology.LocallyConstant.Basic

/-! Schwartz–Bruhat functions at a finite place (tex 8646–8657).
The compactness argument for spanning by rectangular cosets is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic

open Intertwine Intertwine2 WeilIndex Set Filter
open scoped BigOperators Topology

/-- The usual space of locally constant, compactly supported functions. -/
def schwartzBruhat (p : Place) : Submodule ℂ (LocalVectors p → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left⟩

abbrev SchwartzBruhat (p : Place) := schwartzBruhat p

theorem isLocallyConstant_phase (p : Place) : IsLocallyConstant (localPhase p) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn := ((padicIntegers_open p).preimage
    (continuous_id.sub (continuous_const : Continuous fun _ : ℚ_[p.val] => x))).mem_nhds
    (x := x) (by change x - x ∈ PadicInt.subring p.val; simp)
  filter_upwards [hn] with y hy
  exact localPhase_congr_integer p y x hy

theorem continuous_quad (p : Place) (a : Fin 3 → ℕ) :
    Continuous (quad a : LocalVectors p → ℚ_[p.val]) := by
  unfold quad
  fun_prop

theorem continuous_polar (p : Place) (a : Fin 3 → ℕ) :
    Continuous (fun z : LocalVectors p × LocalVectors p => polar a z.1 z.2) := by
  unfold polar
  fun_prop

/-- The preimage of the integer lattice under multiplication coordinate by coordinate. -/
def rectangle (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) : AddSubgroup (LocalVectors p) :=
  AddSubgroup.pi univ fun i => scaledLattice p (s i)

theorem mem_rectangle (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) (x : LocalVectors p) :
    x ∈ rectangle p s ↔ ∀ i, (s i : ℚ_[p.val]) * x i ∈ PadicInt.subring p.val := by
  simp [rectangle, AddSubgroup.mem_pi, scaledLattice]

theorem rectangle_open (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) :
    IsOpen (rectangle p s : Set (LocalVectors p)) := by
  change IsOpen (univ.pi (fun i => (scaledLattice p (s i) : Set ℚ_[p.val])))
  exact isOpen_set_pi finite_univ fun i _ =>
    (padicIntegers_open p).preimage (continuous_const.mul continuous_id)

theorem rectangle_compact (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) :
    IsCompact (rectangle p s : Set (LocalVectors p)) := by
  change IsCompact (univ.pi (fun i => (scaledLattice p (s i) : Set ℚ_[p.val])))
  exact isCompact_univ_pi fun i => scaledLattice_compact p _ (s i).ne_zero

def rectangleCoset (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) (c : LocalVectors p) :
    Set (LocalVectors p) :=
  {x | x - c ∈ rectangle p s}

theorem rectangleCoset_open (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) (c : LocalVectors p) :
    IsOpen (rectangleCoset p s c) :=
  (rectangle_open p s).preimage (continuous_id.sub continuous_const)

theorem rectangleCoset_compact (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) (c : LocalVectors p) :
    IsCompact (rectangleCoset p s c) := by
  have he : rectangleCoset p s c = (fun x => x + c) '' (rectangle p s : Set _) := by
    ext x
    constructor
    · intro h
      exact ⟨x - c, h, sub_add_cancel x c⟩
    · rintro ⟨y, hy, rfl⟩
      change y + c - c ∈ rectangle p s
      rwa [add_sub_cancel_right]
  rw [he]
  exact (rectangle_compact p s).image (continuous_id.add continuous_const)

def rectangleIndicator (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) (c : LocalVectors p) :
    LocalVectors p → ℂ :=
  (rectangleCoset p s c).indicator (fun _ => 1)

theorem rectangleIndicator_mem (p : Place) (s : Fin 3 → ℚ_[p.val]ˣ) (c : LocalVectors p) :
    rectangleIndicator p s c ∈ schwartzBruhat p := by
  classical
  have hk := rectangleCoset_compact p s c
  have ho := rectangleCoset_open p s c
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ rectangleCoset p s c
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp [rectangleIndicator, hx, hy]
    · filter_upwards [hk.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [rectangleIndicator, hx, show y ∉ rectangleCoset p s c from hy]
  · apply hk.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hk.isClosed
    exact support_indicator_subset

theorem rectangleIndicator_one (p : Place) (c : LocalVectors p) :
    rectangleIndicator p 1 c = localCoset p c := by
  have he : rectangleCoset p 1 c = {x | x - c ∈ localLattice p} := by
    ext x
    change x - c ∈ rectangle p 1 ↔ x - c ∈ localLattice p
    simp [mem_rectangle, localLattice]
  change (rectangleCoset p 1 c).indicator (fun _ => 1) =
    ({x | x - c ∈ localLattice p} : Set (LocalVectors p)).indicator (fun _ => 1)
  rw [he]

private theorem rect_basis (p : Place) {U : Set (LocalVectors p)} (hU : U ∈ 𝓝 0) :
    ∃ s : Fin 3 → ℚ_[p.val]ˣ, (rectangle p s : Set _) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := p.val))
  let u : ℚ_[p.val]ˣ := Units.mk0 (p.val : ℚ_[p.val]) (Nat.cast_ne_zero.mpr p.property.ne_zero)
  refine ⟨fun _ => (u ^ n)⁻¹, fun x hx => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (pow_nonneg (norm_nonneg _) _)).2 fun i => ?_) hn
  have hi := (mem_rectangle p _ x).1 hx i
  change ‖((↑((u ^ n)⁻¹) : ℚ_[p.val]) * x i)‖ ≤ 1 at hi
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_mul, norm_inv,
    inv_mul_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero _ u.ne_zero)), mul_one, norm_pow] at hi
  exact hi

private theorem uniform_translation (p : Place) {f : LocalVectors p → ℂ}
    (hf : f ∈ schwartzBruhat p) :
    ∃ s : Fin 3 → ℚ_[p.val]ˣ, ∀ t ∈ rectangle p s, ∀ x, f (x + t) = f x := by
  have he : ∀ᶠ t : LocalVectors p in 𝓝 0, ∀ x ∈ tsupport f, f (x + t) = f x := by
    apply (show IsCompact (tsupport f) from hf.2).eventually_forall_of_forall_eventually
    intro x _
    have h₁ : Tendsto (fun z : LocalVectors p × LocalVectors p => z.2 + z.1)
        (𝓝 (0, x)) (𝓝 x) := by
      simpa only [add_zero] using
        (show Continuous (fun z : LocalVectors p × LocalVectors p => z.2 + z.1) by fun_prop).tendsto (0, x)
    filter_upwards [h₁.eventually (hf.1.eventually_eq x),
      continuous_snd.continuousAt.eventually (hf.1.eventually_eq x)] with z hz hw
    exact hz.trans hw.symm
  obtain ⟨s, hs⟩ := rect_basis p he
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hxt : x + t ∈ tsupport f
  · have h := hs ((rectangle p s).neg_mem ht) (x + t) hxt
    simpa using h.symm
  rw [image_eq_zero_of_notMem_tsupport hxt, image_eq_zero_of_notMem_tsupport hx]

/-- Every Schwartz–Bruhat function is a finite linear combination of rectangular coset indicators. -/
theorem mem_span_rectangles (p : Place) {f : LocalVectors p → ℂ} (hf : f ∈ schwartzBruhat p) :
    f ∈ Submodule.span ℂ {g | ∃ s c, g = rectangleIndicator p s c} := by
  classical
  obtain ⟨s, hs⟩ := uniform_translation p hf
  let L := rectangle p s
  let q := QuotientAddGroup.mk' L
  have hq (x c : LocalVectors p) : q x = q c ↔ x ∈ rectangleCoset p s c :=
    QuotientAddGroup.eq_iff_sub_mem
  have hloc : IsLocallyConstant q := by
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro c
    have he : q ⁻¹' {q c} = rectangleCoset p s c := by
      ext x
      exact hq x c
    rw [he]
    exact rectangleCoset_open p s c
  let K := tsupport f
  let : CompactSpace K := isCompact_iff_compactSpace.mp hf.2
  have hfin : (q '' K).Finite := by
    have he : q '' K = range (fun x : K => q x) := by
      ext r
      exact ⟨fun ⟨x, hx, hr⟩ => ⟨⟨x, hx⟩, hr⟩, fun ⟨x, hr⟩ => ⟨x, x.2, hr⟩⟩
    rw [he]
    exact (hloc.comp_continuous continuous_subtype_val).range_finite
  let T := hfin.toFinset
  let rep : (LocalVectors p ⧸ L) → LocalVectors p :=
    fun r => (QuotientAddGroup.mk_surjective r).choose
  have hr (r : LocalVectors p ⧸ L) : q (rep r) = r :=
    (QuotientAddGroup.mk_surjective r).choose_spec
  have hsum : f = ∑ r ∈ T, f (rep r) • rectangleIndicator p s (rep r) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hv (r : LocalVectors p ⧸ L) :
        rectangleIndicator p s (rep r) x = if q x = r then 1 else 0 := by
      have hi := hq x (rep r)
      rw [hr] at hi
      by_cases h : q x = r
      · simp [rectangleIndicator, h, hi.mp h]
      · simp [rectangleIndicator, h, mt hi.mpr h]
    simp_rw [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with hx
    · have hm : x - rep (q x) ∈ L := (hq x _).mp (hr _).symm
      have h := hs _ hm (rep (q x))
      rw [add_comm, sub_add_cancel] at h
      exact h
    · exact image_eq_zero_of_notMem_tsupport fun h => hx (hfin.mem_toFinset.mpr ⟨x, h, rfl⟩)
  rw [hsum]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rep r, rfl⟩)

#print axioms isLocallyConstant_phase
#print axioms continuous_quad
#print axioms continuous_polar
#print axioms mem_rectangle
#print axioms rectangle_open
#print axioms rectangle_compact
#print axioms rectangleCoset_open
#print axioms rectangleCoset_compact
#print axioms rectangleIndicator_mem
#print axioms rectangleIndicator_one
#print axioms rect_basis
#print axioms uniform_translation
#print axioms mem_span_rectangles

end ZInQ.Manuscript.RC.Metaplectic
