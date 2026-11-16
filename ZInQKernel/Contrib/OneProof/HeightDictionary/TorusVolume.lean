import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.Group.Quotient

/-! # height-dict: the volume of a uniformized compact group (Mathlib only)

The archimedean step of the dictionary between the kernel's coordinate-form Faltings metric
`torusMetricSq Λ c = |c|² covol(Λ)` and the printed metric `(i/2)^g ∫_{A(ℂ)} α ∧ ᾱ`. -/

open MeasureTheory Measure Set Filter Topology Module Metric
open scoped NNReal ENNReal Pointwise

namespace ZInQ.HeightDict.TorusVolume

variable {g : ℕ}

/-- A small ball around `0` meets no other point of its `Λ`-orbit. -/
theorem exists_ball_sub_mem (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x ∈ ball (0 : Fin g → ℂ) r₀, ∀ y ∈ ball (0 : Fin g → ℂ) r₀,
      x - y ∈ Λ → x = y := by
  have h0 : IsOpen ({0} : Set Λ) := isOpen_discrete _
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp h0
  have h0t : (0 : Fin g → ℂ) ∈ t := by
    have : (0 : Λ) ∈ Subtype.val ⁻¹' t := by rw [hts]; rfl
    simpa using this
  obtain ⟨ρ, hρ, hρt⟩ := Metric.isOpen_iff.mp ht 0 h0t
  refine ⟨ρ / 2, by positivity, fun x hx y hy hxy => ?_⟩
  have hd : x - y ∈ ball (0 : Fin g → ℂ) ρ := by
    rw [mem_ball_zero_iff] at hx hy ⊢
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ < ρ / 2 + ρ / 2 := add_lt_add hx hy
      _ = ρ := by ring
  have : (⟨x - y, hxy⟩ : Λ) ∈ Subtype.val ⁻¹' t := hρt hd
  rw [hts] at this
  have h' : x - y = 0 := congrArg Subtype.val this
  exact sub_eq_zero.mp h'

/-- **A fundamental domain containing a ball.** -/
theorem exists_fundamentalDomain_ball (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ D : Set (Fin g → ℂ), MeasurableSet D ∧
      IsAddFundamentalDomain Λ D volume ∧ ball 0 r₀ ⊆ D ∧
      ∀ x ∈ D, ∀ y ∈ ball (0 : Fin g → ℂ) r₀, x - y ∈ Λ → x = y := by
  obtain ⟨r₀, hr₀, hsep⟩ := exists_ball_sub_mem Λ
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hb : Submodule.span ℤ (Set.range b) = Λ :=
    (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ Λ
  set D₀ := ZSpan.fundamentalDomain b
  have hD₀m : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet b
  have huniq : ∀ x : Fin g → ℂ, ∃! l : Λ, (l : Fin g → ℂ) + x ∈ D₀ := by
    intro x
    obtain ⟨v, hv, hvu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
    have hvΛ : (v : Fin g → ℂ) ∈ Λ := (SetLike.ext_iff.mp hb _).mp v.2
    refine ⟨⟨v, hvΛ⟩, hv, fun l hl => ?_⟩
    have hlS : (l : Fin g → ℂ) ∈ Submodule.span ℤ (Set.range b) := (SetLike.ext_iff.mp hb _).mpr l.2
    have := hvu ⟨l, hlS⟩ hl
    exact Subtype.ext (congrArg Subtype.val this : (l : Fin g → ℂ) = v)
  set T : Set (Fin g → ℂ) := {x | ∃ l ∈ Λ, x - l ∈ ball (0 : Fin g → ℂ) r₀}
  have hTo : IsOpen T := by
    have : T = ⋃ l : Λ, (fun x => x - (l : Fin g → ℂ)) ⁻¹' ball 0 r₀ := by
      ext x; simp [T]
    rw [this]
    exact isOpen_iUnion fun l => isOpen_ball.preimage (continuous_id.sub continuous_const)
  set D := ball (0 : Fin g → ℂ) r₀ ∪ (D₀ \ T)
  have hDm : MeasurableSet D := measurableSet_ball.union (hD₀m.diff hTo.measurableSet)
  have hBT : ∀ y ∈ ball (0 : Fin g → ℂ) r₀, ∀ l ∈ Λ, y + l ∈ T := fun y hy l hl =>
    ⟨l, hl, by simpa using hy⟩
  refine ⟨r₀, hr₀, D, hDm, ?_, subset_union_left, ?_⟩
  · refine IsAddFundamentalDomain.mk' hDm.nullMeasurableSet fun x => ?_
    simp only [Submodule.vadd_def, vadd_eq_add]
    by_cases hx : x ∈ T
    · obtain ⟨l₀, hl₀, hxl⟩ := hx
      refine ⟨⟨-l₀, Λ.neg_mem hl₀⟩, Or.inl (by simpa [neg_add_eq_sub] using hxl), ?_⟩
      rintro ⟨l', hl'⟩ (h | h)
      · have := hsep _ h _ hxl (by
          have : l' + x - (x - l₀) = l' + l₀ := by abel
          rw [this]; exact Λ.add_mem hl' hl₀)
        apply Subtype.ext
        show l' = -l₀
        have h2 : l' + x = x - l₀ := this
        linear_combination (exp := 1) h2
      · exfalso
        apply h.2
        have := hBT _ hxl (l' + l₀) (Λ.add_mem hl' hl₀)
        have e : x - l₀ + (l' + l₀) = l' + x := by abel
        rwa [e] at this
    · obtain ⟨l, hl, hlu⟩ := huniq x
      refine ⟨l, Or.inr ⟨hl, fun hT => hx ?_⟩, fun l' hl' => ?_⟩
      · obtain ⟨m, hm, hmx⟩ := hT
        exact ⟨m - l, Λ.sub_mem hm l.2, by
          have e : x - (m - (l : Fin g → ℂ)) = (l : Fin g → ℂ) + x - m := by abel
          rwa [e]⟩
      · rcases hl' with h | h
        · exfalso
          exact hx ⟨-l', Λ.neg_mem l'.2, by
            have e : x - -(l' : Fin g → ℂ) = (l' : Fin g → ℂ) + x := by abel
            rwa [e]⟩
        · exact hlu l' h.1
  · intro x hx y hy hxy
    rcases hx with h | h
    · exact hsep x h y hy hxy
    · exfalso
      apply h.2
      have := hBT y hy (x - y) hxy
      rwa [add_sub_cancel] at this

end ZInQ.HeightDict.TorusVolume
