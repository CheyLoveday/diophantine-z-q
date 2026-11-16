import ZInQKernel.Contrib.OneProof.HeightDictionary

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set MonObj
open MonoidalCategory CartesianMonoidalCategory
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightFix

/-! ## §1. Two finite measures with the same local density are equal -/

section Density

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- **Uniqueness of a measure with given local densities.** On a compact space, let `v p E ≥ 0`
be a "chart volume" of `E` near `p` and `c > 0`. Two finite measures `nu₁, nu₂` that both satisfy
`|nuᵢ(E) − c v_p(E)| ≤ ε v_p(E)` for all measurable `E` in a neighbourhood of each `p` (depending on
`ε`) are equal. -/
theorem eq_of_density (nu₁ nu₂ : Measure X) [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    (v : X → Set X → ℝ) (hv : ∀ p E, 0 ≤ v p E) (c : ℝ) (hc : 0 < c)
    (h₁ : ∀ p, ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |nu₁.real E - c * v p E| ≤ ε * v p E)
    (h₂ : ∀ p, ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |nu₂.real E - c * v p E| ≤ ε * v p E) : nu₁ = nu₂ := by
  -- the bound `|nu₁ E − nu₂ E| ≤ 2ε/(c−ε) nu₁ E`
  have key : ∀ ε : ℝ, 0 < ε → ε < c → ∀ E, MeasurableSet E →
      |nu₁.real E - nu₂.real E| ≤ 2 * ε / (c - ε) * nu₁.real E := by
    intro ε hε hεc
    have hW : ∀ p, ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
        |nu₁.real E - c * v p E| ≤ ε * v p E ∧ |nu₂.real E - c * v p E| ≤ ε * v p E := fun p => by
      obtain ⟨W1, h1, hW1⟩ := h₁ p ε hε
      obtain ⟨W2, h2, hW2⟩ := h₂ p ε hε
      exact ⟨W1 ∩ W2, Filter.inter_mem h1 h2, fun E hE hm =>
        ⟨hW1 E (hE.trans inter_subset_left) hm, hW2 E (hE.trans inter_subset_right) hm⟩⟩
    choose W hWn hWb using hW
    have hce : 0 < c - ε := by linarith
    have loc : ∀ p F, F ⊆ W p → MeasurableSet F →
        |nu₁.real F - nu₂.real F| ≤ 2 * ε / (c - ε) * nu₁.real F := by
      intro p F hF hFm
      obtain ⟨b1, b2⟩ := hWb p F hF hFm
      have hv0 := hv p F
      have h1' : (c - ε) * v p F ≤ nu₁.real F := by
        have := (abs_le.mp b1).1; nlinarith
      have hvle : v p F ≤ nu₁.real F / (c - ε) := by
        rw [le_div_iff₀ hce]; linarith
      have htri : |nu₁.real F - nu₂.real F| ≤ 2 * ε * v p F := by
        have e1 := abs_le.mp b1
        have e2 := abs_le.mp b2
        rw [abs_le]; constructor <;> linarith
      calc |nu₁.real F - nu₂.real F| ≤ 2 * ε * v p F := htri
        _ ≤ 2 * ε * (nu₁.real F / (c - ε)) := by gcongr
        _ = 2 * ε / (c - ε) * nu₁.real F := by ring
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun p => interior (W p))
      (fun p => isOpen_interior)
      (fun p _ => mem_iUnion.mpr ⟨p, mem_interior_iff_mem_nhds.mpr (hWn p)⟩)
    have ind : ∀ s : Finset X, ∀ F, MeasurableSet F → F ⊆ ⋃ p ∈ s, interior (W p) →
        |nu₁.real F - nu₂.real F| ≤ 2 * ε / (c - ε) * nu₁.real F := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro F _ hF
        have : F = ∅ := by simpa using hF
        subst this
        simp
      | insert p s hp ih =>
        intro F hFm hF
        have hFo : MeasurableSet (interior (W p)) := isOpen_interior.measurableSet
        have b1 := loc p (F ∩ interior (W p)) (inter_subset_right.trans interior_subset)
          (hFm.inter hFo)
        have b2 := ih (F \ interior (W p)) (hFm.diff hFo) (by
          intro x hx
          have h := hF hx.1
          simp only [Finset.set_biUnion_insert, mem_union] at h
          rcases h with h | h
          · exact absurd h hx.2
          · exact h)
        have hsplit : F = (F ∩ interior (W p)) ∪ (F \ interior (W p)) :=
          (inter_union_sdiff F _).symm
        have hd : Disjoint (F ∩ interior (W p)) (F \ interior (W p)) :=
          disjoint_sdiff_inter.symm
        have e1 : nu₁.real F = nu₁.real (F ∩ interior (W p)) + nu₁.real (F \ interior (W p)) := by
          conv_lhs => rw [hsplit]
          exact measureReal_union hd (hFm.diff hFo) (measure_ne_top _ _) (measure_ne_top _ _)
        have e2 : nu₂.real F = nu₂.real (F ∩ interior (W p)) + nu₂.real (F \ interior (W p)) := by
          conv_lhs => rw [hsplit]
          exact measureReal_union hd (hFm.diff hFo) (measure_ne_top _ _) (measure_ne_top _ _)
        rw [e1, e2]
        calc |nu₁.real (F ∩ interior (W p)) + nu₁.real (F \ interior (W p)) -
              (nu₂.real (F ∩ interior (W p)) + nu₂.real (F \ interior (W p)))|
            ≤ |nu₁.real (F ∩ interior (W p)) - nu₂.real (F ∩ interior (W p))| +
              |nu₁.real (F \ interior (W p)) - nu₂.real (F \ interior (W p))| := by
              rw [show nu₁.real (F ∩ interior (W p)) + nu₁.real (F \ interior (W p)) -
                (nu₂.real (F ∩ interior (W p)) + nu₂.real (F \ interior (W p))) =
                (nu₁.real (F ∩ interior (W p)) - nu₂.real (F ∩ interior (W p))) +
                (nu₁.real (F \ interior (W p)) - nu₂.real (F \ interior (W p))) by ring]
              exact abs_add_le _ _
          _ ≤ 2 * ε / (c - ε) * nu₁.real (F ∩ interior (W p)) +
              2 * ε / (c - ε) * nu₁.real (F \ interior (W p)) := add_le_add b1 b2
          _ = _ := by ring
    intro E hE
    exact ind t E hE (fun x _ => ht (mem_univ x))
  ext E hE
  have hreal : nu₁.real E = nu₂.real E := by
    refine TorusVolume.eq_of_abs_le (nu₁.real E) fun δ hδ hδ1 => ?_
    have hε : 0 < δ * c / 4 := by positivity
    have hεc : δ * c / 4 < c := by nlinarith
    have hk := key _ hε hεc E hE
    have hM : 0 ≤ nu₁.real E := measureReal_nonneg
    have hcoef : 2 * (δ * c / 4) / (c - δ * c / 4) ≤ δ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    calc |nu₁.real E - nu₂.real E| ≤ 2 * (δ * c / 4) / (c - δ * c / 4) * nu₁.real E := hk
      _ ≤ δ * nu₁.real E := by gcongr
  exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end Density

/-! ## §2. Densities in translated charts on a group -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {g : ℕ}

/-- `nu` has density `c` at `p` relative to Lebesgue measure, in the chart `q ↦ F(p⁻¹ q)` (the chart
`F` at `1` translated to `p`). -/
def DensAt (nu : Measure G) (F : G → (Fin g → ℂ)) (c : ℝ) (p : G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
    |nu.real E - c * (volume ((fun q => F (p⁻¹ * q)) '' E)).toReal| ≤
      ε * (volume ((fun q => F (p⁻¹ * q)) '' E)).toReal

theorem densAt_one_iff (nu : Measure G) (F : G → (Fin g → ℂ)) (c : ℝ) :
    DensAt nu F c 1 ↔ ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : G), ∀ E ⊆ W, MeasurableSet E →
      |(nu E).toReal - c * (volume (F '' E)).toReal| ≤ ε * (volume (F '' E)).toReal := by
  have h : (fun q => F ((1 : G)⁻¹ * q)) = F := by funext q; simp
  simp only [DensAt, h]
  rfl

variable [IsTopologicalGroup G] [BorelSpace G]

/-- Translating a measure translates its densities. -/
theorem densAt_map (nu : Measure G) (F : G → (Fin g → ℂ)) (c : ℝ) (a p : G)
    (h : DensAt nu F c (a⁻¹ * p)) : DensAt (nu.map (a * ·)) F c p := by
  intro ε hε
  obtain ⟨W, hW, hb⟩ := h ε hε
  refine ⟨(fun q => a⁻¹ * q) ⁻¹' W, ?_, fun E hE hEm => ?_⟩
  · exact (continuous_const_mul a⁻¹).continuousAt.preimage_mem_nhds hW
  · have hmeas : Measurable (fun q : G => a * q) := measurable_const_mul a
    have hE' : (fun q => a * q) ⁻¹' E ⊆ W := fun x hx => by
      have := hE hx
      simpa using this
    have himg : (fun q => F ((a⁻¹ * p)⁻¹ * q)) '' ((fun q => a * q) ⁻¹' E) =
        (fun q => F (p⁻¹ * q)) '' E := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨a * x, hx, by simp [_root_.mul_assoc]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨a⁻¹ * x, by simpa using hx, by simp [_root_.mul_assoc]⟩
    have := hb _ hE' (hmeas hEm)
    rw [himg] at this
    rwa [Measure.real, Measure.map_apply hmeas hEm]

/-- A left-invariant measure with density `c` at `1` has density `c` at every point. -/
theorem densAt_of_invariant (nu : Measure G) [nu.IsMulLeftInvariant] (F : G → (Fin g → ℂ)) (c : ℝ)
    (h1 : DensAt nu F c 1) (p : G) : DensAt nu F c p := by
  have := densAt_map nu F c p p (by rwa [inv_mul_cancel])
  rwa [map_mul_left_eq_self] at this

/-- **Uniqueness**: two finite measures with density `c > 0` at every point coincide. -/
theorem eq_of_densAt [CompactSpace G] (nu₁ nu₂ : Measure G) [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    (F : G → (Fin g → ℂ)) (c : ℝ) (hc : 0 < c) (h₁ : ∀ p, DensAt nu₁ F c p)
    (h₂ : ∀ p, DensAt nu₂ F c p) : nu₁ = nu₂ :=
  eq_of_density nu₁ nu₂ (fun p E => (volume ((fun q => F (p⁻¹ * q)) '' E)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) c hc h₁ h₂

/-- **Invariance**: a finite measure with density `c > 0` at every point (in the translated charts)
is left-invariant. -/
theorem isMulLeftInvariant_of_densAt [CompactSpace G] (nu : Measure G) [IsFiniteMeasure nu]
    (F : G → (Fin g → ℂ)) (c : ℝ) (hc : 0 < c) (h : ∀ p, DensAt nu F c p) :
    nu.IsMulLeftInvariant :=
  ⟨fun a => eq_of_densAt (nu.map (a * ·)) nu F c hc (fun p => densAt_map nu F c a p (h _)) h⟩

end Generic

end ZInQ.HeightFix
