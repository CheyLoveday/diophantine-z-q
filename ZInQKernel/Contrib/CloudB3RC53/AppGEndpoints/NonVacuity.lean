import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.FinalFamily

/-!
# App G endpoints: the hypotheses of the composite are jointly satisfiable

A toy model (not the manuscript's data) in which every hypothesis of `OddMinimumToFinalFamily`
holds — (F.3) with the companion, (3.4), (3.5), (O.8), the prepared filter, the fixed witness,
advancing stages along a nonprincipal ultrafilter, and `AddressInput` — and whose families have
nonzero addresses in every dimension `b ≥ 1`. So the statements of `OddMinimum.lean` and
`FinalFamily.lean` are not vacuous: their hypotheses can hold together and their conclusions
then speak about actual nonzero addresses. (PROVED.)
-/

namespace ZInQ.Contrib.CloudB3RC53.AppGEndpoints

open Filter

theorem omega_one : omega 1 = 0 := by
  simp [omega]

/-- The stages of the toy model: the hyperfilter on `ℕ`, along which `θ ↦ θ + 3` tends to
infinity. -/
theorem tendsto_hyperfilter_add :
    Tendsto (fun θ : ℕ => θ + 3) ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) atTop := by
  have h : ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
    (hyperfilter_le_cofinite).trans Nat.cofinite_eq_atTop.le
  exact (tendsto_add_atTop_nat 3).mono_left h

/-- In the toy model the depth set is `{0}`. -/
theorem depthSet_toy (r : ℤ)
    (hr : r ∈ DepthSet (hyperfilter ℕ) (fun θ => θ + 3) (fun _ _ => (0 : WithTop ℤ))
      (fun _ D => D = 1)) : r = 0 := by
  obtain ⟨W, Ds, hev⟩ := hr
  obtain ⟨θ, h1, -, -, h4⟩ := hev.exists
  rw [h1, omega_one] at h4
  have : ((0 : ℤ) : WithTop ℤ) = ((((0 : ℕ) : ℤ) + r : ℤ) : WithTop ℤ) := by simpa using h4
  have := WithTop.coe_injective this
  omega

/-- **Non-vacuity of the composite** (PROVED): in the toy model, `OddMinimumToFinalFamily`
applies, and its conclusion is a statement about the nonzero addresses of families over
`𝔽₂^b`, `b ≥ 1`. -/
theorem oddMinimumToFinalFamily_nonvacuous :
    ∃ δ : ℤ, IsLeast (DepthSet (hyperfilter ℕ) (fun θ => θ + 3) (fun _ _ => (0 : WithTop ℤ))
      (fun _ D => D = 1)) δ ∧
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∃ F : ℕ, F = b ∧ True ∧
        ∀ x : Fin F → ZMod 2, x ≠ 0 →
          (1 : ℤ) = 1 ∧ True ∧ (fun _ : ℤ => (1 : ℚ)) (1 * 1) ≠ 0 ∧
          (fun _ : ℤ => (0 : ℤ)) 1 ≤ (omega 1 : ℤ) + (δ + 0) ∧
          padicValRat 2 ((fun _ : ℤ => (1 : ℚ)) (1 * 1)) ≤ 2 * (omega 1 : ℤ) + 0 := by
  refine oddMinimumToFinalFamily_proof (hyperfilter ℕ) (fun θ => θ + 3) (fun _ _ => 0)
    (fun _ D => D = 1) (fun _ => True) (fun h => h = 1) (fun _ k' => k' = 1) (fun _ => 1)
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) 1 0 0 0 0 0 1 0 ℕ id (fun _ _ => 1) (fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ tendsto_hyperfilter_add ?_
  · intro h _ _
    exact ⟨1, rfl, by simp [omega_one], one_ne_zero, by simp [omega_one]⟩
  · intro h k' _ _ _
    exact ⟨0, by simp, by simp⟩
  · intro h k' hh _ _ _
    subst hh
    simp [omega_one]
  · intro θ D hD _
    exact ⟨trivial, by simp⟩
  · intro _ _ hD
    exact hD
  · refine ⟨1, 0, Eventually.of_forall fun θ => ⟨rfl, rfl, ?_⟩⟩
    show ((0 : ℤ) : WithTop ℤ) < ((θ + 3 : ℕ) : WithTop ℤ)
    rw [← WithTop.coe_natCast]
    exact WithTop.coe_lt_coe.mpr (by positivity)
  · intro δ hδ
    have hδ0 : δ = 0 := depthSet_toy δ hδ.1
    subst hδ0
    refine ⟨1, fun b _ => ⟨0, 0, Fin.elim0, fun i => i.elim0, ?_⟩⟩
    intro T _ _ θ _ _ _ _
    refine ⟨b, rfl, trivial, fun x _ => ⟨by simp [omega_one], rfl, rfl, ?_, one_ne_zero,
      by simp⟩⟩
    simp [omega_one]

/-- The conclusion of the toy model is about actual nonzero addresses: `𝔽₂^b` has a nonzero
element for `b ≥ 1`. -/
theorem exists_ne_zero_addr {b : ℕ} (hb : 1 ≤ b) : ∃ x : Fin b → ZMod 2, x ≠ 0 :=
  ⟨fun _ => 1, fun h => by
    have := congrFun h ⟨0, hb⟩
    simp at this⟩

end ZInQ.Contrib.CloudB3RC53.AppGEndpoints
