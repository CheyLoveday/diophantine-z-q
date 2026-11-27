import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.RCTarget

/-!
# App G endpoints: the hypotheses of the composite are jointly satisfiable

A toy model (not the manuscript's data) in which every hypothesis of `OddMinimumToFinalFamily`
holds — (F.3) with the companion, (3.4), (3.5), (O.8), the prepared filter, the fixed witness,
advancing stages along a nonprincipal ultrafilter, and `AddressInput` — and whose families have
nonzero addresses in every dimension `b ≥ 1`. So the statements of `OddMinimum.lean` and
`FinalFamily.lean` are not vacuous: their hypotheses can hold together and their conclusions
then speak about actual nonzero addresses. A second toy model satisfies every hypothesis of the
field target `FinalFamilyField` together with `¬ OddEmptyUnit` (Branch 2 occurs: the attained
minimum is `0` while `v₂ a(1) = 1`), so that target is not vacuous either. (PROVED.)
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

/-! ### Branch 2 occurs: a model of `FinalFamilyField` with `¬ OddEmptyUnit` -/

theorem omega_three : omega 3 = 1 := by
  simp [omega, ArithmeticFunction.cardDistinctFactors_apply_prime Nat.prime_three]

/-- In the second toy model (`v ≡ 1`, admissible `D ∈ {1, 3}`) the depths are `1` (at `D = 1`)
and `0` (at `D = 3`), so the attained minimum is `0` while `v₂ a(1) = 1`. -/
theorem isLeast_toy2 :
    IsLeast (DepthSet (hyperfilter ℕ) (fun θ => θ + 3) (fun _ _ => (1 : WithTop ℤ))
      (fun _ D => D = 1 ∨ D = 3)) 0 := by
  refine ⟨⟨1, fun _ => 3, Eventually.of_forall fun θ => ⟨Or.inr rfl, by rw [omega_three], ?_,
    by rw [omega_three]; rfl⟩⟩, fun r hr => ?_⟩
  · show ((1 : ℤ) : WithTop ℤ) < ((θ + 3 : ℕ) : WithTop ℤ)
    rw [← WithTop.coe_natCast]
    exact WithTop.coe_lt_coe.mpr (by omega)
  · obtain ⟨W, Ds, hev⟩ := hr
    obtain ⟨θ, h1, -, -, h4⟩ := hev.exists
    have h4' : (1 : ℤ) = (omega (Ds θ) : ℤ) + r := WithTop.coe_injective h4
    rcases h1 with h | h <;> rw [h] at h4'
    · rw [omega_one] at h4'; omega
    · rw [omega_three] at h4'; omega

/-- **Non-vacuity of the field target, in Branch 2** (PROVED): a model where every hypothesis of
`FinalFamilyField` holds and `¬ OddEmptyUnit` holds (`v₂ a(1) = 1 ≠ 0 = δ_o`), so the conclusion
(3.9) is reached, about families whose nonzero addresses are `h_x = 3`. -/
theorem finalFamilyField_nonvacuous :
    ¬ (∀ᶠ θ in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        (fun (_ : ℕ) (_ : ℤ) => (1 : WithTop ℤ)) θ 1 = ((0 : ℤ) : WithTop ℤ)) ∧
    ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∃ F : ℕ, F = b ∧
      (True ∧ ∀ x : Fin F → ZMod 2, x ≠ 0 →
        ((3 : ℤ) = 1 ∨ (3 : ℤ) = 3) ∧ True ∧ (1 : ℚ) ≠ 0 ∧
        (0 : ℤ) ≤ (omega 3 : ℤ) + Co ∧
        padicValRat 2 (1 : ℚ) ≤ 2 * (omega 3 : ℤ) + Ce) := by
  have hne : ¬ (∀ᶠ θ in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
      (fun (_ : ℕ) (_ : ℤ) => (1 : WithTop ℤ)) θ 1 = ((0 : ℤ) : WithTop ℤ)) := by
    intro h
    obtain ⟨θ, hθ⟩ := h.exists
    exact absurd (WithTop.coe_injective hθ : (1 : ℤ) = 0) one_ne_zero
  refine ⟨hne, finalFamilyField_proof (fun D => D = 1 ∨ D = 3) (fun _ => True) (fun _ => 1)
    (fun _ => 0) (fun _ _ => 2) 1 (hyperfilter ℕ) (fun θ => θ + 3) (fun _ _ => 1)
    (fun _ D => D = 1 ∨ D = 3) 0 1 (fun _ k' => k' = 1) (fun _ => 0) 0 0 0 4 0
    ℕ id (fun _ _ => 3) (fun _ => True) ?_ tendsto_hyperfilter_add ?_ ?_ ?_ ?_ isLeast_toy2 ?_ hne⟩
  · intro θ Dd _ _
    exact ⟨trivial, by
      show ((0 : ℤ) : WithTop ℤ) ≤ (1 : WithTop ℤ) + ((0 : ℤ) : WithTop ℤ)
      exact_mod_cast (by norm_num : (0 : ℤ) ≤ 1 + 0)⟩
  · intro h _ _
    exact ⟨1, rfl, by simp [omega_one], one_ne_zero, by
      simp only [padicValRat.one, omega_one]; positivity⟩
  · intro h k' _ _ _
    exact ⟨0, by simp, by simp⟩
  · intro h k' hh _ _ _
    rcases hh with hh | hh <;> subst hh <;> simp [omega_one, omega_three]
  · intro _ _ hD
    exact hD
  · intro _
    refine ⟨0, 1, fun b _ => ⟨1, 0, Fin.elim0, fun i => i.elim0, ?_⟩⟩
    intro T _ _ θ _ _ _ _
    refine ⟨b, rfl, trivial, fun x _ => ⟨by rw [omega_three], Or.inr rfl, Or.inr rfl, ?_,
      one_ne_zero, by simp [omega_three]⟩⟩
    rw [omega_three]
    rfl

end ZInQ.Contrib.CloudB3RC53.AppGEndpoints
