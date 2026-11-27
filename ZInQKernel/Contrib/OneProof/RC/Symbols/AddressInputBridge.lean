import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.FinalFamily
import ZInQKernel.Contrib.OneProof.RC.Symbols.FinalFamily

/-!
# Lane RC2: bridge from the address construction to the App G `AddressInput`

`ZInQ.Contrib.CloudB3RC53.AppGEndpoints.AddressInput` is the hypothesis through which the proof of
Proposition `ex:app-final-family` (tex 10792–10861) consumes the address construction. This file
proves it from:

* the address construction of this lane, PROVED from the coefficient rules:
  `final_family_graphs` (zero-total packets, tex 10587–10623, and Lemma
  `ex:sec7-two-symbol-address` / Proposition `ex:app-simultaneous-address`, tex 2240–2288,
  10554–10790);
* the odd limit symbol with its common-stage property (Proposition `ex:app-odd-stabilization`,
  tex 10508–10552; provided by `odd_stabilization_witness` from stage tables obeying the rules);
* explicit arithmetic hypotheses, not part of tex 10508–10791:
  - the coefficient rules of the odd limit symbol and of the normalized even source of `E^k`
    (App F `ex:app-coefficient-rules`, tex 9447–9976);
  - minimum nonempty seeds of total type zero for both symbols (App G `ex:app-nonempty-seeds`,
    tex 10258–10506, and `ex:sec7-ksplit-seed`, tex 2628–2654);
  - prime realization of a typed graph at an actual stage as a member of the family type, with
    `ω(h_x)` the number of active vertices and the fixed local types (tex 10825–10828:
    "Realize its prescribed forward residue bits by distinct primes using CRT and Dirichlet;
    quadratic reciprocity supplies the reverse bits"; the finite CRT/Dirichlet step is PROVED in
    `Realization.lean`);
  - the odd reading at a valid stage: a unit of the stage table in the tested range is visible
    with `v₂ a_M(D) = δ_o + ω(D)` and `D` admissible (definition of the stage symbol, tex
    10236–10249, and the coefficient-one reading, tex 9670–9704);
  - the even reading: a unit of the normalized even source gives `L_*(Dk) ≠ 0` and
    `v₂ L_*(Dk) ≤ 2ω(D) + C_{e,final}` ((F.1) for the transported source, tex 10079–10094,
    10274–10318, 10854–10855).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset Filter
open ZInQ.Contrib.CloudB3RC53.AppGEndpoints (AddressInput omega)

/-- Reading a projection preserves compatibility. Kind: PROVED. -/
theorem Config.Compatible.mapType' {L L' : Type*} [AddCommGroup L] [AddCommGroup L']
    {ε : L →+ ZMod 2} {ε' : L' →+ ZMod 2} (π : L →+ L') (hε : ∀ x, ε' (π x) = ε x)
    {Γ : Config L} (hΓ : Γ.Compatible ε) : (Γ.mapType π).Compatible ε' := by
  intro v hv w hw hvw
  simp only [Config.mapType, hε]
  exact hΓ v hv w hw hvw

/-- **`AddressInput` from the address construction** (bridge for Proposition
`ex:app-final-family`, tex 10792–10850, consuming tex 10508–10791). Kind: PROVED from the stated
hypotheses (see the module docstring for their tex lines and kinds). For every `b ≥ 1`: the
address program is one typed graph `Γ'` (`final_family_graphs`); its budget is
`W_b = |V(Γ')|`; the single selected truth-table set is the set of stages at which the stage
table agrees with the limit symbol on the `2^b - 1` active graphs (in the ultrafilter by the
common-stage property); at any stage there satisfying the stage conditions, a prime realization
of `Γ'` gives the family, and the two readings turn the units of both symbols at every nonzero
address into the visibility and `L_*` conditions. -/
theorem addressInput_of_address
    (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (prepared : ℤ → Prop) (Lstar : ℤ → ℚ) (k δ CeFinal : ℤ) (Ccoarse : ℚ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop)
    {L L₁ L₂ : Type*} [AddCommGroup L] [Fintype L] [DecidableEq L] [AddCommGroup L₁]
    [AddCommGroup L₂] (hL : ∀ x : L, x + x = 0) (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2)
    (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂) (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) (hε₁ : ∀ x, ε₁ (π₁ x) = ε x) (hε₂ : ∀ x, ε₂ (π₂ x) = ε x)
    (Aodd : ℕ → Config L₁ → ZMod 2) (AoddLim : Config L₁ → ZMod 2) (Aev : Config L₂ → ZMod 2)
    (hlimRules : CoefficientRules ε₁ AoddLim) (hevRules : CoefficientRules ε₂ Aev)
    (hlim : ∀ (n : ℕ) (Γs : Fin n → Config L₁), (∀ i, (Γs i).Compatible ε₁) →
      ∀ᶠ θ in (U : Filter ℕ), ∀ i, Aodd θ (Γs i) = AoddLim (Γs i))
    {Γ₁ : Config L₁} {Γ₂ : Config L₂} (hm₁ : IsMinSeed ε₁ AoddLim Γ₁)
    (hm₂ : IsMinSeed ε₂ Aev Γ₂) (ht₁ : Γ₁.total = 0) (ht₂ : Γ₂.total = 0)
    (Realizes : ℕ → Config L → ℤ → Prop)
    (hreal : ∀ (θ b : ℕ) (Γ : Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Fam, ∃ hdim : dim F = b, FamAdm F ∧ ∀ x : Fin b → ZMod 2, x ≠ 0 →
        Realizes θ (Γ.at act' x) (hfam F (x ∘ Fin.cast hdim)))
    (hrealω : ∀ (θ : ℕ) (Δ : Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      omega D = Δ.V.card ∧ prepared D)
    (hodd : ∀ (θ T W : ℕ) (Δ : Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ W → W + 1 ≤ T → (((max 0 (δ + W) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', adm θ D' → omega D' ≤ T → v θ D' < M θ →
        (((omega D' : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D') →
      max 0 (δ + W) + 2 ≤ (M θ : ℤ) → (T : ℤ) + δ < M θ →
      Aodd θ (Δ.mapType π₁) = 1 → adm θ D ∧ v θ D = (((omega D : ℤ) + δ : ℤ) : WithTop ℤ))
    (hev : ∀ (θ : ℕ) (Δ : Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Aev (Δ.mapType π₂) = 1 →
      Lstar (D * k) ≠ 0 ∧ padicValRat 2 (Lstar (D * k)) ≤ 2 * (omega D : ℤ) + CeFinal) :
    AddressInput U M v adm prepared Lstar k δ CeFinal Ccoarse Fam dim hfam FamAdm := by
  classical
  refine ⟨1, fun b hb => ?_⟩
  obtain ⟨Γ, act', -, hact, ⟨Γ', act'', hΓ', hext, hactΓ, hnew, hunit⟩, -⟩ :=
    final_family_graphs hL π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ hlimRules hevRules hm₁ hm₂ ht₁ ht₂ b hb
  have hact' : ∀ u ∈ Γ'.V, ∃ w, w ≠ 0 ∧ act'' u = some w := by
    intro u hu
    by_cases huΓ : u ∈ Γ.V
    · rw [hactΓ u huΓ]; exact hact u huΓ
    · exact (hnew u hu huΓ).2
  let eY := Fintype.equivFin {x : Fin b → ZMod 2 // x ≠ 0}
  let Γs : Fin (Fintype.card {x : Fin b → ZMod 2 // x ≠ 0}) → Config L₁ :=
    fun i => (Γ'.at act'' (eY.symm i).1).mapType π₁
  have hΓs : ∀ i, (Γs i).Compatible ε₁ := fun i =>
    (Config.at_compatible hΓ' act'' _).mapType' π₁ hε₁
  refine ⟨Γ'.V.card, 1, fun _ => {θ | ∀ i, Aodd θ (Γs i) = AoddLim (Γs i)},
    fun _ => hlim _ Γs hΓs, ?_⟩
  intro T hT1 hT2 θ hθ hF6 hM1 hM2
  have hθ' : ∀ i, Aodd θ (Γs i) = AoddLim (Γs i) := Set.mem_iInter.mp hθ 0
  obtain ⟨F, hdim, hFadm, hR⟩ := hreal θ b Γ' act'' hΓ' hact'
  refine ⟨F, hdim, hFadm, fun y hy => ?_⟩
  set x : Fin b → ZMod 2 := y ∘ Fin.cast hdim.symm with hxdef
  have hxy : x ∘ Fin.cast hdim = y := by
    funext i
    simp [hxdef]
  have hx : x ≠ 0 := by
    intro h0
    apply hy
    rw [← hxy, h0]
    rfl
  have hRx := hR x hx
  rw [hxy] at hRx
  have hcx : (Γ'.at act'' x).Compatible ε := Config.at_compatible hΓ' act'' x
  obtain ⟨hω, hprep⟩ := hrealω θ _ _ hcx hRx
  have hcard : (Γ'.at act'' x).V.card ≤ Γ'.V.card := Finset.card_filter_le _ _
  have hu1 := hunit x hx 0
  have hu2 := hunit x hx 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hu1 hu2
  have hi : Aodd θ ((Γ'.at act'' x).mapType π₁) = 1 := by
    have h := hθ' (eY ⟨x, hx⟩)
    simp only [Γs, Equiv.symm_apply_apply] at h
    rw [h, hu1]
  obtain ⟨hadm, hv⟩ := hodd θ T Γ'.V.card _ _ hcx hRx hcard hT1 hT2 hF6 hM1 hM2 hi
  obtain ⟨hL0, hLe⟩ := hev θ _ _ hcx hRx hu2
  exact ⟨by rw [hω]; exact hcard, hprep, hadm, hv, hL0, hLe⟩

end ZInQ.Manuscript.RC.Symbols
