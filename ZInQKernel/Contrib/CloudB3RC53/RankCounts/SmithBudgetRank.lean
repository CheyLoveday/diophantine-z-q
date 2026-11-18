import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudget

/-!
# RankCounts: the budget (5.7) for RC7's Smith data with unit disks allowed (Elliot's own count)

Manuscript `diophantine_zq.tex`, tex 5375–5387 and 5530–5541. Elliot counts the Smith disks of the
central complex by **total rank**, not by residue cohomology:

> Its only free cohomology generators here are one in degree one and one in degree two. If `m`
> counts all its Smith disks, including those with `e = 0`, then `rank_total C_old = 2 + 2m`.
> … `rank_total C_old ≤ 2d_K + 12`, `m ≤ d_K + 5`, `h₁ ≤ h_K + 2c_E + 2t_K`. (5.7)

and in the clearing (tex 5530–5531) `m_i = rank E_i`, `m = Σ m_i` counts all central Smith disks.
This file proves RC7's two budget hypotheses

    (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK)

for RC7's `SmithBlocks` exactly as it stands (central Smith entries only required nonzero; unit
disks `e = 0` allowed), following that count:

* the total rank of the central Smith complex is `Σ f_k + 2·B.mTot`, every disk counted, including
  unit disks (`sum_finrank_centralCx`) — Elliot's `rank_total C_old = 2 + 2m`;
* with Elliot's first (5.7) bound `rank_total ≤ 2d_K + 12` (input `hrank`; RC7's
  `fixed_field_budget` derives it from (5.7a) and the minimality of the model, tex 5355–5359) and
  the free ranks one of (5.7b), `B.mTot ≤ dK + 5`;
* the torsion of `H^*(D_c)` has length `B.hSmith` for any `B` (a unit disk contributes `e = 0`),
  so (5.7d) gives `B.hSmith ≤ hK + 2cE + 2tK`.

The degree range replaces `B.n ≤ 3`: the complex lives in degrees `0, …, 3`, so no disk has source
degree `≥ 3` (`hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0`; implied by `B.n ≤ 3`).

This supersedes the positive-valuation versions `FixedFieldBudgetSmith` / `RC7Budget57Inputs` of
`SmithBudget.lean` (which remain correct for minimal Smith data). RC7's `hmodel`
(`rankTotal ≤ Σ dim H^k(D_c ⊗ 𝔽₂)`) is the minimality of the model and is not used here.
Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open ZInQ.Manuscript.RC.Determinant (Lam SmithBlocks)
open SmithCx

section Amplitude
variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)

/-- Under the degree range (no disk with source degree `≥ 3`), the padded disk sizes vanish from
degree three on. -/
theorem dd_eq_zero_of_ge (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) {i : ℕ} (hi : 3 ≤ i) :
    dd B i = 0 := by
  by_cases h : i < B.n
  · rw [dd_of_lt B h]; exact hamp i hi h
  · exact dd_of_ge B h

theorem sum_dd_amp (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) :
    ∑ i ∈ Finset.range 3, dd B i = B.mTot := by
  unfold SmithBlocks.mTot
  have h1 : ∑ i ∈ Finset.range B.n, B.m i = ∑ i ∈ Finset.range (B.n + 3), dd B i := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : B.n ≤ B.n + 3))
      (fun i _ hin => dd_of_ge B (fun h => hin (Finset.mem_range.mpr h)))]
    exact Finset.sum_congr rfl fun i hi => (dd_of_lt B (Finset.mem_range.mp hi)).symm
  have h2 : ∑ i ∈ Finset.range 3, dd B i = ∑ i ∈ Finset.range (B.n + 3), dd B i :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      (fun i _ hi3 => dd_eq_zero_of_ge B hamp (by simpa using hi3))
  rw [h1, h2]

theorem sum_sum_val_σ_amp (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) :
    ∑ i ∈ Finset.range 3, ∑ j, ((σ B) i j).valuation = B.hSmith := by
  have hz : ∀ i, 3 ≤ i → ∑ j, ((σ B) i j).valuation = 0 := by
    intro i hi
    have : IsEmpty (Fin (dd B i)) := by rw [dd_eq_zero_of_ge B hamp hi]; infer_instance
    simp
  unfold SmithBlocks.hSmith
  have h1 : ∑ i ∈ Finset.range B.n, ∑ j, (B.s i j).valuation =
      ∑ i ∈ Finset.range (B.n + 3), ∑ j, ((σ B) i j).valuation := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : B.n ≤ B.n + 3))
      (fun i _ hin => sum_val_σ_ge B i (fun h => hin (Finset.mem_range.mpr h)))]
    exact Finset.sum_congr rfl fun i hi => (sum_val_σ B i (Finset.mem_range.mp hi)).symm
  have h2 : ∑ i ∈ Finset.range 3, ∑ j, ((σ B) i j).valuation =
      ∑ i ∈ Finset.range (B.n + 3), ∑ j, ((σ B) i j).valuation :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      (fun i _ hi3 => hz i (by simpa using hi3))
  rw [h1, h2]

/-- The degree-`k` module `D_c^k = ℤ₂^{f_k} × ℤ₂^{m_{k-1}} × ℤ₂^{m_k}` of the central Smith
complex (every disk, unit disks included). -/
abbrev centralCx (fr : ℕ → ℕ) (k : ℕ) : Type := Cx ℤ_[2] fr (dd B) k

theorem finrank_centralCx (fr : ℕ → ℕ) (k : ℕ) :
    Module.finrank ℤ_[2] (centralCx B fr k) = fr k + db (dd B) k + dd B k := by
  simp [centralCx, Cx, Module.finrank_prod, add_assoc]

/-- **Tex 5379–5381 (PROVED): `rank_total = Σ f_k + 2m`, counting all Smith disks, including
those with `e = 0`.** -/
theorem sum_finrank_centralCx (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) :
    ∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr k) = ∑ k : Fin 4, fr k + 2 * B.mTot := by
  have h3 : dd B 3 = 0 := dd_eq_zero_of_ge B hamp le_rfl
  have hs := sum_dd_amp B hamp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
    show ((3 : Fin 4) : ℕ) = 3 from rfl, finrank_centralCx, db, h3]
  omega

/-- **Tex 5382–5383 (PROVED): the torsion of `H^*(D_c)` has total length `B.hSmith`**, for any
central Smith data (a unit disk contributes `e = 0`). -/
theorem sum_length_torsion_centralH_amp (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) :
    ∑ k : Fin 4, Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr k)) =
      (B.hSmith : ℕ∞) := by
  have h := fun k : ℕ => length_torsion_H (f := fr) (σ B) (σ_ne B) k
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [h 0, h 1, h 2, show ((3 : Fin 4) : ℕ) = 3 from rfl, h 3, length_Q_zero,
    length_Q_succ (σ B) (σ_ne B) 0, length_Q_succ (σ B) (σ_ne B) 1, length_Q_succ (σ B) (σ_ne B) 2,
    ← sum_sum_val_σ_amp B hamp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_add]

/-- **The budget (5.7) for RC7's `B` with unit disks allowed** (tex 5375–5387; PROVED). -/
theorem budget_rank (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) {dK : ℕ}
    (hrank : ∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr k) ≤ 2 * dK + 12)
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK := by
  obtain ⟨hi, hij, -, -, hl⟩ := h57d
  constructor
  · have hsum := sum_finrank_centralCx B fr hamp
    have hf1 : fr 1 = 1 := by rw [← (finrank_centralH B) fr 1, e.finrank_eq, hr₁]
    have hf2 : 1 ≤ fr 2 := by
      have := LinearMap.finrank_le_finrank_of_injective hi
      rw [hr₂, (finrank_centralH B) fr 2] at this
      exact this
    have hfr : fr 1 + fr 2 ≤ ∑ k : Fin 4, fr k := by
      simp only [Fin.sum_univ_four]; simp; omega
    omega
  · have hS := sum_length_torsion_centralH_amp B fr hamp
    have h0 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 0)) = 0 := by
      rw [length_torsion_H (σ B) (σ_ne B) 0, length_Q_zero]
    have h1 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 1)) = tK := by
      rw [length_torsion_eq_of_equiv e, ht₁]
    have h2 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 2)) ≤ hK + 2 * cE :=
      (length_torsion_le_of_exact i j hi hij).trans (by rw [hh]; exact add_le_add le_rfl hJ)
    have h3 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 3)) ≤ tK :=
      (length_torsion_le_length _).trans ((Module.length_le_of_surjective l hl).trans ht₃.le)
    simp only [Fin.sum_univ_four] at hS
    have : (B.hSmith : ℕ∞) ≤ (hK + 2 * cE + 2 * tK : ℕ) := by
      rw [← hS]
      calc _ ≤ (0 : ℕ∞) + tK + (hK + 2 * cE) + tK := by
              gcongr
              · exact h0.le
              · exact h1.le
              · exact h2
              · exact h3
        _ = ((hK + 2 * cE + 2 * tK : ℕ) : ℕ∞) := by push_cast; ring
    exact_mod_cast this

end Amplitude

/-! ## The nodes -/

/-- **The budget (5.7) in the form consumed by (5.9), for RC7's `SmithBlocks` as it stands**
(tex 5375–5387, 5530–5541; PROVED). Central Smith entries only nonzero (unit disks allowed); the
complex in degrees `0, …, 3` (`hamp`); Elliot's first (5.7) bound `rank_total ≤ 2d_K + 12` for the
total rank of the central Smith complex (`hrank`, every disk counted); RC7's (5.7d) hypotheses
`e, h57d, ht₁, ht₃, hh, hJ`; and the free ranks one of (5.7b) (`hr₁, hr₂`). Conclusion: RC7's
`hm : B.mTot ≤ dK + 5` and `hh : B.hSmith ≤ hK + 2 * cE + 2 * tK`. -/
def FixedFieldBudgetSmithRank : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ),
    (∀ i, 3 ≤ i → i < B.n → B.m i = 0) →
    ∀ (dK : ℕ), ∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr k) ≤ 2 * dK + 12 →
    ∀ (H1C H2C J H3C : Type) [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
      [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
      (_e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
      (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
      (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3),
      (Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
        Function.Exact δ l ∧ Function.Surjective l) →
    ∀ (tK hK cE : ℕ), Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK →
      Module.length ℤ_[2] H3C = tK →
      Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK →
      Module.length ℤ_[2] J ≤ 2 * cE →
      Module.finrank ℤ_[2] H1C = 1 → Module.finrank ℤ_[2] H2C = 1 →
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK

theorem fixedFieldBudgetSmithRank_proof : FixedFieldBudgetSmithRank := by
  intro S O _ _ _ B fr hamp dK hrank H1C H2C J H3C _ _ _ _ _ _ _ _ e i j δ l h57d tK hK cE ht₁ ht₃
    hh hJ hr₁ hr₂
  exact budget_rank B fr hamp hrank e i j δ l h57d ht₁ ht₃ hh hJ hr₁ hr₂

/-- **RC7's `budget_57` inputs `hsmith`, `[Subsingleton H0D]`, `htors` for RC7's `B` as it stands**
(tex 5375–5383; PROVED; unit disks allowed). With `fr = (0,1,1,0)` and `rankTotal` the total rank
of the central Smith complex (every disk counted): `rankTotal = 2 + 2 * B.mTot`, `H⁰(D_c) = 0`, and
the torsion of `H^*(D_c)` has the length of the cokernels of the central Smith blocks (RC7's
`htors`, `Determinant/Budget.lean`). RC7's `hmodel` is the minimality of the model and is supplied
separately (`RC7Budget57Inputs` in `SmithBudget.lean`, for minimal data). -/
def RC7Budget57InputsRank : Prop :=
  ∀ (S O : Type) [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ),
    (∀ i, 3 ≤ i → i < B.n → B.m i = 0) →
    fr 0 = 0 → fr 1 = 1 → fr 2 = 1 → fr 3 = 0 →
    (∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr k) = 2 + 2 * B.mTot) ∧
    Subsingleton ((centralH B) fr 0) ∧
    (Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 0)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 1)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 2)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] ((centralH B) fr 3)) =
      ∑ i ∈ Finset.range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
        LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin))

theorem rc7Budget57InputsRank_proof : RC7Budget57InputsRank := by
  intro S O _ _ _ B fr hamp h0 h1 h2 h3
  refine ⟨?_, subsingleton_centralH_zero B fr h0, ?_⟩
  · rw [sum_finrank_centralCx B fr hamp]
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 4) : ℕ) = 3 from rfl, h0, h1, h2, h3]
  · have hS := sum_length_torsion_centralH_amp B fr hamp
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two] at hS
    exact hS.trans (sum_length_coker B).symm

/-! ## Non-vacuity with a unit disk -/

namespace ExamplesRank

/-- One central Smith disk `[ℤ₂ --1--> ℤ₂]` with `e = 0` (a unit disk), source degree zero. -/
def Bu : SmithBlocks Lam Lam where
  n := 1
  m := fun _ => 1
  A := fun _ => 0
  A0 := fun _ => Matrix.diagonal fun _ => PowerSeries.C (1 : ℤ_[2])
  s := fun _ _ => 1
  s_ne := fun _ _ => one_ne_zero
  central := fun i => by
    rw [Matrix.diagonal_map (by simp)]
    simp

/-- Free generators `(0, 1, 1, 0)`. -/
def fru : ℕ → ℕ := fun i => if i = 1 ∨ i = 2 then 1 else 0

theorem subsingleton_centralH_three : Subsingleton ((centralH Bu) fru 3) := by
  have e := Hequiv (f := fru) (σ Bu) (σ_ne Bu) 3
  have : Subsingleton ((Fin (fru 3) → ℤ_[2]) × Q (σ Bu) 3) := by
    have h1 : Subsingleton (Fin (fru 3) → ℤ_[2]) :=
      ⟨fun a b => funext fun j => (show Fin 0 from j).elim0⟩
    have h2 : Subsingleton (Q (σ Bu) 3) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
      congr 1
      funext j; exact (show Fin 0 from j).elim0
    infer_instance
  exact e.toEquiv.subsingleton

/-- **Non-vacuity of `FixedFieldBudgetSmithRank` with a unit disk (PROVED).** Every hypothesis is
discharged for central Smith data with one disk of valuation zero (`e = 0`): free generators
`(0,1,1,0)`, `dK = 0`, `H¹C = H¹(D_c)`, `H²C = H²(D_c)`, `J = H³C = 0`. The unit disk is counted
in `B.mTot = 1` and contributes nothing to `B.hSmith = 0`. -/
theorem fixedFieldBudgetSmithRank_nonvacuous : Bu.mTot ≤ 0 + 5 ∧ Bu.hSmith ≤ 0 + 2 * 0 + 2 * 0 := by
  have hamp : ∀ i, 3 ≤ i → i < Bu.n → Bu.m i = 0 := fun i hi hin => by
    simp [Bu] at hin; omega
  refine fixedFieldBudgetSmithRank_proof Lam Lam Bu fru hamp 0 ?_
    ((centralH Bu) fru 1) ((centralH Bu) fru 2) PUnit PUnit (LinearEquiv.refl _ _)
    LinearMap.id 0 0 0 ⟨Function.injective_id, ?_, ?_, ?_, ?_⟩ 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [sum_finrank_centralCx Bu fru hamp]
    decide
  · intro x; simp
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x
    have := subsingleton_centralH_three
    exact ⟨0, Subsingleton.elim _ _⟩
  · rw [length_torsion_H (σ Bu) (σ_ne Bu) 1, length_Q_succ (σ Bu) (σ_ne Bu) 0,
      sum_val_σ Bu 0 (by decide)]
    simp [Bu]
  · simp
  · rw [length_torsion_H (σ Bu) (σ_ne Bu) 2, length_Q_succ (σ Bu) (σ_ne Bu) 1,
      sum_val_σ_ge Bu 1 (by decide)]
  · simp
  · simp [finrank_centralH, fru]
  · simp [finrank_centralH, fru]

end ExamplesRank

end ZInQ.Contrib.CloudB3RC53.RankCounts
