import ZInQKernel.Contrib.OneProof.RC.Symbols.EvenUpper
import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Companion

/-!
# AuxFactor, part 1: Elliot's pieces of the partitionable auxiliary factor (App G)

Manuscript `diophantine_zq.tex`, App G, Proposition `ex:app-rough-companion` and its proof,
tex L10055–10150: (F.1)–(F.3), the partitionability of the negative types, the dummy anchors and
the bound `v₂L_*(hk') ≤ 2ω(h) + 2ω(k') + s(hk') + C_E`.

Lane RC13 assembles (3.3) (`ZInQ.Manuscript.RC.Nonvanishing.roughCompanion`, from Hoffstein–Luo
and the BFH sign through the five-prime proposition) from three inputs: the dummy realization with
partitionability (`hdummy`), the forward rank-zero theorem (`hforward`, PRINT) and (F.2) (`h33b`).
Lane RC2 proves the valuation step of (F.2) (`even_upper_valuation`) from (3.3a), (E.8) and the
Boolean comparison, and the partitionability from anchors (`partitionable_of_anchors`).  This file
supplies Elliot's remaining steps, in those lanes' forms (all `PROVED`):

* `F1_unit` — (F.1), tex 10079–10088: from (E.11) `v₂L_*(σD) = 2v₂a(D) + κ_e`, the lower bound
  (E.9) and a nonzero reference coefficient, the set of integers `v₂a(D) − ω(D)` has an attained
  minimum `δ_e`; a unit of the normalized symbol (equality to this minimum) gives
  `L_*(σD) ≠ 0` and `v₂L_*(σD) = 2ω(D) + C_{e,unit}`, `C_{e,unit} = 2δ_e + κ_e`.
* `F2_bound` — (F.2), tex 10107–10129: RC2's `even_upper_valuation` fed with (F.1); the constant
  is `C_{e,unit} + 2C_loc`, and the result has the form of RC13's input `h33b`.
* `negative_unitSeed_nonempty`, `exists_minSeed`, `negative_partitionable` — the
  partitionability of the negative types, tex 10089–10098: for a source whose symbol vanishes off
  a nonzero total type, every unit seed is nonempty, a seed of least positive size exists, and
  every list of the same total containing the first `r − 1` seed anchors and a nonempty remainder
  is partitionable (RC2's `partitionable_of_anchors`), regardless of the remainder.
* `F3_max` — (F.3), tex 10140–10146: the maximum over the finitely many prepared constants.
-/

namespace ZInQ.Contrib.CloudB3RC53.AuxFactor

open ZInQ.Manuscript.RC.Symbols Finset

/-! ## (F.1) -/

/-- **(F.1)** (tex 10079–10088), `PROVED`.  For one fixed even source: `aNZ D` (`a(D) ≠ 0`),
`va D = v₂a(D)`, `ω D = ω(D)`, `Lnz D` (`L_*(σD) ≠ 0`), `Lval D = v₂L_*(σD)`.  Inputs: (E.11)
(`hE11`: `L_*(σD) ≠ 0 ↔ a(D) ≠ 0`, and then `v₂L_*(σD) = 2v₂a(D) + κ_e`), the lower bound (E.9)
(`hE9`: `v₂a(D) − ω(D) ≥ c`) and a nonzero reference coefficient (`href`).  Conclusion: the
attained minimum `δ_e` of `v₂a(D) − ω(D)` exists, and every `D` attaining it (a unit of the
normalized symbol) has `L_*(σD) ≠ 0` and `v₂L_*(σD) = 2ω(D) + (2δ_e + κ_e)`. -/
theorem F1_unit {P : Type*} (aNZ Lnz : P → Prop) (va Lval : P → ℤ) (ω : P → ℕ) (κ : ℤ)
    (hE11 : ∀ D, (Lnz D ↔ aNZ D) ∧ (aNZ D → Lval D = 2 * va D + κ))
    (c : ℤ) (hE9 : ∀ D, aNZ D → c ≤ va D - ω D) (href : ∃ D, aNZ D) :
    ∃ δ : ℤ, (∃ D, aNZ D ∧ va D - ω D = δ) ∧ (∀ D, aNZ D → δ ≤ va D - ω D) ∧
      ∀ D, aNZ D → va D - ω D = δ → Lnz D ∧ Lval D = 2 * ω D + (2 * δ + κ) := by
  classical
  obtain ⟨δ, ⟨D₀, hD₀, rfl⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ D, aNZ D ∧ va D - ω D = z) ⟨c, fun z ⟨D, hD, hz⟩ => hz ▸ hE9 D hD⟩
    (by obtain ⟨D, hD⟩ := href; exact ⟨_, D, hD, rfl⟩)
  refine ⟨va D₀ - ω D₀, ⟨D₀, hD₀, rfl⟩, fun D hD => hmin _ ⟨D, hD, rfl⟩, fun D hD hDδ => ?_⟩
  refine ⟨(hE11 D).1.mpr hD, ?_⟩
  rw [(hE11 D).2 hD]
  linarith

/-! ## (F.2) -/

/-- **(F.2)** (tex 10107–10129), `PROVED` from (F.1) and the inputs of RC2's
`even_upper_valuation`: with the unit predicate of (F.1) (equality to the minimum `δ_e`), the forward
rank-zero theorem (`hfwd`), (E.8) (`h32`) and the Boolean comparison on the address cubes
(`hmiss`), every corank-zero `d₀` has `L_*(d₀) ≠ 0` and
`v₂L_*(d₀) − 2ω(d₀) − s(d₀) ≤ C_{e,unit} + 2C_loc`. -/
theorem F2_bound {P : Type*} (aNZ Lnz corank0 : P → Prop) (va Lval : P → ℤ) (ω s : P → ℕ)
    (u : P → ℚ_[2]) (κ δ Cloc cE : ℤ)
    (hE11 : ∀ D, (Lnz D ↔ aNZ D) ∧ (aNZ D → Lval D = 2 * va D + κ))
    (hfwd : ∀ p, Lnz p → corank0 p)
    (h32 : ∀ p, corank0 p → (u p = 0 ↔ ¬ Lnz p) ∧
      (Lnz p → |Padic.valuation (u p) - (Lval p - 2 * ω p - s p)| ≤ Cloc))
    (d₀ : P) (hd₀ : corank0 d₀)
    (hmiss : ∀ M : ℤ, ∃ x, (aNZ x ∧ va x - ω x = δ) ∧
      (u x = u d₀ ∨ M - cE ≤ Padic.valuation (u x - u d₀))) :
    Lnz d₀ ∧ Lval d₀ - 2 * ω d₀ - s d₀ ≤ (2 * δ + κ) + 2 * Cloc := by
  refine even_upper_valuation (fun x => aNZ x ∧ va x - ω x = δ) corank0 Lnz u Lval ω s
    (2 * δ + κ) Cloc cE (fun p hp => ?_) hfwd h32 d₀ hd₀ hmiss
  refine ⟨(hE11 p).1.mpr hp.1, ?_⟩
  rw [(hE11 p).2 hp.1]
  linarith [hp.2]

/-! ## Partitionability of the negative types -/

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {A : Config L → ZMod 2}

/-- **Unit seeds of a negative type are nonempty** (tex 10089–10091), `PROVED`: if the symbol
vanishes off a nonzero total type `τ` (the total `(−1/D)` label of a negative type is nonzero),
an empty configuration has total `0 ≠ τ`, so it is not a unit. -/
theorem negative_unitSeed_nonempty {τ : L} (hoff : VanishesOffFilter A τ) (hτ : τ ≠ 0)
    {Γ : Config L} (hΓ : IsUnitSeed ε A Γ) : Γ.V.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := hoff Γ hΓ.2
  simp [Config.total, h] at this
  exact hτ this.symm

/-- **A seed of least positive size exists** (tex 10091–10093), `PROVED`, once some nonempty unit
seed exists (the prepared seed of the source). -/
theorem exists_minSeed (h : ∃ Γ : Config L, IsUnitSeed ε A Γ ∧ Γ.V.Nonempty) :
    ∃ Γ₀, IsMinSeed ε A Γ₀ := by
  classical
  have hex : ∃ n, ∃ Γ : Config L, IsUnitSeed ε A Γ ∧ Γ.V.Nonempty ∧ Γ.V.card = n := by
    obtain ⟨Γ, hΓ, hne⟩ := h; exact ⟨_, Γ, hΓ, hne, rfl⟩
  obtain ⟨Γ, hΓ, hne, hcard⟩ := Nat.find_spec hex
  refine ⟨Γ, hΓ, hne, fun Δ hΔ hΔne => ?_⟩
  rw [hcard]
  exact Nat.find_min' hex ⟨Δ, hΔ, hΔne, rfl⟩

/-- **Partitionability of the negative types** (tex 10089–10098), `PROVED`: for a source whose
symbol satisfies the coefficient rules and vanishes off a nonzero total type `τ`, with a prepared
nonempty unit seed, there is a minimum seed `Γ₀` (of total `τ`, nonempty), and every compatible
list `Γ` of total `τ` containing anchors of the types of `Γ₀` minus one vertex `s` and a nonempty
remainder is partitionable — regardless of how many old primes are in the remainder. -/
theorem negative_partitionable (hA : CoefficientRules ε A) {τ : L} (hoff : VanishesOffFilter A τ)
    (hτ : τ ≠ 0) (hseed : ∃ Γ : Config L, IsUnitSeed ε A Γ) :
    ∃ Γ₀ : Config L, IsMinSeed ε A Γ₀ ∧ Γ₀.total = τ ∧ Γ₀.V.Nonempty ∧
      ∀ (Γ : Config L), Γ.Compatible ε → Γ.total = τ → ∀ (s : ℕ), s ∈ Γ₀.V →
        ∀ anc : ℕ → ℕ, Set.InjOn anc (Γ₀.V.erase s) → (∀ v ∈ Γ₀.V.erase s, anc v ∈ Γ.V) →
          (∀ v ∈ Γ₀.V.erase s, Γ.t (anc v) = Γ₀.t v) →
          (Γ.V \ (Γ₀.V.erase s).image anc).Nonempty → IsPartitionable ε A Γ := by
  obtain ⟨Γ₁, hΓ₁⟩ := hseed
  obtain ⟨Γ₀, hmin⟩ := exists_minSeed (A := A) ⟨Γ₁, hΓ₁, negative_unitSeed_nonempty hoff hτ hΓ₁⟩
  have htot : Γ₀.total = τ := hoff Γ₀ hmin.1.2
  refine ⟨Γ₀, hmin, htot, hmin.2.1, fun Γ hΓ hΓt s hs anc hinj hV ht hrem => ?_⟩
  exact partitionable_of_anchors hA hmin hΓ (hΓt.trans htot.symm) s hs anc hinj hV ht hrem

/-! ## (F.3) -/

/-- **(F.3), the maximum over the prepared constants** (tex 10140–10146), `PROVED`: for finitely
many prepared sources with constants `C i` and a bound holding with the constant of the source that
actually occurs, the bound holds with `C_E = max_i C i`. -/
theorem F3_max {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (C : ι → ℤ) (x : ℤ) (i : ι)
    (hi : i ∈ I) (hx : x ≤ C i) : x ≤ I.sup' hI C :=
  hx.trans (Finset.le_sup' C hi)

/-! ## The rough companion with (F.1)–(F.2) supplied -/

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Manuscript.RC.Nonvanishing in
/-- **The input `h33b` of RC13's `roughCompanion` from (F.1)–(F.2)** (tex 10079–10129), `PROVED`:
for one fixed even source (`hE11`, `hE9`, `href` as in `F1_unit`), with the forward rank-zero
theorem, (E.8) and, for every partitionable corank-zero `d`, the Boolean comparison on its address
cubes (`hmiss`: units at nonzero addresses close to the base), every partitionable corank-zero `d`
satisfies `v₂L_*(d) ≤ 2ω(d) + s(d) + C₁` with `C₁ = C_{e,unit} + 2C_loc`. -/
theorem h33b_of_F (Partitionable CorankZero aNZ Lnz : ℤ → Prop) (va vL : ℤ → ℤ) (sN : ℤ → ℕ)
    (u : ℤ → ℚ_[2]) (κ Cloc cE c : ℤ)
    (hE11 : ∀ D, (Lnz D ↔ aNZ D) ∧ (aNZ D → vL D = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - omega D) (href : ∃ D, aNZ D)
    (hfwd : ∀ p, Lnz p → CorankZero p)
    (h32 : ∀ p, CorankZero p → (u p = 0 ↔ ¬ Lnz p) ∧
      (Lnz p → |Padic.valuation (u p) - (vL p - 2 * omega p - sN p)| ≤ Cloc))
    (hmiss : ∀ δ : ℤ, (∀ D, aNZ D → δ ≤ va D - omega D) → (∃ D, aNZ D ∧ va D - omega D = δ) →
      ∀ d, Partitionable d → CorankZero d → ∀ M : ℤ, ∃ x, (aNZ x ∧ va x - omega x = δ) ∧
        (u x = u d ∨ M - cE ≤ Padic.valuation (u x - u d))) :
    ∃ C₁ : ℤ, ∀ d : ℤ, Partitionable d → CorankZero d →
      vL d ≤ 2 * omega d + (sN d : ℤ) + C₁ := by
  obtain ⟨δ, hatt, hmin, -⟩ := F1_unit aNZ Lnz va vL omega κ hE11 c hE9 href
  refine ⟨2 * δ + κ + 2 * Cloc, fun d hP hC => ?_⟩
  have := (F2_bound aNZ Lnz CorankZero va vL omega sN u κ δ Cloc cE hE11 hfwd h32 d hC
    (hmiss δ hmin hatt d hP hC)).2
  linarith

end ZInQ.Contrib.CloudB3RC53.AuxFactor
