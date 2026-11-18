import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus
import ZInQKernel.Contrib.OneProof.RC.Symbols.EvenUpper

/-!
# Theorem 5.3, Lane RC0 round 2: the even upper bound (3.3b) from lanes RC2 and RC11

`evenUpper33b_of_inputs` (PROVED from lane RC2's `even_upper_valuation`): the input (3.3b) of the
rough companion (Proposition `ex:sec7-even-upper`, tex 2273–2341; App G (F.1)–(F.2)) from
`EvenUpperInputs`: at each partitionable `d` of Selmer corank zero, the units of the even symbol on
the cubes of RC2's `even_upper_cubes` with (3.3a) (App E `ex:app-even-phase`; lane RC11), the
corank-zero central comparison (3.2) for the fixed-form Kato scalar (App E
`ex:app-central-calibration`, (E.8); lane RC11's `EvenScalar32`), and the missing address on those
cubes (Section 9's Boolean bit-degree lemma and cube parity; lanes RC1 and RC2). The forward
rank-zero theorem is not an input: it is `forward_corankZero` (blueprint prints, Kummer glue).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.3b) left by lane RC2's `even_upper_valuation`**, with constants
`C₀` ((3.3a)), `C_loc` ((3.2)) and `c_E` (the Boolean comparison) fixed by the source: for every
partitionable `d ≠ 0` of Selmer corank zero, a unit predicate on twist parameters (the units of the
even symbol on the cubes based at `d`, tex 2311–2322) and the values `u_p(0)` of the common
fixed-form scalar, with
* (3.3a) (tex 2302–2310, App E `ex:app-even-phase`; ELLIOT; owner RC11): a unit `p` has
  `p ≠ 0`, `L_*(p) ≠ 0` and `v₂L_*(p) ≤ 2ω(p) + C₀`;
* (3.2) at corank-zero constituents (tex 1966–1968, App E (E.8); ELLIOT; owner RC11):
  `u_p(0) = 0 ↔ L_*(p) = 0`, and `|v₂u_p(0) − (v₂L_*(p) − 2ω(p) − s(p))| ≤ C_loc` when `L_*(p) ≠ 0`;
* the missing address on the cubes (tex 2322–2341 with 5690–5714; ELLIOT; owners RC1, RC2): for
  every precision `M` a unit `x` with `u_x(0) = u_d(0)` or `v₂(u_x(0) − u_d(0)) ≥ M − c_E`. -/
def EvenUpperInputs : Prop :=
  ∃ C₀ Cloc cE : ℤ, ∀ d : ℤ, d ≠ 0 → W.Partitionable d →
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
    ∃ (unit : ℤ → Prop) (u : ℤ → ℚ_[2]),
      (∀ p, unit p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀) ∧
      (∀ p, p ≠ 0 → Z2Corank (selmerTwoPower (Etw ℓ p)) 0 →
        (u p = 0 ↔ W.Lstar p = 0) ∧
        (W.Lstar p ≠ 0 → |Padic.valuation (u p) -
          (padicValRat 2 (W.Lstar p) - 2 * omega p - shaLength (Etw ℓ p))| ≤ Cloc)) ∧
      (∀ M : ℤ, ∃ x, unit x ∧ (u x = u d ∨ M - cE ≤ Padic.valuation (u x - u d)))

/-- **(3.3b)** (PROVED from lane RC2's `even_upper_valuation`, the normalization of `L_*` and the
forward theorem). -/
theorem evenUpper33b_of_inputs (P : Prints) (hKum : KummerCorankZero) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (h : EvenUpperInputs W) : ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨C₀, Cloc, cE, hd⟩ := h
  refine ⟨C₀ + 2 * Cloc, fun d hd0 hpart hcz => ?_⟩
  obtain ⟨unit, u, h33a, h32, hmiss⟩ := hd d hd0 hpart hcz
  have key := Symbols.even_upper_valuation unit
    (fun p => p ≠ 0 ∧ Z2Corank (selmerTwoPower (Etw ℓ p)) 0)
    (fun p => p ≠ 0 ∧ W.Lstar p ≠ 0) u (fun p => padicValRat 2 (W.Lstar p)) omega
    (fun p => shaLength (Etw ℓ p)) C₀ Cloc cE
    (fun p hp => by
      obtain ⟨hp0, hLp, hle⟩ := h33a p hp
      exact ⟨⟨hp0, hLp⟩, hle⟩)
    (fun p ⟨hp0, hLp⟩ => ⟨hp0, forward_corankZero P hKum hℓ hp0 ((hL p hp0).mp hLp)⟩)
    (fun p ⟨hp0, hcp⟩ => by
      obtain ⟨h1, h2⟩ := h32 p hp0 hcp
      refine ⟨?_, fun ⟨_, hLp⟩ => h2 hLp⟩
      rw [h1]
      constructor
      · intro h0 ⟨_, hne⟩
        exact hne h0
      · intro hn
        by_contra hne
        exact hn ⟨hp0, hne⟩)
    d ⟨hd0, hcz⟩ hmiss
  obtain ⟨-, hle⟩ := key
  have : padicValRat 2 (W.Lstar d) ≤ 2 * (omega d : ℤ) + (shaLength (Etw ℓ d) : ℤ) +
      (C₀ + 2 * Cloc) := by linarith
  simpa [sFun, omega_eq_nonvanishing] using this

end ZInQ.Manuscript.RC.Wiring
