import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Boolean
import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper
import ZInQKernel.Contrib.OneProof.RC.Wiring.Even
import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Pieces

/-!
# EvenUpper, part 2: the inputs of (3.3b) from lane RC11's (3.2) and the Boolean comparison

Manuscript `diophantine_zq.tex`, Proposition `ex:sec7-even-upper` and its proof, tex 2273–2341;
App G (F.1)–(F.2), tex 10079–10129.

**Interface finding.**  RC0's leaf `Wiring.EvenUpperInputs W` asks, for each partitionable
corank-zero `d`, for *one* function `u : ℤ → ℚ₂` of the twist parameter satisfying (3.2) and, for
*every* precision `M`, a unit `x` with `v₂(u_x(0) − u_d(0)) ≥ M − c_E`.  Lane RC11's
`EvenScalar32` (Proposition `ex:sec7-even-scalar`) provides one scalar *per binary family*, and the
manuscript's argument (tex 2322–2341, 10114–10125) takes, for one precision `M` with
`M − c_E > B_e`, one cube of large enough dimension and its scalar.  A single `u` valid for all `M`
would need the scalar to be independent of the family (an intrinsic fixed-form Kato scalar
`u_h(0)`), which RC11's interface does not state.  Since RC2's `even_upper_valuation` (and RC0's
`evenUpper33b_of_inputs`) only use the missing address at the single precision
`M = C₀ + C_loc + c_E + 1`, this file records the faithful single-precision form
`EvenUpperInputsAt W` and proves (all `PROVED`):

* `evenUpper33b_of_inputsAt`: (3.3b), RC0's `EvenUpper33b W C₁`, from `EvenUpperInputsAt W`
  (RC2's valuation argument at the one precision; forward rank-zero as in RC0);
* `evenUpperInputsAt_of`: `EvenUpperInputsAt W` from
  - (3.3a) for the units of the even symbol (`h33a`; App E `ex:app-even-phase`; from (E.11) and
    (E.9) by `AuxFactor.F1_unit`, see `h33a_of_F1`),
  - RC11's (3.2), `EvenScalar32 (Ecurve ℓ) N L`, for RC11's normalization `L` with
    `L.Lstar = W.Lstar` (RC0's `LstarNormalized`),
  - the realized cubes `hcubes` (ELLIOT, tex 2311–2322: RC2's `even_upper_cubes`, realized by
    primes through the address construction, as a binary family of any dimension based at `d`,
    with distinct parameters and units of the symbol at the nonzero addresses),
  - and the Boolean comparison (`boolean_comparison`, PROVED from RC1).

Outside the cube, RC0's form of (3.2) quantifies over every parameter; there `u` is given the value
`2^{v₂L_*(p) − 2ω(p) − s(p)}` (or `0` when `L_*(p) = 0`), which satisfies (3.2) exactly.  Only the
values on the cube enter the argument.
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The single-precision inputs of (3.3b)** (see the module docstring): as RC0's
`EvenUpperInputs`, with the missing address required at the one precision used. -/
def EvenUpperInputsAt : Prop :=
  ∃ C₀ Cloc : ℤ, ∀ d : ℤ, d ≠ 0 → W.Partitionable d →
    Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
    ∃ (unit : ℤ → Prop) (u : ℤ → ℚ_[2]),
      (∀ p, unit p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀) ∧
      (∀ p, p ≠ 0 → Z2Corank (selmerTwoPower (Etw ℓ p)) 0 →
        (u p = 0 ↔ W.Lstar p = 0) ∧
        (W.Lstar p ≠ 0 → |Padic.valuation (u p) -
          (padicValRat 2 (W.Lstar p) - 2 * omega p - shaLength (Etw ℓ p))| ≤ Cloc)) ∧
      (∃ x, unit x ∧ (u x = u d ∨ C₀ + Cloc + 1 ≤ Padic.valuation (u x - u d)))

/-- **(3.3b) from the single-precision inputs** (tex 2322–2341, App G (F.2)), `PROVED`. -/
theorem evenUpper33b_of_inputsAt (P : Prints) (hKum : KummerCorankZero) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (h : EvenUpperInputsAt W) : ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨C₀, Cloc, hd⟩ := h
  refine ⟨C₀ + 2 * Cloc, fun d hd0 hpart hcz => ?_⟩
  obtain ⟨unit, u, h33a, h32, x, hx, hcong⟩ := hd d hd0 hpart hcz
  -- the bound at units
  have hux : ∀ y, unit y → u y ≠ 0 ∧ Padic.valuation (u y) ≤ C₀ + Cloc := by
    intro y hy
    obtain ⟨hy0, hLy, hle⟩ := h33a y hy
    have hcy := forward_corankZero P hKum hℓ hy0 ((hL y hy0).mp hLy)
    obtain ⟨h1, h2⟩ := h32 y hy0 hcy
    refine ⟨fun h0 => hLy (h1.mp h0), ?_⟩
    have := (abs_le.mp (h2 hLy)).2
    have hs : (0 : ℤ) ≤ shaLength (Etw ℓ y) := Int.natCast_nonneg _
    linarith
  -- the base
  have hbase : u d ≠ 0 ∧ Padic.valuation (u d) ≤ C₀ + Cloc := by
    by_contra hcon
    obtain ⟨hx0, hxle⟩ := hux x hx
    rcases hcong with heq | hge
    · rw [heq] at hx0 hxle; exact hcon ⟨hx0, hxle⟩
    · have hsum : (u x - u d) + u d ≠ 0 := by rwa [sub_add_cancel]
      have hmin := Padic.le_valuation_add hsum
      rw [sub_add_cancel] at hmin
      by_cases hd' : u d = 0
      · rw [hd', sub_zero] at hge; linarith
      · have hv : C₀ + Cloc < Padic.valuation (u d) := by
          by_contra hle; exact hcon ⟨hd', not_lt.mp hle⟩
        have : C₀ + Cloc + 1 ≤ min (Padic.valuation (u x - u d)) (Padic.valuation (u d)) :=
          le_min hge (by linarith)
        linarith
  obtain ⟨h1, h2⟩ := h32 d hd0 hcz
  have hLd : W.Lstar d ≠ 0 := fun h0 => hbase.1 (h1.mpr h0)
  have := (abs_le.mp (h2 hLd)).1
  have hle : padicValRat 2 (W.Lstar d) ≤ 2 * (omega d : ℤ) + (shaLength (Etw ℓ d) : ℤ) +
      (C₀ + 2 * Cloc) := by linarith [hbase.2]
  simpa [sFun, omega_eq_nonvanishing] using hle

/-- RC11's `ω` (number of prime factors of `|h|`) is the wiring's `ω`. -/
theorem even_omega_eq (h : ℤ) : (Even.omega h : ℤ) = (omega h : ℤ) := by
  simp only [Even.omega, omega, ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors,
    List.card_toFinset]

/-- **The single-precision inputs from RC11's (3.2), (3.3a), the realized cubes and the Boolean
comparison** (tex 2302–2341), `PROVED`. -/
theorem evenUpperInputsAt_of (unitSym : ℤ → Prop) (C₀ : ℤ)
    (h33a : ∀ p, unitSym p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀)
    {N₀ : ℕ} (L : Even.CentralNormalization (Ecurve ℓ)) (hLW : L.Lstar = W.Lstar)
    (h32 : Even.EvenScalar32 (Ecurve ℓ) N₀ L)
    (hcubes : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧ Function.Injective fam.h ∧
        ∀ x, x ≠ 0 → unitSym (fam.h x)) :
    EvenUpperInputsAt W := by
  classical
  obtain ⟨Cev, C, h32⟩ := h32
  refine ⟨C₀, C, fun d hd0 hpart hcz => ?_⟩
  set M : ℕ := (C₀ + C + 1).toNat + Cev with hM
  obtain ⟨fam, hb, hh0, hinj, hunit⟩ := hcubes d hd0 hpart hcz (2 ^ (M - 1))
  obtain ⟨uf, hint, hzero, hbd⟩ := h32 fam
  -- the scalar on parameters
  let art : ℤ → ℚ_[2] := fun p => if W.Lstar p = 0 then 0 else
    (2 : ℚ_[2]) ^ (padicValRat 2 (W.Lstar p) - 2 * (omega p : ℤ) - (shaLength (Etw ℓ p) : ℤ))
  let u : ℤ → ℚ_[2] := fun p =>
    if hp : ∃ x, fam.h x = p then Even.central (Even.charEval uf hp.choose) else art p
  have hu_fam : ∀ x, u (fam.h x) = Even.central (Even.charEval uf x) := by
    intro x
    have hp : ∃ y, fam.h y = fam.h x := ⟨x, rfl⟩
    simp only [u, dif_pos hp]
    rw [hinj hp.choose_spec]
  refine ⟨unitSym, u, h33a, fun p hp0 hcp => ?_, ?_⟩
  · by_cases hp : ∃ x, fam.h x = p
    · obtain ⟨x, rfl⟩ := hp
      rw [hu_fam]
      have hcz' : Even.CorankZero (Ecurve ℓ) (fam.h x) := hcp
      refine ⟨by rw [hzero x hcz', hLW], fun hL => ?_⟩
      have := hbd x hcz' (by rwa [hLW])
      rw [hLW, even_omega_eq] at this
      exact_mod_cast this
    · have hart : u p = art p := by simp only [u, dif_neg hp]
      rw [hart]
      by_cases hL : W.Lstar p = 0
      · simp [art, hL]
      · simp only [art, if_neg hL]
        refine ⟨⟨fun h0 => absurd h0 (zpow_ne_zero _ two_ne_zero), fun h0 => absurd h0 hL⟩,
          fun _ => ?_⟩
        rw [Padic.valuation_zpow]
        have h2 : (2 : ℚ_[2]).valuation = 1 := by simp
        rw [h2, mul_one, sub_self, abs_zero]
        exact_mod_cast Nat.zero_le C
  · -- the missing address at the one precision
    obtain ⟨x, hx0, hcong⟩ := boolean_comparison uf Cev hint M (by
      have : 2 ^ (M - 1) - 1 < 2 ^ (M - 1) := Nat.sub_lt (Nat.two_pow_pos _) one_pos
      omega)
    refine ⟨fam.h x, hunit x hx0, ?_⟩
    rw [hu_fam, ← hh0, hu_fam]
    rcases hcong with heq | hge
    · exact Or.inl heq
    · right
      have : (C₀ + C + 1 : ℤ) ≤ (M : ℤ) - Cev := by
        rw [hM]; push_cast; have := Int.self_le_toNat (C₀ + C + 1); omega
      exact le_trans (by exact_mod_cast this) hge

/-- A unit of the normalized even symbol: a nonzero coefficient attaining the minimum of
`v₂a(D) − ω(D)` (tex 10083–10085: "A unit of the normalized symbol means precisely equality to
this minimum"). -/
def UnitMin (aNZ : ℤ → Prop) (va : ℤ → ℤ) (p : ℤ) : Prop :=
  aNZ p ∧ ∀ D, aNZ D → va p - omega p ≤ va D - omega D

/-- **(3.3a) from (E.11) and (E.9)** (tex 2302–2310, App G (F.1)), `PROVED` from
`AuxFactor.F1_unit`: the units of the normalized even symbol satisfy (3.3a) with
`C₀ = 2δ_e + κ_e`. -/
theorem h33a_of_F1 (aNZ : ℤ → Prop) (va : ℤ → ℤ) (κ c : ℤ)
    (hE11 : ∀ D, (W.Lstar D ≠ 0 ↔ aNZ D) ∧ (aNZ D → padicValRat 2 (W.Lstar D) = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - omega D) (href : ∃ D, aNZ D) (hNZ : ∀ D, aNZ D → D ≠ 0) :
    ∃ C₀ : ℤ, ∀ p, UnitMin aNZ va p →
      p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀ := by
  obtain ⟨δ, ⟨D₀, hD₀, hD₀δ⟩, hmin, hF⟩ := AuxFactor.F1_unit aNZ (fun D => W.Lstar D ≠ 0) va
    (fun D => padicValRat 2 (W.Lstar D)) omega κ hE11 c hE9 href
  refine ⟨2 * δ + κ, fun p ⟨hp, hpmin⟩ => ?_⟩
  have hpδ : va p - omega p = δ := le_antisymm (hD₀δ ▸ hpmin D₀ hD₀) (hmin p hp)
  exact ⟨hNZ p hp, (hF p hp hpδ).1, (hF p hp hpδ).2.le⟩

/-- **(3.3b) assembled** (Proposition `ex:sec7-even-upper`, tex 2273–2341; App G (F.1)–(F.2)),
`PROVED` from: the prints and Kummer glue of RC0 (`P`, `hKum`), RC0's `LstarTarget`, RC11's
normalization (`LstarNormalized`) and (3.2) (`EvenScalar32`), App E's (E.11) and (E.9) (`hE11`,
`hE9`, `href`, for the even source's coefficients `a(D)`), and the realized cubes `hcubes` whose
nonzero addresses are units of the symbol (equality to the attained minimum). -/
theorem evenUpper33b_of_RC11 (P : Prints) (hKum : KummerCorankZero) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (hN : LstarNormalized W.toRCData) {N₀ : ℕ}
    (h32 : ∀ L : Even.CentralNormalization (Ecurve ℓ), L.Lstar = W.Lstar →
      Even.EvenScalar32 (Ecurve ℓ) N₀ L)
    (aNZ : ℤ → Prop) (va : ℤ → ℤ) (κ c : ℤ)
    (hE11 : ∀ D, (W.Lstar D ≠ 0 ↔ aNZ D) ∧ (aNZ D → padicValRat 2 (W.Lstar D) = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - omega D) (href : ∃ D, aNZ D) (hNZ : ∀ D, aNZ D → D ≠ 0)
    (hcubes : ∀ d : ℤ, d ≠ 0 → W.Partitionable d →
      Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧ Function.Injective fam.h ∧
        ∀ x, x ≠ 0 → UnitMin aNZ va (fam.h x)) :
    ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨L, hLW⟩ := hN
  obtain ⟨C₀, h33a⟩ := h33a_of_F1 W aNZ va κ c hE11 hE9 href hNZ
  exact evenUpper33b_of_inputsAt W P hKum hℓ hL
    (evenUpperInputsAt_of W _ _ h33a L hLW (h32 L hLW) hcubes)

end ZInQ.Contrib.CloudB3RC53.EvenUpper
