import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3

/-!
# Prepared negative types and the fourth auxiliary-factor clause

The negative types used in Appendix G have unsigned index seven modulo eight.
For each prepared type, a unit seed is nonempty. A minimum nonempty seed depends
only on its vertex labels, and matching all but one of its anchors, with a
nonempty remainder, gives a contraction certificate. This is the content of
Appendix G, lines 10096--10105, used at line 10139.

The phrase "every total type" at lines 10131--10132 is read in the context of
these prepared negative sources (lines 10057 and 10096), not as nonvanishing in
every possible local filter. No seed is requested at an unprepared type.

The combinatorial claim is proved below from unit seeds at prepared types only.
Its seed input is reduced further to retained squarefree coefficients with a
nonzero reference, a lower bound, and the actual symbol reading at the attained
minimum. The minimum is proved to exist; it is not an input. The coefficient
lower bound is also derived from the two valuation statements (E.9) and (E.11).
The dictionary proves the reading identity whenever the symbol is its reading
of that fixed normalized source.

The source input below is a data specification, not a new printed theorem.
Producing it for the actual even forms remains an explicit mathematical
obligation: the reference and phase-normalized source of Appendix E, the
valuation comparisons, and the identification of the fixed symbol. There are
no additional analytic nonvanishing assumptions and no new printed leaves.
-/

set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Wiring
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
  ZInQ.Contrib.CloudB3RC53.AuxFactor Finset

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- A least normalized coefficient depth: attainment and a lower bound on all
retained nonzero coefficients. Appendix G, lines 10083--10087. -/
def LeastCoefficientDepth (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ) : Prop :=
  (∃ D : ℕ, F D ∧ a D ≠ 0 ∧
    Padic.valuation (a D) - (D.primeFactors.card : ℤ) = δ) ∧
  ∀ D : ℕ, F D → a D ≠ 0 →
    δ ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ)

/-- The attained minimum follows from a nonzero reference and an integer lower
bound. No unit or minimum is assumed. Appendix G, lines 10083--10087. -/
theorem leastCoefficientDepth_exists (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (c : ℤ)
    (href : ∃ D : ℕ, F D ∧ a D ≠ 0)
    (hlow : ∀ D : ℕ, F D → a D ≠ 0 →
      c ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ)) :
    ∃ δ : ℤ, LeastCoefficientDepth a F δ := by
  obtain ⟨δ, hatt, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ D : ℕ, F D ∧ a D ≠ 0 ∧
      Padic.valuation (a D) - (D.primeFactors.card : ℤ) = z)
    ⟨c, fun z ⟨D, hF, ha, hz⟩ => hz ▸ hlow D hF ha⟩
    (by obtain ⟨D, hF, ha⟩ := href; exact ⟨_, D, hF, ha, rfl⟩)
  exact ⟨δ, hatt, fun D hF ha => hmin _ ⟨D, hF, ha, rfl⟩⟩

/-- The valuation part of (E.9) and the same-source equality (E.11) imply the
coefficient-depth lower bound. Here `C` is the lower-bound constant after
omitting the nonnegative term `s(D)`. Both comparisons remain explicit inputs;
this theorem proves only their arithmetic consequence. -/
theorem coefficientDepth_lowerBound_of_E9_E11 (a : ℕ → ℚ_[2]) (F : ℕ → Prop)
    (vL : ℕ → ℤ) (κ C : ℤ)
    (hE11 : ∀ D : ℕ, F D → a D ≠ 0 → vL D = 2 * Padic.valuation (a D) + κ)
    (hE9 : ∀ D : ℕ, F D → a D ≠ 0 → 2 * (D.primeFactors.card : ℤ) + C ≤ vL D) :
    ∀ D : ℕ, F D → a D ≠ 0 →
      (C - κ) / 2 ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ) := by
  intro D hF ha
  have heq := hE11 D hF ha
  have hle := hE9 D hF ha
  omega

/-- Retained indices of a negative source: positive squarefree indices seven
modulo eight, good at the type conductor, with the prescribed total type.
This records the filter, not an analytic nonvanishing assertion. -/
def NegativeCoefficientFilter (T : TypeData L ε) (τ : L) (F : ℕ → Prop) : Prop :=
  ∀ D : ℕ, F D → 0 < D ∧ Squarefree D ∧ D % 8 = 7 ∧
    (∀ p ∈ D.primeFactors, T.Good p) ∧
    (primeConfig D.primeFactors T.typ).total = τ

/-- The actual symbol on retained prime configurations is the coefficient
symbol of the same source at the same normalized depth. This is a definition
of the required reading identity, not a coefficient-rule hypothesis. -/
def NormalizedPrimeReading (T : TypeData L ε) (A : Config L → ZMod 2)
    (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ) : Prop :=
  ∀ D : ℕ, F D → A (primeConfig D.primeFactors T.typ) = coeffSymbol a δ F D

/-- The dictionary discharges the reading identity. The lower bound, the
reference and the choice of minimum are not used in this definitional bridge. -/
theorem normalizedPrimeReading_of_dictionary (T : TypeData L ε) (τ : L)
    (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ)
    (hF : NegativeCoefficientFilter T τ F)
    (hswap : ∀ B : ℕ, FixedUFactorization T (coeffReading a δ F) B) :
    NormalizedPrimeReading T (symb T (coeffReading a δ F)) a F δ := by
  intro D hD
  obtain ⟨_, hsf, _, hgood, _⟩ := hF D hD
  rw [symb_primeConfig T a δ F (hswap _) D.primeFactors hgood le_rfl]
  change coeffSymbol a δ F (∏ p ∈ D.primeFactors, p) = coeffSymbol a δ F D
  rw [Nat.prod_primeFactors_of_squarefree hsf]

/-- Minimal source-level ingredients for the prepared types. The source and
filter are fixed first. The lower bound and nonzero reference imply a unique
attained least depth; at that depth `A τ` must read this same source. In
particular, the last field does not assert that a minimum or a unit exists.
All quantification over total types is restricted to `PreparedType`.

The four obligations are separated: filter specification, nonzero reference,
coefficient lower bound, and normalized reading. None is called a printed
existence theorem for the actual form. -/
def PreparedEvenSourceInput {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (A : L → Config L → ZMod 2) : Prop :=
  ∀ τ : L, PreparedType W T τ →
    ∃ (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (c : ℤ),
      NegativeCoefficientFilter T τ F ∧
      (∃ D : ℕ, F D ∧ a D ≠ 0) ∧
      (∀ D : ℕ, F D → a D ≠ 0 →
        c ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ)) ∧
      ∀ δ : ℤ, LeastCoefficientDepth a F δ →
        NormalizedPrimeReading T (A τ) a F δ

/-- The exact prepared-seed input of the auxiliary-factor interface follows
from the source-level ingredients. A least-depth index gives an actual unit
on its compatible graph of good prime factors. -/
theorem preparedSeedInput_of_evenSourceInput {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (A : L → Config L → ZMod 2)
    (hsrc : PreparedEvenSourceInput W T A) :
    ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ := by
  intro τ hτ
  obtain ⟨a, F, c, hF, href, hlow, hread⟩ := hsrc τ hτ
  obtain ⟨δ, hδ⟩ := leastCoefficientDepth_exists a F c href hlow
  obtain ⟨D, hD, ha, hdepth⟩ := hδ.1
  obtain ⟨_, _, _, hgood, _⟩ := hF D hD
  have hf : IsReal T (primeConfig D.primeFactors T.typ) id :=
    ⟨Set.injOn_id _, fun p hp => ⟨hgood p hp, rfl⟩, fun _ _ _ _ _ => rfl⟩
  refine ⟨primeConfig D.primeFactors T.typ, compatible_of_real T hf, ?_⟩
  rw [hread δ hδ D hD]
  unfold coeffSymbol
  apply ite_eq_left
  refine ⟨hD, ha, ?_⟩
  linarith

/-- A prepared total type has sign coordinate one, because its unsigned
squarefree index is seven modulo eight. This is a sign-coordinate statement,
not an assertion about the elliptic curve's root number. -/
theorem preparedType_sign_one {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S) {τ : L}
    (hτ : PreparedType W T τ) : ε τ = 1 := by
  obtain ⟨d, hd, h8, hsf, hdS, _, rfl⟩ := hτ
  set V := d.natAbs.primeFactors with hV
  have hgood : ∀ p ∈ V, T.Good p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hprime, (Nat.Prime.coprime_iff_not_dvd hprime).mpr ?_⟩
    intro hpm
    exact hdS p (hmS p hprime hpm) (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have hodd : ∀ p ∈ V, Odd p := by
    intro p hp
    rcases (hgood p hp).1.eq_two_or_odd' with htwo | ho
    · exact False.elim ((hgood p hp).ne_two htwo)
    · exact ho
  have hprod : ∏ p ∈ V, p = d.natAbs :=
    Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsf)
  have habs : (d.natAbs : ℤ) = -d := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hseven : d.natAbs % 8 = 7 := by omega
  have hhalf : ((d.natAbs / 2 : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, show d.natAbs / 2 % 2 = 1 by omega]
    rfl
  have hsign : ε (primeConfig V T.typ).total = ∑ p ∈ V, ((p / 2 : ℕ) : ZMod 2) := by
    change ε (∑ p ∈ V, T.typ p) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun p hp => T.sign p (hgood p hp).1 (hgood p hp).2
  change ε (primeConfig V T.typ).total = 1
  rw [hsign, ← half_prod_odd V hodd, hprod]
  exact hhalf

/-- The text-faithful fourth clause, including the argument of Appendix G,
lines 10096--10105. At each prepared type, every unit seed is nonempty, a
minimum nonempty seed exists and its total is the prepared type, its bits are
irrelevant, and its first `r - 1` labels suffice for an anchor certificate with
a nonempty remainder. There is no quantification over unprepared types. -/
def PreparedClauseFour {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (A : L → Config L → ZMod 2) : Prop :=
  ∀ τ : L, PreparedType W T τ →
    (∀ Δ : Config L, IsUnitSeed ε (A τ) Δ → Δ.V.Nonempty) ∧
    ∃ Γ₀ : Config L, IsMinSeed ε (A τ) Γ₀ ∧ Γ₀.total = τ ∧
      (∀ Δ : Config L, Δ.Compatible ε → Δ.V = Γ₀.V →
        (∀ v ∈ Γ₀.V, Δ.t v = Γ₀.t v) → A τ Δ = 1) ∧
      ∀ Γ : Config L, Γ.Compatible ε → Γ.total = τ →
        ∀ s : ℕ, s ∈ Γ₀.V → ∀ anc : ℕ → ℕ,
          Set.InjOn anc (Γ₀.V.erase s) →
          (∀ v ∈ Γ₀.V.erase s, anc v ∈ Γ.V) →
          (∀ v ∈ Γ₀.V.erase s, Γ.t (anc v) = Γ₀.t v) →
          (Γ.V \ (Γ₀.V.erase s).image anc).Nonempty → IsPartitionable ε (A τ) Γ

/-- The entire prepared-type clause follows from the coefficient rules,
vanishing off the filter, and units at prepared types only. No edge-invariance
or partitionability assumption is added. -/
theorem preparedClauseFour_of_preparedSeeds {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (hseed : ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ) :
    PreparedClauseFour W T A := by
  intro τ hτ
  have hne : τ ≠ 0 := by
    intro hzero
    have hsign := preparedType_sign_one W T hmS hτ
    rw [hzero, map_zero] at hsign
    exact zero_ne_one hsign
  obtain ⟨Γ₀, hmin, htot, _, hpart⟩ :=
    negative_partitionable (hA τ) (hoff τ) hne (hseed τ hτ)
  exact ⟨fun Δ hΔ => negative_unitSeed_nonempty (hoff τ) hne hΔ,
    Γ₀, hmin, htot, fun Δ hΔ hV ht => minSeed_bits_irrelevant (hA τ) hmin hΔ hV ht, hpart⟩

/-- The faithful fourth clause supplies exactly the seed argument of
`auxFactor_of_prepared`, with no extra hypothesis and no change of type data. -/
theorem preparedSeedInput_of_clauseFour {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (A : L → Config L → ZMod 2)
    (h4 : PreparedClauseFour W T A) :
    ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ := by
  intro τ hτ
  obtain ⟨_, Γ₀, hmin, _, _, _⟩ := h4 τ hτ
  exact ⟨Γ₀, hmin.1⟩

/-- The prepared fourth clause is proved from the separated coefficient-source
ingredients. The least depth, nonempty minimum seeds, independence of bits and
anchor contraction are all conclusions, not additional leaves. -/
theorem preparedClauseFour_of_evenSourceInput {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (hsrc : PreparedEvenSourceInput W T A) : PreparedClauseFour W T A :=
  preparedClauseFour_of_preparedSeeds W T hmS A hA hoff
    (preparedSeedInput_of_evenSourceInput W T A hsrc)

/-- Direct integration: replacing the fourth input by the faithful prepared
clause produces the existing auxiliary factor. The other inputs are unchanged. -/
theorem auxFactor_of_clauseFour {ℓ : ℕ} (W : WData ℓ)
    (hS : ∀ p ∈ W.S, p.Prime) (hS2 : 2 ∈ W.S) [Fintype L]
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (h4 : PreparedClauseFour W T A)
    (hspec : ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) →
      IsPartitionable ε (A (primeConfig d.natAbs.primeFactors T.typ).total)
        (primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d) :
    ∃ A₀ : ℕ, AuxFactor W A₀ :=
  auxFactor_of_prepared W hS hS2 T hmS A hA hoff
    (preparedSeedInput_of_clauseFour W T A h4) hspec

end ZInQ.Contrib.RC53Assist.AuxFactor
