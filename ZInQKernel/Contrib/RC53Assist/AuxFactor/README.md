# Prepared negative-type clause 4: verification record

Result: final single-file compilation succeeded with exit code 0 and no warnings.
The dependency build had completed before compilation. All nine declarations
below were checked, and every axiom report contains only the standard three
axioms propext, Classical.choice, and Quot.sound.

Scope: this is a proved combinatorial clause and a conditional reduction of its
prepared-seed input to PreparedEvenSourceInput. It is not an unconditional
construction of the actual even forms or a proof of seeds at all total types.

Remaining source obligation, for each PreparedType W T tau, fixed before h:
1. the original negative coefficient filter consists of positive squarefree
   indices seven modulo eight, good at the type conductor, with total tau;
2. the actual phase-normalized coefficients have a nonzero retained reference;
3. their valuation minus the prime-factor count has an integer lower bound;
4. A tau is the reading of that same source at its least normalized depth.
The attained minimum, nonempty minimum seeds, independence of internal bits,
and anchor contraction are proved, not remaining inputs. The lower-bound
arithmetic is proved from (E.9) and (E.11); the reading identity is proved by the
dictionary when A is its actual normalized source symbol. No new printed leaf
is introduced. The reference/source construction is the Appendix E obligation
at lines 7793--7810, not an assumed nonvanishing theorem for unprepared filters.

The literal phrase "every total type" at lines 10131--10132 is not proved.
PreparedClauseFour formalizes its use for the prepared negative sources of
lines 10057, 10096--10105, and 10139. A type's sign coordinate is not the curve's
root number.

Exact compiler output follows.

leastCoefficientDepth_exists : ∀ (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (c : ℤ),
  (∃ D, F D ∧ a D ≠ 0) →
    (∀ (D : ℕ), F D → a D ≠ 0 → c ≤ (a D).valuation - ↑(#D.primeFactors)) → ∃ δ, LeastCoefficientDepth a F δ
coefficientDepth_lowerBound_of_E9_E11 : ∀ (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (vL : ℕ → ℤ) (κ C : ℤ),
  (∀ (D : ℕ), F D → a D ≠ 0 → vL D = 2 * (a D).valuation + κ) →
    (∀ (D : ℕ), F D → a D ≠ 0 → 2 * ↑(#D.primeFactors) + C ≤ vL D) →
      ∀ (D : ℕ), F D → a D ≠ 0 → (C - κ) / 2 ≤ (a D).valuation - ↑(#D.primeFactors)
@normalizedPrimeReading_of_dictionary : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε)
  (τ : L) (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ),
  NegativeCoefficientFilter T τ F →
    (∀ (B : ℕ), FixedUFactorization T (coeffReading a δ F) B) →
      NormalizedPrimeReading T (symb T (coeffReading a δ F)) a F δ
@preparedSeedInput_of_evenSourceInput : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} {ℓ : ℕ} (W : WData ℓ)
  (T : TypeData L ε) (A : L → Config L → ZMod 2),
  PreparedEvenSourceInput W T A → ∀ (τ : L), PreparedType W T τ → ∃ Γ, IsUnitSeed ε (A τ) Γ
@preparedType_sign_one : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} {ℓ : ℕ} (W : WData ℓ)
  (T : TypeData L ε), (∀ (p : ℕ), Nat.Prime p → p ∣ T.m → p ∈ W.S) → ∀ {τ : L}, PreparedType W T τ → ε τ = 1
@preparedClauseFour_of_preparedSeeds : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} {ℓ : ℕ} (W : WData ℓ)
  (T : TypeData L ε),
  (∀ (p : ℕ), Nat.Prime p → p ∣ T.m → p ∈ W.S) →
    ∀ (A : L → Config L → ZMod 2),
      (∀ (τ : L), CoefficientRules ε (A τ)) →
        (∀ (τ : L), VanishesOffFilter (A τ) τ) →
          (∀ (τ : L), PreparedType W T τ → ∃ Γ, IsUnitSeed ε (A τ) Γ) → PreparedClauseFour W T A
@preparedSeedInput_of_clauseFour : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} {ℓ : ℕ} (W : WData ℓ)
  (T : TypeData L ε) (A : L → Config L → ZMod 2),
  PreparedClauseFour W T A → ∀ (τ : L), PreparedType W T τ → ∃ Γ, IsUnitSeed ε (A τ) Γ
@preparedClauseFour_of_evenSourceInput : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} {ℓ : ℕ} (W : WData ℓ)
  (T : TypeData L ε),
  (∀ (p : ℕ), Nat.Prime p → p ∣ T.m → p ∈ W.S) →
    ∀ (A : L → Config L → ZMod 2),
      (∀ (τ : L), CoefficientRules ε (A τ)) →
        (∀ (τ : L), VanishesOffFilter (A τ) τ) → PreparedEvenSourceInput W T A → PreparedClauseFour W T A
@auxFactor_of_clauseFour : ∀ {L : Type} [inst : AddCommGroup L] {ε : L →+ ZMod 2} {ℓ : ℕ} (W : WData ℓ),
  (∀ p ∈ W.S, Nat.Prime p) →
    2 ∈ W.S →
      ∀ [Fintype L] (T : TypeData L ε),
        (∀ (p : ℕ), Nat.Prime p → p ∣ T.m → p ∈ W.S) →
          ∀ (A : L → Config L → ZMod 2),
            (∀ (τ : L), CoefficientRules ε (A τ)) →
              (∀ (τ : L), VanishesOffFilter (A τ) τ) →
                PreparedClauseFour W T A →
                  (∀ d < 0,
                      Squarefree d →
                        (∀ p ∈ W.S, ¬↑p ∣ d) →
                          IsPartitionable ε (A (primeConfig d.natAbs.primeFactors T.typ).total)
                              (primeConfig d.natAbs.primeFactors T.typ) →
                            W.Partitionable d) →
                    ∃ A₀, AuxFactor W A₀
'ZInQ.Contrib.RC53Assist.AuxFactor.leastCoefficientDepth_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.coefficientDepth_lowerBound_of_E9_E11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.normalizedPrimeReading_of_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.preparedSeedInput_of_evenSourceInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.preparedType_sign_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.preparedClauseFour_of_preparedSeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.preparedSeedInput_of_clauseFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.preparedClauseFour_of_evenSourceInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.RC53Assist.AuxFactor.auxFactor_of_clauseFour' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit code: 0]
