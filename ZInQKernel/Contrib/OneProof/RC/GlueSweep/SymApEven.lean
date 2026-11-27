import ZInQKernel.Contrib.OneProof.RC.GlueSweep.SymRules
import ZInQKernel.Contrib.OneProof.RC.KSplit.Seed

/-!
# Lane RC22 (glue sweep, symbols): the GLUE `ApEven` of the coefficient dictionary, PROVED

The coefficient dictionary of the shared top layer (`CoefficientDictionary/Rules.lean`) takes the
GLUE

`ApEven T ap : ∀ p, T.Good p → Even (ap p)`

(tex 9585, 9593: "`a_p ≡ p + 1 (mod 4)` for every good prime, all of `E[2]` being rational") as a
hypothesis of `coefficientRules_symb`, `rulesUpTo_symb`, `coefficientRules_of_model` and
`TraceModel.rulesUpTo_of_model` (and a field of `RC12Readings`, `SymRules.lean`). For the actual curve `y² = x(x − m)(x + 3m)` (`m = ℓ` for `E_ℓ`,
`m = kℓ` for `E^{(k)}`) and `a_p` the Dirichlet coefficient at `p` of Mathlib's `L(E, s)`, it is
PROVED here from lane RC3's results: `LFunction_curve_apply_prime` (`a_p = p + 1 − #Ẽ(𝔽_p)` at
`p ∤ 6m`) and `four_dvd_card` (full rational two-torsion gives `4 ∣ #Ẽ(𝔽_p)`), for type data whose
good primes avoid `6m` (the fixed support contains `2`, `3` and the primes of `m`).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Sym

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **`a_p` of the curve is even at every good prime** (the GLUE `ApEven` of the coefficient
dictionary, tex 9585, 9593–9594 and 10475–10476: "full rational two-torsion gives
`a_p ≡ p + 1 (mod 4)`"; `p` is odd). Here `a_p` is the coefficient at `p` of Mathlib's
`L(curve m, s)`. Kind: PROVED, from: the good primes of `T` do not divide `6m`. Consumer: the
hypothesis `hap : ApEven T ap` of `CoefficientDictionary.coefficientRules_symb`,
`rulesUpTo_symb`, `coefficientRules_of_model`, `TraceModel.rulesUpTo_of_model`; dischargers:
lane RC3's `LFunction_curve_apply_prime` and `four_dvd_card`. -/
theorem apEven_curve (T : TypeData L ε) (m : ℤ) (hT : ∀ p, T.Good p → ¬ (p : ℤ) ∣ 6 * m) :
    ApEven T (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) := by
  intro p hp
  have hp6 := hT p hp
  have hpp : p.Prime := hp.1
  have := Fact.mk hpp
  have hp2 : p ≠ 2 := fun h => hp6 (by rw [h]; exact ⟨3 * m, by push_cast; ring⟩)
  have hp3 : p ≠ 3 := fun h => hp6 (by rw [h]; exact ⟨2 * m, by push_cast; ring⟩)
  have hnd : ∀ q : ℕ, q.Prime → q ≠ p → ((q : ℕ) : ZMod p) ≠ 0 := fun q hq hqp h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).mp h).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := hnd 2 Nat.prime_two (Ne.symm hp2); exact_mod_cast this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := hnd 3 Nat.prime_three (Ne.symm hp3); exact_mod_cast this
  have hm0 : ((m : ℤ) : ZMod p) ≠ 0 := fun h =>
    hp6 (Dvd.dvd.mul_left ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h) 6)
  have h4card := ZInQ.Manuscript.RC.KSplit.four_dvd_card h2 h3 hm0
  show Even ((ZInQ.Manuscript.curve (m : ℚ)).LFunction p)
  rw [ZInQ.Manuscript.RC.KSplit.LFunction_curve_apply_prime m p hp6]
  obtain ⟨c, hc⟩ := h4card
  obtain ⟨j, hj⟩ := hpp.odd_of_ne_two hp2
  refine ⟨(j : ℤ) + 1 - 2 * c, ?_⟩
  rw [hc, hj]
  push_cast
  ring

/-- A sufficient condition for `apEven_curve`: the conductor of the type data is divisible by
`6m` (the fixed support of the types contains `2`, `3` and the primes of `m`, tex 2015–2030).
Kind: PROVED. -/
theorem good_not_dvd_of_dvd_conductor (T : TypeData L ε) {m : ℤ} (hm : (6 * m).natAbs ∣ T.m) :
    ∀ p, T.Good p → ¬ (p : ℤ) ∣ 6 * m := by
  intro p hp hdvd
  have h1 : p ∣ (6 * m).natAbs := Int.natCast_dvd.mp hdvd
  have h2 : p ∣ T.m := h1.trans hm
  have h3 : p ∣ Nat.gcd p T.m := Nat.dvd_gcd dvd_rfl h2
  rw [hp.2] at h3
  exact hp.1.one_lt.ne' (Nat.dvd_one.mp h3)

/-- **Lane RC12's readings with `a_p` of the actual curve** (the bundle `RC12Readings` of
`SymRules.lean`, i.e. the hypotheses of `CoefficientDictionary.coefficientRules_symb`), with the
GLUE `ApEven` discharged by `apEven_curve`. Kind: PROVED, from: the readings on prime sets
(fixed-`U` factorization, (O.12) at coefficient one with `a_p` of `curve m`, primary isolation) at
every budget, and good primes prime to `6m`. -/
theorem rc12Readings_curve {T : TypeData L ε} {R : Finset ℕ → ZMod 2} (m : ℤ)
    (hswap : ∀ B, FixedUFactorization T R B)
    (hO12 : ∀ B, O12Reading T R (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) B)
    (hprim : ∀ B, PrimaryReading T R B) (hT : ∀ p, T.Good p → ¬ (p : ℤ) ∣ 6 * m) :
    RC12Readings T R (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) :=
  ⟨hswap, hO12, apEven_curve T m hT, hprim⟩

/-- **The coefficient rules of the actual symbol, for the actual curve** (Lemma
`ex:sec7-coefficient-rules`, tex 2102–2136; App F `ex:app-coefficient-rules`, tex 9884–9976),
with `a_p` the coefficient of Mathlib's `L(curve m, s)`: the GLUE `ApEven` is discharged by
`apEven_curve`. Kind: PROVED, from: lane RC12's readings at every budget with this `a_p`, and good
primes prime to `6m`. Consumer: lane RC2's `CoefficientRules`; discharger:
`CoefficientDictionary.coefficientRules_symb` with `apEven_curve`. -/
theorem coefficientRules_symb_curve {T : TypeData L ε} {R : Finset ℕ → ZMod 2} (m : ℤ)
    (hswap : ∀ B, FixedUFactorization T R B)
    (hO12 : ∀ B, O12Reading T R (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) B)
    (hprim : ∀ B, PrimaryReading T R B) (hT : ∀ p, T.Good p → ¬ (p : ℤ) ∣ 6 * m) :
    CoefficientRules ε (symb T R) :=
  (rc12Readings_curve m hswap hO12 hprim hT).rules

/-- **The stage rules of an actual stage symbol, for the actual curve** (tex 10533–10538):
`CoefficientDictionary.rulesUpTo_symb` with the GLUE `ApEven` discharged by `apEven_curve`.
Kind: PROVED, from: lane RC12's stage readings at budget `W + 1` with `a_p` of `curve m`, and good
primes prime to `6m`. Consumer: lane RC2's `RulesUpTo` (hypothesis `hvalid` of
`odd_stabilization`); discharger: `CoefficientDictionary.rulesUpTo_symb`. -/
theorem rulesUpTo_symb_curve {T : TypeData L ε} {R : Finset ℕ → ZMod 2} (m : ℤ) {W : ℕ}
    (hswap : FixedUFactorization T R (W + 1))
    (hO12 : O12Reading T R (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) (W + 1))
    (hprim : PrimaryReading T R (W + 1)) (hT : ∀ p, T.Good p → ¬ (p : ℤ) ∣ 6 * m) :
    RulesUpTo ε (symb T R) W :=
  rulesUpTo_symb T R _ W hswap hO12 (apEven_curve T m hT) hprim

end ZInQ.Manuscript.RC.GlueSweep.Sym
