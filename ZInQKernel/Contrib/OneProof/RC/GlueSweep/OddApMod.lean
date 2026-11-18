import ZInQKernel.Contrib.OneProof.RC.Odd.Statements
import ZInQKernel.Contrib.OneProof.RC.Odd.Traces
import ZInQKernel.Contrib.OneProof.RC.KSplit.Ap
import ZInQKernel.Contrib.OneProof.RC.KSplit.TwoPrimary

/-!
# Lane RC22 (glue sweep), odd share: `a_q ≡ q + 1 (mod 4)` for the actual curve

Manuscript (11/5), Appendix F: the odd source uses `a_q ≡ q + 1 (mod 4)` at every good prime
(tex 9558–9569, 9585–9617: "full rational two-torsion"), so that the shell factors have the
parities of (O.9)–(O.11), and `a_p` even in the omission rule (tex 9919–9931).

Lane RC12 takes this as the field `ap_mod` of `SourceHyp` (hence of the ELLIOT statement
`OddStageSource`), for an abstract `ap : ℕ → ℤ`, and as the hypothesis `hap : Even ap` of
`cp_sum_odd`. For the actual curve `y² = x(x − m)(x + 3m)` (`m = ℓ` for `E_ℓ`, `m = Dℓ` for the
twist `E_ℓ^{(D)}`) with `a_q` the Dirichlet coefficient at `q` of Mathlib's `L(E, s)`, it is PROVED
here from lane RC3's `LFunction_curve_apply_prime` (`a_q = q + 1 − #Ẽ(𝔽_q)` at `q ∤ 6m`) and
`four_dvd_card` (the rational two-torsion gives `4 ∣ #Ẽ(𝔽_q)`):

* `ap_mod_four_curve`: `a_q ≡ q + 1 (mod 4)` for every prime `q ∤ 6m`;
* `sourceHyp_curve`, `oddStageSource_curve`: lane RC12's `SourceHyp` / `OddStageSource` at
  `ap := a_·(curve m)` with the fields `prime`, `odd`, `ap_mod` discharged, for good primes avoiding
  `6m` (the fixed support contains `2`, `3` and the primes of `m`);
* `cp_sum_odd_curve`: lane RC12's `cp_sum_odd` with `hap` discharged.

(The companion statement `ApEven` of the coefficient dictionary is the symbols share's
`GlueSweep.Sym.apEven_curve`, by the same route.)
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Odd

/-- **`a_q ≡ q + 1 (mod 4)` for the curve `y² = x(x − m)(x + 3m)`** at every prime `q ∤ 6m`
(tex 9558–9569, 9585–9594). PROVED from lane RC3's `KSplit.LFunction_curve_apply_prime` and
`KSplit.four_dvd_card`. Consumer: the field `ap_mod` of lane RC12's `SourceHyp`. -/
theorem ap_mod_four_curve (m : ℤ) {q : ℕ} (hq : q.Prime) (hq6 : ¬ (q : ℤ) ∣ 6 * m) :
    (ZInQ.Manuscript.curve (m : ℚ)).LFunction q ≡ q + 1 [ZMOD 4] := by
  have := Fact.mk hq
  have hq2 : q ≠ 2 := fun h => hq6 (by rw [h]; exact ⟨3 * m, by push_cast; ring⟩)
  have hq3 : q ≠ 3 := fun h => hq6 (by rw [h]; exact ⟨2 * m, by push_cast; ring⟩)
  have hnd : ∀ r : ℕ, r.Prime → r ≠ q → ((r : ℕ) : ZMod q) ≠ 0 := fun r hr hrq h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hrq ((Nat.prime_dvd_prime_iff_eq hq hr).mp h).symm
  have h2 : (2 : ZMod q) ≠ 0 := by
    have := hnd 2 Nat.prime_two (Ne.symm hq2); exact_mod_cast this
  have h3 : (3 : ZMod q) ≠ 0 := by
    have := hnd 3 Nat.prime_three (Ne.symm hq3); exact_mod_cast this
  have hm0 : ((m : ℤ) : ZMod q) ≠ 0 := fun h =>
    hq6 (Dvd.dvd.mul_left ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h) 6)
  obtain ⟨c, hc⟩ := ZInQ.Manuscript.RC.KSplit.four_dvd_card h2 h3 hm0
  rw [ZInQ.Manuscript.RC.KSplit.LFunction_curve_apply_prime m q hq6, hc]
  refine Int.modEq_iff_dvd.mpr ⟨c, ?_⟩
  push_cast
  ring

/-- **PROVED** (tex 9558–9569: the good primes are odd). A prime `q ∤ 6m` is odd. Discharges the
field `SourceHyp.odd` in `sourceHyp_curve`. -/
theorem odd_of_not_dvd_six_mul {m : ℤ} {q : ℕ} (hq : q.Prime) (hq6 : ¬ (q : ℤ) ∣ 6 * m) :
    Odd (q : ℤ) := by
  have hq2 : q ≠ 2 := fun h => hq6 (by rw [h]; exact ⟨3 * m, by push_cast; ring⟩)
  exact_mod_cast hq.odd_of_ne_two hq2

/-- **Lane RC12's `SourceHyp` at the actual curve, with `prime`, `odd`, `ap_mod` discharged**
(App F, tex 9471–9636). PROVED: for good primes that are primes not dividing `6m`, the
coefficients `a_q` of Mathlib's `L(curve m, s)` satisfy `a_q ≡ q + 1 (mod 4)`
(`ap_mod_four_curve`). Remaining (ELLIOT, the actual theta stage): the recurrence (O.6) `recur`,
`a(0) = 0`, the depth inequality, the multiplicativity of `η`. Consumer: `SourceHyp.ap_mod`
(and `.prime`, `.odd`); discharger: lane RC3's `LFunction_curve_apply_prime`, `four_dvd_card`. -/
theorem sourceHyp_curve {R : Type*} [CommRing R] {T δ : ℕ} {χ : ℕ → R} {GoodPrime : ℕ → Prop}
    {a : ℕ → R} (m : ℤ) (hgood : ∀ q, GoodPrime q → q.Prime ∧ ¬ (q : ℤ) ∣ 6 * m)
    (recur : ∀ q (hq : GoodPrime q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @ZInQ.Manuscript.RC.Odd.RecAt R _ q ⟨(hgood q hq).1⟩ (χ q) ε
        ((ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a)
    (zero : a 0 = 0)
    (depth : ∀ n, (2 : R) ^ (min T (δ + (ZInQ.Manuscript.RC.Odd.oddPart n).card)) ∣ a n)
    (mul : ∀ x y, χ (x * y) = χ x * χ y) (one : χ 1 = 1) :
    ZInQ.Manuscript.RC.Odd.SourceHyp T δ χ GoodPrime
      (fun q => (ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a where
  prime q hq := (hgood q hq).1
  odd q hq := odd_of_not_dvd_six_mul (hgood q hq).1 (hgood q hq).2
  ap_mod q hq := ap_mod_four_curve m (hgood q hq).1 (hgood q hq).2
  recur := recur
  zero := zero
  depth := depth
  mul := mul
  one := one

/-- **Lane RC12's `OddStageSource` at the actual curve** (App F, tex 8409–9100, 9471–9636), with
`prime`, `odd`, `ap_mod` discharged as in `sourceHyp_curve`. PROVED. Consumer:
`Odd.OddStageSource` (hence `Odd.O9_odd_stage`, `Odd.O11_odd_stage`). -/
theorem oddStageSource_curve {M δ : ℕ} {η : ℕ → ZMod (2 ^ M)} {Good : ℕ → Prop}
    {a : ℕ → ZMod (2 ^ M)} (m : ℤ) (hgood : ∀ q, Good q → q.Prime ∧ ¬ (q : ℤ) ∣ 6 * m)
    (recur : ∀ q (hq : Good q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @ZInQ.Manuscript.RC.Odd.RecAt (ZMod (2 ^ M)) _ q ⟨(hgood q hq).1⟩ (η q) ε
        ((ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a)
    (zero : a 0 = 0)
    (depth : ∀ n, (2 : ZMod (2 ^ M)) ^ (min M (δ + (ZInQ.Manuscript.RC.Odd.oddPart n).card)) ∣ a n)
    (mul : ∀ x y, η (x * y) = η x * η y) (one : η 1 = 1) :
    ZInQ.Manuscript.RC.Odd.OddStageSource M δ η Good
      (fun q => (ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a :=
  sourceHyp_curve m hgood recur zero depth mul one

/-- **Lane RC12's `cp_sum_odd` at the actual curve** (tex 9924–9925): `C_p(vr₀) + C_p(vr₁) =
a_p − 1` is odd, with `hap : Even a_p` discharged for `p ∤ 6m` (`ap_mod_four_curve` and lane RC12's
`even_ap`). PROVED. Consumer: `Odd.cp_sum_odd` (hypothesis `hap`). -/
theorem cp_sum_odd_curve (m : ℤ) {p : ℕ} (hp : p.Prime) (hp6 : ¬ (p : ℤ) ∣ 6 * m) {κ₀ : ℤ}
    (hκ : κ₀ = 1 ∨ κ₀ = -1) :
    ZInQ.Manuscript.RC.Odd.Cp ((ZInQ.Manuscript.curve (m : ℚ)).LFunction p) κ₀ +
        ZInQ.Manuscript.RC.Odd.Cp ((ZInQ.Manuscript.curve (m : ℚ)).LFunction p) (-κ₀) =
      (ZInQ.Manuscript.curve (m : ℚ)).LFunction p - 1 ∧
    Odd (ZInQ.Manuscript.RC.Odd.Cp ((ZInQ.Manuscript.curve (m : ℚ)).LFunction p) κ₀ +
        ZInQ.Manuscript.RC.Odd.Cp ((ZInQ.Manuscript.curve (m : ℚ)).LFunction p) (-κ₀)) :=
  ZInQ.Manuscript.RC.Odd.cp_sum_odd
    (ZInQ.Manuscript.RC.Odd.even_ap (odd_of_not_dvd_six_mul hp hp6) (ap_mod_four_curve m hp hp6))
    hκ

end ZInQ.Manuscript.RC.GlueSweep.Odd
