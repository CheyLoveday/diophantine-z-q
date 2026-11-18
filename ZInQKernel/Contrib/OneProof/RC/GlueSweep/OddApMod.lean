import ZInQKernel.Contrib.OneProof.RC.Odd.Statements
import ZInQKernel.Contrib.OneProof.RC.Odd.Traces
import ZInQKernel.Contrib.OneProof.RC.KSplit.Ap
import ZInQKernel.Contrib.OneProof.RC.KSplit.TwoPrimary

/-!
# Lane RC22 (glue sweep), odd share: `a_q ≡ q + 1 (mod 4)` for the actual curve

Manuscript (11/5), Appendix F: the odd source uses `a_q ≡ q + 1 (mod 4)` at every good prime
(tex 9558–9569, 9585–9617: "full rational two-torsion"), so that the shell factors have the
parities of (O.9)–(O.11), and `a_p` even in the omission rule (tex 9919–9931).

Lane RC12 takes this as the field `ap_mod` of `SourceCore` / `SourceHyp` (hence of the ELLIOT
statement `OddStageCore` and of `OddStageSource`), for an abstract `ap : ℕ → ℤ`, and as the
hypothesis `hap : Even ap` of
`cp_sum_odd`. For the actual curve `y² = x(x − m)(x + 3m)` (`m = ℓ` for `E_ℓ`, `m = Dℓ` for the
twist `E_ℓ^{(D)}`) with `a_q` the Dirichlet coefficient at `q` of Mathlib's `L(E, s)`, it is PROVED
here from lane RC3's `LFunction_curve_apply_prime` (`a_q = q + 1 − |Ẽ(𝔽_q)|` at `q ∤ 6m`) and
`four_dvd_card` (the rational two-torsion gives `4 ∣ |Ẽ(𝔽_q)|`):

* `ap_mod_four_curve`: `a_q ≡ q + 1 (mod 4)` for every prime `q ∤ 6m`;
* `sourceCore_curve`, `sourceHyp_curve`, `oddStageCore_curve`, `oddStageSource_curve`: lane RC12's
  `SourceCore` / `SourceHyp` / `OddStageCore` / `OddStageSource` at `ap := a_·(curve m)` with the
  fields `prime`, `odd`, `ap_mod` discharged, for good primes avoiding `6m` (the fixed support
  contains `2`, `3` and the primes of `m`);
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

/-- **Lane RC12's `SourceCore` at the actual curve, with `prime`, `odd`, `ap_mod` discharged**
(App F, tex 9471–9636). PROVED: for good primes that are primes not dividing `6m`, the
coefficients `a_q` of Mathlib's `L(curve m, s)` satisfy `a_q ≡ q + 1 (mod 4)`
(`ap_mod_four_curve`). Remaining (ELLIOT, the actual theta stage): the recurrence (O.6) `recur`,
`a(0) = 0`, the support conditions, the multiplicativity of `η`. Consumer: `SourceCore.ap_mod`
(and `.prime`, `.odd`); discharger: lane RC3's `LFunction_curve_apply_prime`, `four_dvd_card`. -/
theorem sourceCore_curve {R : Type*} [CommRing R] {χ : ℕ → R} {GoodPrime adm : ℕ → Prop}
    {a : ℕ → R} (m : ℤ) (hgood : ∀ q, GoodPrime q → q.Prime ∧ ¬ (q : ℤ) ∣ 6 * m)
    (recur : ∀ q (hq : GoodPrime q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @ZInQ.Manuscript.RC.Odd.RecAt R _ q ⟨(hgood q hq).1⟩ (χ q) ε
        ((ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a)
    (zero : a 0 = 0) (support : ∀ n, (∃ q ∈ n.primeFactors, ¬ GoodPrime q) → a n = 0)
    (support_adm : ∀ D, Squarefree D → ¬ adm D → a D = 0)
    (mul : ∀ x y, χ (x * y) = χ x * χ y) (one : χ 1 = 1) :
    ZInQ.Manuscript.RC.Odd.SourceCore χ GoodPrime adm
      (fun q => (ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a where
  prime q hq := (hgood q hq).1
  odd q hq := odd_of_not_dvd_six_mul (hgood q hq).1 (hgood q hq).2
  ap_mod q hq := ap_mod_four_curve m (hgood q hq).1 (hgood q hq).2
  recur := recur
  zero := zero
  support := support
  support_adm := support_adm
  mul := mul
  one := one

/-- **Lane RC12's `SourceHyp` at the actual curve, with `prime`, `odd`, `ap_mod` discharged**
(App F, tex 9471–9636): `sourceCore_curve` together with the depth inequality at the squarefree
parameters of the stage support (integer depth `δ`, truncation `T`). PROVED. Consumer:
`SourceHyp.ap_mod` (and `.prime`, `.odd`). -/
theorem sourceHyp_curve {R : Type*} [CommRing R] {T : ℕ} {δ : ℤ} {χ : ℕ → R}
    {GoodPrime adm : ℕ → Prop} {a : ℕ → R} (m : ℤ)
    (hgood : ∀ q, GoodPrime q → q.Prime ∧ ¬ (q : ℤ) ∣ 6 * m)
    (recur : ∀ q (hq : GoodPrime q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @ZInQ.Manuscript.RC.Odd.RecAt R _ q ⟨(hgood q hq).1⟩ (χ q) ε
        ((ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a)
    (zero : a 0 = 0) (support : ∀ n, (∃ q ∈ n.primeFactors, ¬ GoodPrime q) → a n = 0)
    (support_adm : ∀ D, Squarefree D → ¬ adm D → a D = 0)
    (depth : ∀ D, Squarefree D → adm D →
      (2 : R) ^ (min (T : ℤ) (δ + ArithmeticFunction.cardDistinctFactors D)).toNat ∣ a D)
    (mul : ∀ x y, χ (x * y) = χ x * χ y) (one : χ 1 = 1) :
    ZInQ.Manuscript.RC.Odd.SourceHyp T δ χ GoodPrime adm
      (fun q => (ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a :=
  { toSourceCore := sourceCore_curve m hgood recur zero support support_adm mul one
    depth := depth }

/-- **Lane RC12's `OddStageCore` at the actual curve** (App F, tex 8409–9100, 9471–9636), with
coefficients in `𝒪/2^M𝒪` and `prime`, `odd`, `ap_mod` discharged as in `sourceCore_curve`. PROVED.
Consumer: `Odd.OddStageCore` (hence, through App G's stage choice `Odd.oddStageSource_eventually`,
`Odd.O9_odd_stage`, `Odd.O11_odd_stage`). -/
theorem oddStageCore_curve {O : Type*} [CommRing O] {M : ℕ}
    {η : ℕ → ZInQ.Manuscript.RC.Odd.StageRing O M} {Good adm : ℕ → Prop}
    {a : ℕ → ZInQ.Manuscript.RC.Odd.StageRing O M} (m : ℤ)
    (hgood : ∀ q, Good q → q.Prime ∧ ¬ (q : ℤ) ∣ 6 * m)
    (recur : ∀ q (hq : Good q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @ZInQ.Manuscript.RC.Odd.RecAt (ZInQ.Manuscript.RC.Odd.StageRing O M) _ q
        ⟨(hgood q hq).1⟩ (η q) ε ((ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a)
    (zero : a 0 = 0) (support : ∀ n, (∃ q ∈ n.primeFactors, ¬ Good q) → a n = 0)
    (support_adm : ∀ D, Squarefree D → ¬ adm D → a D = 0)
    (mul : ∀ x y, η (x * y) = η x * η y) (one : η 1 = 1) :
    ZInQ.Manuscript.RC.Odd.OddStageCore O M η Good adm
      (fun q => (ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a :=
  sourceCore_curve m hgood recur zero support support_adm mul one

/-- **Lane RC12's `OddStageSource` at the actual curve** (App F, tex 8409–9100, 9471–9636; App G,
tex 10208–10227), with coefficients in `𝒪/2^M𝒪` and `prime`, `odd`, `ap_mod` discharged as in
`sourceCore_curve`: a stage valid for the budget `(W_U, R)` with odd minimum `δ_o` (`N_0 + R ≤ M`
and the depth truncated at `N_0 + R`). PROVED. Consumer: `Odd.OddStageSource` (hence
`Odd.O9_odd_stage`, `Odd.O11_odd_stage`); the depth itself is produced by
`Odd.sourceHyp_depth_of_oddMinimumF6` / `Odd.oddStageSource_eventually`. -/
theorem oddStageSource_curve {O : Type*} [CommRing O] {WU R M : ℕ} {δo : ℤ}
    {η : ℕ → ZInQ.Manuscript.RC.Odd.StageRing O M} {Good adm : ℕ → Prop}
    {a : ℕ → ZInQ.Manuscript.RC.Odd.StageRing O M} (m : ℤ)
    (hgood : ∀ q, Good q → q.Prime ∧ ¬ (q : ℤ) ∣ 6 * m)
    (recur : ∀ q (hq : Good q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @ZInQ.Manuscript.RC.Odd.RecAt (ZInQ.Manuscript.RC.Odd.StageRing O M) _ q
        ⟨(hgood q hq).1⟩ (η q) ε ((ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a)
    (zero : a 0 = 0) (support : ∀ n, (∃ q ∈ n.primeFactors, ¬ Good q) → a n = 0)
    (support_adm : ∀ D, Squarefree D → ¬ adm D → a D = 0)
    (hM : ZInQ.Manuscript.RC.Odd.budgetLevel δo WU R ≤ M)
    (depth : ∀ D, Squarefree D → adm D →
      (2 : ZInQ.Manuscript.RC.Odd.StageRing O M) ^
        (min ((ZInQ.Manuscript.RC.Odd.budgetLevel δo WU R : ℕ) : ℤ)
          (δo + ArithmeticFunction.cardDistinctFactors D)).toNat ∣ a D)
    (mul : ∀ x y, η (x * y) = η x * η y) (one : η 1 = 1) :
    ZInQ.Manuscript.RC.Odd.OddStageSource O WU R M δo η Good adm
      (fun q => (ZInQ.Manuscript.curve (m : ℚ)).LFunction q) a :=
  ⟨hM, sourceHyp_curve m hgood recur zero support support_adm depth mul one⟩

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
