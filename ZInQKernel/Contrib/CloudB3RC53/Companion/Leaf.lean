import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves

/-!
# The final companion, part 2: the level primes split, and RC0's `CompanionLeaf`

Manuscript `diophantine_zq.tex`, "Fixing the final companion" (tex L2595–2603): "Use a separate
even symbol on negative discriminants square at `2N`, excluding the fixed odd support, the
ramification support of `E[8]`, and the exceptional imaginary fields. Choose a unit `k` of this
symbol. Then `L(E^{(k)},1) ≠ 0`." RC0's leaf `ZInQ.Manuscript.RC.Wiring.CompanionLeaf`
(`RC/Wiring/Leaves.lean`) records the properties of `k` the deduction uses.

* `levelPrimes_split_rc`: from RC0's companion conditions (`RCSteps.companion` /
  `CompanionTarget`: `k < 0`, squarefree, `k ≡ 1 mod 4`, `UnitSquareAt p k` at the primes of
  `2N`), every prime of the level splits in any quadratic field containing `√k`, and
  `disc ℚ(√k) = k` (PROVED, from `Companion.levelPrimes_split` and `splittingCriterion_proof`).
* `exists_companion`: a `k` with every recorded property of `CompanionLeaf` except membership of
  its primes in the fixed support (PROVED from lane RC13's `genusPartner`, i.e. from the printed
  leaves Hoffstein–Luo, BFH's twist sign and BCDT, with `w(E_ℓ) = −1`, a base support `S ⊇ {2, 3} ∪
  primes(ℓ) ∪ primes(N)` and avoidance of the primes of `h_*`);
* `companionLeaf_of`: `CompanionLeaf W` for data whose `kfin` is such a `k` and whose support
  contains the primes of `k` (the support is enlarged by the primes of `k` after `k` is fixed,
  tex L2600–2603: "Fix `k` and `K = ℚ(√k)` … The added stationary tests at the primes of `k`").

DEPARTURE (recorded): Elliot chooses `k` as a *unit* of the separate even symbol; `CompanionLeaf`
records only the consequences used by the deduction (`L(E^{(k)},1) ≠ 0` and the local conditions),
and these are supplied here directly by the nonvanishing theorem (`genusPartner`), as in the text's
step "Then `L(E^{(k)},1) ≠ 0`". If another leaf (e.g. the address input) uses the unit property of
`k` itself, it is not supplied by this file.
-/

noncomputable section

open NumberField

namespace ZInQ.Contrib.CloudB3RC53.Companion

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Nonvanishing

/-! ### Every level prime splits in `ℚ(√k)` -/

/-- **The level primes split in `ℚ(√kfin)`, from RC0's companion conditions** (PROVED): for a
quadratic field `K` containing a square root of `kfin`, with `kfin < 0`, `kfin % 4 = 1`,
`Squarefree kfin` and `UnitSquareAt p kfin` at every prime `p ∣ 2N` (the conditions in
`RCSteps.companion` and `CompanionLeaf`): `disc K = kfin` and every prime of `N` splits in `K`. -/
theorem levelPrimes_split_rc {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {kfin : ℤ} (hk0 : kfin < 0) (hk4 : kfin % 4 = 1)
    (hksq : Squarefree kfin) {N : ℕ} (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * N → UnitSquareAt p kfin)
    {s : K} (hs : s ^ 2 = kfin) :
    discr K = kfin ∧ ∀ p : ℕ, p.Prime → p ∣ N → CST.SplitsIn K p :=
  levelPrimes_split hK hk0 hk4 hksq (fun p hp hpN => hk2N p hp hpN) hs

/-! ### A square of `ℚ_p` prime to `p` is a square modulo `p` -/

theorem isSquare_zmod_of_isSquareAt {p : ℕ} [hp : Fact p.Prime] {k : ℤ}
    (h : IsSquareAt p (k : ℚ)) : IsSquare (k : ZMod p) := by
  obtain ⟨x, hx⟩ := h hp
  have hk1 : ‖((k : ℚ) : ℚ_[p])‖ ≤ 1 := by
    rw [show (((k : ℚ) : ℚ_[p])) = ((k : ℤ) : ℚ_[p]) by push_cast; rfl]
    exact Padic.norm_int_le_one k
  have hx1 : ‖x‖ ≤ 1 := by
    have : ‖x‖ * ‖x‖ ≤ 1 := by rw [← norm_mul, ← hx]; exact hk1
    nlinarith [norm_nonneg x]
  let y : ℤ_[p] := ⟨x, hx1⟩
  have hy : y * y = (k : ℤ_[p]) := by
    apply Subtype.ext
    change x * x = ((k : ℤ_[p]) : ℚ_[p])
    rw [← hx, PadicInt.coe_intCast]
    push_cast; rfl
  refine ⟨PadicInt.toZMod y, ?_⟩
  rw [← map_mul, hy, map_intCast]

/-! ### The final companion -/

/-- **A final companion** (tex L2595–2603; PROVED from lane RC13's `genusPartner`): with
`w(E_ℓ) = −1` and a base support `S ⊇ {2, 3} ∪ primes(ℓ)` containing the primes of the level, for
`h_* ≠ 0` there is `k < 0`, squarefree, `≠ −1, −3`, `k ≡ 1 (mod 4)`, a unit square at every prime of
`2N`, prime to `h_*` and to `S`, with `L(E^{(k)}, 1) ≠ 0`. -/
theorem exists_companion (hHL : HoffsteinLuo) (hTS : BFHTwistSign)
    (hBCDT : ZInQ.Manuscript.PoleS12.BCDTThmA) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hw : ZInQ.Contrib.CloudB3RC53.RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S)
    (hlevel : ∀ p : ℕ, p.Prime → p ∣ CST.newformLevel (Ecurve ℓ) → p ∈ S)
    {hstar : ℤ} (hstar0 : hstar ≠ 0) :
    ∃ k : ℤ, k < 0 ∧ Squarefree k ∧ k ≠ -1 ∧ k ≠ -3 ∧ k % 4 = 1 ∧
      (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p k) ∧
      IsCoprime k hstar ∧ AnalyticRank (Etw ℓ k) 0 ∧ (∀ p ∈ S, ¬ (p : ℤ) ∣ k) := by
  obtain ⟨k, hk0, hk8, hkF, hkS, hkB, -, hkL⟩ :=
    genusPartner hHL hTS hBCDT hℓ hw hS h2 h3 hℓS hstar.natAbs.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hodd : Odd k := ⟨k / 2, by omega⟩
  obtain ⟨hksq, hk4⟩ := hkF.squarefree_of_odd hodd
  refine ⟨k, hk0, hksq, by omega, by omega, hk4, fun p hp hpd => ?_, ?_, ?_,
    fun p hp => (hkS p hp).2⟩
  · -- a unit square at the primes of `2N`
    have hpS : p ∈ S := by
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]; exact h2
      · exact hlevel p hp h
    refine ⟨(hkS p hpS).2, fun hp2 => hk8, fun hp2 => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    exact isSquare_zmod_of_isSquareAt (hkS p hpS).1
  · -- prime to `h_*`
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    refine Nat.coprime_of_dvd fun p hp hpk hph => ?_
    have hmem : p ∈ hstar.natAbs.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hph, Int.natAbs_ne_zero.mpr hstar0⟩
    exact hkB p hmem (Int.natCast_dvd.mpr hpk)
  · -- `L(E^{(k)}, 1) ≠ 0`
    rw [Etw, qtwist_Ecurve]
    exact hkL

/-- **RC0's `CompanionLeaf`** for data whose final companion `kfin` has the properties of
`exists_companion` and whose fixed support contains the primes of `kfin` (PROVED; the
normalization `LstarTarget` converts `L(E^{(k)}, 1) ≠ 0` into `L_*(k) ≠ 0`). -/
theorem companionLeaf_of {ℓ : ℕ} (W : WData ℓ) (hL : LstarTarget W.toRCData)
    (hk : W.kfin < 0 ∧ Squarefree W.kfin ∧ W.kfin ≠ -1 ∧ W.kfin ≠ -3 ∧ W.kfin % 4 = 1 ∧
      (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin) ∧
      IsCoprime W.kfin W.hstar ∧ AnalyticRank (Etw ℓ W.kfin) 0)
    (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.kfin → p ∈ W.S) : CompanionLeaf W := by
  intro _
  obtain ⟨hk0, hksq, h1, h3, hk4, h2N, hcop, hL0⟩ := hk
  exact ⟨hk0, hksq, h1, h3, hS, hk4, h2N, hcop, (hL _ hk0.ne).mpr hL0⟩

end ZInQ.Contrib.CloudB3RC53.Companion
