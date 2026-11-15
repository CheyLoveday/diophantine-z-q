import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.TYZChain.Lcal

/-!
# h29-split: `TYZLemma29Mod2` against TYZ Lemma 2.9 and Proposition 2.3 in printed form

Report: `docs/research/h29-split.md`. Results log: `scratch/h29-split/log.md`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1,
Asian J. Math. 21 (2017). Line numbers `Lnnnn` refer to the arXiv source `Period7.tex`. That source is
not on this host, so the statements below are QUOTED from `docs/research/nt-tyz.md` §1.2 (which
read them in the source), `rv-nt-tyz.md` (row I2, finding B1) and `rv-tyz-inputs.md` §1.2.

* **Lemma 2.9** (L1062–1066; §2 assumes `n ≡ 1, 2, 3 (mod 8)` positive squarefree, L499):
  `Σ ε(d₁, d₂) 𝓛(d₁)𝓛(d₂) = Q(n)` with `ε(d₁, d₂) = ±1`, over the non-ordered decompositions
  `n = d₁d₂` with `d₁, d₂ > 0` and `d₂ ≡ 1 (mod 8)`.
* **Proposition 2.3** (L580–586): `f_n((B̂^×)²) ⊂ 1 + 2ℤ`; therefore `Q(n) ≡ g(n) (mod 2)`.

Here `Q(n)` is TYZ's genus period, `Σ_{t ∈ 2Cl_n} f_n(t)`: `f_n` is TYZ's test vector (§2.2,
Theorems 2.4 and 2.6), a function on `B^× \ B̂^×` (`B` the quaternion algebra over `ℚ` ramified at
`2, ∞`) restricted along an embedding `K_n = ℚ(√−n) → B`. It is left `K^×`-invariant and right
`Ô_K^×`-invariant on `K̂^×`, so its restriction is a function on `Cl_n = Cl(𝓞_{K_n})`
(`scratch/rv-tyz-inputs/log.md`, Step 1: "left `K^×`, right `Ô_K^× ⊂ U_n`, centre").

Layout.
* §1 The printed forms, with the genus period as a parameter: `Lemma29Printed Q`,
  `Prop23Cong Q` (the conclusion of Prop. 2.3) and, over Mathlib's class group, `Prop23Odd f`
  (its first assertion, restricted to `K̂^×`) with `genusPeriod f`.
* §2 Glue (proved): the "therefore" of Prop. 2.3 (`genusPeriod_mod_two`), and the mod-2 reduction
  `tyzLemma29Mod2_of_printed : Lemma29Printed Q → Prop23Cong Q → TYZLemma29Mod2`, for every `Q`.
* §3 Inertness (proved): with `Q` (or `f`) not pinned, the printed pair is equivalent to the target
  (`exists_printedQ_iff`, `exists_printedF_iff`). So the split is not a split into leaves until TYZ's
  test vector `f_n` is a Lean definition.
* §4 The alternative printed leaf `TYZThm11Mod2` (TYZ Theorem 1.1, congruence): given
  `TYZThm11Integral` (the field `h11` of `frozenTarget`) it is equivalent to the target.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H29Split

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp NumberField

/-! ## §1. The printed forms -/

/-- `ℓ` is a sign choice of TYZ's `𝓛` on the squarefree classes `1, 3 (mod 8)`; this is the
hypothesis on `ℓ` in `TYZLemma29Mod2`. -/
def IsLcalSign (ℓ : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m

theorem tyzLemma29Mod2_iff_forall : TYZLemma29Mod2 ↔ ∀ ℓ, IsLcalSign ℓ → LemmaTwoEight ℓ :=
  Iff.rfl

/-- The non-ordered decompositions `m = d₁d₂` with `d₂ ≡ 1 (mod 8)` of an odd squarefree `m > 1`,
indexed by one member `d`. For `m ≡ 3`, `d = d₂` (the other factor is `≡ 3`, so the pair is
determined by `d₂`). For `m ≡ 1`, both factors are `≡ 1` and `d ≠ m/d`; the pair `{d, m/d}` is
indexed by its smaller member (`d² < m`). -/
def pairIdx (m : ℕ) : Finset ℕ :=
  m.divisors.filter (fun d => d % 8 = 1 ∧ (m % 8 = 1 → d * d < m))

/-- **TYZ Lemma 2.9 (L1062–1066), printed form, odd classes, with the genus period `Q` as a
parameter.** For every sign choice `ℓ` of `𝓛` and squarefree `1 < m ≡ 1, 3 (mod 8)` there are signs
`ε = ±1` with `w · Σ_{m = d₁d₂, d₂ ≡ 1} ε 𝓛(d₁)𝓛(d₂) = Q(m)`, where `w = 1`, or `w = 3 = w_K` at
`m = 3`.

The factor `w`: TYZ's proof gives `w_K Σ ε𝓛𝓛 = Q(m)` with `w_K = [𝓞_K^× : {±1}]`, which is `3` for
`ℚ(√−3)` and `1` for the other `ℚ(√−m)`, `m > 1` odd squarefree (rv-nt-tyz B1, confirmed by
rv-tyz-inputs §1.2; it is not decided whether Lemma 2.9 or Theorem 2.1 is misprinted). The
disjunction is implied by the printed lemma (`w = 1`) and by the corrected one. Restricting to odd
`m > 1` and quantifying over all sign choices `ℓ` (a sign change of `ℓ` is absorbed by `ε`) also
weakens or preserves the print. -/
def Lemma29Printed (Q : ℕ → ℤ) : Prop :=
  ∀ ℓ : ℕ → ℤ, IsLcalSign ℓ → ∀ m : ℕ, Squarefree m → 1 < m → (m % 8 = 1 ∨ m % 8 = 3) →
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧ ∃ w : ℤ, (w = 1 ∨ (m = 3 ∧ w = 3)) ∧
      w * ∑ d ∈ pairIdx m, ε d * (ℓ (m / d) * ℓ d) = Q m

/-- **TYZ Proposition 2.3 (L580–586), conclusion, odd classes, with `Q` as a parameter**:
`Q(m) ≡ g(m) (mod 2)`, `g(m) = #2Cl(ℚ(√−m))` (`gNat`, TYZ L363). -/
def Prop23Cong (Q : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((Q m : ℤ) : ZMod 2) = (gNat m : ZMod 2)

/-- A family of integer functions on the class groups `Cl(𝓞_{ℚ(√−n)})`, `n ≠ 0` (the type of the
restriction of TYZ's test vectors `f_n` to `K̂_n^×`). -/
abbrev ClFun : Type := ∀ (n : ℕ) [NeZero n], ClassGroup (𝓞 (QNeg n)) → ℤ

/-- The subgroup `2Cl_n` of squares, as a finset. -/
def sqClasses (n : ℕ) [NeZero n] : Finset (ClassGroup (𝓞 (QNeg n))) := by
  classical
  exact Finset.univ.filter
    (fun t => t ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range)

/-- The genus period `Q_f(n) = Σ_{t ∈ 2Cl_n} f_n(t)` (`0` at `n = 0`). -/
def genusPeriod (f : ClFun) (n : ℕ) : ℤ :=
  if h : n = 0 then 0 else haveI : NeZero n := ⟨h⟩; ∑ t ∈ sqClasses n, f n t

/-- **TYZ Proposition 2.3 (L580–586), first assertion, restricted to `K̂^×` (odd classes)**: `f_n` takes
odd values on `2Cl_n`. (Printed: `f_n((B̂^×)²) ⊂ 1 + 2ℤ`; a class `t ∈ 2Cl_n` is `s²` up to `K^×` and
`Ô_K^×`, under which `f_n` is invariant, so the printed assertion gives this one.) -/
def Prop23Odd (f : ClFun) : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ t ∈ sqClasses n, Odd (f n t)

/-! ## §2. Glue -/

theorem mem_sqClasses {n : ℕ} [NeZero n] {t : ClassGroup (𝓞 (QNeg n))} :
    t ∈ sqClasses n ↔
      t ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range := by
  classical
  simp [sqClasses]

theorem one_mem_sqClasses (n : ℕ) [NeZero n] : (1 : ClassGroup (𝓞 (QNeg n))) ∈ sqClasses n :=
  mem_sqClasses.mpr (Subgroup.one_mem _)

/-- `#2Cl_n = g(n)`. -/
theorem card_sqClasses (n : ℕ) [NeZero n] : (sqClasses n).card = gCl n := by
  rw [gCl, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_sqClasses)

theorem gNat_of_ne {n : ℕ} [NeZero n] : gNat n = gCl n := by
  simp [gNat, NeZero.ne n]

theorem genusPeriod_of_ne (f : ClFun) {n : ℕ} [NeZero n] :
    genusPeriod f n = ∑ t ∈ sqClasses n, f n t := by
  simp [genusPeriod, NeZero.ne n]

theorem intCast_eq_one_of_odd {a : ℤ} (h : Odd a) : ((a : ℤ) : ZMod 2) = 1 :=
  ZMod.intCast_eq_one_iff_odd.mpr h

/-- **The "therefore" of Proposition 2.3**: odd values on `2Cl_n` give `Q(n) ≡ #2Cl_n = g(n)`. -/
theorem genusPeriod_mod_two (f : ClFun) {n : ℕ} [NeZero n]
    (hf : ∀ t ∈ sqClasses n, Odd (f n t)) :
    ((genusPeriod f n : ℤ) : ZMod 2) = (gNat n : ZMod 2) := by
  rw [genusPeriod_of_ne, gNat_of_ne, ← card_sqClasses]
  push_cast
  rw [Finset.sum_congr rfl fun t ht => intCast_eq_one_of_odd (hf t ht)]
  simp

theorem prop23Cong_of_odd {f : ClFun} (h : Prop23Odd f) : Prop23Cong (genusPeriod f) := by
  intro m hsq hcl
  have : NeZero m := ⟨hsq.ne_zero⟩
  exact genusPeriod_mod_two f (h m hsq hcl)

theorem cast_sum_eps (s : Finset ℕ) (ε a : ℕ → ℤ) (hε : ∀ d, ε d = 1 ∨ ε d = -1) :
    ((∑ d ∈ s, ε d * a d : ℤ) : ZMod 2) = ((∑ d ∈ s, a d : ℤ) : ZMod 2) := by
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rcases hε d with h | h <;> rw [h] <;> simp [ZMod.neg_eq_self_mod_two]

theorem pairIdx_one {m : ℕ} (hm : m % 8 = 1) :
    pairIdx m = m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m) := by
  unfold pairIdx
  refine Finset.filter_congr fun d _ => ?_
  simp [hm]

theorem pairIdx_three {m : ℕ} (hm : m % 8 = 3) :
    pairIdx m = m.divisors.filter (fun d => d % 8 = 1) := by
  unfold pairIdx
  refine Finset.filter_congr fun d _ => ?_
  simp [hm]

/-- One instance of the printed lemma, read modulo 2. -/
theorem sum_mod_two_of_printed {Q : ℕ → ℤ} (hP : Lemma29Printed Q) {ℓ : ℕ → ℤ} (hℓ : IsLcalSign ℓ)
    {m : ℕ} (hsq : Squarefree m) (h1 : 1 < m) (hcl : m % 8 = 1 ∨ m % 8 = 3) :
    ((∑ d ∈ pairIdx m, ℓ (m / d) * ℓ d : ℤ) : ZMod 2) = ((Q m : ℤ) : ZMod 2) := by
  obtain ⟨ε, hε, w, hw, heq⟩ := hP ℓ hℓ m hsq h1 hcl
  have hw2 : ((w : ℤ) : ZMod 2) = 1 := by
    rcases hw with rfl | ⟨-, rfl⟩
    · simp
    · decide
  rw [← heq, ← cast_sum_eps _ ε _ hε]
  push_cast
  rw [hw2, one_mul]

/-- **The mod-2 reduction (glue)**: the printed Lemma 2.9 and the conclusion of Proposition 2.3,
for the same `Q`, give the target. -/
theorem tyzLemma29Mod2_of_printed {Q : ℕ → ℤ} (hP : Lemma29Printed Q) (hC : Prop23Cong Q) :
    TYZLemma29Mod2 := by
  intro ℓ hℓ
  constructor
  · intro m hsq h1 hm
    have := sum_mod_two_of_printed hP hℓ hsq h1 (Or.inl hm)
    rw [pairIdx_one hm, hC m hsq (Or.inl hm)] at this
    rw [← this]
    push_cast
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  · intro m hsq hm
    have h1 : 1 < m := by omega
    have := sum_mod_two_of_printed hP hℓ hsq h1 (Or.inr hm)
    rw [pairIdx_three hm, hC m hsq (Or.inr hm)] at this
    exact this

/-- **The split, over the genus period of a class-group function `f`**: Lemma 2.9 for `Q_f` and
Proposition 2.3's first assertion for `f` give the target, for every `f`. -/
theorem tyzLemma29Mod2_of_printedF {f : ClFun} (hP : Lemma29Printed (genusPeriod f))
    (hO : Prop23Odd f) : TYZLemma29Mod2 :=
  tyzLemma29Mod2_of_printed hP (prop23Cong_of_odd hO)

/-! ## §3. Inertness: with `Q` (or `f`) not pinned, the printed pair is the target -/

theorem sq_eq_of_sign {ℓ ℓ' : ℕ → ℤ} (hℓ : IsLcalSign ℓ) (hℓ' : IsLcalSign ℓ') {d : ℕ}
    (hsq : Squarefree d) (hcl : d % 8 = 1 ∨ d % 8 = 3) : ℓ d ^ 2 = ℓ' d ^ 2 := by
  have h : ((ℓ d : ℂ)) ^ 2 = ((ℓ' d : ℂ)) ^ 2 := (hℓ d hsq hcl).trans (hℓ' d hsq hcl).symm
  exact_mod_cast h

theorem mem_pairIdx_facts {m d : ℕ} (hsq : Squarefree m) (hcl : m % 8 = 1 ∨ m % 8 = 3)
    (hd : d ∈ pairIdx m) :
    (Squarefree d ∧ (d % 8 = 1 ∨ d % 8 = 3)) ∧
      (Squarefree (m / d) ∧ (m / d % 8 = 1 ∨ m / d % 8 = 3)) := by
  simp only [pairIdx, Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdm, -⟩, hd8, -⟩ := hd
  refine ⟨⟨hsq.squarefree_of_dvd hdm, Or.inl hd8⟩,
    ⟨hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm), ?_⟩⟩
  rcases hcl with h | h
  · left; rw [div_mod8_of hdm h hd8 (Or.inl rfl)]
  · right; rw [div_mod8_of hdm h hd8 (Or.inl rfl)]

open Classical in
/-- The canonical `Q`: the sum `Σ ℓ₀(m/d)ℓ₀(d)` for one chosen sign choice `ℓ₀` (if there is one),
and `g(m)` otherwise. -/
def canonQ : ℕ → ℤ := fun m =>
  if h : (∃ ℓ, IsLcalSign ℓ) ∧ 1 < m then ∑ d ∈ pairIdx m, h.1.choose (m / d) * h.1.choose d
  else (gNat m : ℤ)

theorem lemma29Printed_canonQ : Lemma29Printed canonQ := by
  classical
  intro ℓ hℓ m hsq h1 hcl
  have hex : ∃ ℓ, IsLcalSign ℓ := ⟨ℓ, hℓ⟩
  have hQ : canonQ m = ∑ d ∈ pairIdx m, hex.choose (m / d) * hex.choose d := by
    rw [canonQ, dif_pos ⟨hex, h1⟩]
  have h0 := hex.choose_spec
  refine ⟨fun d => if ℓ (m / d) * ℓ d = hex.choose (m / d) * hex.choose d then 1 else -1,
    fun d => by dsimp only; split_ifs <;> simp, 1, Or.inl rfl, ?_⟩
  rw [one_mul, hQ]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨⟨hs1, hc1⟩, ⟨hs2, hc2⟩⟩ := mem_pairIdx_facts hsq hcl hd
  have e1 := sq_eq_of_sign hℓ h0 hs1 hc1
  have e2 := sq_eq_of_sign hℓ h0 hs2 hc2
  have e : (ℓ (m / d) * ℓ d) ^ 2 = (hex.choose (m / d) * hex.choose d) ^ 2 := by
    rw [mul_pow, mul_pow, e1, e2]
  dsimp only
  split_ifs with hc
  · rw [hc, one_mul]
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with h | h
    · exact absurd h hc
    · rw [h]; ring

theorem prop23Cong_canonQ (h29 : TYZLemma29Mod2) : Prop23Cong canonQ := by
  classical
  intro m hsq hcl
  by_cases h : (∃ ℓ, IsLcalSign ℓ) ∧ 1 < m
  · rw [canonQ, dif_pos h]
    have hL := h29 _ h.1.choose_spec
    rcases hcl with hm | hm
    · rw [pairIdx_one hm, ← hL.1 m hsq h.2 hm]
      push_cast
      exact Finset.sum_congr rfl fun d _ => mul_comm _ _
    · rw [pairIdx_three hm, ← hL.2 m hsq hm]
  · rw [canonQ, dif_neg h]
    push_cast
    rfl

/-- **Inertness, `Q`-level**: some `Q` satisfies the printed Lemma 2.9 and the conclusion of
Proposition 2.3 iff the target holds. So the two printed statements are leaves only once `Q` is
pinned (TYZ's genus period). -/
theorem exists_printedQ_iff :
    (∃ Q : ℕ → ℤ, Lemma29Printed Q ∧ Prop23Cong Q) ↔ TYZLemma29Mod2 :=
  ⟨fun ⟨_, hP, hC⟩ => tyzLemma29Mod2_of_printed hP hC,
    fun h29 => ⟨canonQ, lemma29Printed_canonQ, prop23Cong_canonQ h29⟩⟩

open Classical in
/-- A class-group function with genus period `canonQ`: `canonQ n − (g(n) − 1)` at the trivial class,
`1` elsewhere. -/
def canonF : ClFun := fun n _ t => if t = 1 then canonQ n - ((gCl n : ℤ) - 1) else 1

theorem genusPeriod_canonF {n : ℕ} (hn : n ≠ 0) : genusPeriod canonF n = canonQ n := by
  classical
  have : NeZero n := ⟨hn⟩
  rw [genusPeriod_of_ne, ← Finset.add_sum_erase _ _ (one_mem_sqClasses n)]
  have hrest : ∑ t ∈ (sqClasses n).erase 1, canonF n t = ((gCl n : ℤ) - 1) := by
    rw [Finset.sum_congr rfl fun t ht => (by
      simp only [canonF, if_neg (Finset.ne_of_mem_erase ht)] : canonF n t = 1)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem (one_mem_sqClasses n),
      card_sqClasses]
    have : 1 ≤ gCl n := by
      rw [← card_sqClasses]; exact Finset.card_pos.mpr ⟨1, one_mem_sqClasses n⟩
    push_cast [this]
    ring
  rw [hrest, show canonF n 1 = canonQ n - ((gCl n : ℤ) - 1) by simp [canonF]]
  ring

theorem prop23Odd_canonF (h29 : TYZLemma29Mod2) : Prop23Odd canonF := by
  classical
  intro n _ hsq hcl t _
  simp only [canonF]
  split_ifs
  · rw [← ZMod.intCast_eq_one_iff_odd]
    have hc := prop23Cong_canonQ h29 n hsq hcl
    rw [gNat_of_ne] at hc
    push_cast
    rw [hc]
    ring
  · exact odd_one

/-- **Inertness, `f`-level**: some class-group function `f` satisfies the printed Lemma 2.9 for its
genus period and the first assertion of Proposition 2.3 iff the target holds. -/
theorem exists_printedF_iff :
    (∃ f : ClFun, Lemma29Printed (genusPeriod f) ∧ Prop23Odd f) ↔ TYZLemma29Mod2 := by
  refine ⟨fun ⟨_, hP, hO⟩ => tyzLemma29Mod2_of_printedF hP hO, fun h29 => ⟨canonF, ?_,
    prop23Odd_canonF h29⟩⟩
  intro ℓ hℓ m hsq h1 hcl
  rw [genusPeriod_canonF (by omega)]
  exact lemma29Printed_canonQ ℓ hℓ m hsq h1 hcl

/-! ## §4. The alternative printed leaf: TYZ Theorem 1.1, congruence -/

/-- **Given `TYZThm11Integral`, the target is equivalent to `TYZThm11Mod2`** (TYZ Theorem 1.1,
second assertion, set-partition reading): `→` by Lemma N1 (`PropN.lemmaN1`) with `𝓛(1) = ±1`
(`TYZLcal.tyzLcalOne_of_leaves`), `←` by `lemma29Mod2_of_thm11Mod2`. -/
theorem thm11Mod2_iff (h11 : TYZThm11Integral) : TYZThm11Mod2 ↔ TYZLemma29Mod2 := by
  refine ⟨lemma29Mod2_of_thm11Mod2, fun h29 ℓ hℓ => ?_⟩
  have h1 : lcalSq 1 = 1 := ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves h11 h29
  have hsq1 : ℓ 1 ^ 2 = 1 := by
    have := hℓ 1 squarefree_one (Or.inl rfl)
    rw [h1] at this
    exact_mod_cast this
  have hpm : ((ℓ 1 : ℤ) : ZMod 2) = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq1.trans (one_pow 2).symm) with h | h <;> rw [h] <;>
      decide
  let ℓ' : ℕ → ℤ := fun m => if m = 1 then 1 else ℓ m
  have hcong : ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) →
      ((ℓ m : ℤ) : ZMod 2) = ℓ' m := by
    intro m _ _
    by_cases hm : m = 1
    · subst hm; simp [ℓ', hpm]
    · simp [ℓ', hm]
  have hL' : LemmaTwoEight ℓ' := ZInQ.Contrib.TYZLcal.lemmaTwoEight_congr hcong (h29 ℓ hℓ)
  have hN := lemmaN1 (L := ℓ') (by simp [ℓ']) hL'
  intro m hsq hcl
  rw [hcong m hsq hcl]
  exact hN m hsq hcl

/-- The target from the printed Theorem 1.1 congruence (the theorem of type exactly
`TYZLemma29Mod2` once `TYZThm11Mod2` is given). -/
theorem tyzLemma29Mod2_of_thm11Mod2 (h : TYZThm11Mod2) : TYZLemma29Mod2 :=
  lemma29Mod2_of_thm11Mod2 h

end ZInQ.Contrib.TYZDecomp.H29Split

#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printed
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedF
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.exists_printedQ_iff
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.exists_printedF_iff
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.thm11Mod2_iff
