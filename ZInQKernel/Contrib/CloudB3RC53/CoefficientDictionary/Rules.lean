import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Realize

/-!
# The coefficient dictionary, part 2: the coefficient rules for the actual symbols

Manuscript `diophantine_zq.tex`, Lemma `ex:sec7-coefficient-rules` (L2102–2149) and its proof,
Proposition `ex:app-coefficient-rules` (App F, L9884–9976).

The abstract symbol `symb T R` (the reading of any prime realization, `Realize.lean`) satisfies
lane RC2's coefficient rules (`CoefficientRules`, and `RulesUpTo` within a finite budget at an odd
stage), from lane RC12's readings on prime sets:

* `FixedUFactorization` (RC12 `Traces.factor_through_squares`, tex L9745–9750): the reading of a
  new vertex depends only on its type and its residue bits with the others;
* `O12Reading` (RC12 (O.12) at coefficient one and the fresh-prime Hecke formula, tex
  L9905–9926): for every prescribed label of a fresh vertex `q` adjoining `U ∋ p` there are fresh
  representatives `q, q_τ, r₀, r₁` of `g, gτ, gφ, gτφ` — with the **product-label rule**
  (tex L9932–9945): `r₀, r₁` carry the summed type `ℓ_p + ℓ_q` and the summed bits
  `(p/s) + (q/s)` at every other `s ∈ U`, and opposite Legendre signs at `p` — and
  `c₁ 𝒜_V(Vr₁) − c₀ 𝒜_V(Vr₀) = 𝒜_U(Uq_τ) − 𝒜_U(Uq)` with `c_i = C_p(vr_i) mod 2`,
  `C_p(vr₀) = Cp a_p κ₀`, `C_p(vr₁) = Cp a_p (−κ₀)`, `κ₀ = ±1` (the Legendre sign `(ψ/η)(p)(−vr₀/p)`);
* `ApEven` (GLUE: `a_p ≡ p + 1 (mod 4)` for every good prime, all of `E[2]` being rational,
  tex L9585, L9593): `a_p` is even;
* `PrimaryReading` (RC12 `Traces.primary_isolation_reading`, tex L9947–9948): a fresh vertex of
  trivial label reads zero.

PROVED here: contraction (`symb_contraction`; from RC12's `omission_rule` and `cp_sum_odd`, the
two `V`-symbols agreeing by the fixed-`U` factorization), primary isolation
(`symb_primary_isolation`), graph dependence (`symb_graph_dependence`), and the assembled
`rulesUpTo_symb`, `coefficientRules_symb`. `symb_primeConfig`: on a configuration of good primes
the symbol of the coefficient reading is RC2's `readPrimes`, the actual symbol of
Definition `ex:sec7-symbol`.
-/

namespace ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ### The readings of lane RC12, on prime sets -/

/-- **(O.12) at coefficient one, with the product-label rule** (tex L9905–9945; RC12's
`O12_diag`, `O12_unramified` and the Hecke formula `H_U[pr] ≡ η(p) C_p(vr) 2^{−n_V−1} a(vr)`,
read in `𝔽₂`): within the budget `B`, for `U ∋ p` and every prescribed type `ℓ` and bits `bq` of a
fresh vertex, there are fresh good representatives `q, q_τ, r₀, r₁` of `g, gτ, gφ, gτφ` (`τ` the
inertia, `φ` a Frobenius at `p`) and a Legendre sign `κ₀ = ±1` with the identity of RC12's
`omission_rule` hypothesis `hO12`. -/
def O12Reading (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ) : Prop :=
  ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ (ℓ : L) (bq : ℕ → ZMod 2), ∃ (q qτ r0 r1 : ℕ) (κ0 : ℤ),
      T.Good q ∧ T.Good qτ ∧ T.Good r0 ∧ T.Good r1 ∧ q ∉ U ∧ qτ ∉ U ∧ r0 ∉ U ∧ r1 ∉ U ∧
      T.typ q = ℓ ∧ T.typ qτ = ℓ ∧ (∀ s ∈ U, legBit q s = bq s) ∧
      (∀ s ∈ U, s ≠ p → legBit qτ s = bq s) ∧ legBit qτ p = bq p + 1 ∧
      T.typ r0 = T.typ p + ℓ ∧ T.typ r1 = T.typ p + ℓ ∧
      (∀ s ∈ U, s ≠ p → legBit r0 s = legBit p s + bq s ∧ legBit r1 s = legBit p s + bq s) ∧
      legBit r1 p = legBit r0 p + 1 ∧ (κ0 = 1 ∨ κ0 = -1) ∧
      ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) * R (insert r1 (U.erase p)) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * R (insert r0 (U.erase p)) =
        R (insert qτ U) - R (insert q U)

/-- **GLUE: `a_p` is even at every good prime** (tex L9585, L9593: `a_p ≡ p + 1 (mod 4)` for a
prime split in `ℚ(E[2]) = ℚ`). -/
def ApEven (T : TypeData L ε) (ap : ℕ → ℤ) : Prop := ∀ p, T.Good p → Even (ap p)

/-- **Primary isolation, read on prime sets** (tex L9947–9948; RC12's
`primary_isolation_reading`): within the budget, a fresh vertex of trivial type and trivial bits
with the others reads zero. -/
def PrimaryReading (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (B : ℕ) : Prop :=
  ∀ (W : Finset ℕ) (q : ℕ), (∀ s ∈ W, T.Good s) → T.Good q → q ∉ W → (insert q W).card ≤ B →
    T.typ q = 0 → (∀ s ∈ W, legBit q s = 0) → R (insert q W) = 0

/-! ### Bits of the derived configurations -/

theorem zmod2_add_add_self (x y : ZMod 2) : x + y + y = x := by revert x y; decide

/-- The image of an erased vertex under a map injective on the vertex set. -/
theorem image_erase_of_injOn' {V : Finset ℕ} {f : ℕ → ℕ} (hf : Set.InjOn f V) {v : ℕ}
    (hv : v ∈ V) : (V.erase v).image f = (V.image f).erase (f v) := by
  ext x
  simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨u, ⟨huv, hu⟩, rfl⟩
    exact ⟨fun h => huv (hf hu hv h), u, hu, rfl⟩
  · rintro ⟨hx, u, hu, rfl⟩
    exact ⟨u, ⟨fun h => hx (h ▸ rfl), hu⟩, rfl⟩

/-- A reverse bit from a forward bit, by reciprocity and compatibility. -/
theorem rev_bit (T : TypeData L ε) {Γ : Config L} (hΓ : Γ.Compatible ε) {a w : ℕ}
    (ha : a ∈ Γ.V) (hw : w ∈ Γ.V) (haw : a ≠ w) {pa q : ℕ} (hpa : T.Good pa) (hq : T.Good q)
    (hne : pa ≠ q) (hta : T.typ pa = Γ.t a) (htq : T.typ q = Γ.t w)
    (hfwd : legBit q pa = Γ.z w a) : legBit pa q = Γ.z a w := by
  rw [T.legBit_rev hpa hq hne, hfwd, hta, htq]
  have hc := hΓ w hw a ha (Ne.symm haw)
  have := TypeData.zmod2_eq_of_add hc
  rw [this, mul_comm (ε (Γ.t w))]
  exact zmod2_add_add_self _ _

omit [AddCommGroup L] in
theorem flip_z (Γ : Config L) (v w a b : ℕ) :
    (Γ.flip v w).z a b = Γ.z a b + if a ≠ b ∧ s(a, b) = s(v, w) then 1 else 0 := by
  simp only [Config.flip, Config.flipBy, mem_singleton]

theorem flip_compatible {Γ : Config L} (hΓ : Γ.Compatible ε) (v w : ℕ) :
    (Γ.flip v w).Compatible ε := by
  intro a ha b hb hab
  have h := hΓ a ha b hb hab
  change (Γ.flip v w).z a b + (Γ.flip v w).z b a = ε (Γ.t a) * ε (Γ.t b)
  rw [flip_z, flip_z, Sym2.eq_swap (a := b)]
  by_cases hc : a ≠ b ∧ s(a, b) = s(v, w)
  · have hc' : b ≠ a ∧ s(a, b) = s(v, w) := ⟨Ne.symm hc.1, hc.2⟩
    rw [if_pos' hc, if_pos' hc', ← h]
    generalize Γ.z a b = x
    generalize Γ.z b a = y
    revert x y; decide
  · have hc' : ¬ (b ≠ a ∧ s(a, b) = s(v, w)) := fun h' => hc ⟨Ne.symm h'.1, h'.2⟩
    rw [if_neg' hc, if_neg' hc', add_zero, add_zero, h]

/-- The `𝔽₂` identity for the reverse bit at a contracted vertex. -/
theorem contract_bit_id (x1 y1 x2 y2 e g f : ZMod 2) (h1 : x1 + y1 = e * f)
    (h2 : x2 + y2 = g * f) : x1 + x2 + f * (e + g) = y1 + y2 := by
  revert x1 y1 x2 y2 e g f; decide

/-! ### Contraction -/

open Classical in
/-- **Contraction** (`ex:sec7-coefficient-rules` rule 2, tex L2117–2128; proof tex L9905–9945):
`A(Γ) + A(Γ with the bit of v, w changed) = A(Γ/(v, w))` for the symbol of the readings. -/
theorem symb_contraction (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) {B : ℕ}
    (hswap : FixedUFactorization T R B) (hO12 : O12Reading T R ap B) (hap : ApEven T ap)
    {Γ : Config L} (hB : Γ.V.card ≤ B) (hΓ : Γ.Compatible ε) {v w : ℕ} (hv : v ∈ Γ.V)
    (hw : w ∈ Γ.V) (hvw : v ≠ w) :
    symb T R Γ + symb T R (Γ.flip v w) = symb T R (Γ.contract v w) := by
  set V' := Γ.V.erase w with hV'
  have hres : (Γ.restrict V').Compatible ε :=
    fun a ha b hb hab => hΓ a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) hab
  obtain ⟨f, hfinj, hft, hfz⟩ := exists_real T hres
  change Set.InjOn f V' at hfinj
  change ∀ u ∈ V', T.Good (f u) ∧ T.typ (f u) = Γ.t u at hft
  change ∀ a ∈ V', ∀ b ∈ V', a ≠ b → legBit (f a) (f b) = Γ.z a b at hfz
  set U := V'.image f with hU
  have hvV' : v ∈ V' := mem_erase.mpr ⟨hvw, hv⟩
  set p := f v with hp
  have hpU : p ∈ U := mem_image_of_mem f hvV'
  have hUgood : ∀ s ∈ U, T.Good s := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    exact (hft u hu).1
  have hUcard : U.card = V'.card := card_image_of_injOn hfinj
  have hV'card : V'.card + 1 = Γ.V.card := card_erase_add_one hw
  have hUB : U.card + 1 ≤ B := by omega
  let bq : ℕ → ZMod 2 := fun s => if h : ∃ u ∈ V', f u = s then Γ.z w h.choose else 0
  have hbq : ∀ u ∈ V', bq (f u) = Γ.z w u := by
    intro u hu
    have h : ∃ u' ∈ V', f u' = f u := ⟨u, hu, rfl⟩
    simp only [bq, dif_pos' h]
    rw [hfinj h.choose_spec.1 hu h.choose_spec.2]
  obtain ⟨q, qτ, r0, r1, κ0, hq, hqτ, hr0, hr1, hqU, hqτU, hr0U, hr1U, htq, htqτ, hbitq,
    hbitqτ, hbitqτp, htr0, htr1, hbitr, -, hκ, hO⟩ := hO12 U p hpU hUgood hUB (Γ.t w) bq
  have hfU : ∀ u ∈ V', f u ∈ U := fun u hu => mem_image_of_mem f hu
  have hmemV' : ∀ u ∈ Γ.V, u ≠ w → u ∈ V' := fun u hu huw => mem_erase.mpr ⟨huw, hu⟩
  -- the realization of `Γ` with `w ↦ q`
  have hg : IsReal T Γ (Function.update f w q) := by
    refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
    · by_cases haw : a = w <;> by_cases hbw : b = w
      · rw [haw, hbw]
      · rw [haw, Function.update_self, Function.update_of_ne hbw] at hab
        exact absurd (hab ▸ hfU b (hmemV' b hb hbw)) hqU
      · rw [hbw, Function.update_self, Function.update_of_ne haw] at hab
        exact absurd (hab.symm ▸ hfU a (hmemV' a ha haw)) hqU
      · rw [Function.update_of_ne haw, Function.update_of_ne hbw] at hab
        exact hfinj (hmemV' a ha haw) (hmemV' b hb hbw) hab
    · by_cases haw : a = w
      · subst haw; rw [Function.update_self]; exact ⟨hq, htq⟩
      · rw [Function.update_of_ne haw]; exact hft a (hmemV' a ha haw)
    · by_cases haw : a = w
      · subst haw
        have hbw : b ≠ a := Ne.symm hab
        rw [Function.update_self, Function.update_of_ne hbw, hbitq _ (hfU b (hmemV' b hb hbw)),
          hbq b (hmemV' b hb hbw)]
      · by_cases hbw : b = w
        · subst hbw
          rw [Function.update_self, Function.update_of_ne haw]
          have hb' := hmemV' a ha haw
          exact rev_bit T hΓ ha hb hab (hft a hb').1 hq (fun h => hqU (h ▸ hfU a hb'))
            (hft a hb').2 htq (by rw [hbitq _ (hfU a hb'), hbq a hb'])
        · rw [Function.update_of_ne haw, Function.update_of_ne hbw]
          exact hfz a (hmemV' a ha haw) b (hmemV' b hb hbw) hab
  -- the realization of `Γ` with the bit of `v, w` changed, `w ↦ q_τ`
  have hflipc := flip_compatible hΓ v w
  have hgτ : IsReal T (Γ.flip v w) (Function.update f w qτ) := by
    refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
    · change a ∈ Γ.V at ha
      change b ∈ Γ.V at hb
      by_cases haw : a = w <;> by_cases hbw : b = w
      · rw [haw, hbw]
      · rw [haw, Function.update_self, Function.update_of_ne hbw] at hab
        exact absurd (hab ▸ hfU b (hmemV' b hb hbw)) hqτU
      · rw [hbw, Function.update_self, Function.update_of_ne haw] at hab
        exact absurd (hab.symm ▸ hfU a (hmemV' a ha haw)) hqτU
      · rw [Function.update_of_ne haw, Function.update_of_ne hbw] at hab
        exact hfinj (hmemV' a ha haw) (hmemV' b hb hbw) hab
    · change a ∈ Γ.V at ha
      change T.Good _ ∧ T.typ _ = Γ.t a
      by_cases haw : a = w
      · subst haw; rw [Function.update_self]; exact ⟨hqτ, htqτ⟩
      · rw [Function.update_of_ne haw]; exact hft a (hmemV' a ha haw)
    · change a ∈ Γ.V at ha
      change b ∈ Γ.V at hb
      by_cases haw : a = w
      · subst haw
        have hbw : b ≠ a := Ne.symm hab
        rw [Function.update_self, Function.update_of_ne hbw, flip_z]
        by_cases hbv : b = v
        · subst hbv
          have hc : a ≠ b ∧ s(a, b) = s(b, a) := ⟨hab, Sym2.eq_swap⟩
          rw [if_pos' hc, hbitqτp, hbq b hvV']
        · have hc : ¬ (a ≠ b ∧ s(a, b) = s(v, a)) := by
            rintro ⟨-, h⟩
            rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
            · exact hvw h1.symm
            · exact hbv h2
          rw [if_neg' hc, add_zero, hbitqτ _ (hfU b (hmemV' b hb hbw))
            (fun h => hbv (hfinj (hmemV' b hb hbw) hvV' h)), hbq b (hmemV' b hb hbw)]
      · by_cases hbw : b = w
        · subst hbw
          rw [Function.update_self, Function.update_of_ne haw]
          have hb' := hmemV' a ha haw
          refine rev_bit T hflipc ha hb hab (hft a hb').1 hqτ (fun h => hqτU (h ▸ hfU a hb'))
            (hft a hb').2 htqτ ?_
          rw [flip_z]
          by_cases hav : a = v
          · subst hav
            have hc : b ≠ a ∧ s(b, a) = s(a, b) := ⟨Ne.symm hab, Sym2.eq_swap⟩
            rw [if_pos' hc, hbitqτp, hbq a hvV']
          · have hc : ¬ (b ≠ a ∧ s(b, a) = s(v, b)) := by
              rintro ⟨-, h⟩
              rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
              · exact hvw h1.symm
              · exact hav h2
            rw [if_neg' hc, add_zero, hbitqτ _ (hfU a hb') (fun h => hav (hfinj hb' hvV' h)),
              hbq a hb']
        · rw [Function.update_of_ne haw, Function.update_of_ne hbw, flip_z]
          have hc : ¬ (a ≠ b ∧ s(a, b) = s(v, w)) := by
            rintro ⟨-, h⟩
            rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
            · exact hbw h2
            · exact haw h1
          rw [if_neg' hc, add_zero]
          exact hfz a (hmemV' a ha haw) b (hmemV' b hb hbw) hab
  -- the realization of the contraction `Γ/(v, w)`, `v ↦ r₀`
  have hh0 : IsReal T (Γ.contract v w) (Function.update f v r0) := by
    have hzc : ∀ a b, (Γ.contract v w).z a b = if a = v then Γ.z v b + Γ.z w b
        else if b = v then Γ.z a v + Γ.z a w else Γ.z a b := fun _ _ => rfl
    refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
    · change a ∈ V' at ha
      change b ∈ V' at hb
      by_cases hav : a = v <;> by_cases hbv : b = v
      · rw [hav, hbv]
      · rw [hav, Function.update_self, Function.update_of_ne hbv] at hab
        exact absurd (hab ▸ hfU b hb) hr0U
      · rw [hbv, Function.update_self, Function.update_of_ne hav] at hab
        exact absurd (hab.symm ▸ hfU a ha) hr0U
      · rw [Function.update_of_ne hav, Function.update_of_ne hbv] at hab
        exact hfinj ha hb hab
    · change a ∈ V' at ha
      change T.Good _ ∧ T.typ _ = Function.update Γ.t v (Γ.t v + Γ.t w) a
      by_cases hav : a = v
      · subst hav
        rw [Function.update_self, Function.update_self, htr0, (hft a hvV').2]
        exact ⟨hr0, rfl⟩
      · rw [Function.update_of_ne hav, Function.update_of_ne hav]; exact hft a ha
    · change a ∈ V' at ha
      change b ∈ V' at hb
      rw [hzc]
      by_cases hav : a = v
      · subst hav
        have hbv : b ≠ a := Ne.symm hab
        rw [if_pos' rfl, Function.update_self, Function.update_of_ne hbv,
          (hbitr _ (hfU b hb) fun h => hbv (hfinj hb hvV' h)).1, hbq b hb, hfz a hvV' b hb hab]
      · rw [if_neg' hav]
        by_cases hbv : b = v
        · subst hbv
          rw [if_pos' rfl, Function.update_self, Function.update_of_ne hav]
          have hne : f a ≠ r0 := fun h => hr0U (h ▸ hfU a ha)
          rw [T.legBit_rev (hft a ha).1 hr0 hne, (hbitr _ (hfU a ha)
            fun h => hav (hfinj ha hvV' h)).1, hbq a ha, hfz b hvV' a ha (Ne.symm hab), htr0,
            (hft a ha).2, (hft b hvV').2, map_add]
          have hwV : w ∈ Γ.V := hw
          have haV : a ∈ Γ.V := mem_of_mem_erase ha
          have h1 := hΓ b hv a haV (Ne.symm hab)
          have h2 := hΓ w hw a haV (fun h => (mem_erase.mp ha).1 h.symm)
          exact contract_bit_id _ _ _ _ _ _ _ h1 h2
        · rw [if_neg' hbv, Function.update_of_ne hav, Function.update_of_ne hbv]
          exact hfz a ha b hb hab
  -- images
  have himg : Γ.V.image (Function.update f w q) = insert q U := by
    rw [← insert_erase hw, image_insert, Function.update_self]
    congr 1
    refine image_congr fun u hu => ?_
    exact Function.update_of_ne (mem_erase.mp hu).1 _ _
  have himgτ : (Γ.flip v w).V.image (Function.update f w qτ) = insert qτ U := by
    change Γ.V.image _ = _
    rw [← insert_erase hw, image_insert, Function.update_self]
    congr 1
    refine image_congr fun u hu => ?_
    exact Function.update_of_ne (mem_erase.mp hu).1 _ _
  have himg0 : (Γ.contract v w).V.image (Function.update f v r0) = insert r0 (U.erase p) := by
    change V'.image _ = _
    rw [← insert_erase hvV', image_insert, Function.update_self]
    congr 1
    rw [hU, hp, ← image_erase_of_injOn' hfinj hvV']
    refine image_congr fun u hu => ?_
    exact Function.update_of_ne (mem_erase.mp hu).1 _ _
  rw [symb_eq T R hswap hΓ hB hg, symb_eq T R hswap hflipc hB hgτ,
    symb_eq T R hswap (compatible_of_real T hh0) (by change V'.card ≤ B; omega) hh0,
    himg, himgτ, himg0]
  -- the two `V`-symbols agree (the omitted form's level omits the whole prime `p`)
  have hV : R (insert r0 (U.erase p)) = R (insert r1 (U.erase p)) := by
    refine hswap (U.erase p) r0 r1 ?_ (fun s hs => hUgood s (mem_of_mem_erase hs)) hr0 hr1
      (fun h => hr0U (mem_of_mem_erase h)) (fun h => hr1U (mem_of_mem_erase h))
      (htr0.trans htr1.symm) fun s hs => ?_
    · calc (insert r0 (U.erase p)).card ≤ (U.erase p).card + 1 := card_insert_le _ _
        _ = U.card := card_erase_add_one hpU
        _ ≤ B := by omega
    · have h := hbitr s (mem_of_mem_erase hs) (mem_erase.mp hs).1
      rw [h.1, h.2]
  -- `c_p(vr₀) + c_p(vr₁) = 1` (RC12 `cp_sum_odd`)
  have hc : ((Cp (ap p) κ0 : ℤ) : ZMod 2) + ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) = 1 := by
    rw [← Int.cast_add]
    exact ZMod.intCast_eq_one_iff_odd.mpr (cp_sum_odd (hap p (hUgood p hpU)) hκ).2
  rw [add_comm]
  exact omission_rule _ _ _ _ _ _ hO hV hc

/-! ### Primary isolation and graph dependence -/

/-- **Primary isolation** (`ex:sec7-coefficient-rules` rule 3, tex L2129–2131; proof
tex L9947–9953). -/
theorem symb_primary_isolation (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) (hprim : PrimaryReading T R B) {Γ : Config L}
    (hB : Γ.V.card ≤ B) (hΓ : Γ.Compatible ε) {v : ℕ} (hv : v ∈ Γ.V) (ht : Γ.t v = 0)
    (hz : ∀ w ∈ Γ.V, w ≠ v → Γ.z v w = 0 ∧ Γ.z w v = 0) : symb T R Γ = 0 := by
  obtain ⟨f, hf⟩ := exists_real T hΓ
  rw [symb_eq T R hswap hΓ hB hf, ← insert_erase hv, image_insert]
  refine hprim _ _ (fun s hs => ?_) (hf.2.1 v hv).1 (fun h => ?_) ?_ ((hf.2.1 v hv).2.trans ht)
    fun s hs => ?_
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    exact (hf.2.1 u (mem_of_mem_erase hu)).1
  · obtain ⟨u, hu, hfu⟩ := mem_image.mp h
    exact (mem_erase.mp hu).1 (hf.1 (mem_of_mem_erase hu) hv hfu)
  · rw [← image_insert, insert_erase hv]
    exact card_image_le.trans hB
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    rw [hf.2.2 v hv u (mem_of_mem_erase hu) (Ne.symm (mem_erase.mp hu).1)]
    exact (hz u (mem_of_mem_erase hu) (mem_erase.mp hu).1).1

open Classical in
/-- **Graph dependence** (`ex:sec7-coefficient-rules` rule 1, tex L2108–2116; proof
tex L9955–9974): isomorphic typed graphs have the same symbol. -/
theorem symb_graph_dependence (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) {Γ Δ : Config L} (hB : Γ.V.card ≤ B)
    (hΓ : Γ.Compatible ε) (hiso : Γ.IsIso Δ) : symb T R Γ = symb T R Δ := by
  obtain ⟨e, het, hez⟩ := hiso
  obtain ⟨f, hf⟩ := exists_real T hΓ
  let g : ℕ → ℕ := fun u => if h : u ∈ Δ.V then f (e.symm ⟨u, h⟩) else 0
  have hgv : ∀ (u : ℕ) (h : u ∈ Δ.V), g u = f (e.symm ⟨u, h⟩) := fun u h => dif_pos' h
  have hg : IsReal T Δ g := by
    refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
    · rw [hgv a ha, hgv b hb] at hab
      have := hf.1 (e.symm ⟨a, ha⟩).2 (e.symm ⟨b, hb⟩).2 hab
      have h2 : (⟨a, ha⟩ : Δ.V) = ⟨b, hb⟩ := e.symm.injective (Subtype.ext this)
      exact congrArg Subtype.val h2
    · rw [hgv a ha]
      have h1 := hf.2.1 _ (e.symm ⟨a, ha⟩).2
      have h2 := het (e.symm ⟨a, ha⟩)
      rw [e.apply_symm_apply] at h2
      exact ⟨h1.1, h1.2.trans h2.symm⟩
    · rw [hgv a ha, hgv b hb]
      have hne : e.symm ⟨a, ha⟩ ≠ e.symm ⟨b, hb⟩ := fun h =>
        hab (congrArg Subtype.val (e.symm.injective h))
      have hne' : (e.symm ⟨a, ha⟩ : ℕ) ≠ e.symm ⟨b, hb⟩ := fun h => hne (Subtype.ext h)
      have h2 := hez (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) hne
      rw [e.apply_symm_apply, e.apply_symm_apply] at h2
      rw [hf.2.2 _ (e.symm ⟨a, ha⟩).2 _ (e.symm ⟨b, hb⟩).2 hne', h2]
  have hcard : Δ.V.card = Γ.V.card := by
    rw [← Fintype.card_coe Δ.V, ← Fintype.card_coe Γ.V]
    exact (Fintype.card_congr e).symm
  have himg : Δ.V.image g = Γ.V.image f := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (e.symm ⟨u, hu⟩).2, (hgv u hu).symm⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨e ⟨u, hu⟩, (e ⟨u, hu⟩).2, ?_⟩
      rw [hgv _ (e ⟨u, hu⟩).2]
      simp
  rw [symb_eq T R hswap hΓ hB hf,
    symb_eq T R hswap (compatible_of_real T hg) (hcard ▸ hB) hg, himg]

/-! ### The coefficient rules -/

/-- **The coefficient rules within a finite budget** (`ex:sec7-coefficient-rules`, as used at
one odd stage: "a rule is asserted only when all its inputs, outputs and coefficient divisions lie
in the chosen finite budget", tex L2104–2107): from RC12's readings within the budget `W + 1`, the
symbol of the readings satisfies RC2's `RulesUpTo ε _ W`. -/
theorem rulesUpTo_symb (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (W : ℕ)
    (hswap : FixedUFactorization T R (W + 1)) (hO12 : O12Reading T R ap (W + 1))
    (hap : ApEven T ap) (hprim : PrimaryReading T R (W + 1)) :
    RulesUpTo ε (symb T R) W where
  graph_dependence _ _ hB hΓ hiso := symb_graph_dependence T R hswap hB hΓ hiso
  contraction _ hB hΓ _ hv _ hw hvw := symb_contraction T R ap hswap hO12 hap hB hΓ hv hw hvw
  primary_isolation _ hB hΓ _ hv ht hz := symb_primary_isolation T R hswap hprim hB hΓ hv ht hz

/-- **The coefficient rules** (`ex:sec7-coefficient-rules`; App F `ex:app-coefficient-rules`):
from RC12's readings at every size (the even source), the symbol of the readings satisfies RC2's
`CoefficientRules`. -/
theorem coefficientRules_symb (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ)
    (hswap : ∀ B, FixedUFactorization T R B) (hO12 : ∀ B, O12Reading T R ap B)
    (hap : ApEven T ap) (hprim : ∀ B, PrimaryReading T R B) :
    CoefficientRules ε (symb T R) where
  graph_dependence _ _ hΓ hiso := symb_graph_dependence T R (hswap _) le_rfl hΓ hiso
  contraction _ hΓ _ hv _ hw hvw :=
    symb_contraction T R ap (hswap _) (hO12 _) hap le_rfl hΓ hv hw hvw
  primary_isolation _ hΓ _ hv ht hz :=
    symb_primary_isolation T R (hswap _) (hprim _) le_rfl hΓ hv ht hz

/-! ### The actual symbol -/

/-- The reading of a coefficient source on a set of primes: RC2's `coeffSymbol` at the Fourier
index `∏ p` (tex L2044–2046). -/
noncomputable def coeffReading (a : ℕ → ℚ_[2]) (δ : ℤ) (inFilter : ℕ → Prop)
    (W : Finset ℕ) : ZMod 2 :=
  coeffSymbol a δ inFilter (∏ p ∈ W, p)

/-- **The dictionary for the actual symbol**: on the typed graph of a set of good primes (RC2's
`primeConfig`, with the types `T.typ`), the abstract symbol of the coefficient reading is RC2's
`readPrimes`, the symbol of Definition `ex:sec7-symbol` at `D = ∏ p`. -/
theorem symb_primeConfig (T : TypeData L ε) (a : ℕ → ℚ_[2]) (δ : ℤ) (inFilter : ℕ → Prop)
    {B : ℕ} (hswap : FixedUFactorization T (coeffReading a δ inFilter) B) (V : Finset ℕ)
    (hV : ∀ p ∈ V, T.Good p) (hB : V.card ≤ B) :
    symb T (coeffReading a δ inFilter) (primeConfig V T.typ) =
      readPrimes a δ inFilter (primeConfig V T.typ) := by
  have hf : IsReal T (primeConfig V T.typ) id :=
    ⟨Set.injOn_id _, fun v hv => ⟨hV v hv, rfl⟩, fun v _ w _ _ => rfl⟩
  rw [symb_eq T _ hswap (compatible_of_real T hf) hB hf]
  simp [coeffReading, readPrimes, primeConfig]

end ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
