import ZInQKernel.Contrib.OneProof.RC.Symbols.SymbolDef
import ZInQKernel.Contrib.OneProof.RC.Symbols.Stabilization
import ZInQKernel.Contrib.OneProof.RC.Odd.Bridge
import ZInQKernel.Contrib.OneProof.RC.Odd.Traces

/-!
# The coefficient dictionary, part 1: prime realizations of typed graphs

Manuscript `diophantine_zq.tex`: Definition `ex:sec7-typed-graph` (L2015–2066), Definition
`ex:sec7-symbol` (L2068–2100), Lemma `ex:sec7-coefficient-rules` (L2102–2149) and its proof in
App F, Proposition `ex:app-coefficient-rules` (L9884–9976, in particular the product-label rule
L9932–9945 and the bridge copies L9955–9974).

This file is the dictionary between lane RC2's abstract configurations (`Config L`, compatible
typed graphs) and prime realizations, on which lane RC12's arithmetic readings live:

* `TypeData`: the type of a prime (`typ p ∈ L`, its values under the fixed quadratic characters and
  its unit squareclasses at the fixed support), with the two arithmetic facts used (GLUE, named
  after them): **types are read from residue classes** modulo a conductor `m` (`2 ∣ m`), every type
  in the realizable alphabet `L` being the type of every prime in some reduced class; and the
  **sign coordinate** `ε(typ p) = (p − 1)/2 mod 2`;
* `IsReal T Γ f`: `f` realizes `Γ` by distinct good primes with the prescribed types and residue
  bits `z_{vw} = 0/1 ⟺ (p_v/p_w) = ±1` (RC2's `legBit`);
* `realizeNat`: realizations exist with any prescribed types, bits at finitely many old primes and
  forward bits among the new ones (from RC2's `finite_realization_nat`: CRT and Dirichlet);
* `reading_eq_of_real`: **the reading does not depend on the realization** (tex L9955–9974): two
  realizations of a compatible graph read the same, through a fresh copy and a bridge copy and
  RC12's one-at-a-time replacement `replace_chain`, under RC12's fixed-`U` factorization
  (`FixedUFactorization`: a reading depends on a new vertex only through its type and its residue
  bits with the others, from `Traces.factor_through_squares`, tex L9745–9750);
* `symb`: the symbol on abstract configurations, the reading of any prime realization;
  `symb_eq`: it equals the reading of every realization.

All statements are PROVED; the arithmetic inputs are hypotheses named after the facts.
-/

namespace ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **The type data of primes** (Definition `ex:sec7-typed-graph`, tex L2017–2030), with the two
arithmetic facts used about it (GLUE):
* `classes` — types are read from reduced residue classes modulo the conductor `m` of the fixed
  quadratic characters and squareclasses (`2 ∣ m`); every element of the realizable alphabet `L`
  is the type of every prime in some reduced class;
* `sign` — the sign coordinate of the type is `ε(typ p) = (p − 1)/2 mod 2` (tex L2037–2039).
A *good* prime is a prime prime to `m` (so odd and outside the fixed support). -/
structure TypeData (L : Type*) [AddCommGroup L] (ε : L →+ ZMod 2) where
  /-- the conductor of the type characters -/
  m : ℕ
  m_pos : 0 < m
  two_dvd : 2 ∣ m
  /-- the type of a prime -/
  typ : ℕ → L
  /-- GLUE: types are read from residue classes -/
  classes : ∀ ℓ : L, ∃ c : ZMod m, IsUnit c ∧ ∀ p : ℕ, p.Prime → (p : ZMod m) = c → typ p = ℓ
  /-- GLUE: the sign coordinate -/
  sign : ∀ p : ℕ, p.Prime → Nat.Coprime p m → ε (typ p) = ((p / 2 : ℕ) : ZMod 2)

namespace TypeData

variable (T : TypeData L ε)

/-- A good prime: prime and prime to the conductor. -/
def Good (p : ℕ) : Prop := p.Prime ∧ Nat.Coprime p T.m

theorem Good.ne_two {T : TypeData L ε} {p : ℕ} (hp : T.Good p) : p ≠ 2 :=
  ne_two_of_coprime_even T.two_dvd hp.2

/-- In characteristic two, `a + b = c` gives `a = b + c`. -/
theorem zmod2_eq_of_add {a b c : ZMod 2} (h : a + b = c) : a = b + c := by
  revert a b c; decide

/-- **Reverse bits by reciprocity** (tex L2037–2041): for distinct good primes,
`(p/q)` is `(q/p)` corrected by the product of the sign coordinates. -/
theorem legBit_rev {p q : ℕ} (hp : T.Good p) (hq : T.Good q) (hpq : p ≠ q) :
    legBit p q = legBit q p + ε (T.typ p) * ε (T.typ q) := by
  have h := legBit_reciprocity hp.1 hq.1 hp.ne_two hq.ne_two hpq
  rw [← T.sign p hp.1 hp.2, ← T.sign q hq.1 hq.2] at h
  exact zmod2_eq_of_add h

end TypeData

/-! ### Realizations -/

/-- **A prime realization** of a typed graph `Γ` (tex L2031–2034): distinct good primes `f v`,
`v ∈ Γ.V`, of the prescribed types, with residue bits `z_{vw} = legBit (f v) (f w)`. -/
def IsReal (T : TypeData L ε) (Γ : Config L) (f : ℕ → ℕ) : Prop :=
  Set.InjOn f Γ.V ∧ (∀ v ∈ Γ.V, T.Good (f v) ∧ T.typ (f v) = Γ.t v) ∧
    ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w → legBit (f v) (f w) = Γ.z v w

/-- An indexed realization along an enumeration `ord` of the vertices. -/
def IsRealIdx (T : TypeData L ε) (Γ : Config L) (ord : ℕ → ℕ) (k : ℕ) (x : ℕ → ℕ) : Prop :=
  Set.InjOn x (range k) ∧ (∀ i < k, T.Good (x i) ∧ T.typ (x i) = Γ.t (ord i)) ∧
    ∀ i < k, ∀ j < k, i ≠ j → legBit (x i) (x j) = Γ.z (ord i) (ord j)

/-- A realized graph is compatible: its bits obey reciprocity. -/
theorem compatible_of_real (T : TypeData L ε) {Γ : Config L} {f : ℕ → ℕ} (hf : IsReal T Γ f) :
    Γ.Compatible ε := by
  intro v hv w hw hvw
  have hne : f v ≠ f w := fun h => hvw (hf.1 hv hw h)
  rw [← hf.2.2 v hv w hw hvw, ← hf.2.2 w hw v hv (Ne.symm hvw),
    T.legBit_rev (hf.2.1 v hv).1 (hf.2.1 w hw).1 hne, ← (hf.2.1 v hv).2, ← (hf.2.1 w hw).2]
  generalize legBit (f w) (f v) = a
  generalize ε (T.typ (f v)) * ε (T.typ (f w)) = b
  revert a b; decide

/-! ### Enumerations of a vertex set -/

theorem dif_pos' {c : Prop} [Decidable c] {α : Sort*} {t : c → α} {e : ¬c → α} (h : c) :
    dite c t e = t h := by simp [h]

theorem if_pos' {c : Prop} [Decidable c] {α : Sort*} {t e : α} (h : c) : ite c t e = t := by
  simp [h]

theorem if_neg' {c : Prop} [Decidable c] {α : Sort*} {t e : α} (h : ¬c) : ite c t e = e := by
  simp [h]

/-- The `i`-th vertex of `V` in increasing order (`0` past the end). -/
noncomputable def enumV (V : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < V.card then V.orderEmbOfFin rfl ⟨i, h⟩ else 0

theorem enumV_mem {V : Finset ℕ} {i : ℕ} (h : i < V.card) : enumV V i ∈ V := by
  rw [enumV, dif_pos' (h)]; exact V.orderEmbOfFin_mem rfl _

theorem enumV_inj {V : Finset ℕ} {i j : ℕ} (hi : i < V.card) (hj : j < V.card)
    (h : enumV V i = enumV V j) : i = j := by
  rw [enumV, enumV, dif_pos' (hi), dif_pos' (hj)] at h
  exact congrArg Fin.val ((V.orderEmbOfFin rfl).injective h)

theorem exists_enumV {V : Finset ℕ} {v : ℕ} (hv : v ∈ V) : ∃ i < V.card, enumV V i = v := by
  have : v ∈ Set.range (V.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hv
  obtain ⟨⟨i, hi⟩, h⟩ := this
  exact ⟨i, hi, by rw [enumV, dif_pos' (hi)]; exact h⟩

theorem image_enumV (V : Finset ℕ) : (range V.card).image (enumV V) = V := by
  ext v
  simp only [mem_image, mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => h ▸ enumV_mem hi, fun hv => exists_enumV hv⟩

open Classical in
/-- The index of a vertex in the enumeration. -/
noncomputable def idxV (V : Finset ℕ) (v : ℕ) : ℕ :=
  if h : ∃ i < V.card, enumV V i = v then h.choose else 0

theorem idxV_spec {V : Finset ℕ} {v : ℕ} (hv : v ∈ V) :
    idxV V v < V.card ∧ enumV V (idxV V v) = v := by
  classical
  have h := exists_enumV hv
  rw [idxV, dif_pos' (h)]
  exact h.choose_spec

theorem isRealIdx_of_isReal {T : TypeData L ε} {Γ : Config L} {f : ℕ → ℕ} (hf : IsReal T Γ f) :
    IsRealIdx T Γ (enumV Γ.V) Γ.V.card (fun i => f (enumV Γ.V i)) := by
  refine ⟨fun i hi j hj h => ?_, fun i hi => hf.2.1 _ (enumV_mem hi), ?_⟩
  · exact enumV_inj (mem_range.mp hi) (mem_range.mp hj)
      (hf.1 (enumV_mem (mem_range.mp hi)) (enumV_mem (mem_range.mp hj)) h)
  · intro i hi j hj hij
    exact hf.2.2 _ (enumV_mem hi) _ (enumV_mem hj) fun h => hij (enumV_inj hi hj h)

theorem image_comp_enumV (V : Finset ℕ) (f : ℕ → ℕ) :
    (range V.card).image (fun i => f (enumV V i)) = V.image f := by
  rw [show (fun i => f (enumV V i)) = f ∘ enumV V from rfl, ← image_image, image_enumV]

theorem isReal_of_isRealIdx {T : TypeData L ε} {Γ : Config L} {x : ℕ → ℕ}
    (hx : IsRealIdx T Γ (enumV Γ.V) Γ.V.card x) : IsReal T Γ (fun v => x (idxV Γ.V v)) := by
  refine ⟨fun v hv w hw h => ?_, fun v hv => ?_, fun v hv w hw hvw => ?_⟩
  · have h1 := idxV_spec (Finset.mem_coe.mp hv)
    have h2 := idxV_spec (Finset.mem_coe.mp hw)
    have := hx.1 (mem_range.mpr h1.1) (mem_range.mpr h2.1) h
    rw [← h1.2, ← h2.2, this]
  · have h1 := idxV_spec hv
    have := hx.2.1 _ h1.1
    rw [h1.2] at this
    exact this
  · have h1 := idxV_spec hv
    have h2 := idxV_spec hw
    have hne : idxV Γ.V v ≠ idxV Γ.V w := fun h => hvw (by rw [← h1.2, ← h2.2, h])
    have := hx.2.2 _ h1.1 _ h2.1 hne
    rw [h1.2, h2.2] at this
    exact this

/-! ### Existence of realizations (CRT and Dirichlet) -/

/-- **Realizations with prescribed data** (tex L2151–2174, RC2's `finite_realization_nat`, with
the GLUE `TypeData.classes`): `k` distinct good primes, outside `old ∪ avoid`, of prescribed types
`ty i`, with prescribed bits at the old (good) primes and forward bits among themselves. -/
theorem realizeNat (T : TypeData L ε) (old avoid : Finset ℕ) (hold : ∀ p ∈ old, T.Good p)
    (ty : ℕ → L) (bitOld : ℕ → ℕ → ZMod 2) (bitNew : ℕ → ℕ → ZMod 2) (k : ℕ) :
    ∃ q : ℕ → ℕ, (∀ i < k, ∀ j < k, q i = q j → i = j) ∧
      (∀ i < k, T.Good (q i) ∧ q i ∉ old ∧ q i ∉ avoid ∧ T.typ (q i) = ty i) ∧
      (∀ i < k, ∀ p ∈ old, legBit (q i) p = bitOld i p) ∧
      (∀ i < k, ∀ j < i, legBit (q i) (q j) = bitNew i j) := by
  choose cls hcls htyp using fun i => T.classes (ty i)
  obtain ⟨q, hinj, hq, hold', hnew⟩ := finite_realization_nat T.m T.m_pos T.two_dvd old hold
    avoid cls hcls bitOld bitNew k
  refine ⟨q, hinj, fun i hi => ?_, hold', hnew⟩
  obtain ⟨hp, ho, ha, hc⟩ := hq i hi
  have hcop : Nat.Coprime (q i) T.m := (ZMod.isUnit_iff_coprime _ _).mp (hc ▸ hcls i)
  exact ⟨⟨hp, hcop⟩, ho, ha, htyp i (q i) hp hc⟩

/-- A realization of a compatible graph by primes of an indexed family (no old primes). -/
theorem exists_realIdx (T : TypeData L ε) {Γ : Config L} (hΓ : Γ.Compatible ε)
    (avoid : Finset ℕ) :
    ∃ x : ℕ → ℕ, IsRealIdx T Γ (enumV Γ.V) Γ.V.card x ∧ ∀ i < Γ.V.card, x i ∉ avoid := by
  set k := Γ.V.card
  obtain ⟨q, hinj, hq, -, hnew⟩ := realizeNat T ∅ avoid (by simp) (fun i => Γ.t (enumV Γ.V i))
    (fun _ _ => 0) (fun i j => Γ.z (enumV Γ.V i) (enumV Γ.V j)) k
  refine ⟨q, ⟨fun i hi j hj h => hinj i (mem_range.mp hi) j (mem_range.mp hj) h,
    fun i hi => ⟨(hq i hi).1, (hq i hi).2.2.2⟩, fun i hi j hj hij => ?_⟩,
    fun i hi => (hq i hi).2.2.1⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- reverse bit by reciprocity and compatibility
    have hne : q i ≠ q j := fun h => hij (hinj i hi j hj h)
    rw [T.legBit_rev (hq i hi).1 (hq j hj).1 hne, hnew j hj i hlt, (hq i hi).2.2.2,
      (hq j hj).2.2.2]
    have hc := hΓ _ (enumV_mem hj) _ (enumV_mem hi) fun h => hij (enumV_inj hi hj h.symm)
    have := TypeData.zmod2_eq_of_add hc
    rw [this, mul_comm]
    generalize Γ.z (enumV Γ.V i) (enumV Γ.V j) = a
    generalize ε (Γ.t (enumV Γ.V i)) * ε (Γ.t (enumV Γ.V j)) = b
    revert a b; decide
  · exact hnew i hi j hgt

/-- A realization of a compatible graph exists. -/
theorem exists_real (T : TypeData L ε) {Γ : Config L} (hΓ : Γ.Compatible ε) :
    ∃ f : ℕ → ℕ, IsReal T Γ f := by
  obtain ⟨x, hx, -⟩ := exists_realIdx T hΓ ∅
  exact ⟨_, isReal_of_isRealIdx hx⟩

/-! ### The fixed-`U` factorization and the replacement chains -/

/-- **RC12's fixed-`U` factorization, read on prime sets** (tex L2108–2112 rule 1, L9745–9750,
`Traces.factor_through_squares`): within the budget `B`, the reading of `W ∪ {p}` depends on the
new good prime `p` only through its type and its residue bits with the primes of `W` (its
Frobenius in the elementary quadratic extension unramified outside `S ∪ W`). -/
def FixedUFactorization (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (B : ℕ) : Prop :=
  ∀ (W : Finset ℕ) (p p' : ℕ), (insert p W).card ≤ B → (∀ s ∈ W, T.Good s) → T.Good p →
    T.Good p' → p ∉ W → p' ∉ W → T.typ p = T.typ p' → (∀ s ∈ W, legBit p s = legBit p' s) →
    R (insert p W) = R (insert p' W)

open Classical in
/-- The label of `p` relative to `W` used in RC12's `replace_chain`: its type and bits with `W`
when the factorization applies, and `p` itself otherwise. -/
noncomputable def lab (T : TypeData L ε) (B : ℕ) (p : ℕ) (W : Finset ℕ) :
    (L × (ℕ → ZMod 2)) ⊕ ℕ :=
  if T.Good p ∧ (∀ s ∈ W, T.Good s) ∧ (insert p W).card ≤ B then
    Sum.inl (T.typ p, fun s => if s ∈ W then legBit p s else 0)
  else Sum.inr p

theorem swap_of_lab (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (B : ℕ)
    (hswap : FixedUFactorization T R B) (W : Finset ℕ) (p p' : ℕ) (hp : p ∉ W) (hp' : p' ∉ W)
    (h : lab T B p W = lab T B p' W) : R (insert p W) = R (insert p' W) := by
  classical
  unfold lab at h
  by_cases h1 : T.Good p ∧ (∀ s ∈ W, T.Good s) ∧ (insert p W).card ≤ B
  · by_cases h2 : T.Good p' ∧ (∀ s ∈ W, T.Good s) ∧ (insert p' W).card ≤ B
    · rw [if_pos' h1, if_pos' h2] at h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨ht, hb⟩ := h
      refine hswap W p p' h1.2.2 h1.2.1 h1.1 h2.1 hp hp' ht fun s hs => ?_
      have := congrFun hb s
      simpa [hs] using this
    · rw [if_pos' h1, if_neg' h2] at h
      exact absurd h Sum.inl_ne_inr
  · by_cases h2 : T.Good p' ∧ (∀ s ∈ W, T.Good s) ∧ (insert p' W).card ≤ B
    · rw [if_neg' h1, if_pos' h2] at h
      exact absurd h Sum.inr_ne_inl
    · rw [if_neg' h1, if_neg' h2] at h
      rw [Sum.inr_injective h]

theorem card_chainSet_le (x y : ℕ → ℕ) (k i : ℕ) (hi : i < k) :
    (insert (x i) (chainRest x y k i)).card ≤ k := by
  unfold chainRest
  calc (insert (x i) ((range i).image y ∪ (Ico (i + 1) k).image x)).card
      ≤ ((range i).image y ∪ (Ico (i + 1) k).image x).card + 1 := card_insert_le _ _
    _ ≤ (range i).card + (Ico (i + 1) k).card + 1 := by
        gcongr
        exact (card_union_le _ _).trans (add_le_add card_image_le card_image_le)
    _ = k := by rw [card_range, Nat.card_Ico]; omega

/-- **One chain of replacements between disjoint realizations** (tex L9960–9964, RC12's
`replace_chain`): if `y`'s bits to the primes of `x` are those of the graph, the readings agree. -/
theorem chain_eq (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) {Γ : Config L} (hΓ : Γ.Compatible ε) {ord : ℕ → ℕ}
    {k : ℕ} (hkB : k ≤ B) (hordV : ∀ i < k, ord i ∈ Γ.V)
    (hord : ∀ i < k, ∀ j < k, i ≠ j → ord i ≠ ord j) {x y : ℕ → ℕ}
    (hx : IsRealIdx T Γ ord k x) (hy : IsRealIdx T Γ ord k y) (hxy : ∀ i < k, ∀ j < k, x i ≠ y j)
    (hcross : ∀ i < k, ∀ j < k, i ≠ j → legBit (y i) (x j) = Γ.z (ord i) (ord j)) :
    R ((range k).image x) = R ((range k).image y) := by
  classical
  refine replace_chain R (lab T B) (swap_of_lab T R B hswap) x y k hx.1 hy.1 hxy fun i hi => ?_
  have hgoodW : ∀ s ∈ chainRest x y k i, T.Good s := by
    intro s hs
    simp only [chainRest, mem_union, mem_image, mem_range, mem_Ico] at hs
    rcases hs with ⟨j, hj, rfl⟩ | ⟨j, ⟨_, hj⟩, rfl⟩
    · exact (hy.2.1 j (by omega)).1
    · exact (hx.2.1 j hj).1
  have hcard : (insert (x i) (chainRest x y k i)).card ≤ B :=
    (card_chainSet_le x y k i hi).trans hkB
  have hcard' : (insert (y i) (chainRest x y k i)).card ≤ B := by
    refine le_trans ?_ hcard
    have hxn : x i ∉ chainRest x y k i := by
      simp only [chainRest, mem_union, mem_image, mem_range, mem_Ico, not_or, not_exists,
        not_and]
      refine ⟨fun j hj h => hxy i hi j (by omega) h.symm, fun j hj h => ?_⟩
      have := hx.1 (mem_range.mpr (by omega)) (mem_range.mpr hi) h
      omega
    rw [card_insert_of_notMem hxn]
    exact card_insert_le _ _
  unfold lab
  rw [if_pos' ⟨(hx.2.1 i hi).1, hgoodW, hcard⟩, if_pos' ⟨(hy.2.1 i hi).1, hgoodW, hcard'⟩]
  congr 1
  refine Prod.ext (by rw [(hx.2.1 i hi).2, (hy.2.1 i hi).2]) (funext fun s => ?_)
  show (if s ∈ chainRest x y k i then legBit (x i) s else 0) =
    (if s ∈ chainRest x y k i then legBit (y i) s else 0)
  split_ifs with hs
  · simp only [chainRest, mem_union, mem_image, mem_range, mem_Ico] at hs
    rcases hs with ⟨j, hj, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩
    · -- `s = y j`, `j < i`: reverse the cross bit
      have hij : i ≠ j := by omega
      have hne : x i ≠ y j := hxy i hi j (by omega)
      rw [hy.2.2 i hi j (by omega) hij, T.legBit_rev (hx.2.1 i hi).1 (hy.2.1 j (by omega)).1 hne,
        hcross j (by omega) i hi (Ne.symm hij), (hx.2.1 i hi).2, (hy.2.1 j (by omega)).2]
      have hc := hΓ _ (hordV i hi) _ (hordV j (by omega)) (hord i hi j (by omega) hij)
      have := TypeData.zmod2_eq_of_add hc
      rw [this, mul_comm]
    · -- `s = x j`, `i < j`
      have hij : i ≠ j := by omega
      rw [hx.2.2 i hi j hj2 hij, hcross i hi j hj2 hij]
  · rfl

/-- Reverse a cross bit by reciprocity: if `b`'s bits to the primes of `y` are those of the graph,
then `y`'s bits to the primes of `b` are too. -/
theorem cross_rev (T : TypeData L ε) {Γ : Config L} (hΓ : Γ.Compatible ε) {ord : ℕ → ℕ} {k : ℕ}
    (hordV : ∀ i < k, ord i ∈ Γ.V) (hord : ∀ i < k, ∀ j < k, i ≠ j → ord i ≠ ord j)
    {b y : ℕ → ℕ} (hb : IsRealIdx T Γ ord k b) (hy : IsRealIdx T Γ ord k y)
    (hby : ∀ i < k, ∀ j < k, b i ≠ y j)
    (hcross : ∀ i < k, ∀ j < k, i ≠ j → legBit (b i) (y j) = Γ.z (ord i) (ord j)) :
    ∀ i < k, ∀ j < k, i ≠ j → legBit (y i) (b j) = Γ.z (ord i) (ord j) := by
  intro i hi j hj hij
  rw [T.legBit_rev (hy.2.1 i hi).1 (hb.2.1 j hj).1 (fun h => hby j hj i hi h.symm),
    hcross j hj i hi (Ne.symm hij), (hy.2.1 i hi).2, (hb.2.1 j hj).2]
  have hc := hΓ _ (hordV i hi) _ (hordV j hj) (hord i hi j hj hij)
  have := TypeData.zmod2_eq_of_add hc
  rw [this, mul_comm]

open Classical in
/-- A fresh realization whose bits to the primes of two given realizations `x, y` (overlapping at
most index by index) are those of the graph (CRT and Dirichlet; tex L9956–9958, L9966–9968). -/
theorem exists_bridge (T : TypeData L ε) {Γ : Config L} (hΓ : Γ.Compatible ε) {x y : ℕ → ℕ}
    (hx : IsRealIdx T Γ (enumV Γ.V) Γ.V.card x) (hy : IsRealIdx T Γ (enumV Γ.V) Γ.V.card y)
    (hcons : ∀ i < Γ.V.card, ∀ j < Γ.V.card, x i = y j → i = j) (avoid : Finset ℕ) :
    ∃ b : ℕ → ℕ, IsRealIdx T Γ (enumV Γ.V) Γ.V.card b ∧ (∀ i < Γ.V.card, b i ∉ avoid) ∧
      (∀ i < Γ.V.card, ∀ j < Γ.V.card, b i ≠ x j ∧ b i ≠ y j) ∧
      (∀ i < Γ.V.card, ∀ j < Γ.V.card, i ≠ j →
        legBit (b i) (x j) = Γ.z (enumV Γ.V i) (enumV Γ.V j) ∧
        legBit (b i) (y j) = Γ.z (enumV Γ.V i) (enumV Γ.V j)) := by
  set k := Γ.V.card
  set ord := enumV Γ.V
  let old : Finset ℕ := (range k).image x ∪ (range k).image y
  have hold : ∀ p ∈ old, T.Good p := by
    intro p hp
    simp only [old, mem_union, mem_image, mem_range] at hp
    rcases hp with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact (hx.2.1 j hj).1
    · exact (hy.2.1 j hj).1
  let bitOld : ℕ → ℕ → ZMod 2 := fun i p =>
    if h : ∃ j < k, x j = p ∨ y j = p then Γ.z (ord i) (ord h.choose) else 0
  have hbitx : ∀ i j, j < k → bitOld i (x j) = Γ.z (ord i) (ord j) := by
    intro i j hj
    have h : ∃ j' < k, x j' = x j ∨ y j' = x j := ⟨j, hj, Or.inl rfl⟩
    simp only [bitOld, dif_pos' (h)]
    obtain ⟨hlt, hor⟩ := h.choose_spec
    rcases hor with h1 | h1
    · rw [hx.1 (mem_range.mpr hlt) (mem_range.mpr hj) h1]
    · rw [(hcons j hj _ hlt h1.symm).symm]
  have hbity : ∀ i j, j < k → bitOld i (y j) = Γ.z (ord i) (ord j) := by
    intro i j hj
    have h : ∃ j' < k, x j' = y j ∨ y j' = y j := ⟨j, hj, Or.inr rfl⟩
    simp only [bitOld, dif_pos' (h)]
    obtain ⟨hlt, hor⟩ := h.choose_spec
    rcases hor with h1 | h1
    · rw [hcons _ hlt j hj h1]
    · rw [hy.1 (mem_range.mpr hlt) (mem_range.mpr hj) h1]
  obtain ⟨b, hinj, hb, hbold, hnew⟩ := realizeNat T old avoid hold (fun i => Γ.t (ord i)) bitOld
    (fun i j => Γ.z (ord i) (ord j)) k
  have hbreal : IsRealIdx T Γ ord k b := by
    refine ⟨fun i hi j hj h => hinj i (mem_range.mp hi) j (mem_range.mp hj) h,
      fun i hi => ⟨(hb i hi).1, (hb i hi).2.2.2⟩, fun i hi j hj hij => ?_⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hne : b i ≠ b j := fun h => hij (hinj i hi j hj h)
      rw [T.legBit_rev (hb i hi).1 (hb j hj).1 hne, hnew j hj i hlt, (hb i hi).2.2.2,
        (hb j hj).2.2.2]
      have hc := hΓ _ (enumV_mem hj) _ (enumV_mem hi) fun h => hij (enumV_inj hi hj h.symm)
      have := TypeData.zmod2_eq_of_add hc
      rw [this, mul_comm]
      generalize Γ.z (ord i) (ord j) = a
      generalize ε (Γ.t (ord i)) * ε (Γ.t (ord j)) = c
      revert a c; decide
    · exact hnew i hi j hgt
  refine ⟨b, hbreal, fun i hi => (hb i hi).2.2.1,
    fun i hi j hj => ⟨fun h => (hb i hi).2.1 ?_, fun h => (hb i hi).2.1 ?_⟩,
    fun i hi j hj _ => ⟨?_, ?_⟩⟩
  · rw [h]; exact mem_union_left _ (mem_image_of_mem _ (mem_range.mpr hj))
  · rw [h]; exact mem_union_right _ (mem_image_of_mem _ (mem_range.mpr hj))
  · rw [hbold i hi _ (mem_union_left _ (mem_image_of_mem _ (mem_range.mpr hj))), hbitx i j hj]
  · rw [hbold i hi _ (mem_union_right _ (mem_image_of_mem _ (mem_range.mpr hj))), hbity i j hj]

/-- **The reading does not depend on the realization** (tex L9955–9974): two realizations of a
compatible graph within the budget read the same. The first is replaced by a fresh copy avoiding
both, then by a bridge copy, then by the second, one vertex at a time. -/
theorem reading_eq_of_real (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) {Γ : Config L} (hΓ : Γ.Compatible ε)
    (hB : Γ.V.card ≤ B) {f g : ℕ → ℕ} (hf : IsReal T Γ f) (hg : IsReal T Γ g) :
    R (Γ.V.image f) = R (Γ.V.image g) := by
  set k := Γ.V.card
  have hordV : ∀ i < k, enumV Γ.V i ∈ Γ.V := fun i hi => enumV_mem hi
  have hord : ∀ i < k, ∀ j < k, i ≠ j → enumV Γ.V i ≠ enumV Γ.V j :=
    fun i hi j hj hij h => hij (enumV_inj hi hj h)
  have hx := isRealIdx_of_isReal hf
  have hy := isRealIdx_of_isReal hg
  rw [← image_comp_enumV Γ.V f, ← image_comp_enumV Γ.V g]
  set x := fun i => f (enumV Γ.V i)
  set y := fun i => g (enumV Γ.V i)
  have hxinj : ∀ i < k, ∀ j < k, x i = x j → i = j :=
    fun i hi j hj h => hx.1 (mem_range.mpr hi) (mem_range.mpr hj) h
  -- a fresh copy `c` of `x`, avoiding both realizations (tex L9969–9972)
  obtain ⟨c, hc, hcy, hcx, hccross⟩ := exists_bridge T hΓ hx hx hxinj ((range k).image y)
  have h1 : R ((range k).image x) = R ((range k).image c) :=
    chain_eq T R hswap hΓ hB hordV hord hx hc (fun i hi j hj h => (hcx j hj i hi).1 h.symm)
      fun i hi j hj hij => (hccross i hi j hj hij).1
  have hcy' : ∀ i < k, ∀ j < k, c i ≠ y j :=
    fun i hi j hj h => hcy i hi (h ▸ mem_image_of_mem _ (mem_range.mpr hj))
  -- a bridge copy `b` matching `c` and `y` (tex L9956–9964)
  obtain ⟨b, hb, -, hbcy, hbcross⟩ := exists_bridge T hΓ hc hy
    (fun i hi j hj h => absurd h (hcy' i hi j hj)) ∅
  have h2 : R ((range k).image c) = R ((range k).image b) :=
    chain_eq T R hswap hΓ hB hordV hord hc hb (fun i hi j hj h => (hbcy j hj i hi).1 h.symm)
      fun i hi j hj hij => (hbcross i hi j hj hij).1
  have h3 : R ((range k).image b) = R ((range k).image y) :=
    chain_eq T R hswap hΓ hB hordV hord hb hy (fun i hi j hj => (hbcy i hi j hj).2)
      (cross_rev T hΓ hordV hord hb hy (fun i hi j hj => (hbcy i hi j hj).2)
        fun i hi j hj hij => (hbcross i hi j hj hij).2)
  exact h1.trans (h2.trans h3)

/-! ### The symbol on abstract configurations -/

open Classical in
/-- **The symbol on abstract typed graphs**: the reading `R` of any prime realization (and `0`
for an unrealizable configuration). For `R` the coefficient reading of a source
(`readPrimes`), this is the actual symbol of Definition `ex:sec7-symbol` as a function of the
typed graph (tex L2093–2096). -/
noncomputable def symb (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (Γ : Config L) : ZMod 2 :=
  if h : ∃ f, IsReal T Γ f then R (Γ.V.image h.choose) else 0

/-- **The dictionary**: on a compatible graph within the budget, the symbol is the reading of
every prime realization. -/
theorem symb_eq (T : TypeData L ε) (R : Finset ℕ → ZMod 2) {B : ℕ}
    (hswap : FixedUFactorization T R B) {Γ : Config L} (hΓ : Γ.Compatible ε)
    (hB : Γ.V.card ≤ B) {f : ℕ → ℕ} (hf : IsReal T Γ f) : symb T R Γ = R (Γ.V.image f) := by
  classical
  have h : ∃ f, IsReal T Γ f := ⟨f, hf⟩
  rw [symb, dif_pos' (h)]
  exact reading_eq_of_real T R hswap hΓ hB h.choose_spec hf

end ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
