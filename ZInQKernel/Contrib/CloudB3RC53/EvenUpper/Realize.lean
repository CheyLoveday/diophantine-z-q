import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Cubes
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Realize
import ZInQKernel.Contrib.OneProof.RC.Symbols.EvenUpper
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Realization

/-!
# EvenUpper, part 4: the realized cubes (`hcubes`)

Manuscript `diophantine_zq.tex`, tex 2318–2322: "For a partitionable parameter `d` already known to
have Selmer corank zero, keep all its prime factors stationary. Lemma `ex:sec7-one-symbol-address`
gives arbitrarily large binary cubes based at `d`, with no old prime removed, whose other addresses
satisfy (3.3a)"; realization by primes, tex 2151–2174.

This file makes lane RC2's `one_symbol_address` concrete by primes and discharges the input
`hcubes` of `evenUpperInputsAt_of'` / `evenUpper33b_of_RC11'` (`Cubes.lean`).

* `exists_real_extension` (`PROVED`, RC2's `finite_realization_nat`: CRT and Dirichlet): a
  compatible extension `Γ'` of the typed graph of a set `P` of good primes (RC2's `primeConfig`)
  whose new vertices have type zero is realized by the identity on `P` and by distinct new primes
  `≡ 1 (mod m·K)` with the prescribed residue bits (reverse bits by reciprocity).
* `cubeQ` and its lemmas (`PROVED`): the new factor `Q_x` of the parameter at an address is the
  product of the new primes present there; `Q_0 = 1`, `Q_x ≡ 1 (mod 8N₀)`, `Q_x` is squarefree and
  prime to `d`, and `Q_{x+y} Q_x Q_y` is a square (the activations are linear).
* `realized_cubes` (`PROVED`): for squarefree `d` whose primes are good and prime to `N₀`, with
  the typed graph of its primes partitionable for the dictionary symbol `symb T R`, and every
  `b ≥ 1`, RC11's `BinaryFamily N₀` with `h_x = d·Q_x`, based at `d`, whose nonzero addresses are
  readings `R = 1` of good prime sets (so units, by `hunitR`).  The family need not have distinct
  parameters; `Cubes.lean` does not need them.
* `hcubes_of_dictionary`, `evenUpper33b_of_dictionary` (`PROVED`): the wiring into RC0's
  `EvenUpper33b`.

Hypotheses (named after what they state; none is a model structure):
* `hswap`, `hA` — the readings of lane RC12 through the coefficient dictionary
  (`FixedUFactorization`; `CoefficientRules` of `symb T R`, which `coefficientRules_symb` derives
  from RC12's readings). They do not use `TraceModel` or `ConstituentModel`.
* `htyp1` (GLUE, `TypeData.classes`: types are read from reduced classes modulo `m` through
  characters) — a prime `≡ 1 (mod m)` has type zero.
* `hspec` — the meaning of `W.Partitionable` (Definition `ex:sec7-seed-partition`, tex 2144–2185,
  read through the dictionary, as in `AuxFactor/Dictionary.lean`): `d` is squarefree, its primes
  are good and prime to the level, and the typed graph of its primes is partitionable.
* `hunitR` — (3.3a)'s unit: a reading one at a set of good primes is a unit at `sgn(d)·∏ p`
  (App E (E.11) at the minimum depth, tex 2302–2310).
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

section Realization

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- A realization restricts to every address (`PROVED`). -/
theorem isReal_at (T : TypeData L ε) {Γ : Config L} {f : ℕ → ℕ} (hf : IsReal T Γ f) {b : ℕ}
    (act : ℕ → Option (Fin b → ZMod 2)) (x : Fin b → ZMod 2) : IsReal T (Γ.at act x) f := by
  classical
  have hsub : ∀ v ∈ (Γ.at act x).V, v ∈ Γ.V := by
    intro v hv; simp only [Config.at, Finset.mem_filter] at hv; exact hv.1
  exact ⟨fun v hv w hw h => hf.1 (hsub v hv) (hsub w hw) h, fun v hv => hf.2.1 v (hsub v hv),
    fun v hv w hw hvw => hf.2.2 v (hsub v hv) w (hsub w hw) hvw⟩

/-- A reverse bit from the forward bit, by reciprocity and compatibility (`PROVED`). -/
theorem legBit_of_rev (T : TypeData L ε) {Γ : Config L} (hΓ : Γ.Compatible ε) {v w : ℕ}
    (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hvw : v ≠ w) {a c : ℕ} (ha : T.Good a ∧ T.typ a = Γ.t v)
    (hc : T.Good c ∧ T.typ c = Γ.t w) (hac : a ≠ c) (h : legBit c a = Γ.z w v) :
    legBit a c = Γ.z v w := by
  rw [T.legBit_rev ha.1 hc.1 hac, h, ha.2, hc.2]
  have := TypeData.zmod2_eq_of_add (hΓ v hv w hw hvw)
  rw [this]

/-- **Realization of an extension with stationary old primes** (tex 2151–2174, RC2's
`finite_realization_nat`), `PROVED`. -/
theorem exists_real_extension (T : TypeData L ε) (K : ℕ) (hK : 0 < K)
    (htyp1 : ∀ q : ℕ, q.Prime → ((q : ℕ) : ZMod T.m) = 1 → T.typ q = 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, T.Good p ∧ Nat.Coprime p K) (Γ' : Config L)
    (hΓ' : Γ'.Compatible ε) (hext : (primeConfig P T.typ).Extends Γ')
    (hnew : ∀ v ∈ Γ'.V, v ∉ P → Γ'.t v = 0) :
    ∃ f : ℕ → ℕ, IsReal T Γ' f ∧ (∀ v ∈ P, f v = v) ∧
      ∀ v ∈ Γ'.V, v ∉ P → f v ∉ P ∧ ((f v : ℕ) : ZMod (T.m * K)) = 1 := by
  classical
  set Vn := Γ'.V.filter (· ∉ P) with hVn
  have hm : 0 < T.m * K := Nat.mul_pos T.m_pos hK
  have h2 : 2 ∣ T.m * K := dvd_mul_of_dvd_left T.two_dvd K
  have hold : ∀ p ∈ P, p.Prime ∧ Nat.Coprime p (T.m * K) := fun p hp =>
    ⟨(hP p hp).1.1, Nat.Coprime.mul_right (hP p hp).1.2 (hP p hp).2⟩
  obtain ⟨q, hinj, hq, hqold, hqnew⟩ := finite_realization_nat (T.m * K) hm h2 P hold ∅
    (fun _ => 1) (fun _ => isUnit_one) (fun i p => Γ'.z (enumV Vn i) p)
    (fun i j => Γ'.z (enumV Vn i) (enumV Vn j)) Vn.card
  have hqgood : ∀ i < Vn.card, T.Good (q i) ∧ T.typ (q i) = 0 := by
    intro i hi
    obtain ⟨hp, -, -, hc⟩ := hq i hi
    have hcop : Nat.Coprime (q i) (T.m * K) :=
      (ZMod.isUnit_iff_coprime _ _).mp (by rw [hc]; exact isUnit_one)
    refine ⟨⟨hp, Nat.Coprime.coprime_dvd_right (dvd_mul_right T.m K) hcop⟩, htyp1 _ hp ?_⟩
    have := congrArg (ZMod.castHom (dvd_mul_right T.m K) (ZMod T.m)) hc
    simpa using this
  let f : ℕ → ℕ := fun v => if v ∈ P then v else q (idxV Vn v)
  have hfP : ∀ v ∈ P, f v = v := fun v hv => by simp [f, hv]
  have hmemVn : ∀ v ∈ Γ'.V, v ∉ P → v ∈ Vn := fun v hv hvP => by simp [hVn, hv, hvP]
  have hfN : ∀ v ∈ Γ'.V, v ∉ P → f v = q (idxV Vn v) ∧ idxV Vn v < Vn.card ∧
      enumV Vn (idxV Vn v) = v := fun v hv hvP => by
    refine ⟨by simp [f, hvP], idxV_spec (hmemVn v hv hvP)⟩
  -- types
  have htype : ∀ v ∈ Γ'.V, T.Good (f v) ∧ T.typ (f v) = Γ'.t v := by
    intro v hv
    by_cases hvP : v ∈ P
    · rw [hfP v hvP, hext.2.1 v hvP]; exact ⟨(hP v hvP).1, rfl⟩
    · obtain ⟨hf, hi, -⟩ := hfN v hv hvP
      rw [hf, hnew v hv hvP]; exact hqgood _ hi
  have hfnotP : ∀ v ∈ Γ'.V, v ∉ P → f v ∉ P := fun v hv hvP => by
    obtain ⟨hf, hi, -⟩ := hfN v hv hvP; rw [hf]; exact (hq _ hi).2.1
  -- injectivity
  have hinjOn : Set.InjOn f Γ'.V := by
    intro v hv w hw hfvw
    by_cases hvP : v ∈ P <;> by_cases hwP : w ∈ P
    · rwa [hfP v hvP, hfP w hwP] at hfvw
    · exact absurd (by rw [← hfvw, hfP v hvP]; exact hvP) (hfnotP w hw hwP)
    · exact absurd (by rw [hfvw, hfP w hwP]; exact hwP) (hfnotP v hv hvP)
    · obtain ⟨hfv, hiv, hev⟩ := hfN v hv hvP
      obtain ⟨hfw, hiw, hew⟩ := hfN w hw hwP
      rw [hfv, hfw] at hfvw
      rw [← hev, ← hew, hinj _ hiv _ hiw hfvw]
  -- forward bits (new over old, and new over earlier new)
  have hbits : ∀ v ∈ Γ'.V, ∀ w ∈ Γ'.V, v ≠ w → legBit (f v) (f w) = Γ'.z v w := by
    -- the bits that are prescribed directly
    have hdir : ∀ v ∈ Γ'.V, ∀ w ∈ Γ'.V, v ≠ w → v ∉ P →
        (w ∈ P ∨ (w ∉ P ∧ idxV Vn w < idxV Vn v)) → legBit (f v) (f w) = Γ'.z v w := by
      intro v hv w hw hvw hvP hcase
      obtain ⟨hfv, hiv, hev⟩ := hfN v hv hvP
      rcases hcase with hwP | ⟨hwP, hlt⟩
      · rw [hfv, hfP w hwP, hqold _ hiv w hwP, hev]
      · obtain ⟨hfw, hiw, hew⟩ := hfN w hw hwP
        rw [hfv, hfw, hqnew _ hiv _ hlt, hev, hew]
    have hne : ∀ v ∈ Γ'.V, ∀ w ∈ Γ'.V, v ≠ w → f v ≠ f w := fun v hv w hw hvw h =>
      hvw (hinjOn hv hw h)
    intro v hv w hw hvw
    by_cases hvP : v ∈ P <;> by_cases hwP : w ∈ P
    · rw [hfP v hvP, hfP w hwP, hext.2.2 v hvP w hwP]; rfl
    · exact legBit_of_rev T hΓ' hv hw hvw (htype v hv) (htype w hw) (hne v hv w hw hvw)
        (hdir w hw v hv (Ne.symm hvw) hwP (Or.inl hvP))
    · exact hdir v hv w hw hvw hvP (Or.inl hwP)
    · have hij : idxV Vn v ≠ idxV Vn w := fun h => hvw (by
        rw [← (hfN v hv hvP).2.2, ← (hfN w hw hwP).2.2, h])
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact legBit_of_rev T hΓ' hv hw hvw (htype v hv) (htype w hw) (hne v hv w hw hvw)
          (hdir w hw v hv (Ne.symm hvw) hwP (Or.inr ⟨hvP, hlt⟩))
      · exact hdir v hv w hw hvw hvP (Or.inr ⟨hwP, hgt⟩)
  exact ⟨f, ⟨hinjOn, htype, hbits⟩, hfP, fun v hv hvP => ⟨hfnotP v hv hvP, by
    obtain ⟨hf, hi, -⟩ := hfN v hv hvP; rw [hf]; exact (hq _ hi).2.2.2⟩⟩

end Realization

section Family

open Classical in
/-- The new factor of the parameter at an address: the product of the realized new primes present
there. -/
noncomputable def cubeQ {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ) (f : ℕ → ℕ)
    (x : Fin b → ZMod 2) : ℕ :=
  ∏ v ∈ Vn, if present act x v then f v else 1

/-- No new prime is present at the zero address (`PROVED`). -/
theorem cubeQ_zero {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ) (f : ℕ → ℕ)
    (hact : ∀ v ∈ Vn, ∃ w, act v = some w) : cubeQ act Vn f 0 = 1 := by
  classical
  unfold cubeQ
  refine Finset.prod_eq_one fun v hv => ?_
  obtain ⟨w, hw⟩ := hact v hv
  have : ¬ present act 0 v := by simp [present, hw]
  simp [this]

/-- `Q_x ≡ 1` modulo the class of the new primes (`PROVED`). -/
theorem cubeQ_mod {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ) (f : ℕ → ℕ)
    (K : ℕ) (hf : ∀ v ∈ Vn, ((f v : ℕ) : ZMod K) = 1) (x : Fin b → ZMod 2) :
    ((cubeQ act Vn f x : ℕ) : ZMod K) = 1 := by
  classical
  unfold cubeQ
  rw [Nat.cast_prod]
  refine Finset.prod_eq_one fun v hv => ?_
  split_ifs
  · exact hf v hv
  · simp

/-- `Q_{x+y} Q_x Q_y` is a square: the activations are linear (`PROVED`). -/
theorem cubeQ_hom {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ) (f : ℕ → ℕ)
    (hact : ∀ v ∈ Vn, ∃ w, act v = some w) (x y : Fin b → ZMod 2) :
    IsSquare (cubeQ act Vn f (x + y) * cubeQ act Vn f x * cubeQ act Vn f y) := by
  classical
  unfold cubeQ
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.isSquare_prod _ fun v hv => ?_
  obtain ⟨w, hw⟩ := hact v hv
  simp only [present, hw]
  have hsum : (∑ i, w i * (x + y) i) = (∑ i, w i * x i) + ∑ i, w i * y i := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsum]
  generalize (∑ i, w i * x i) = a
  generalize (∑ i, w i * y i) = c
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 c with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨f v, by simp⟩
  · exact ⟨f v, by simp⟩
  · exact ⟨f v, by simp [h11]⟩

open Classical in
/-- `Q_x` is the product of the new primes present at `x` (`PROVED`). -/
theorem cubeQ_eq_prod_filter {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ)
    (f : ℕ → ℕ) (x : Fin b → ZMod 2) :
    cubeQ act Vn f x = ∏ v ∈ Vn.filter (present act x), f v := by
  classical
  unfold cubeQ
  rw [Finset.prod_filter]

/-- `Q_x` is squarefree (`PROVED`). -/
theorem cubeQ_squarefree {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ)
    (f : ℕ → ℕ) (hp : ∀ v ∈ Vn, (f v).Prime) (hinj : Set.InjOn f Vn) (x : Fin b → ZMod 2) :
    Squarefree (cubeQ act Vn f x) := by
  classical
  rw [cubeQ_eq_prod_filter]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha c hc hac => ?_)
    fun v hv => (hp v (Finset.mem_filter.mp hv).1).squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  have ha' := (Finset.mem_filter.mp ha).1
  have hc' := (Finset.mem_filter.mp hc).1
  exact (Nat.coprime_primes (hp a ha') (hp c hc')).mpr fun h => hac (hinj ha' hc' h)

/-- `Q_x` is prime to `n` when the new primes do not divide it (`PROVED`). -/
theorem coprime_cubeQ {b : ℕ} (act : ℕ → Option (Fin b → ZMod 2)) (Vn : Finset ℕ)
    (f : ℕ → ℕ) (n : ℕ) (hn : n ≠ 0) (hp : ∀ v ∈ Vn, (f v).Prime ∧ f v ∉ n.primeFactors)
    (x : Fin b → ZMod 2) : Nat.Coprime n (cubeQ act Vn f x) := by
  classical
  unfold cubeQ
  refine Nat.Coprime.prod_right fun v hv => ?_
  split_ifs
  · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hp v hv).1).mpr fun hd => ?_)
    exact (hp v hv).2 (Nat.mem_primeFactors.mpr ⟨(hp v hv).1, hd, hn⟩)
  · exact Nat.coprime_one_right n

/-- A natural number `≡ 1 (mod 8N₀)` is a square at every prime dividing `2N₀`. -/
theorem isSquareAt_of_mod {N₀ : ℕ} (Q : ℕ) (hQ : ((Q : ℕ) : ZMod (8 * N₀)) = 1) {p : ℕ}
    (hp : p.Prime) (hpN : p ∣ 2 * N₀) :
    ZInQ.Manuscript.RC.Nonvanishing.IsSquareAt p (Q : ℚ) := by
  have hmod : Q ≡ 1 [MOD 8 * N₀] := by
    rw [← ZMod.natCast_eq_natCast_iff, hQ, Nat.cast_one]
  by_cases hp2 : p = 2
  · subst hp2
    have h8 : (Q : ℤ) ≡ 1 [ZMOD 8] := by
      have := Nat.ModEq.of_mul_right N₀ hmod
      exact_mod_cast Int.natCast_modEq_iff.mpr this
    have := ZInQ.Manuscript.RC.Nonvanishing.isSquareAt_two_div_of_modEq (a := Q) (b := 1)
      odd_one h8
    simpa using this
  · have hpN0 : p ∣ N₀ := by
      rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
      · exact h
    have hmp : Q ≡ 1 [MOD p] := Nat.ModEq.of_dvd (Dvd.dvd.mul_left hpN0 8) hmod
    have hmp' : (Q : ℤ) ≡ 1 [ZMOD p] := by exact_mod_cast Int.natCast_modEq_iff.mpr hmp
    have hnd : ¬ (p : ℤ) ∣ 1 := by
      intro h
      have := Int.natCast_dvd_natCast.mp (by exact_mod_cast h : (p : ℤ) ∣ ((1 : ℕ) : ℤ))
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have := ZInQ.Manuscript.RC.Nonvanishing.isSquareAt_div_of_modEq hp2 hnd hmp'
    simpa using this

end Family


section Cube

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **The realized cubes** (tex 2311–2322 made concrete by primes, tex 2151–2174), `PROVED`. -/
theorem realized_cubes (T : TypeData L ε) (R : Finset ℕ → ZMod 2)
    (hswap : ∀ B, FixedUFactorization T R B) (hA : CoefficientRules ε (symb T R))
    (htyp1 : ∀ q : ℕ, q.Prime → ((q : ℕ) : ZMod T.m) = 1 → T.typ q = 0)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (unitSym : ℤ → Prop) (d : ℤ) (hsq : Squarefree d)
    (hgood : ∀ p ∈ d.natAbs.primeFactors, T.Good p ∧ Nat.Coprime p N₀)
    (hpart : IsPartitionable ε (symb T R) (primeConfig d.natAbs.primeFactors T.typ))
    (hunitR : ∀ W : Finset ℕ, (∀ p ∈ W, T.Good p) → R W = 1 →
      unitSym (d.sign * ∏ p ∈ W, (p : ℤ)))
    (b : ℕ) (hb : 1 ≤ b) :
    ∃ fam : ZInQ.Manuscript.RC.Even.BinaryFamily N₀, fam.b = b ∧ fam.h 0 = d ∧
      ∀ x, x ≠ 0 → unitSym (fam.h x) := by
  classical
  set P := d.natAbs.primeFactors with hPdef
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hn0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  set Γ := primeConfig P T.typ with hΓdef
  have hf0 : IsReal T Γ id :=
    ⟨Set.injOn_id _, fun v hv => ⟨(hgood v hv).1, rfl⟩, fun v _ w _ _ => rfl⟩
  have hΓ : Γ.Compatible ε := compatible_of_real T hf0
  obtain ⟨Γ', act'', hΓ', hext, hact, hnew, hunit⟩ :=
    one_symbol_address hA Γ hΓ hpart.1 (partitionable_terminalNonzero hA hΓ hpart) b hb
  have hcop8 : ∀ p ∈ P, Nat.Coprime p (8 * N₀) := by
    intro p hp
    refine Nat.Coprime.mul_right ?_ (hgood p hp).2
    have h2 : Nat.Coprime p 2 :=
      (Nat.coprime_primes (hgood p hp).1.1 Nat.prime_two).mpr (hgood p hp).1.ne_two
    simpa using Nat.Coprime.pow_right 3 h2
  obtain ⟨f, hf, hfP, hfN⟩ := exists_real_extension T (8 * N₀) (by omega) htyp1 P
    (fun p hp => ⟨(hgood p hp).1, hcop8 p hp⟩) Γ' hΓ' hext (fun v hv hvP => (hnew v hv hvP).1)
  set Vn := Γ'.V.filter (· ∉ P) with hVn
  have hVact : ∀ v ∈ Vn, ∃ w, act'' v = some w := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, w, -, hw⟩ := hnew v hv hvP
    exact ⟨w, hw⟩
  have hVprime : ∀ v ∈ Vn, (f v).Prime ∧ f v ∉ P := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    exact ⟨(hf.2.1 v hv).1.1, (hfN v hv hvP).1⟩
  have hVmod : ∀ v ∈ Vn, ((f v : ℕ) : ZMod (8 * N₀)) = 1 := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    have := congrArg (ZMod.castHom (dvd_mul_left (8 * N₀) T.m) (ZMod (8 * N₀)))
      (hfN v hv hvP).2
    simpa using this
  have hinjVn : Set.InjOn f Vn := fun v hv w hw h =>
    hf.1 (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 h
  set Q := cubeQ act'' Vn f with hQdef
  have hQ0 : Q 0 = 1 := cubeQ_zero act'' Vn f hVact
  have hQmod : ∀ x, ((Q x : ℕ) : ZMod (8 * N₀)) = 1 := cubeQ_mod act'' Vn f _ hVmod
  have hQodd : ∀ x, Odd (Q x) := by
    intro x
    have h := hQmod x
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
    have h2 : Q x ≡ 1 [MOD 2] := Nat.ModEq.of_dvd ⟨4 * N₀, by ring⟩ h
    exact Nat.odd_iff.mpr h2
  have hQpos : ∀ x, (0 : ℤ) < Q x := fun x => by exact_mod_cast (hQodd x).pos
  have hdodd : Odd d := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have h2P : 2 ∈ P := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, Int.ofNat_dvd_left.mp h2, hn0⟩
    exact (hgood 2 h2P).1.ne_two rfl
  let fam : ZInQ.Manuscript.RC.Even.BinaryFamily N₀ :=
    { b := b
      h := fun x => d * (Q x : ℤ)
      odd := fun x => Int.odd_mul.mpr ⟨hdodd, (hQodd x).natCast⟩
      sqfree := fun x => by
        rw [← Int.squarefree_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.squarefree_mul_iff.mpr ⟨coprime_cubeQ act'' Vn f _ hn0 hVprime x,
          Int.squarefree_natAbs.mpr hsq, cubeQ_squarefree act'' Vn f
            (fun v hv => (hVprime v hv).1) hinjVn x⟩
      sign := fun x => by
        simp only [hQ0, Nat.cast_one, mul_one]
        have := hQpos x
        constructor
        · intro h; by_contra hd; nlinarith [not_lt.mp hd]
        · intro h; positivity
      local_sq := fun x p hp => by
        have := Fact.mk p.2
        have hs := ZInQ.Manuscript.RC.Nonvanishing.isSquareAt_mul
          (ZInQ.Manuscript.RC.Nonvanishing.isSquareAt_sq (d : ℚ))
          (isSquareAt_of_mod (Q x) (hQmod x) p.2 hp) (Fact.mk p.2)
        have he : (((d * (Q x : ℤ) * (d * (Q 0 : ℤ)) : ℤ) : ℚ_[(p : ℕ)])) =
            ((((d : ℚ) ^ 2 * (Q x : ℚ) : ℚ)) : ℚ_[(p : ℕ)]) := by
          rw [hQ0]; push_cast; ring
        rw [he]; exact hs
      hom := fun x y => by
        obtain ⟨r, hr⟩ := cubeQ_hom act'' Vn f hVact x y
        have hr' : ((Q (x + y) : ℕ) : ℤ) * Q x * Q y = (r : ℤ) * r := by exact_mod_cast hr
        refine ⟨d * d * r, ?_⟩
        rw [hQ0]; push_cast
        linear_combination d ^ 4 * hr' }
  refine ⟨fam, rfl, by simp [fam, hQ0], fun x hx => ?_⟩
  have h1 : symb T R (Γ'.at act'' x) = 1 := by simpa using hunit x hx 0
  have hfx := isReal_at T hf act'' x
  rw [symb_eq T R (hswap _) (Config.at_compatible hΓ' act'' x) le_rfl hfx] at h1
  have hgoodW : ∀ p ∈ (Γ'.at act'' x).V.image f, T.Good p := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact (hfx.2.1 v hv).1
  have hu := hunitR _ hgoodW h1
  have heq : d.sign * ∏ p ∈ (Γ'.at act'' x).V.image f, (p : ℤ) = fam.h x := by
    rw [Finset.prod_image (fun v hv w hw h => hfx.1 hv hw h),
      ← Finset.prod_filter_mul_prod_filter_not (Γ'.at act'' x).V (· ∈ P)]
    have hVxP : (Γ'.at act'' x).V.filter (· ∈ P) = P := by
      ext v
      simp only [Config.at, Finset.mem_filter]
      constructor
      · rintro ⟨-, hv⟩; exact hv
      · intro hv
        exact ⟨⟨hext.1 hv, by simp [present, hact v hv]⟩, hv⟩
    have hVxN : (Γ'.at act'' x).V.filter (· ∉ P) = Vn.filter (present act'' x) := by
      ext v
      simp only [Config.at, hVn, Finset.mem_filter]
      tauto
    rw [hVxP, hVxN, Finset.prod_congr rfl (fun v hv => by rw [hfP v hv])]
    have hprodP : ∏ v ∈ P, (v : ℤ) = d.natAbs := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsq)]
    rw [hprodP, ← mul_assoc, Int.sign_mul_natAbs]
    simp only [fam, hQdef, cubeQ_eq_prod_filter]
    push_cast
    rfl
  rw [← heq]; exact hu

end Cube

section Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **The input `hcubes` of `evenUpperInputsAt_of'`** from the coefficient dictionary, `PROVED`
from `realized_cubes`. -/
theorem hcubes_of_dictionary {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (R : ℤ → Finset ℕ → ZMod 2) (hswap : ∀ d B, FixedUFactorization T (R d) B)
    (hA : ∀ d, CoefficientRules ε (symb T (R d)))
    (htyp1 : ∀ q : ℕ, q.Prime → ((q : ℕ) : ZMod T.m) = 1 → T.typ q = 0)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (unitSym : ℤ → Prop)
    (hspec : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      Squarefree d ∧ (∀ p ∈ d.natAbs.primeFactors, T.Good p ∧ Nat.Coprime p N₀) ∧
        IsPartitionable ε (symb T (R d)) (primeConfig d.natAbs.primeFactors T.typ))
    (hunitR : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) →
      R d V = 1 → unitSym (d.sign * ∏ p ∈ V, (p : ℤ))) :
    ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : ZInQ.Manuscript.RC.Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧
        ∀ x, x ≠ 0 → unitSym (fam.h x) := by
  intro d hd0 hpart hcz b
  obtain ⟨hsq, hgood, hP⟩ := hspec d hd0 hpart hcz
  obtain ⟨fam, hb, h0, hu⟩ := realized_cubes T (R d) (hswap d) (hA d) htyp1 hN₀ unitSym d hsq
    hgood hP (hunitR d hd0 hpart) (b + 1) (Nat.le_add_left 1 b)
  exact ⟨fam, by omega, h0, hu⟩

/-- **(3.3b) assembled with the realized cubes** (tex 2273–2341), `PROVED` from
`evenUpper33b_of_RC11'` and `hcubes_of_dictionary`. -/
theorem evenUpper33b_of_dictionary {ℓ : ℕ} (W : WData ℓ) (P : Prints) (hKum : KummerCorankZero)
    (hℓ : 0 < ℓ) (hL : LstarTarget W.toRCData) (hN : LstarNormalized W.toRCData) {N₀ : ℕ}
    (hN₀ : 0 < N₀)
    (h32 : ∀ L : ZInQ.Manuscript.RC.Even.CentralNormalization (Ecurve ℓ), L.Lstar = W.Lstar →
      ZInQ.Manuscript.RC.Even.EvenScalar32 (Ecurve ℓ) N₀ L)
    (aNZ : ℤ → Prop) (va : ℤ → ℤ) (κ c : ℤ)
    (hE11 : ∀ D, (W.Lstar D ≠ 0 ↔ aNZ D) ∧ (aNZ D → padicValRat 2 (W.Lstar D) = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - Nonvanishing.omega D) (href : ∃ D, aNZ D)
    (hNZ : ∀ D, aNZ D → D ≠ 0)
    (T : TypeData L ε) (R : ℤ → Finset ℕ → ZMod 2) (hswap : ∀ d B, FixedUFactorization T (R d) B)
    (hA : ∀ d, CoefficientRules ε (symb T (R d)))
    (htyp1 : ∀ q : ℕ, q.Prime → ((q : ℕ) : ZMod T.m) = 1 → T.typ q = 0)
    (hspec : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      Squarefree d ∧ (∀ p ∈ d.natAbs.primeFactors, T.Good p ∧ Nat.Coprime p N₀) ∧
        IsPartitionable ε (symb T (R d)) (primeConfig d.natAbs.primeFactors T.typ))
    (hunitR : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) →
      R d V = 1 → UnitMin aNZ va (d.sign * ∏ p ∈ V, (p : ℤ))) :
    ∃ C₁ : ℤ, EvenUpper33b W C₁ :=
  evenUpper33b_of_RC11' W P hKum hℓ hL hN h32 aNZ va κ c hE11 hE9 href hNZ
    (hcubes_of_dictionary W T R hswap hA htyp1 hN₀ _ hspec hunitR)

end Wiring

end ZInQ.Contrib.CloudB3RC53.EvenUpper
