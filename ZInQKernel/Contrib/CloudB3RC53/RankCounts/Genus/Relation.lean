import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Statements
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-!
# Genus bound, stage 7: a principal product of ramified primes (the ideal of `√d`)

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:limits-residual-bound`, tex 4507–4511:

> Their classes have exponent two, and the principal ideal of `√d`, where `d` is the squarefree
> radicand of `K`, supplies a nonempty relation among them. … The excluded field `ℚ(i)` would also
> satisfy the inequality, since its class group is trivial.

Write `K = ℚ(θ)` with `θ ∈ 𝒪_K`, `θ² = m`, `m` a squarefree integer (`Splitting.exists_sqrt_gen`).
If `m ≠ −1`, every prime `P_p` of `𝒪_K` above a prime `p ∣ m` contains `θ` and `σθ = −θ`, so it is
neither split nor inert (otherwise `θ ∈ (p)`, and taking norms `p² ∣ m`): it is ramified,
`P_p² = (p)`; and `(θ) = ∏_{p ∣ m} P_p` (both sides square to `(m)`). If `m = −1` (`K = ℚ(i)`),
Elliot's relation from `√d` is empty, and we use instead `(1 + θ) = P₂` with `P₂` the ramified
prime above `2` (`(1 + θ)² = 2θ`); this is the triviality of the class of `P₂` behind Elliot's remark
on `ℚ(i)` (DEPARTURE in form only: the relation `[P₂] = 1` replaces the appeal to the class number
of `ℚ(i)`). Either way some nonempty product of distinct ramified primes is principal:
`ramRelation_of : RamRelation K hK2`, from the trichotomy `PrimeTrichotomy K hK2` (stage 1).
Kinds: PROVED (from `PrimeTrichotomy`).
-/

noncomputable section

open NumberField Pointwise

namespace ZInQ.Contrib.CloudB3RC53.RankCounts.Genus

variable {K : Type} [Field K] [NumberField K]

/-- The norm of an integer `a` in `𝒪_K`, `[K : ℚ] = 2`, is `a²`. -/
theorem norm_intCast (hK2 : Module.finrank ℚ K = 2) (a : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K)) = a ^ 2 := by
  rw [← eq_intCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank, hK2]

/-- Taking norms: if `b = a y` in `𝒪_K` with `a, b ∈ ℤ`, then `a² ∣ b²`. -/
theorem sq_dvd_sq_of_eq_mul (hK2 : Module.finrank ℚ K = 2) {a b : ℤ} {y : 𝓞 K}
    (h : (b : 𝓞 K) = a * y) : a ^ 2 ∣ b ^ 2 := by
  have := congrArg (Algebra.norm ℤ) h
  rw [map_mul, norm_intCast hK2, norm_intCast hK2] at this
  exact ⟨_, this⟩

omit [NumberField K] in
/-- Two rational primes in a proper ideal of `𝒪_K` are equal. -/
theorem prime_eq_of_mem {P : Ideal (𝓞 K)} (hP : P ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : ((p : ℤ) : 𝓞 K) ∈ P) (hqP : ((q : ℤ) : 𝓞 K) ∈ P) : p = q := by
  by_contra hne
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom (𝓞 K))
  apply hP
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

/-- The rational prime given by the trichotomy lies in `P`. -/
theorem mem_of_trichotomy {hK2 : Module.finrank ℚ K = 2} {P : Ideal (𝓞 K)} {p : ℕ}
    (h : (conjAut hK2 • P ≠ P ∧ P * conjAut hK2 • P = Ideal.span {((p : ℤ) : 𝓞 K)}) ∨
     (conjAut hK2 • P = P ∧ P = Ideal.span {((p : ℤ) : 𝓞 K)}) ∨
     (conjAut hK2 • P = P ∧ P ^ 2 = Ideal.span {((p : ℤ) : 𝓞 K)})) :
    ((p : ℤ) : 𝓞 K) ∈ P := by
  have hs : ((p : ℤ) : 𝓞 K) ∈ Ideal.span {((p : ℤ) : 𝓞 K)} := Ideal.mem_span_singleton_self _
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · rw [← h] at hs
    exact Ideal.mul_le_left hs
  · rw [← h] at hs
    exact hs
  · rw [← h] at hs
    exact Ideal.pow_le_self two_ne_zero hs

theorem conjAut_smul_conjAut_smul (hK2 : Module.finrank ℚ K = 2) (I : Ideal (𝓞 K)) :
    conjAut hK2 • conjAut hK2 • I = I := by
  rw [smul_smul, conjAut_mul_self, one_smul]

/-- A maximal ideal and a different conjugate are coprime. -/
theorem sup_conjAut_eq_top (hK2 : Module.finrank ℚ K = 2) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hne : conjAut hK2 • P ≠ P) : P ⊔ conjAut hK2 • P = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hPM : P = M := hP.eq_of_le hM.ne_top (le_sup_left.trans hle)
  have h1 : conjAut hK2 • P ≤ P := (le_sup_right.trans hle).trans hPM.ge
  have h2 : P ≤ conjAut hK2 • P := by
    have := Ideal.pointwise_smul_le_pointwise_smul_iff (a := conjAut hK2) |>.mpr h1
    rwa [conjAut_smul_conjAut_smul] at this
  exact hne (le_antisymm h1 h2)

/-- `σθ = −θ` for `θ ∉ ℚ` with `θ² ∈ ℚ`. -/
theorem conjAut_smul_sqrt (hK2 : Module.finrank ℚ K = 2) {θ : 𝓞 K} {m : ℤ}
    (hθ2 : (θ : K) ^ 2 = m) (hθ : (θ : K) ∉ (algebraMap ℚ K).range) :
    conjAut hK2 • θ = -θ := by
  have hs : (conjAut hK2 (θ : K)) ^ 2 = (θ : K) ^ 2 := by
    rw [← map_pow, hθ2, show ((m : ℤ) : K) = algebraMap ℚ K (m : ℚ) by simp, AlgEquiv.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · obtain ⟨q, hq⟩ := exists_rat_of_conjAut_eq hK2 h
    exact absurd ⟨q, hq.symm⟩ hθ
  · exact RingOfIntegers.ext h

/-- **A prime containing an element `x` and its conjugate ideal, with `x ∉ (p)`, is ramified**
(via the trichotomy: split would give `x ∈ P ⊓ σP = P σP = (p)`, inert `x ∈ P = (p)`). -/
theorem ramified_of_mem (hK2 : Module.finrank ℚ K = 2) (hT : PrimeTrichotomy K hK2)
    {P : Ideal (𝓞 K)} (hPmax : P.IsMaximal) (hne : P ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hpP : ((p : ℤ) : 𝓞 K) ∈ P) {x : 𝓞 K} (hxP : x ∈ P) (hxσ : x ∈ conjAut hK2 • P)
    (hx : x ∉ Ideal.span {((p : ℤ) : 𝓞 K)}) :
    RamPrime K hK2 P ∧ P ^ 2 = Ideal.span {((p : ℤ) : 𝓞 K)} := by
  obtain ⟨p', hp', h⟩ := hT P hPmax.isPrime hne
  have hp'P := mem_of_trichotomy h
  obtain rfl := prime_eq_of_mem hPmax.ne_top hp' hp hp'P hpP
  rcases h with ⟨hσ, h⟩ | ⟨-, h⟩ | ⟨hσ, h⟩
  · exfalso
    apply hx
    rw [← h, Ideal.mul_eq_inf_of_coprime (sup_conjAut_eq_top hK2 hPmax hσ)]
    exact ⟨hxP, hxσ⟩
  · exact absurd (h ▸ hxP) hx
  · exact ⟨⟨hPmax.isPrime, hσ, p', hp', h⟩, h⟩

/-- **The square trick**: if `A ∣ (x)` and `A² = (x)²`, then `(x) = A` (Dedekind cancellation). -/
theorem span_eq_of_dvd_of_sq_eq {x : 𝓞 K} (hx : x ≠ 0) {A : Ideal (𝓞 K)}
    (hA : A ∣ Ideal.span {x}) (hsq : A ^ 2 = Ideal.span {x} ^ 2) : Ideal.span {x} = A := by
  obtain ⟨Q, hQ⟩ := hA
  have hx0 : Ideal.span {x} ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hx)
  have hQ2 : Q ^ 2 = 1 := by
    have h : Ideal.span {x} ^ 2 * Q ^ 2 = Ideal.span {x} ^ 2 * 1 := by
      calc Ideal.span {x} ^ 2 * Q ^ 2 = (A * Q) ^ 2 := by rw [mul_pow, hsq]
        _ = Ideal.span {x} ^ 2 * 1 := by rw [← hQ, mul_one]
    exact mul_left_cancel₀ hx0 h
  have hQ1 : Q = ⊤ := by
    rw [Ideal.one_eq_top] at hQ2
    exact top_le_iff.mp (hQ2 ▸ Ideal.pow_le_self two_ne_zero)
  rw [hQ, hQ1, Ideal.mul_top]

/-- A rational prime is not a unit of `𝒪_K`: `(p) ≠ 𝒪_K`. -/
theorem span_prime_ne_top (hK2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    Ideal.span {((p : ℤ) : 𝓞 K)} ≠ ⊤ := by
  intro h
  rw [Ideal.span_singleton_eq_top] at h
  have hu := h.map (Algebra.norm ℤ)
  rw [norm_intCast hK2, Int.isUnit_iff] at hu
  have := hp.two_le
  rcases hu with hu | hu <;> nlinarith

theorem intCast_prime_ne_zero {p : ℕ} (hp : p.Prime) : ((p : ℤ) : 𝓞 K) ≠ 0 := by
  have : ((p : ℤ) : 𝓞 K) = ((p : ℕ) : 𝓞 K) := by push_cast; rfl
  rw [this, Nat.cast_ne_zero]
  exact hp.ne_zero

/-- **Stage 7, case `m ≠ −1`: `(θ) = ∏_{p ∣ m} P_p`, a nonempty product of distinct ramified
primes** (tex 4507–4509, "the principal ideal of `√d`"). -/
theorem ramRelation_of_sqrt (hK2 : Module.finrank ℚ K = 2) (hT : PrimeTrichotomy K hK2)
    {θ : 𝓞 K} {m : ℤ} (hsq : Squarefree m) (hθ2 : (θ : K) ^ 2 = m)
    (hθ : (θ : K) ∉ (algebraMap ℚ K).range) (hm : m ≠ -1) : RamRelation K hK2 := by
  classical
  have hθ2' : θ ^ 2 = (m : 𝓞 K) := RingOfIntegers.ext (by push_cast; exact hθ2)
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    exact hθ ⟨0, by simp⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  have hm1 : m ≠ 1 := by
    rintro rfl
    have h1 : ((θ : K) - 1) * ((θ : K) + 1) = 0 := by
      have := hθ2; push_cast at this; linear_combination this
    rcases mul_eq_zero.mp h1 with h | h
    · exact hθ ⟨1, by rw [map_one]; linear_combination -h⟩
    · exact hθ ⟨-1, by rw [map_neg, map_one]; linear_combination -h⟩
  have hnat : 1 < m.natAbs := by omega
  set pf := m.natAbs.primeFactors with hpf
  have hpfne : pf.Nonempty := Nat.nonempty_primeFactors.mpr hnat
  have hex : ∀ p ∈ pf, ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ ((p : ℤ) : 𝓞 K) ∈ P := by
    intro p hp
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _
      (span_prime_ne_top hK2 (Nat.prime_of_mem_primeFactors hp))
    exact ⟨P, hP, hle (Ideal.mem_span_singleton_self _)⟩
  choose! Pf hPmax hpP using hex
  have hprime : ∀ p ∈ pf, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hθP : ∀ p ∈ pf, θ ∈ Pf p := by
    intro p hp
    obtain ⟨c, hc⟩ : (p : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have hmem : θ ^ 2 ∈ Pf p := by
      rw [hθ2', hc, Int.cast_mul]
      exact Ideal.mul_mem_right _ _ (hpP p hp)
    exact (hPmax p hp).isPrime.mem_of_pow_mem 2 hmem
  have hσθ := conjAut_smul_sqrt hK2 hθ2 hθ
  have hθσ : ∀ p ∈ pf, θ ∈ conjAut hK2 • Pf p := by
    intro p hp
    have := Ideal.smul_mem_pointwise_smul (conjAut hK2) θ (Pf p) (hθP p hp)
    rw [hσθ] at this
    exact (Ideal.neg_mem_iff _).mp this
  have hθnot : ∀ p ∈ pf, θ ∉ Ideal.span {((p : ℤ) : 𝓞 K)} := by
    intro p hp hmem
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    have heq : ((m : ℤ) : 𝓞 K) = (((p : ℤ) ^ 2 : ℤ) : 𝓞 K) * y ^ 2 := by
      rw [← hθ2', ← hy]; push_cast; ring
    have hd := sq_dvd_sq_of_eq_mul hK2 heq
    rw [Int.pow_dvd_pow_iff two_ne_zero, sq] at hd
    have hu := hsq _ hd
    rw [Int.isUnit_iff] at hu
    have := (hprime p hp).two_le
    omega
  have hne : ∀ p ∈ pf, Pf p ≠ ⊥ := by
    intro p hp hbot
    have := hpP p hp
    rw [hbot, Ideal.mem_bot] at this
    exact intCast_prime_ne_zero (hprime p hp) this
  have hram : ∀ p ∈ pf, RamPrime K hK2 (Pf p) ∧ Pf p ^ 2 = Ideal.span {((p : ℤ) : 𝓞 K)} :=
    fun p hp => ramified_of_mem hK2 hT (hPmax p hp) (hne p hp) (hprime p hp) (hpP p hp)
      (hθP p hp) (hθσ p hp) (hθnot p hp)
  have hinj : Set.InjOn Pf pf := by
    intro p hp q hq hpq
    exact prime_eq_of_mem (hPmax p hp).ne_top (hprime p hp) (hprime q hq) (hpP p hp)
      (hpq ▸ hpP q hq)
  refine ⟨pf.image Pf, hpfne.image _, ?_, θ, hθ0, ?_⟩
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact (hram p hp).1
  rw [Finset.prod_image hinj]
  symm
  apply span_eq_of_dvd_of_sq_eq hθ0
  · apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact Ideal.isCoprime_iff_sup_eq.mpr ((hPmax p hp).coprime_of_ne (hPmax q hq)
        (fun h => hpq (hinj hp hq h)))
    · intro p hp
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (hθP p hp))
  · rw [← Finset.prod_pow, Finset.prod_congr rfl (fun p hp => (hram p hp).2),
      Ideal.prod_span_singleton, Ideal.span_singleton_pow, hθ2']
    have hprod : ∏ p ∈ pf, ((p : ℤ) : 𝓞 K) = ((m.natAbs : ℤ) : 𝓞 K) := by
      rw [← Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsq)]
      push_cast; rfl
    rw [hprod]
    rcases Int.natAbs_eq m with h | h
    · rw [← h]
    · conv_rhs => rw [h]
      rw [Int.cast_neg, Ideal.span_singleton_neg]

/-- **Stage 7, case `m = −1` (`K = ℚ(i)`): `(1 + θ) = P₂`, the ramified prime above `2`**
(tex 4510–4511: the relation `[P₂] = 1` behind "its class group is trivial"). -/
theorem ramRelation_of_sqrt_neg_one (hK2 : Module.finrank ℚ K = 2) (hT : PrimeTrichotomy K hK2)
    {θ : 𝓞 K} (hθ2 : (θ : K) ^ 2 = ((-1 : ℤ) : K)) (hθ : (θ : K) ∉ (algebraMap ℚ K).range) :
    RamRelation K hK2 := by
  classical
  have hθ2' : θ ^ 2 = -1 := RingOfIntegers.ext (by push_cast at hθ2 ⊢; exact hθ2)
  have hsqx : (1 + θ) ^ 2 = 2 * θ := by linear_combination hθ2'
  have hθu : IsUnit θ := IsUnit.of_mul_eq_one (-θ) (by linear_combination -hθ2')
  have hσθ := conjAut_smul_sqrt hK2 hθ2 hθ
  have hσθK : conjAut hK2 (θ : K) = -(θ : K) := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hσθ
    simpa using this
  have h2 : ((2 : ℕ) : ℤ) = 2 := rfl
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ (span_prime_ne_top hK2 Nat.prime_two)
  have h2P : ((((2 : ℕ) : ℤ)) : 𝓞 K) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have h2P' : (2 : 𝓞 K) ∈ P := by simpa using h2P
  have hxP : 1 + θ ∈ P := by
    apply hPmax.isPrime.mem_of_pow_mem 2
    rw [hsqx]
    exact Ideal.mul_mem_right _ _ h2P'
  have hxσ : 1 + θ ∈ conjAut hK2 • P := by
    have h1 := Ideal.smul_mem_pointwise_smul (conjAut hK2) (1 + θ) P hxP
    have h2 := Ideal.smul_mem_pointwise_smul (conjAut hK2) (2 : 𝓞 K) P h2P'
    have e1 : conjAut hK2 • (1 + θ) = 1 - θ := by
      rw [smul_add, smul_one, hσθ, sub_eq_add_neg]
    have e2 : conjAut hK2 • (2 : 𝓞 K) = 2 := RingOfIntegers.ext (by
      change conjAut hK2 ((2 : 𝓞 K) : K) = ((2 : 𝓞 K) : K)
      exact map_ofNat _ 2)
    rw [e1] at h1
    rw [e2] at h2
    have : 1 + θ = (1 - θ) + 2 * θ := by ring
    rw [this]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_right _ _ h2)
  have hnorm : Algebra.norm ℤ (1 + θ) = 2 := by
    have hK : algebraMap ℚ K (Algebra.norm ℚ ((1 + θ : 𝓞 K) : K)) = algebraMap ℚ K 2 := by
      rw [norm_eq_mul_conjAut hK2]
      push_cast
      rw [map_add, map_one, hσθK]
      have : (θ : K) ^ 2 = -1 := by push_cast at hθ2; exact hθ2
      rw [map_ofNat]
      linear_combination -this
    have hQ := (algebraMap ℚ K).injective hK
    rw [← Algebra.coe_norm_int] at hQ
    exact_mod_cast hQ
  have hxnot : 1 + θ ∉ Ideal.span {((((2 : ℕ) : ℤ)) : 𝓞 K)} := by
    intro hmem
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    have := congrArg (Algebra.norm ℤ) hy
    rw [map_mul, norm_intCast hK2, hnorm] at this
    omega
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at h2P
    exact intCast_prime_ne_zero Nat.prime_two h2P
  obtain ⟨hram, hP2⟩ := ramified_of_mem hK2 hT hPmax hPne Nat.prime_two h2P hxP hxσ hxnot
  have hx0 : (1 + θ : 𝓞 K) ≠ 0 := by
    intro h0
    apply hθ
    refine ⟨-1, ?_⟩
    have := congrArg (fun y : 𝓞 K => (y : K)) h0
    push_cast at this ⊢
    linear_combination -this
  refine ⟨{P}, Finset.singleton_nonempty _, by simpa using hram, 1 + θ, hx0, ?_⟩
  rw [Finset.prod_singleton]
  symm
  apply span_eq_of_dvd_of_sq_eq hx0
  · exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxP)
  · rw [hP2, Ideal.span_singleton_pow, hsqx, Ideal.span_singleton_mul_right_unit hθu]
    simp

/-- **Stage 7 of Elliot's genus argument (tex 4507–4511): some nonempty product of distinct
ramified primes of `𝒪_K` is principal.** PROVED from the trichotomy `PrimeTrichotomy`. -/
theorem ramRelation_of (hK2 : Module.finrank ℚ K = 2) (_hTC : IsTotallyComplex K)
    (hT : PrimeTrichotomy K hK2) : RamRelation K hK2 := by
  obtain ⟨θ, m, hsq, hθ2, hθ⟩ := Splitting.exists_sqrt_gen hK2
  by_cases hm : m = -1
  · subst hm
    exact ramRelation_of_sqrt_neg_one hK2 hT hθ2 hθ
  · exact ramRelation_of_sqrt hK2 hT hsq hθ2 hθ hm

end ZInQ.Contrib.CloudB3RC53.RankCounts.Genus
