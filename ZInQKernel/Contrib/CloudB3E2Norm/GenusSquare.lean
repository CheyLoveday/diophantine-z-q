import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Setup

/-!
# Genus theory, local part: when `q*` is a square, and Frobenius on square roots

Manuscript `diophantine_zq.tex`, tex 2683–2684 (`h_x = ∏ (q*)^{λ_q(x)}`, `q* = (−1)^{(q−1)/2} q`)
and tex 2847–2855 (the quadratic character `χ_h` factors through `Gal(H_f/K)`).

* `qstar q = (−1)^{(q−1)/2} q` (definition).
* **`isSquare_qstar_of_card`** (PROVED): in a finite field `F` of odd characteristic prime to `q`
  whose cardinality is a nonzero square modulo `q`, `q*` is a square (quadratic reciprocity in
  the form of Mathlib's `FiniteField.isSquare_odd_prime_iff`).
* **`frob_sqrt_eq`** (PROVED): an arithmetic Frobenius `φ` at a prime `Q` fixes a square root `x`
  of `c` (with `φ x = ± x`) when `c` is a square modulo `Q`, `2 ∉ Q` and `c ∉ Q`: `φ x ≡ x^N ≡ t^N
  ≡ t ≡ x (mod Q)` for `t² ≡ c`.
* `norm_int_add_mul_cast` (PROVED): `N(a + q y) ≡ a² (mod q)` in a quadratic field.
* **`isSquare_qstar_residue`** (PROVED): for `K` imaginary quadratic, `q` an odd prime and a prime
  `𝔭 = (a + q y)` of `𝒪_K` prime to `2q`, `q*` is a square modulo `𝔭` (the residue field has
  `N(a + q y) ≡ a² ≢ 0` elements, `N > 0` as `K` is imaginary).

Kinds: definition and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.GenusSquare

/-- `q* = (−1)^{(q−1)/2} q` (tex 2684). Kind: definition. -/
def qstar (q : ℕ) : ℤ := (-1) ^ (q / 2) * q

/-- **`q*` is a square in a finite field whose cardinality is a nonzero square modulo `q`**
(PROVED; quadratic reciprocity). -/
theorem isSquare_qstar_of_card {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqF : (q : F) ≠ 0) {a : ZMod q} (ha : a ≠ 0)
    (hcard : ((Fintype.card F : ℕ) : ZMod q) = a ^ 2) :
    IsSquare ((qstar q : ℤ) : F) := by
  classical
  have hsq := FiniteField.isSquare_odd_prime_iff (F := F) hF hq2
  have hχN : quadraticChar (ZMod q) ((Fintype.card F : ℕ) : ZMod q) = 1 := by
    rw [hcard]
    exact quadraticChar_sq_one' ha
  have hq2' : ringChar (ZMod q) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hneg1 : quadraticChar (ZMod q) (-1) = ZMod.χ₄ q := by
    rw [quadraticChar_neg_one hq2', ZMod.card]
  have hNodd := FiniteField.odd_card_of_char_ne_two hF
  have hqodd : q % 2 = 1 := (Fact.out : q.Prime).eq_one_or_self_of_dvd 2 |> fun _ =>
    Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two hq2)
  -- squares in `F` through the quadratic character
  have hsqF : ∀ x : F, x ≠ 0 → (IsSquare x ↔ quadraticChar F x = 1) := fun x hx =>
    (quadraticChar_one_iff_isSquare hx).symm
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hcast : ((qstar q : ℤ) : F) = (-1) ^ (q / 2) * (q : F) := by
    simp [qstar]
  rw [hcast]
  rcases Nat.odd_mod_four_iff.mp hqodd with hq4 | hq4
  · -- `q ≡ 1 (mod 4)`: `q* = q`
    have hev : (-1 : F) ^ (q / 2) = 1 := by
      have : q / 2 = 2 * (q / 4) := by omega
      rw [this, pow_mul]; simp
    rw [hev, one_mul, hsq]
    have hχ4q : quadraticChar (ZMod q) (-1) = 1 := by
      rw [hneg1, ZMod.χ₄_nat_one_mod_four hq4]
    rcases Nat.odd_mod_four_iff.mp hNodd with hN4 | hN4
    · rw [ZMod.χ₄_nat_one_mod_four hN4]; simp [hχN]
    · rw [ZMod.χ₄_nat_three_mod_four hN4]
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      rw [show -((Fintype.card F : ℕ) : ZMod q) = (-1) * ((Fintype.card F : ℕ) : ZMod q) by ring,
        map_mul, hχ4q, hχN]
      decide
  · -- `q ≡ 3 (mod 4)`: `q* = −q`
    have hod : (-1 : F) ^ (q / 2) = -1 := by
      have : q / 2 = 2 * (q / 4) + 1 := by omega
      rw [this, pow_succ, pow_mul]; simp
    rw [hod]
    have hχ4q : quadraticChar (ZMod q) (-1) = -1 := by
      rw [hneg1, ZMod.χ₄_nat_three_mod_four hq4]
    rcases Nat.odd_mod_four_iff.mp hNodd with hN4 | hN4
    · -- `−1` and `q` are squares
      have h1 : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.2 (by omega)
      have h2 : IsSquare (q : F) := by
        rw [hsq, ZMod.χ₄_nat_one_mod_four hN4]; simp [hχN]
      exact h1.mul h2
    · -- `−1` and `q` are non-squares
      have h1 : ¬ IsSquare (-1 : F) := fun h => FiniteField.isSquare_neg_one_iff.1 h hN4
      have h2 : ¬ IsSquare (q : F) := by
        rw [hsq, ZMod.χ₄_nat_three_mod_four hN4]
        simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul, ne_eq,
          not_not]
        rw [show -((Fintype.card F : ℕ) : ZMod q) = (-1) * ((Fintype.card F : ℕ) : ZMod q) by
          ring, map_mul, hχ4q, hχN]
        ring
      rw [hsqF _ (mul_ne_zero hm1 hqF), map_mul]
      rw [← quadraticChar_neg_one_iff_not_isSquare] at h1 h2
      rw [h1, h2]
      decide

/-- **An arithmetic Frobenius fixes a square root of a square modulo `Q`** (PROVED): for
`x² = c`, `c ≡ t² (mod Q)`, `2 ∉ Q`, `c ∉ Q` and `φ x = ± x`, `φ x = x`. -/
theorem frob_sqrt_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {φ : S →ₐ[R] S}
    {Q : Ideal S} [Q.IsPrime] (H : φ.IsArithFrobAt Q) {x : S} {c t : R}
    (hx : x ^ 2 = algebraMap R S c) (hct : algebraMap R S c - algebraMap R S t ^ 2 ∈ Q)
    (h2 : (2 : S) ∉ Q) (hc : algebraMap R S c ∉ Q) (hpm : φ x = x ∨ φ x = -x) : φ x = x := by
  -- `x ≡ ε t` for a sign `ε`
  have hfac : (x - algebraMap R S t) * (x + algebraMap R S t) ∈ Q := by
    have : (x - algebraMap R S t) * (x + algebraMap R S t) =
        algebraMap R S c - algebraMap R S t ^ 2 := by rw [← hx]; ring
    rw [this]; exact hct
  have hfix : ∀ r : R, algebraMap R S r - algebraMap R S r ^ Nat.card (R ⧸ Q.under R) ∈ Q :=
    fun r => by simpa using H (algebraMap R S r)
  have key : φ x - x ∈ Q := by
    obtain ⟨u, hu, hux⟩ : ∃ u : R, x - algebraMap R S u ∈ Q ∧ True := by
      rcases Ideal.IsPrime.mem_or_mem ‹_› hfac with h | h
      · exact ⟨t, h, trivial⟩
      · exact ⟨-t, by simpa [sub_neg_eq_add] using h, trivial⟩
    have hpow : x ^ Nat.card (R ⧸ Q.under R) - algebraMap R S u ^ Nat.card (R ⧸ Q.under R) ∈ Q :=
      by
        have := Ideal.Quotient.eq.mpr hu
        rw [← Ideal.Quotient.eq, map_pow, map_pow, this]
    have e : φ x - x = (φ x - x ^ Nat.card (R ⧸ Q.under R)) +
        (x ^ Nat.card (R ⧸ Q.under R) - algebraMap R S u ^ Nat.card (R ⧸ Q.under R)) -
        (algebraMap R S u - algebraMap R S u ^ Nat.card (R ⧸ Q.under R)) +
        -(x - algebraMap R S u) := by ring
    rw [e]
    exact Q.add_mem (Q.sub_mem (Q.add_mem (H x) hpow) (hfix u)) (Q.neg_mem hu)
  rcases hpm with h | h
  · exact h
  · exfalso
    rw [h, show -x - x = -(2 * x) by ring, Q.neg_mem_iff] at key
    rcases Ideal.IsPrime.mem_or_mem ‹_› key with h' | h'
    · exact h2 h'
    · exact hc (by rw [← hx, pow_two]; exact Q.mul_mem_left _ h')

open NumberField

/-- **`N(a + q y) ≡ a² (mod q)`** in a quadratic field (PROVED): the multiplication matrix of
`a + q y` is `a + q M_y`. -/
theorem norm_int_add_mul_cast {K : Type*} [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (a : ℤ) (q : ℕ) (y : 𝓞 K) :
    ((Algebra.norm ℤ ((a : 𝓞 K) + (q : 𝓞 K) * y) : ℤ) : ZMod q) = (a : ZMod q) ^ 2 := by
  classical
  let b := RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hK2]
  have e : (a : 𝓞 K) + (q : 𝓞 K) * y =
      algebraMap ℤ (𝓞 K) a + algebraMap ℤ (𝓞 K) (q : ℤ) * y := by simp
  rw [e, Algebra.norm_eq_matrix_det b, ← eq_intCast (Int.castRingHom (ZMod q)), RingHom.map_det,
    map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  have hM : (Int.castRingHom (ZMod q)).mapMatrix
      (algebraMap ℤ (Matrix _ _ ℤ) a + algebraMap ℤ (Matrix _ _ ℤ) (q : ℤ) *
        Algebra.leftMulMatrix b y) = Matrix.diagonal (fun _ => (a : ZMod q)) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, map_add, map_mul, eq_intCast,
      Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
    split_ifs <;> simp
  rw [hM, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, hcard]


/-- **`q*` is a square modulo a prime generated by `a + q y`** (PROVED; `K` imaginary quadratic,
`q` odd, the prime prime to `2q`): the residue field has `N(a + q y) ≡ a²` elements. -/
theorem isSquare_qstar_residue {K : Type} [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) {𝔭 : Ideal (𝓞 K)} [𝔭.IsMaximal] {a : ℤ} {y : 𝓞 K}
    (h𝔭 : 𝔭 = Ideal.span {(a : 𝓞 K) + (q : 𝓞 K) * y}) (hq𝔭 : (q : 𝓞 K) ∉ 𝔭)
    (h2𝔭 : (2 : 𝓞 K) ∉ 𝔭) :
    ∃ t : 𝓞 K, ((qstar q : ℤ) : 𝓞 K) - t ^ 2 ∈ 𝔭 := by
  classical
  set β := (a : 𝓞 K) + (q : 𝓞 K) * y
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField K)
  have : Finite (𝓞 K ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 hne
  let : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  let : Fintype (𝓞 K ⧸ 𝔭) := Fintype.ofFinite _
  have h2F : ringChar (𝓞 K ⧸ 𝔭) ≠ 2 := by
    intro h
    apply h2𝔭
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := (ringChar.spec (𝓞 K ⧸ 𝔭) 2).2 (by rw [h])
    rw [map_ofNat]
    exact_mod_cast this
  have hqF : ((q : ℕ) : 𝓞 K ⧸ 𝔭) ≠ 0 := by
    intro h
    apply hq𝔭
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h
  -- the cardinality of the residue field is the norm of `β`
  have hβ0 : (β : K) ≠ 0 := by
    intro h
    have : β = 0 := by exact_mod_cast h
    exact hne (by rw [h𝔭, this, Ideal.span_singleton_eq_bot.2 rfl])
  have hpos := ZInQ.Contrib.CloudB3RC53.RankCounts.Genus.norm_pos hK2 hTC hβ0
  rw [← Algebra.coe_norm_int] at hpos
  have hcardN : (Fintype.card (𝓞 K ⧸ 𝔭) : ℤ) = Algebra.norm ℤ β := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h𝔭,
      Ideal.absNorm_span_singleton, Int.natCast_natAbs, abs_of_pos (by exact_mod_cast hpos)]
  have hcard : ((Fintype.card (𝓞 K ⧸ 𝔭) : ℕ) : ZMod q) = (a : ZMod q) ^ 2 := by
    have := norm_int_add_mul_cast hK2 a q y
    rw [← hcardN] at this
    exact_mod_cast this
  have ha : (a : ZMod q) ≠ 0 := by
    intro ha
    rw [ha, zero_pow two_ne_zero, ZMod.natCast_eq_zero_iff] at hcard
    obtain ⟨n, hp, hn⟩ := FiniteField.card (𝓞 K ⧸ 𝔭) (ringChar (𝓞 K ⧸ 𝔭))
    rw [hn] at hcard
    have hqp : q ∣ ringChar (𝓞 K ⧸ 𝔭) := (Fact.out : q.Prime).dvd_of_dvd_pow hcard
    exact hqF ((ringChar.spec (𝓞 K ⧸ 𝔭) q).2 (by
      rw [(Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hp).1 hqp]))
  obtain ⟨u, hu⟩ := isSquare_qstar_of_card h2F hq2 hqF ha hcard
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨t, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_intCast, hu]
  ring

end ZInQ.Contrib.CloudB3E2.GenusSquare
