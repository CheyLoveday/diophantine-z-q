import ZInQKernel.Contrib.RC53Assist.TateCurve.KummerUniformization

/-!
# Existence of compatible Kummer roots

The root systems used in the multiplicative uniformization are constructed
in an algebraically closed field of characteristic zero. Their existence is
proved, rather than left as a printed or glue hypothesis.

Reference: elementary algebra of roots of unity and algebraic closures;
Silverman, *The Arithmetic of Elliptic Curves*, III.7 for the inverse limit.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

variable {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **PROVED**: a nonzero element has an `ℓ`-th root that is still nonzero.
Locator: algebraic closedness. -/
theorem unit_root_exists (x : Fˣ) : ∃ y : Fˣ, y ^ ℓ = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) (Fact.out : ℓ.Prime).pos
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow (Fact.out : ℓ.Prime).ne_zero] at hy
    exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext hy⟩

/-- **PROVED**: a primitive `ℓ`-th root exists as a field unit.
Locator: `HasEnoughRootsOfUnity` for an algebraically closed field. -/
theorem primitive_unit_exists : ∃ ζ : Fˣ, IsPrimitiveRoot ζ ℓ := by
  have : NeZero (ℓ : F) := ⟨Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F ℓ
  exact ⟨(hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit,
    hζ.isUnit_unit (Fact.out : ℓ.Prime).ne_zero⟩

/-- **PROVED**: once the order is a positive power of `ℓ`, every `ℓ`-th
root of a primitive root is primitive at the next level.
Locator: the order formula `ord(x^ℓ) = ord(x)/ℓ`. -/
theorem primitive_lift_of_positive {n : ℕ} (hn : n ≠ 0) (ζ y : Fˣ)
    (hζ : IsPrimitiveRoot ζ (ℓ ^ n)) (hy : y ^ ℓ = ζ) :
    IsPrimitiveRoot y (ℓ ^ (n + 1)) := by
  have hp : ℓ.Prime := Fact.out
  have hyN : y ^ (ℓ ^ (n + 1)) = 1 := by
    rw [pow_succ', pow_mul, hy, hζ.pow_eq_one]
  obtain ⟨k, hk, hord⟩ := (Nat.dvd_prime_pow hp).mp
    (orderOf_dvd_of_pow_eq_one hyN)
  have hk0 : k ≠ 0 := by
    intro h
    have hy1 : y = 1 := by
      apply orderOf_eq_one_iff.mp
      simpa [h] using hord
    have hζ1 : ζ = 1 := by simpa [hy1] using hy.symm
    have hN1 : ℓ ^ n = 1 := by simpa [hζ1] using hζ.eq_orderOf
    exact hn (Nat.pow_right_injective hp.two_le (by simpa using hN1))
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hdiv : ℓ ∣ orderOf y := by
    rw [hord]
    exact dvd_pow_self ℓ (Nat.succ_ne_zero _)
  have horder := hζ.eq_orderOf
  rw [← hy, orderOf_pow_of_dvd hp.ne_zero hdiv, hord, pow_succ,
    Nat.mul_div_cancel _ hp.pos] at horder
  have hnk : n = k' := Nat.pow_right_injective hp.two_le horder
  rw [IsPrimitiveRoot.iff_orderOf, hord, ← hnk]

/-- **PROVED**: primitive roots lift compatibly at every level, including
level zero. Locator: `primitive_unit_exists` and `primitive_lift_of_positive`. -/
theorem primitive_root_lift (n : ℕ) (ζ : Fˣ)
    (hζ : IsPrimitiveRoot ζ (ℓ ^ n)) :
    ∃ y : Fˣ, IsPrimitiveRoot y (ℓ ^ (n + 1)) ∧ y ^ ℓ = ζ := by
  by_cases hn : n = 0
  · subst n
    have hζ1 : ζ = 1 := by simpa using hζ
    obtain ⟨y, hy⟩ := primitive_unit_exists (F := F) (ℓ := ℓ)
    exact ⟨y, by simpa using hy, by simpa [hζ1] using hy.pow_eq_one⟩
  · obtain ⟨y, hy⟩ := unit_root_exists (ℓ := ℓ) ζ
    exact ⟨y, primitive_lift_of_positive hn ζ y hζ hy, hy⟩

/-- **PROVED**: every nonzero parameter admits the compatible primitive
roots of unity and compatible roots of the parameter required by the Kummer
construction. This supplies non-vacuity independently of any uniformization
or Tate-module theorem. Locator: recursion using `primitive_root_lift` and
`unit_root_exists`. -/
theorem kummerRoots_nonempty (q : Fˣ) : Nonempty (KummerRoots q ℓ) := by
  classical
  let next := fun n (z : {z : Fˣ // IsPrimitiveRoot z (ℓ ^ n)}) =>
    primitive_root_lift (F := F) (ℓ := ℓ) n (z : Fˣ) z.2
  let step := fun n (z : {z : Fˣ // IsPrimitiveRoot z (ℓ ^ n)}) =>
    (⟨(next n z).choose, (next n z).choose_spec.1⟩ :
      {z : Fˣ // IsPrimitiveRoot z (ℓ ^ (n + 1))})
  let z : ∀ n, {z : Fˣ // IsPrimitiveRoot z (ℓ ^ n)} :=
    fun n => Nat.rec (motive := fun n => {z : Fˣ // IsPrimitiveRoot z (ℓ ^ n)})
      ⟨1, by simpa using (IsPrimitiveRoot.one : IsPrimitiveRoot (1 : Fˣ) 1)⟩ step n
  let f : Fˣ → Fˣ := fun x => (unit_root_exists (ℓ := ℓ) x).choose
  have hf : ∀ x : Fˣ, f x ^ ℓ = x := fun x =>
    (unit_root_exists (ℓ := ℓ) x).choose_spec
  let t : ℕ → Fˣ := fun n => Nat.rec q (fun _ x => f x) n
  have ht : ∀ n, t (n + 1) ^ ℓ = t n := fun n => hf (t n)
  have htN : ∀ n, t n ^ (ℓ ^ n) = q := by
    intro n
    induction n with
    | zero => simp [t]
    | succ n ih => rw [pow_succ', pow_mul, ht, ih]
  refine ⟨{
    unity := fun n => (z n).val
    root := t
    primitive := fun n => (z n).property
    root_power := htN
    unity_step := ?_
    root_step := ht }⟩
  intro n
  exact (next n (z n)).choose_spec.2

end ZInQ.Contrib.RC53Assist.TateCurve
