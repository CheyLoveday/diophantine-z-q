import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings

/-!
# Two-dimensional inertia actions

The finite-image argument for potentially good reduction and the ramified-twist
argument for potentially multiplicative reduction are linear algebra. They are
proved here without any local-reduction assertion as a hypothesis.

References: Silverman, *The Arithmetic of Elliptic Curves*, VII.5 and VII.7
for the arithmetic application. Pages have not been checked. The proofs below
use only the stated algebraic hypotheses.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.GlobalTrace
open Module

section SquareZero

variable {R : Type*} [Ring R]

/-- **PROVED**: powers of a square-zero perturbation of the identity.
Locator: the binomial identity, proved by induction. -/
theorem pow_one_add_of_square_zero (x : R) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one]
      have hn : (n • x) * x = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hx, mul_zero]
      rw [hn, add_zero, succ_nsmul]
      abel

end SquareZero

section Matrices

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- **PROVED**: in dimension two, determinant one and a singular `A - 1`
force `(A - 1)² = 0`. Locator: the two-by-two determinant formula. -/
theorem matrix_sub_one_square_zero (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 1) (hsing : (A - 1).det = 0) :
    (A - 1) * (A - 1) = 0 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using hdet
  have hs : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
    simpa [Matrix.det_fin_two, Matrix.sub_apply, Matrix.one_apply] using hsing
  have ht : A 0 0 + A 1 1 = 2 := by linear_combination hd - hs
  have h00 : ((A - 1) * (A - 1)) 0 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    change (A 0 0 - 1) * (A 0 0 - 1) + A 0 1 * A 1 0 = 0
    linear_combination A 0 0 * ht - hd
  have h01 : ((A - 1) * (A - 1)) 0 1 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    change (A 0 0 - 1) * A 0 1 + A 0 1 * (A 1 1 - 1) = 0
    linear_combination A 0 1 * ht
  have h10 : ((A - 1) * (A - 1)) 1 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    change A 1 0 * (A 0 0 - 1) + (A 1 1 - 1) * A 1 0 = 0
    linear_combination A 1 0 * ht
  have h11 : ((A - 1) * (A - 1)) 1 1 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    change A 1 0 * A 0 1 + (A 1 1 - 1) * (A 1 1 - 1) = 0
    linear_combination A 1 1 * ht - hd
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- **PROVED**: a nonidentity finite-order element of `SL₂` has no eigenvalue
one in characteristic zero. Locator: `matrix_sub_one_square_zero` and the
square-zero binomial identity. No semisimplicity or fixed-line assertion is
assumed. -/
theorem matrix_finite_order_sub_one_det_ne_zero
    (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1)
    (hne : A ≠ 1) (n : ℕ) (hn : n ≠ 0) (hpow : A ^ n = 1) :
    (A - 1).det ≠ 0 := by
  intro hsing
  have hx := matrix_sub_one_square_zero A hdet hsing
  have hp := pow_one_add_of_square_zero (A - 1) hx n
  have hcancel : (1 : Matrix (Fin 2) (Fin 2) K) + (A - 1) = A := by abel
  rw [hcancel, hpow] at hp
  have hz : n • (A - 1) = 0 := by
    exact (add_eq_left.mp hp.symm)
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  apply hne
  apply sub_eq_zero.mp
  ext i j
  have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M i j) hz
  simpa only [Matrix.smul_apply, Matrix.zero_apply, nsmul_eq_mul,
    mul_eq_zero, hnK, false_or] using hij

end Matrices

section Augmentation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- **PROVED**: the image of any inertia defect is contained in the
augmentation subspace. Locator: the definition of `inertiaAugmentation`. -/
theorem range_sub_one_le_augmentation (ρ : Representation K G V)
    (I : Subgroup G) (i : G) (hi : i ∈ I) :
    LinearMap.range (ρ i - 1) ≤ inertiaAugmentation ρ I := by
  rintro _ ⟨v, rfl⟩
  exact Submodule.subset_span ⟨i, hi, v, rfl⟩

/-- **PROVED**: an invertible inertia defect makes the augmentation all of
`V`. Locator: `range_sub_one_le_augmentation`. -/
theorem augmentation_eq_top_of_sub_one_surjective (ρ : Representation K G V)
    (I : Subgroup G) (i : G) (hi : i ∈ I)
    (hsurj : Function.Surjective (ρ i - (1 : Module.End K V))) :
    inertiaAugmentation ρ I = ⊤ := by
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr hsurj]
  exact range_sub_one_le_augmentation ρ I i hi

/-- **PROVED**: in dimension two over characteristic zero, one nontrivial
finite-order inertia operator of determinant one already kills all
coinvariants. Locator: `matrix_finite_order_sub_one_det_ne_zero`. -/
theorem augmentation_eq_top_of_finite_order [CharZero K]
    (ρ : Representation K G V) (I : Subgroup G) (b : Basis (Fin 2) K V)
    (i : G) (hi : i ∈ I) (hdet : LinearMap.det (ρ i) = 1)
    (hne : ρ i ≠ 1) (n : ℕ) (hn : n ≠ 0) (hpow : (ρ i) ^ n = 1) :
    inertiaAugmentation ρ I = ⊤ := by
  classical
  let A := LinearMap.toMatrixAlgEquiv b (ρ i)
  have hA : (A - 1).det ≠ 0 := by
    apply matrix_finite_order_sub_one_det_ne_zero A
    · change (LinearMap.toMatrix b b (ρ i)).det = 1
      exact (LinearMap.det_toMatrix b (ρ i)).trans hdet
    · intro h
      apply hne
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_one]
      exact h
    · exact hn
    · simpa only [map_pow, map_one] using
        congrArg (LinearMap.toMatrixAlgEquiv b) hpow
  apply augmentation_eq_top_of_sub_one_surjective ρ I i hi
  have h := (Matrix.toLinearEquiv b (A - 1) (isUnit_iff_ne_zero.mpr hA)).surjective
  change Function.Surjective (Matrix.toLin b b (A - 1)) at h
  have hmap : Matrix.toLin b b (A - 1) = ρ i - 1 := by
    change Matrix.toLin b b
      (LinearMap.toMatrix b b (ρ i) - 1) = ρ i - 1
    rw [← LinearMap.toMatrix_one b, ← map_sub, Matrix.toLin_toMatrix]
  rwa [hmap] at h

/-- **PROVED**: for a two-dimensional determinant-one representation,
any nonunipotent inertia operator kills the coinvariants. A singular defect
would have square zero, hence would be nilpotent.
Locator: `matrix_sub_one_square_zero`. -/
theorem augmentation_eq_top_of_nonunipotent
    (ρ : Representation K G V) (I : Subgroup G) (b : Basis (Fin 2) K V)
    (i : G) (hi : i ∈ I) (hdet : LinearMap.det (ρ i) = 1)
    (hnot : ¬IsNilpotent (ρ i - (1 : Module.End K V))) :
    inertiaAugmentation ρ I = ⊤ := by
  classical
  let A := LinearMap.toMatrixAlgEquiv b (ρ i)
  have hA : (A - 1).det ≠ 0 := by
    intro hsing
    have hdetA : A.det = 1 := (LinearMap.det_toMatrix b (ρ i)).trans hdet
    have hs := matrix_sub_one_square_zero A hdetA hsing
    apply hnot
    refine ⟨2, ?_⟩
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_pow, map_sub, map_one, map_zero, sq]
    exact hs
  apply augmentation_eq_top_of_sub_one_surjective ρ I i hi
  have h := (Matrix.toLinearEquiv b (A - 1) (isUnit_iff_ne_zero.mpr hA)).surjective
  change Function.Surjective (Matrix.toLin b b (A - 1)) at h
  have hmap : Matrix.toLin b b (A - 1) = ρ i - 1 := by
    change Matrix.toLin b b
      (LinearMap.toMatrix b b (ρ i) - 1) = ρ i - 1
    rw [← LinearMap.toMatrix_one b, ← map_sub, Matrix.toLin_toMatrix]
  rwa [hmap] at h

/-- **PROVED**: an operator in a finite inertia image has finite order.
Locator: finiteness of the set of powers, applied to the unit-valued
representation. -/
theorem inertia_operator_isOfFinOrder (ρ : Representation K G V)
    (I : Subgroup G) (hfinite : (ρ '' (I : Set G)).Finite)
    (i : G) (hi : i ∈ I) : IsOfFinOrder (ρ i) := by
  rw [← Representation.asGroupHom_apply, Units.isOfFinOrder_val, ← finite_powers]
  refine (hfinite.preimage Units.val_injective.injOn).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨i ^ n, I.pow_mem hi n, by simp [Representation.asGroupHom_apply]⟩

/-- **PROVED**: a nontrivial finite inertia image in `SL₂` has zero
coinvariants in characteristic zero. No vanishing of fixed vectors,
semisimplicity, or coinvariant assertion is an input.
Locator: `augmentation_eq_top_of_finite_order`. -/
theorem augmentation_eq_top_of_finite_image [CharZero K]
    (ρ : Representation K G V) (I : Subgroup G) (b : Basis (Fin 2) K V)
    (hfinite : (ρ '' (I : Set G)).Finite)
    (hdet : ∀ i ∈ I, LinearMap.det (ρ i) = 1)
    (hnontrivial : ¬∀ i ∈ I, ρ i = 1) : inertiaAugmentation ρ I = ⊤ := by
  classical
  push Not at hnontrivial
  obtain ⟨i, hi, hne⟩ := hnontrivial
  obtain ⟨n, hn, hpow⟩ := (inertia_operator_isOfFinOrder ρ I hfinite i hi).exists_pow_eq_one
  exact augmentation_eq_top_of_finite_order ρ I b i hi (hdet i hi) hne n hn.ne' hpow

/-- **PROVED**: a scalar inertia action different from the identity kills
all coinvariants, in every dimension. Locator: the inverse scalar explicitly
solves `(ρ(i) - 1)v = w`. -/
theorem augmentation_eq_top_of_scalar (ρ : Representation K G V)
    (I : Subgroup G) (i : G) (hi : i ∈ I) (c : K) (hc : c ≠ 1)
    (hscalar : ∀ v, ρ i v = c • v) : inertiaAugmentation ρ I = ⊤ := by
  apply augmentation_eq_top_of_sub_one_surjective ρ I i hi
  intro w
  refine ⟨(c - 1)⁻¹ • w, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, hscalar]
  calc
    c • (c - 1)⁻¹ • w - (c - 1)⁻¹ • w =
        (c - 1) • ((c - 1)⁻¹ • w) := by module
    _ = w := by
      rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hc), one_smul]

/-- **PROVED**: a ramified quadratic twist of an upper-triangular Tate
representation has zero coinvariants. It suffices that one inertia element
has sign `-1`; its defect has diagonal entries `-2`.
Locator: the displayed Tate action; characteristic different from two. -/
theorem augmentation_eq_top_of_ramified_tate [NeZero (2 : K)]
    (ρ : Representation K G V) (I : Subgroup G) (b : Basis (Fin 2) K V)
    (i : G) (hi : i ∈ I) (k : K)
    (h0 : ρ i (b 0) = -b 0)
    (h1 : ρ i (b 1) = -(b 1 + k • b 0)) :
    inertiaAugmentation ρ I = ⊤ := by
  apply augmentation_eq_top_of_sub_one_surjective ρ I i hi
  intro w
  have hdec : w = b.repr w 0 • b 0 + b.repr w 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr w]
    rw [Fin.sum_univ_two]
  let d := -(b.repr w 1) / 2
  let a := -(b.repr w 0 + k * d) / 2
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  have ha : -2 * a - k * d = b.repr w 0 := by
    dsimp [a]
    field_simp
    ring
  have hd : -2 * d = b.repr w 1 := by
    dsimp [d]
    field_simp
  refine ⟨a • b 0 + d • b 1, ?_⟩
  have hv : (ρ i - 1) (a • b 0 + d • b 1) =
      (-2 * a - k * d) • b 0 + (-2 * d) • b 1 := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, map_smul, h0, h1]
    module
  rw [hv, ha, hd, ← hdec]

end Augmentation

end ZInQ.Contrib.RC53Assist.TateCurve
