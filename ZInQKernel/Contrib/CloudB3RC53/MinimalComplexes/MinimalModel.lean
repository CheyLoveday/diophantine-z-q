import Mathlib
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.DegreewiseInvertible

/-!
# RC53 MinimalComplexes: the minimal model of a bounded finite free complex over a local ring

The "minimal-complex reduction" used twice in the proof of Theorem 5.3:

* Lemma `ex:limits-fixed-field-budget`, tex L5357–5359 ("a finite free model of `C_old` over `Λ`
  [...] by cancelling unit entries at its maximal ideal `(2, t)`") and tex L5404–5409 ("Cancel unit
  disks in `C_0` [...] Decompose `D` over `Λ` into a minimal complex `D_min` and unit disks `E`");
* the central lane's base-zero lemma (`RC/Central/BaseZero.lean`, module docstring, its lines
  18–24: "the actual bounded finite free complex after cancelling its unit disks [...]; GLUE,
  textbook minimal-complex reduction over a local ring").

**Statement.** Over a local ring `R` with maximal ideal `𝔪`, every bounded complex of finite free
`R`-modules is isomorphic, by a degree-preserving change of bases, to the direct sum of a minimal
complex (all entries of its differential in `𝔪`) and finitely many unit disks `[R --1--> R]`.

**Form (`DEPARTURE`, form only).** A bounded complex of finite free modules with chosen bases is
recorded as a finite index set `I` (the union of the bases of all degrees), a degree function
`deg : I → ℤ`, and one square matrix `d : Matrix I I R` with `d a b ≠ 0 → deg a = deg b + 1` (the
differential raises degree by one) and `d * d = 0`. An isomorphism of complexes is an invertible
matrix `P` (inverse `Q`) that preserves degrees; the transported differential is `P * d * Q`. The
splitting is recorded by a kind function (`0`: minimal part, `1`: source of a disk, `2`: target of a
disk) and the partner involution pairing the two ends of each disk (`SplitForm`).

Nodes (PROVED):
* `MinimalModelSplit` (tex L5357–5359, L5404–5409): the minimal model exists.
* `SplitMinimalPart`: in split form, the kind-`0` part is itself a graded square-zero matrix
  (a complex) all of whose entries lie in `𝔪` (a minimal complex).
* `MinimalPartDims` (tex L5357–5359): the number of minimal basis vectors in degree `n` is
  `dim_k Hⁿ(K ⊗ k)` (`resDim`, defined by rank–nullity over the residue field `k = R/𝔪`).
* `CentralTwoTermModel` (the form of the central lane's `baseZero_core`, tex L4346–4358): if
  `Hⁿ(K ⊗ k) = 0` for `n ∉ {1, 2}` and both remaining dimensions are one, then `K` is, after a
  degree-preserving change of bases, unit disks plus `[R --δ--> R]` in degrees one and two with
  `δ ∈ 𝔪`; the `1 × 1` matrix `(δ)` has residue rank `0` (`hcentral` with `m = 0`).
-/

namespace ZInQ.Contrib.CloudB3RC53.MinimalComplexes

open Matrix

universe u v

section Graded

variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

/-- `d` raises degree by one: `d a b ≠ 0 → deg a = deg b + 1`. -/
def IsGradedDiff (deg : I → ℤ) (d : Matrix I I R) : Prop :=
  ∀ a b, d a b ≠ 0 → deg a = deg b + 1

/-- `P` preserves degree: `P a b ≠ 0 → deg a = deg b`. -/
def IsDegPreserving (deg : I → ℤ) (P : Matrix I I R) : Prop :=
  ∀ a b, P a b ≠ 0 → deg a = deg b

/-- **Split form** of a differential over a local ring: with `kind x = 0` (minimal part),
`1` (disk source), `2` (disk target) and an involution `partner` pairing disk ends, the only
nonzero entries are inside the minimal part (and these lie in `𝔪`) and the disk entries
`d (partner x) x = 1`. -/
def SplitForm [IsLocalRing R] (d : Matrix I I R) (kind : I → Fin 3) (partner : I → I) : Prop :=
  (∀ x, kind x = 1 → kind (partner x) = 2 ∧ partner (partner x) = x ∧ d (partner x) x = 1) ∧
  (∀ x, kind x = 2 → kind (partner x) = 1 ∧ partner (partner x) = x) ∧
  (∀ x y, d y x ≠ 0 → (kind x = 0 ∧ kind y = 0) ∨ (kind x = 1 ∧ y = partner x)) ∧
  (∀ x y, kind x = 0 → kind y = 0 → d y x ∈ IsLocalRing.maximalIdeal R)

theorem isDegPreserving_one (deg : I → ℤ) : IsDegPreserving deg (1 : Matrix I I R) := by
  intro a b h
  by_cases hab : a = b
  · rw [hab]
  · exact absurd (one_apply_ne hab) h

theorem IsDegPreserving.mul {deg : I → ℤ} {P Q : Matrix I I R} (hP : IsDegPreserving deg P)
    (hQ : IsDegPreserving deg Q) : IsDegPreserving deg (P * Q) := by
  intro a b h
  rw [mul_apply] at h
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [hP a y (left_ne_zero_of_mul hy), hQ y b (right_ne_zero_of_mul hy)]

theorem IsGradedDiff.conj {deg : I → ℤ} {P d Q : Matrix I I R} (hP : IsDegPreserving deg P)
    (hd : IsGradedDiff deg d) (hQ : IsDegPreserving deg Q) : IsGradedDiff deg (P * d * Q) := by
  intro a b h
  rw [mul_apply] at h
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hw
  rw [mul_apply] at h1
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  rw [hP a y (left_ne_zero_of_mul hy), hd y w (right_ne_zero_of_mul hy),
    hQ w b (right_ne_zero_of_mul hw)]

theorem conj_sq_zero {P d Q : Matrix I I R} (hQP : Q * P = 1) (hd : d * d = 0) :
    P * d * Q * (P * d * Q) = 0 := by
  have : P * d * Q * (P * d * Q) = P * (d * (Q * P) * d) * Q := by simp only [Matrix.mul_assoc]
  rw [this, hQP, Matrix.mul_one, hd, Matrix.mul_zero, Matrix.zero_mul]

theorem IsGradedDiff.diag_zero {deg : I → ℤ} {d : Matrix I I R} (hd : IsGradedDiff deg d)
    (a : I) : d a a = 0 := by
  by_contra h
  have := hd a a h
  omega

theorem degP_one_add {deg : I → ℤ} {X : Matrix I I R} (hX : ∀ a b, X a b ≠ 0 → deg a = deg b) :
    IsDegPreserving deg (1 + X) := by
  intro a b h
  by_cases hab : a = b
  · rw [hab]
  · rw [Matrix.add_apply, one_apply_ne hab, zero_add] at h
    exact hX a b h

theorem degP_one_sub {deg : I → ℤ} {X : Matrix I I R} (hX : ∀ a b, X a b ≠ 0 → deg a = deg b) :
    IsDegPreserving deg (1 - X) := by
  intro a b h
  by_cases hab : a = b
  · rw [hab]
  · rw [Matrix.sub_apply, one_apply_ne hab, zero_sub, neg_ne_zero] at h
    exact hX a b h

theorem inv_one_add_sq_zero {X : Matrix I I R} (hX : X * X = 0) :
    (1 + X) * (1 - X) = 1 ∧ (1 - X) * (1 + X) = 1 := by
  constructor
  · rw [add_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hX]; abel
  · rw [sub_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hX]; abel

/-! ### One unit pivot -/

/-- Row operations in the target degree clear the pivot column `a₀` outside the pivot row. -/
theorem clear_col (deg : I → ℤ) (d : Matrix I I R) (hg : IsGradedDiff deg d) {a0 b0 : I}
    (hab : a0 ≠ b0) (hdeg : deg b0 = deg a0 + 1) (v : R) (hv : v * d b0 a0 = 1) :
    ∃ P Q : Matrix I I R, P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
      (P * d * Q) b0 a0 = d b0 a0 ∧ ∀ x, x ≠ b0 → (P * d * Q) x a0 = 0 := by
  set X : Matrix I I R := Matrix.of fun x z => if z = b0 ∧ x ≠ b0 then -(d x a0 * v) else 0
    with hXdef
  have hXX : X * X = 0 := by
    ext x z
    rw [mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro y _
    simp only [hXdef, of_apply]
    split_ifs with h1 h2 <;> simp_all
  have hXdeg : ∀ a b, X a b ≠ 0 → deg a = deg b := by
    intro a b h
    simp only [hXdef, of_apply] at h
    split_ifs at h with h1
    · rw [h1.1, hdeg]
      have : d a a0 ≠ 0 := by intro h0; apply h; rw [h0, zero_mul, neg_zero]
      exact hg a a0 this
    · exact absurd rfl h
  have hcol : ∀ y, X y a0 = 0 := by intro y; simp [hXdef, hab]
  obtain ⟨h1, h2⟩ := inv_one_add_sq_zero hXX
  refine ⟨1 + X, 1 - X, h1, h2, degP_one_add hXdeg, degP_one_sub hXdeg, ?_⟩
  have key : (1 + X) * d * (1 - X) = d + X * d - (d * X + X * d * X) := by noncomm_ring
  have hMX : ∀ (M : Matrix I I R) x, (M * X) x a0 = 0 := by
    intro M x; simp [mul_apply, hcol]
  have hXd : ∀ x, (X * d) x a0 = X x b0 * d b0 a0 := by
    intro x
    rw [mul_apply]
    apply Finset.sum_eq_single b0
    · intro y _ hy; simp [hXdef, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨?_, fun x hx => ?_⟩
  · rw [key, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, hMX, hMX, hXd]
    simp [hXdef]
  · rw [key, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, hMX, hMX, hXd]
    simp only [hXdef, of_apply, true_and, hx, ne_eq, not_false_eq_true, ite_true, add_zero,
      sub_zero]
    linear_combination (-(d x a0)) * hv

/-- Column operations in the source degree clear the pivot row `b₀` outside the pivot column,
keeping the pivot column cleared. -/
theorem clear_row (deg : I → ℤ) (d : Matrix I I R) (hg : IsGradedDiff deg d) {a0 b0 : I}
    (hab : a0 ≠ b0) (hdeg : deg b0 = deg a0 + 1) (v : R) (hv : v * d b0 a0 = 1)
    (hcol0 : ∀ x, x ≠ b0 → d x a0 = 0) :
    ∃ P Q : Matrix I I R, P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
      (P * d * Q) b0 a0 = d b0 a0 ∧ (∀ x, x ≠ b0 → (P * d * Q) x a0 = 0) ∧
      ∀ z, z ≠ a0 → (P * d * Q) b0 z = 0 := by
  set Y : Matrix I I R := Matrix.of fun x z => if x = a0 ∧ z ≠ a0 then d b0 z * v else 0
    with hYdef
  have hYY : Y * Y = 0 := by
    ext x z
    rw [mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro y _
    simp only [hYdef, of_apply]
    split_ifs with h1 h2 <;> simp_all
  have hYdeg : ∀ a b, Y a b ≠ 0 → deg a = deg b := by
    intro a b h
    simp only [hYdef, of_apply] at h
    split_ifs at h with h1
    · have : d b0 b ≠ 0 := by intro h0; apply h; rw [h0, zero_mul]
      have := hg b0 b this
      rw [h1.1]; omega
    · exact absurd rfl h
  have rowY : ∀ z, Y b0 z = 0 := by intro z; simp [hYdef, Ne.symm hab]
  have colY : ∀ y, Y y a0 = 0 := by intro y; simp [hYdef]
  have hbb : d b0 b0 = 0 := hg.diag_zero b0
  obtain ⟨h1, h2⟩ := inv_one_add_sq_zero hYY
  refine ⟨1 + Y, 1 - Y, h1, h2, degP_one_add hYdeg, degP_one_sub hYdeg, ?_⟩
  have key : (1 + Y) * d * (1 - Y) = d + Y * d - (d * Y + Y * d * Y) := by noncomm_ring
  have hMY : ∀ (M : Matrix I I R) x, (M * Y) x a0 = 0 := by
    intro M x; simp [mul_apply, colY]
  have hYdrow : ∀ z, (Y * d) b0 z = 0 := by intro z; simp [mul_apply, rowY]
  have hYdYrow : ∀ z, (Y * d * Y) b0 z = 0 := by
    intro z; rw [mul_apply]; apply Finset.sum_eq_zero; intro w _; rw [hYdrow, zero_mul]
  have hdYrow : ∀ z, (d * Y) b0 z = d b0 a0 * Y a0 z := by
    intro z
    rw [mul_apply]
    apply Finset.sum_eq_single a0
    · intro y _ hy; simp [hYdef, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hYdcol : ∀ x, (Y * d) x a0 = 0 := by
    intro x
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y = b0
    · rw [hy]; simp [hYdef, hbb]
    · rw [hcol0 y hy, mul_zero]
  refine ⟨?_, fun x hx => ?_, fun z hz => ?_⟩
  · rw [key, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, hMY, hMY, hYdrow]
    simp
  · rw [key, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, hMY, hMY, hYdcol, hcol0 x hx]
    simp
  · rw [key, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, hYdrow, hYdYrow, hdYrow]
    simp only [hYdef, of_apply, true_and, hz, ne_eq, not_false_eq_true, ite_true, add_zero]
    linear_combination (-(d b0 z)) * hv

/-- A diagonal rescaling of the target degree makes the pivot equal to `1`, keeping zeros. -/
theorem scale_pivot (deg : I → ℤ) (d : Matrix I I R) {a0 b0 : I} (hab : a0 ≠ b0) (v : R)
    (hv : v * d b0 a0 = 1) :
    ∃ P Q : Matrix I I R, P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
      (P * d * Q) b0 a0 = 1 ∧ ∀ x z, d x z = 0 → (P * d * Q) x z = 0 := by
  set f : I → R := fun x => if x = b0 then v else 1
  set g : I → R := fun x => if x = b0 then d b0 a0 else 1
  have hdiagP : ∀ (k : I → R), IsDegPreserving deg (diagonal k) := by
    intro k a b h
    by_cases hab' : a = b
    · rw [hab']
    · exact absurd (diagonal_apply_ne k hab') h
  have hfg : diagonal f * diagonal g = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext x
    simp only [f, g]; split_ifs
    · exact hv
    · exact mul_one 1
  have hgf : diagonal g * diagonal f = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext x
    simp only [f, g]; split_ifs
    · rw [mul_comm]; exact hv
    · exact mul_one 1
  refine ⟨diagonal f, diagonal g, hfg, hgf, hdiagP f, hdiagP g, ?_, fun x z h => ?_⟩
  · rw [mul_diagonal, diagonal_mul]
    simp [f, g, hab, hv]
  · rw [mul_diagonal, diagonal_mul, h, mul_zero, zero_mul]

/-- **One unit pivot.** If `d b₀ a₀` is a unit, a degree-preserving change of bases makes the pivot
`1`, and clears row and column of both `a₀` and `b₀` except the pivot. -/
theorem pivot (deg : I → ℤ) (d : Matrix I I R) (hg : IsGradedDiff deg d) (hd : d * d = 0)
    {a0 b0 : I} (hab : a0 ≠ b0) (hdeg : deg b0 = deg a0 + 1) (v : R) (hv : v * d b0 a0 = 1) :
    ∃ P Q : Matrix I I R, P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
      (P * d * Q) b0 a0 = 1 ∧ (∀ x, x ≠ b0 → (P * d * Q) x a0 = 0) ∧
      (∀ z, z ≠ a0 → (P * d * Q) b0 z = 0) ∧ (∀ x, (P * d * Q) x b0 = 0) ∧
      (∀ z, (P * d * Q) a0 z = 0) := by
  obtain ⟨P1, Q1, h11, h12, hP1, hQ1, hb1, hc1⟩ := clear_col deg d hg hab hdeg v hv
  have hg1 : IsGradedDiff deg (P1 * d * Q1) := IsGradedDiff.conj hP1 hg hQ1
  have hv1 : v * (P1 * d * Q1) b0 a0 = 1 := by rw [hb1]; exact hv
  obtain ⟨P2, Q2, h21, h22, hP2, hQ2, hb2, hc2, hr2⟩ :=
    clear_row deg (P1 * d * Q1) hg1 hab hdeg v hv1 hc1
  have hv2 : v * (P2 * (P1 * d * Q1) * Q2) b0 a0 = 1 := by rw [hb2]; exact hv1
  obtain ⟨P3, Q3, h31, h32, hP3, hQ3, hb3, h0⟩ :=
    scale_pivot deg (P2 * (P1 * d * Q1) * Q2) hab v hv2
  have hd1 := conj_sq_zero h12 hd
  have hd2 := conj_sq_zero h22 hd1
  have hD := conj_sq_zero h32 hd2
  have hconj : P3 * P2 * P1 * d * (Q1 * Q2 * Q3) = P3 * (P2 * (P1 * d * Q1) * Q2) * Q3 := by
    simp only [Matrix.mul_assoc]
  refine ⟨P3 * P2 * P1, Q1 * Q2 * Q3, ?_, ?_, (hP3.mul hP2).mul hP1, (hQ1.mul hQ2).mul hQ3, ?_⟩
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P1 Q1, h11, Matrix.one_mul, ← Matrix.mul_assoc P2 Q2, h21,
      Matrix.one_mul, h31]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q3 P3, h32, Matrix.one_mul, ← Matrix.mul_assoc Q2 P2, h22,
      Matrix.one_mul, h12]
  rw [hconj]
  set D := P3 * (P2 * (P1 * d * Q1) * Q2) * Q3 with hDdef
  have hDcol : ∀ x, x ≠ b0 → D x a0 = 0 := fun x hx => h0 x a0 (hc2 x hx)
  have hDrow : ∀ z, z ≠ a0 → D b0 z = 0 := fun z hz => h0 b0 z (hr2 z hz)
  refine ⟨hb3, hDcol, hDrow, fun x => ?_, fun z => ?_⟩
  · have h := congrFun (congrFun hD x) a0
    rw [mul_apply, Finset.sum_eq_single b0, hb3, mul_one] at h
    · exact h
    · intro y _ hy; rw [hDcol y hy, mul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · have h := congrFun (congrFun hD b0) z
    rw [mul_apply, Finset.sum_eq_single a0, hb3, one_mul] at h
    · exact h
    · intro y _ hy; rw [hDrow y hy, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

/-! ### Extension from a complement of the pivot pair -/

section Ext

variable (p : I → Prop) [DecidablePred p]

/-- Extend a matrix on `{x // p x}` by the identity outside. -/
def extM (M : Matrix (Subtype p) (Subtype p) R) : Matrix I I R :=
  Matrix.of fun x z =>
    if hx : p x then (if hz : p z then M ⟨x, hx⟩ ⟨z, hz⟩ else 0) else (if x = z then 1 else 0)

theorem sum_eq_sum_subtype (f : I → R) (hf : ∀ x, ¬ p x → f x = 0) :
    ∑ x, f x = ∑ x : Subtype p, f x := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · rfl
  · exact hf x h

theorem extM_mul_apply_pos (M : Matrix (Subtype p) (Subtype p) R) (N : Matrix I I R) {x : I}
    (hx : p x) (z : I) : (extM p M * N) x z = ∑ y : Subtype p, M ⟨x, hx⟩ y * N y z := by
  rw [mul_apply, sum_eq_sum_subtype p]
  · apply Finset.sum_congr rfl
    intro y _
    simp [extM, hx, y.2]
  · intro y hy
    simp [extM, hx, hy]

theorem extM_mul_apply_neg (M : Matrix (Subtype p) (Subtype p) R) (N : Matrix I I R) {x : I}
    (hx : ¬ p x) (z : I) : (extM p M * N) x z = N x z := by
  rw [mul_apply, Finset.sum_eq_single x]
  · simp [extM, hx]
  · intro y _ hy
    simp [extM, hx, Ne.symm hy]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_extM_apply_pos (N : Matrix I I R) (M : Matrix (Subtype p) (Subtype p) R) (x : I)
    {z : I} (hz : p z) : (N * extM p M) x z = ∑ y : Subtype p, N x y * M y ⟨z, hz⟩ := by
  rw [mul_apply, sum_eq_sum_subtype p]
  · apply Finset.sum_congr rfl
    intro y _
    simp [extM, hz, y.2]
  · intro y hy
    have hyz : y ≠ z := fun h => hy (h ▸ hz)
    simp [extM, hy, hyz]

theorem mul_extM_apply_neg (N : Matrix I I R) (M : Matrix (Subtype p) (Subtype p) R) (x : I)
    {z : I} (hz : ¬ p z) : (N * extM p M) x z = N x z := by
  rw [mul_apply, Finset.sum_eq_single z]
  · simp [extM, hz]
  · intro y _ hy
    by_cases hpy : p y
    · simp [extM, hpy, hz]
    · simp [extM, hpy, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem extM_mul_extM (M N : Matrix (Subtype p) (Subtype p) R) :
    extM p M * extM p N = extM p (M * N) := by
  ext x z
  by_cases hx : p x
  · rw [extM_mul_apply_pos p M _ hx]
    by_cases hz : p z
    · have e : ∀ y : Subtype p, extM p N y z = N y ⟨z, hz⟩ := fun y => by simp [extM, y.2, hz]
      simp only [e]
      simp [extM, hx, hz, mul_apply]
    · have e : ∀ y : Subtype p, extM p N y z = 0 := fun y => by simp [extM, y.2, hz]
      simp only [e, mul_zero, Finset.sum_const_zero]
      simp [extM, hx, hz]
  · rw [extM_mul_apply_neg p M _ hx]
    simp [extM, hx]

theorem extM_one : extM p (1 : Matrix (Subtype p) (Subtype p) R) = 1 := by
  ext x z
  by_cases hx : p x
  · by_cases hz : p z
    · simp [extM, hx, hz, one_apply, Subtype.ext_iff]
    · have hxz : x ≠ z := fun h => hz (h ▸ hx)
      simp [extM, hx, hz, one_apply_ne hxz]
  · by_cases hxz : x = z
    · subst hxz; simp [extM, hx]
    · simp [extM, hx, hxz, one_apply_ne hxz]

theorem extM_degP {deg : I → ℤ} (M : Matrix (Subtype p) (Subtype p) R)
    (hM : IsDegPreserving (fun y : Subtype p => deg y) M) : IsDegPreserving deg (extM p M) := by
  intro a b h
  simp only [extM, of_apply] at h
  split_ifs at h with ha hb hab
  · exact hM _ _ h
  · exact absurd rfl h
  · rw [hab]
  · exact absurd rfl h

end Ext

/-! ### The minimal model -/

theorem minimal_split_aux [IsLocalRing R] (n : ℕ) :
    ∀ (J : Type v) [Fintype J] [DecidableEq J], Fintype.card J = n →
      ∀ (deg : J → ℤ) (d : Matrix J J R), IsGradedDiff deg d → d * d = 0 →
        ∃ (P Q : Matrix J J R) (kind : J → Fin 3) (partner : J → J),
          P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
          SplitForm (P * d * Q) kind partner := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro J _ _ hcard deg d hg hd
  by_cases hmin : ∀ a b, d a b ∈ IsLocalRing.maximalIdeal R
  · refine ⟨1, 1, fun _ => 0, id, Matrix.mul_one 1, Matrix.mul_one 1, isDegPreserving_one deg,
      isDegPreserving_one deg, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one]
    exact ⟨fun x h => by simp at h, fun x h => by simp at h,
      fun x y _ => Or.inl ⟨rfl, rfl⟩, fun x y _ _ => hmin y x⟩
  push Not at hmin
  obtain ⟨b0, a0, hba⟩ := hmin
  have hu : IsUnit (d b0 a0) := by
    by_contra h
    exact hba ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
  have hdeg : deg b0 = deg a0 + 1 := hg b0 a0 hu.ne_zero
  have hab : a0 ≠ b0 := by intro h; rw [h] at hdeg; omega
  have hv : ((hu.unit⁻¹ : Rˣ) : R) * d b0 a0 = 1 := hu.val_inv_mul
  obtain ⟨P1, Q1, h11, h12, hP1, hQ1, hD1, hcol, hrow, hcolb, hrowa⟩ :=
    pivot deg d hg hd hab hdeg _ hv
  set d2 := P1 * d * Q1 with hd2def
  have hg2 : IsGradedDiff deg d2 := IsGradedDiff.conj hP1 hg hQ1
  have hdd2 : d2 * d2 = 0 := conj_sq_zero h12 hd
  -- the complement of the pivot pair
  set p : J → Prop := fun x => x ≠ a0 ∧ x ≠ b0 with hpdef
  have hpa : ¬ p a0 := fun h => h.1 rfl
  have hpb : ¬ p b0 := fun h => h.2 rfl
  have hnp : ∀ x, ¬ p x → x = a0 ∨ x = b0 := by
    intro x hx
    by_contra h
    push Not at h
    exact hx h
  set d' : Matrix (Subtype p) (Subtype p) R := d2.submatrix Subtype.val Subtype.val with hd'def
  have hg' : IsGradedDiff (fun y : Subtype p => deg y) d' := fun a b h => hg2 a b h
  have hdd' : d' * d' = 0 := by
    ext x z
    have h := congrFun (congrFun hdd2 x.1) z.1
    rw [mul_apply, sum_eq_sum_subtype p] at h
    · simpa [hd'def, mul_apply] using h
    · intro y hy
      rcases hnp y hy with rfl | rfl
      · rw [hcol x.1 x.2.2, zero_mul]
      · rw [hrow z.1 z.2.1, mul_zero]
  have hlt : Fintype.card (Subtype p) < n := by
    rw [← hcard]; exact Fintype.card_subtype_lt hpa
  obtain ⟨P', Q', kind', partner', h1', h2', hP', hQ', s1, s2, s3, s4⟩ :=
    ih _ hlt (Subtype p) rfl _ d' hg' hdd'
  -- the extended change of bases
  set F := extM p P' * d2 * extM p Q' with hFdef
  have hFin : ∀ x z (hx : p x) (hz : p z), F x z = (P' * d' * Q') ⟨x, hx⟩ ⟨z, hz⟩ := by
    intro x z hx hz
    rw [hFdef, mul_extM_apply_pos p _ _ x hz, mul_apply]
    apply Finset.sum_congr rfl
    intro w _
    rw [extM_mul_apply_pos p P' d2 hx, mul_apply]
    rfl
  have hFout : ∀ x z, ¬ (p x ∧ p z) → F x z = if x = b0 ∧ z = a0 then 1 else 0 := by
    intro x z hxz
    by_cases hz : p z
    · have hx : ¬ p x := fun hx => hxz ⟨hx, hz⟩
      rw [hFdef, mul_extM_apply_pos p _ _ x hz]
      rw [if_neg (fun h => hz.1 h.2)]
      apply Finset.sum_eq_zero
      intro w _
      rw [extM_mul_apply_neg p P' d2 hx]
      rcases hnp x hx with rfl | rfl
      · rw [hrowa, zero_mul]
      · rw [hrow w.1 w.2.1, zero_mul]
    · rw [hFdef, mul_extM_apply_neg p _ _ x hz]
      rcases hnp z hz with rfl | rfl
      · by_cases hx : p x
        · rw [extM_mul_apply_pos p P' d2 hx, if_neg (fun h => hx.2 h.1)]
          apply Finset.sum_eq_zero
          intro y _
          rw [hcol y.1 y.2.2, mul_zero]
        · rw [extM_mul_apply_neg p P' d2 hx]
          rcases hnp x hx with rfl | rfl
          · rw [hrowa, if_neg (fun h => hab h.1)]
          · rw [hD1, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg (fun h => hab h.2.symm)]
        by_cases hx : p x
        · rw [extM_mul_apply_pos p P' d2 hx]
          apply Finset.sum_eq_zero
          intro y _
          rw [hcolb, mul_zero]
        · rw [extM_mul_apply_neg p P' d2 hx, hcolb]
  -- kinds and partners
  set kind : J → Fin 3 := fun x => if hx : p x then kind' ⟨x, hx⟩ else if x = a0 then 1 else 2
    with hkdef
  set partner : J → J := fun x =>
    if hx : p x then (partner' ⟨x, hx⟩).1 else if x = a0 then b0 else a0 with hptdef
  have hk : ∀ y : Subtype p, kind y = kind' y := fun y => by simp [hkdef, y.2]
  have hpt : ∀ y : Subtype p, partner y = (partner' y).1 := fun y => by simp [hptdef, y.2]
  have hka : kind a0 = 1 := by simp [hkdef, hpa]
  have hkb : kind b0 = 2 := by simp [hkdef, hpb, Ne.symm hab]
  have hpta : partner a0 = b0 := by simp [hptdef, hpa]
  have hptb : partner b0 = a0 := by simp [hptdef, hpb, Ne.symm hab]
  have hFba : F b0 a0 = 1 := by rw [hFout b0 a0 (fun h => hpb h.1), if_pos ⟨rfl, rfl⟩]
  refine ⟨extM p P' * P1, Q1 * extM p Q', kind, partner, ?_, ?_, (extM_degP p P' hP').mul hP1,
    hQ1.mul (extM_degP p Q' hQ'), ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P1, h11, Matrix.one_mul, extM_mul_extM, h1', extM_one]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (extM p Q'), extM_mul_extM, h2', extM_one,
      Matrix.one_mul, h12]
  have hconj : extM p P' * P1 * d * (Q1 * extM p Q') = F := by
    rw [hFdef, hd2def]; simp only [Matrix.mul_assoc]
  rw [hconj]
  refine ⟨fun x hx1 => ?_, fun x hx2 => ?_, fun x y hne => ?_, fun x y hx0 hy0 => ?_⟩
  · by_cases hx : p x
    · have hk1 : kind' ⟨x, hx⟩ = 1 := by rw [← hk ⟨x, hx⟩]; exact hx1
      obtain ⟨a1, a2, a3⟩ := s1 ⟨x, hx⟩ hk1
      have e1 : partner x = (partner' ⟨x, hx⟩).1 := hpt ⟨x, hx⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [e1, hk]; exact a1
      · rw [e1, hpt, a2]
      · rw [e1, hFin _ _ (partner' ⟨x, hx⟩).2 hx]; exact a3
    · rcases hnp x hx with rfl | rfl
      · exact ⟨by rw [hpta, hkb], by rw [hpta, hptb], by rw [hpta, hFba]⟩
      · rw [hkb] at hx1; exact absurd hx1 (by decide)
  · by_cases hx : p x
    · have hk2 : kind' ⟨x, hx⟩ = 2 := by rw [← hk ⟨x, hx⟩]; exact hx2
      obtain ⟨a1, a2⟩ := s2 ⟨x, hx⟩ hk2
      have e1 : partner x = (partner' ⟨x, hx⟩).1 := hpt ⟨x, hx⟩
      exact ⟨by rw [e1, hk]; exact a1, by rw [e1, hpt, a2]⟩
    · rcases hnp x hx with rfl | rfl
      · rw [hka] at hx2; exact absurd hx2 (by decide)
      · exact ⟨by rw [hptb, hka], by rw [hptb, hpta]⟩
  · by_cases hxy : p x ∧ p y
    · rw [hFin y x hxy.2 hxy.1] at hne
      rcases s3 ⟨x, hxy.1⟩ ⟨y, hxy.2⟩ hne with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · left; exact ⟨by rw [hk ⟨x, hxy.1⟩]; exact c1, by rw [hk ⟨y, hxy.2⟩]; exact c2⟩
      · right
        refine ⟨by rw [hk ⟨x, hxy.1⟩]; exact c1, ?_⟩
        rw [hpt ⟨x, hxy.1⟩, ← c2]
    · rw [hFout y x (fun h => hxy ⟨h.2, h.1⟩)] at hne
      split_ifs at hne with h
      · obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨hka, hpta.symm⟩
      · exact absurd rfl hne
  · have hpx : p x := by
      by_contra hx
      rcases hnp x hx with rfl | rfl
      · rw [hka] at hx0; exact absurd hx0 (by decide)
      · rw [hkb] at hx0; exact absurd hx0 (by decide)
    have hpy : p y := by
      by_contra hy
      rcases hnp y hy with rfl | rfl
      · rw [hka] at hy0; exact absurd hy0 (by decide)
      · rw [hkb] at hy0; exact absurd hy0 (by decide)
    rw [hFin y x hpy hpx]
    exact s4 ⟨x, hpx⟩ ⟨y, hpy⟩ (by rw [← hk]; exact hx0) (by rw [← hk]; exact hy0)

end Graded

/-- **The minimal model of a bounded finite free complex over a local ring** (Lemma
`ex:limits-fixed-field-budget`, tex L5357–5359 "by cancelling unit entries at its maximal ideal",
tex L5404–5409 "Decompose `D` over `Λ` into a minimal complex `D_min` and unit disks `E`"; the
"textbook minimal-complex reduction over a local ring" cited as GLUE in the central lane's
base-zero lemma). Let `R` be a local ring and `(I, deg, d)` a bounded complex of finite free
`R`-modules with chosen bases (`d` raises degree by one, `d * d = 0`; `DEPARTURE`, form only, see
the module docstring). Then there is a degree-preserving invertible change of bases `P` (inverse
`Q`) after which the differential `P * d * Q` is in split form: the direct sum of a minimal
complex (the kind-`0` basis vectors, differential entries in `𝔪`) and unit disks
`[R x --1--> R (partner x)]`. Classification: PROVED. -/
def MinimalModelSplit : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d : Matrix I I R), IsGradedDiff deg d → d * d = 0 →
      ∃ (P Q : Matrix I I R) (kind : I → Fin 3) (partner : I → I),
        P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
        SplitForm (P * d * Q) kind partner

theorem minimalModelSplit_proof : MinimalModelSplit.{u, v} := by
  intro R _ _ I _ _ deg d hg hd
  exact minimal_split_aux (Fintype.card I) I rfl deg d hg hd

/-- **The minimal part is a minimal complex.** If a graded square-zero `D` is in split form, its
restriction `m` to the kind-`0` basis vectors raises degree by one, satisfies `m * m = 0`, and has
all entries in `𝔪`. Classification: PROVED. -/
def SplitMinimalPart : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (D : Matrix I I R) (kind : I → Fin 3) (partner : I → I),
    IsGradedDiff deg D → D * D = 0 → SplitForm D kind partner →
      let m : Matrix {x // kind x = 0} {x // kind x = 0} R := D.submatrix Subtype.val Subtype.val
      IsGradedDiff (fun y : {x // kind x = 0} => deg y) m ∧ m * m = 0 ∧
        ∀ a b, m a b ∈ IsLocalRing.maximalIdeal R

theorem splitMinimalPart_proof : SplitMinimalPart.{u, v} := by
  intro R _ _ I _ _ deg D kind partner hg hD ⟨_, _, s3, s4⟩ m
  refine ⟨fun a b h => hg a b h, ?_, fun a b => s4 b.1 a.1 b.2 a.2⟩
  ext a b
  have h := congrFun (congrFun hD a.1) b.1
  rw [mul_apply, sum_eq_sum_subtype (fun x => kind x = 0)] at h
  · simpa [m, mul_apply] using h
  · intro y hy
    by_cases h0 : D y b.1 = 0
    · rw [h0, mul_zero]
    · rcases s3 b.1 y h0 with ⟨-, c⟩ | ⟨c, -⟩
      · exact absurd c hy
      · rw [b.2] at c; exact absurd c (by decide)

/-- Non-vacuity: the zero differential on any graded finite index set satisfies the hypotheses
(and is already minimal). PROVED. -/
theorem minimalModel_example {R : Type u} [CommRing R] (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) : IsGradedDiff deg (0 : Matrix I I R) ∧ (0 : Matrix I I R) * 0 = 0 :=
  ⟨fun _ _ h => absurd rfl h, Matrix.mul_zero 0⟩

/-! ### Residue-field cohomology and the size of the minimal part -/

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Type*} [Fintype I] [DecidableEq I]

/-- The columns of degree `n` of the residue matrix `d ⊗ k` (`k = R/𝔪`): the matrix of the residue
differential `d̄ⁿ : (K ⊗ k)ⁿ → (K ⊗ k)ⁿ⁺¹`. -/
noncomputable def resCols (deg : I → ℤ) (d : Matrix I I R) (n : ℤ) :
    Matrix I {a // deg a = n} (IsLocalRing.ResidueField R) :=
  (d.map (IsLocalRing.residue R)).submatrix id Subtype.val

/-- **`dim_k Hⁿ(K ⊗ k)`**, by rank–nullity over the residue field:
`dim (K ⊗ k)ⁿ − rank d̄ⁿ − rank d̄ⁿ⁻¹`. -/
noncomputable def resDim (deg : I → ℤ) (d : Matrix I I R) (n : ℤ) : ℤ :=
  (Fintype.card {a // deg a = n} : ℤ) - (resCols deg d n).rank - (resCols deg d (n - 1)).rank

theorem IsDegPreserving.map {K : Type*} [CommRing K] {deg : I → ℤ} {P : Matrix I I R}
    (hP : IsDegPreserving deg P) (φ : R →+* K) : IsDegPreserving deg (P.map φ) := by
  intro a b h
  apply hP a b
  intro h0
  apply h
  rw [map_apply, h0, map_zero]

/-- Restricting the columns of `X * Q` to degree `n`, for degree-preserving `Q`. -/
theorem cols_mul_degP {K : Type*} [CommRing K] (deg : I → ℤ) (X Q : Matrix I I K)
    (hQ : IsDegPreserving deg Q) (n : ℤ) :
    (X * Q).submatrix id (Subtype.val : {a // deg a = n} → I) =
      X.submatrix id (Subtype.val : {a // deg a = n} → I) *
        Q.submatrix (Subtype.val : {a // deg a = n} → I) (Subtype.val : {a // deg a = n} → I) := by
  ext x a
  rw [submatrix_apply, mul_apply, mul_apply, sum_eq_sum_subtype (fun y => deg y = n)]
  · rfl
  · intro y hy
    have : Q y a = 0 := by
      by_contra h
      exact hy ((hQ y a h).trans a.2)
    simp [this]

/-- The degree-`n` blocks of a degree-preserving inverse pair are inverse to each other. -/
theorem block_mul_degP {K : Type*} [CommRing K] (deg : I → ℤ) (P Q : Matrix I I K)
    (hQ : IsDegPreserving deg Q) (hPQ : P * Q = 1) (n : ℤ) :
    P.submatrix (Subtype.val : {a // deg a = n} → I) (Subtype.val : {a // deg a = n} → I) *
      Q.submatrix (Subtype.val : {a // deg a = n} → I) (Subtype.val : {a // deg a = n} → I) = 1 := by
  ext a b
  have h := congrFun (congrFun hPQ a.1) b.1
  rw [mul_apply, sum_eq_sum_subtype (fun y => deg y = n)] at h
  · rw [mul_apply]
    simp only [submatrix_apply]
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · have : a.1 ≠ b.1 := fun e => hab (Subtype.ext e)
      rw [one_apply_ne this, one_apply_ne hab]
  · intro y hy
    have : Q y b = 0 := by
      by_contra h0
      exact hy ((hQ y b h0).trans b.2)
    simp [this]

/-- **The residue cohomology dimensions are invariant under a degree-preserving change of
bases.** PROVED. -/
theorem resDim_conj {deg : I → ℤ} {P d Q : Matrix I I R} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hP : IsDegPreserving deg P) (hQ : IsDegPreserving deg Q) (n : ℤ) :
    (resCols deg (P * d * Q) n).rank = (resCols deg d n).rank := by
  set φ := IsLocalRing.residue R
  have hPm : P.map φ * Q.map φ = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ φ.map_zero φ.map_one]
  have hQm : Q.map φ * P.map φ = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ φ.map_zero φ.map_one]
  have hblk := block_mul_degP deg (Q.map φ) (P.map φ) (hP.map φ) hQm n
  unfold resCols
  rw [Matrix.map_mul, Matrix.map_mul, cols_mul_degP deg _ _ (hQ.map φ) n]
  have : (P.map φ * d.map φ).submatrix id (Subtype.val : {a // deg a = n} → I) =
      P.map φ * (d.map φ).submatrix id Subtype.val := by
    ext x a; simp [mul_apply]
  rw [this, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_right_inverse hblk),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse hPm)]

/-- In split form, the residue matrix is the partial permutation matrix of the disks. -/
theorem split_residue {D : Matrix I I R} {kind : I → Fin 3} {partner : I → I}
    (hS : SplitForm D kind partner) (y x : I) :
    D.map (IsLocalRing.residue R) y x = if kind x = 1 ∧ y = partner x then 1 else 0 := by
  obtain ⟨s1, -, s3, s4⟩ := hS
  rw [map_apply]
  split_ifs with h
  · obtain ⟨hk, rfl⟩ := h
    rw [(s1 x hk).2.2, map_one]
  · by_cases h0 : D y x = 0
    · rw [h0, map_zero]
    · rcases s3 x y h0 with ⟨c1, c2⟩ | c
      · exact (IsLocalRing.residue_eq_zero_iff _).2 (s4 x y c1 c2)
      · exact absurd c h

/-- In split form, `rank d̄ⁿ` is the number of disks starting in degree `n`. PROVED. -/
theorem rank_resCols_split (deg : I → ℤ) {D : Matrix I I R} {kind : I → Fin 3}
    {partner : I → I} (hS : SplitForm D kind partner) (n : ℤ) :
    (resCols deg D n).rank = Fintype.card {x : {a // deg a = n} // kind x.1 = 1} := by
  set K := IsLocalRing.ResidueField R
  set S := {x : {a // deg a = n} // kind x.1 = 1}
  have hinv : ∀ s : S, partner (partner s.1.1) = s.1.1 := fun s => (hS.1 s.1.1 s.2).2.1
  set A : Matrix I S K := Matrix.of fun y s => if y = partner s.1.1 then 1 else 0 with hA
  set B : Matrix S {a // deg a = n} K := Matrix.of fun s x => if s.1 = x then 1 else 0 with hB
  have hAB : resCols deg D n = A * B := by
    ext y x
    rw [resCols, submatrix_apply, split_residue hS, mul_apply]
    by_cases hk : kind x.1 = 1
    · rw [Finset.sum_eq_single ⟨x, hk⟩]
      · simp [hA, hB, hk]
      · intro s _ hs
        have : s.1 ≠ x := fun h => hs (Subtype.ext h)
        simp [hB, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg (fun h => hk h.1)]
      apply (Finset.sum_eq_zero _).symm
      intro s _
      have : s.1 ≠ x := fun h => hk (h ▸ s.2)
      simp [hB, this]
  have hAA : Aᵀ * A = 1 := by
    ext s s'
    rw [mul_apply, one_apply]
    rw [Finset.sum_eq_single (partner s.1.1)]
    · by_cases hss : s = s'
      · subst hss; simp [hA]
      · have hne : partner s.1.1 ≠ partner s'.1.1 := by
          intro h
          apply hss
          apply Subtype.ext; apply Subtype.ext
          rw [← hinv s, h, hinv s']
        simp [hA, hne, hss]
    · intro y _ hy
      simp [hA, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hBB : B * Bᵀ = 1 := by
    ext s s'
    rw [mul_apply, one_apply, Finset.sum_eq_single s.1]
    · by_cases hss : s = s'
      · subst hss; simp [hB]
      · have hne : s'.1 ≠ s.1 := fun h => hss (Subtype.ext h.symm)
        simp [hB, hne, hss]
    · intro x _ hx
      have : s.1 ≠ x := fun h => hx h.symm
      simp [hB, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hAB]
  apply le_antisymm
  · exact (rank_mul_le_right A B).trans (rank_le_card_height B)
  · have h1 : Fintype.card S ≤ B.rank := by
      rw [← rank_one (R := K) (n := S), ← hBB]
      exact rank_mul_le_left B Bᵀ
    have h2 : B.rank ≤ (A * B).rank := by
      have : Aᵀ * (A * B) = B := by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
      calc B.rank = (Aᵀ * (A * B)).rank := by rw [this]
        _ ≤ (A * B).rank := rank_mul_le_right _ _
    exact h1.trans h2

/-- Disks ending in degree `n` correspond to disks starting in degree `n − 1`. -/
theorem card_kind_two (deg : I → ℤ) {D : Matrix I I R} {kind : I → Fin 3} {partner : I → I}
    (hg : IsGradedDiff deg D) (hS : SplitForm D kind partner) (n : ℤ) :
    Fintype.card {x : {a // deg a = n} // kind x.1 = 2} =
      Fintype.card {x : {a // deg a = n - 1} // kind x.1 = 1} := by
  obtain ⟨s1, s2, -, -⟩ := hS
  have hdeg1 : ∀ x, kind x = 1 → deg (partner x) = deg x + 1 := by
    intro x hx
    apply hg
    rw [(s1 x hx).2.2]
    exact one_ne_zero
  have hdeg2 : ∀ y, kind y = 2 → deg y = deg (partner y) + 1 := by
    intro y hy
    have hp := (s2 y hy)
    have := hdeg1 (partner y) hp.1
    rw [hp.2] at this
    exact this
  refine Fintype.card_congr
    { toFun := fun y => ⟨⟨partner y.1.1, by have := hdeg2 y.1.1 y.2; rw [y.1.2] at this; omega⟩,
        (s2 y.1.1 y.2).1⟩
      invFun := fun x => ⟨⟨partner x.1.1, by rw [hdeg1 x.1.1 x.2, x.1.2]; ring⟩,
        (s1 x.1.1 x.2).1⟩
      left_inv := fun y => by
        apply Subtype.ext; apply Subtype.ext
        exact (s2 y.1.1 y.2).2
      right_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext
        exact (s1 x.1.1 x.2).2.1 }

/-- The basis vectors of degree `n` split by kind. -/
theorem card_deg_eq_kinds (deg : I → ℤ) (kind : I → Fin 3) (n : ℤ) :
    Fintype.card {a // deg a = n} =
      Fintype.card {x : {a // deg a = n} // kind x.1 = 0} +
      Fintype.card {x : {a // deg a = n} // kind x.1 = 1} +
      Fintype.card {x : {a // deg a = n} // kind x.1 = 2} := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : {a // deg a = n} => kind x.1)),
    Fintype.card_sigma, Fin.sum_univ_three]

end Residue

/-- **The minimal part has the size of the residue cohomology.** If `P * d * Q` is in split form
(for a degree-preserving inverse pair `P, Q`), the number of minimal basis vectors of degree `n`
equals `dim_k Hⁿ(K ⊗ k) = resDim deg d n` (rank–nullity over the residue field; tex L5357–5359:
the minimal model has total rank the total dimension of the residue cohomology).
Classification: PROVED. -/
def MinimalPartDims : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d P Q : Matrix I I R) (kind : I → Fin 3) (partner : I → I),
    IsGradedDiff deg d → P * Q = 1 → Q * P = 1 → IsDegPreserving deg P →
    IsDegPreserving deg Q → SplitForm (P * d * Q) kind partner →
      ∀ n : ℤ, resDim deg d n = Fintype.card {x : {a // deg a = n} // kind x.1 = 0}

theorem minimalPartDims_proof : MinimalPartDims.{u, v} := by
  intro R _ _ I _ _ deg d P Q kind partner hg hPQ hQP hP hQ hS n
  have hgD : IsGradedDiff deg (P * d * Q) := IsGradedDiff.conj hP hg hQ
  unfold resDim
  rw [← resDim_conj hPQ hQP hP hQ n, ← resDim_conj hPQ hQP hP hQ (n - 1),
    rank_resCols_split deg hS, rank_resCols_split deg hS, card_deg_eq_kinds deg kind n,
    card_kind_two deg hgD hS n]
  push_cast
  ring

/-- **The central two-term model** (the form used by the central lane's base-zero lemma,
`RC/Central/BaseZero.lean`, `baseZero_core`, which takes `D : Matrix (Fin (m + 1)) (Fin (m + 1)) A`
with `hcentral : (D.map ρ).rank = m`; tex L4346–4358). Let `R` be a local ring and `(I, deg, d)` a
bounded complex of finite free `R`-modules whose residue cohomology `Hⁿ(K ⊗ k)` vanishes for
`n ∉ {1, 2}` and has dimension one in degrees one and two. Then, after a degree-preserving change
of bases, `K` is the direct sum of unit disks and the two-term complex `[R s₁ --δ--> R s₂]` in
degrees one and two, with `δ ∈ 𝔪`; the `1 × 1` matrix `D = (δ)` satisfies `(D.map ρ).rank = 0`,
i.e. `hcentral` with `m = 0`. Classification: PROVED. -/
def CentralTwoTermModel : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d : Matrix I I R), IsGradedDiff deg d → d * d = 0 →
    (∀ n, n ≠ 1 → n ≠ 2 → resDim deg d n = 0) → resDim deg d 1 = 1 → resDim deg d 2 = 1 →
      ∃ (P Q : Matrix I I R) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
        P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
        SplitForm (P * d * Q) kind partner ∧
        kind s₁ = 0 ∧ kind s₂ = 0 ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
        (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
        (P * d * Q) s₂ s₁ ∈ IsLocalRing.maximalIdeal R ∧
        ((Matrix.of fun _ _ => (P * d * Q) s₂ s₁ : Matrix (Fin (0 + 1)) (Fin (0 + 1)) R).map
          (IsLocalRing.residue R)).rank = 0

theorem centralTwoTermModel_proof : CentralTwoTermModel.{u, v} := by
  intro R _ _ I _ _ deg d hg hd h0 h1 h2
  obtain ⟨P, Q, kind, partner, hPQ, hQP, hP, hQ, hS⟩ := minimalModelSplit_proof R I deg d hg hd
  have hdim := minimalPartDims_proof R I deg d P Q kind partner hg hPQ hQP hP hQ hS
  have e1 : Fintype.card {x : {a // deg a = 1} // kind x.1 = 0} = 1 := by
    have := hdim 1; rw [h1] at this; exact_mod_cast this.symm
  have e2 : Fintype.card {x : {a // deg a = 2} // kind x.1 = 0} = 1 := by
    have := hdim 2; rw [h2] at this; exact_mod_cast this.symm
  obtain ⟨t₁, ht₁⟩ := Fintype.card_eq_one_iff.mp e1
  obtain ⟨t₂, ht₂⟩ := Fintype.card_eq_one_iff.mp e2
  refine ⟨P, Q, kind, partner, t₁.1.1, t₂.1.1, hPQ, hQP, hP, hQ, hS, t₁.2, t₂.2, t₁.1.2, t₂.1.2,
    fun x hx => ?_, hS.2.2.2 _ _ t₁.2 t₂.2, ?_⟩
  · by_cases hx1 : deg x = 1
    · left
      have := ht₁ ⟨⟨x, hx1⟩, hx⟩
      rw [← this]
    · by_cases hx2 : deg x = 2
      · right
        have := ht₂ ⟨⟨x, hx2⟩, hx⟩
        rw [← this]
      · exfalso
        have e0 := hdim (deg x)
        rw [h0 _ hx1 hx2] at e0
        have hpos : 0 < Fintype.card {y : {a // deg a = deg x} // kind y.1 = 0} :=
          Fintype.card_pos_iff.mpr ⟨⟨⟨x, rfl⟩, hx⟩⟩
        omega
  · have hz : (Matrix.of fun _ _ => (P * d * Q) t₂.1.1 t₁.1.1 :
        Matrix (Fin (0 + 1)) (Fin (0 + 1)) R).map (IsLocalRing.residue R) = 0 := by
      ext i j
      simp only [map_apply, of_apply, Matrix.zero_apply]
      exact (IsLocalRing.residue_eq_zero_iff _).2 (hS.2.2.2 _ _ t₁.2 t₂.2)
    rw [hz, rank_zero]

end ZInQ.Contrib.CloudB3RC53.MinimalComplexes
