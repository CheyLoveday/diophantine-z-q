import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Finite-order eigenvalues, integral coefficients, and reduction of a common lattice. -/

set_option autoImplicit false

namespace DS966Lifting

open Matrix Polynomial
open scoped Matrix

/-- Each root of the characteristic polynomial of a finite-order matrix is a root of unity,
without any assumption on the characteristic or the splitting of the full polynomial. -/
theorem root_pow_eq_one {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {M : Matrix n n K} {m : ℕ} (hM : M ^ m = 1) {x : K}
    (hx : M.charpoly.IsRoot x) : x ^ m = 1 := by
  have h := spectrum.pow_mem_pow M m (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx)
  rwa [hM, spectrum.one_eq, Set.mem_singleton_iff] at h

/-- The two roots in a split characteristic polynomial, counted with multiplicity. -/
theorem charpoly_eq_two_factors {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (hs : M.charpoly.Splits) :
    ∃ x y : K, M.charpoly = (X - C x) * (X - C y) := by
  have hcard : M.charpoly.roots.card = 2 := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
    simp
  obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hcard
  exact ⟨x, y, by rw [hs.eq_prod_roots_of_monic M.charpoly_monic, hxy]; simp⟩

/-- A quadratic factorization gives the trace and determinant over any nonzero base ring. -/
theorem trace_det_of_factors {R : Type*} [CommRing R] [Nontrivial R]
    {M : Matrix (Fin 2) (Fin 2) R} {x y : R}
    (hxy : M.charpoly = (X - C x) * (X - C y)) :
    M.trace = x + y ∧ M.det = x * y := by
  have hnorm : (X - C x) * (X - C y) = X ^ 2 - C (x + y) * X + C (x * y) := by
    rw [map_add, map_mul]
    ring
  rw [hnorm, Matrix.charpoly_fin_two] at hxy
  have htr := congrArg (fun p : R[X] => p.coeff 1) hxy
  have hdet := congrArg (fun p : R[X] => p.coeff 0) hxy
  constructor
  · apply neg_injective
    simpa [Polynomial.coeff_mul_X, neg_add_rev] using htr
  · simpa using hdet

/-- Traces and determinants of split finite-order two-dimensional matrices are the sum and
product of two roots of unity, including in positive characteristic. -/
theorem exists_trace_det_roots {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    {m : ℕ} (hs : M.charpoly.Splits) (hM : M ^ m = 1) :
    ∃ x y : K, x ^ m = 1 ∧ y ^ m = 1 ∧ M.trace = x + y ∧ M.det = x * y := by
  obtain ⟨x, y, hxy⟩ := charpoly_eq_two_factors M hs
  refine ⟨x, y, root_pow_eq_one hM ?_, root_pow_eq_one hM ?_, trace_det_of_factors hxy⟩
  · rw [hxy]; simp [Polynomial.IsRoot]
  · rw [hxy]; simp [Polynomial.IsRoot]

/-- No integral matrix model is needed to deduce integrality of the character and determinant. -/
theorem isIntegral_trace_det {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    {m : ℕ} (hm : 0 < m) (hs : M.charpoly.Splits) (hM : M ^ m = 1) :
    IsIntegral ℤ M.trace ∧ IsIntegral ℤ M.det := by
  obtain ⟨x, y, hx, hy, ht, hd⟩ := exists_trace_det_roots hs hM
  have hx' : IsIntegral ℤ x := IsIntegral.of_pow hm (hx ▸ isIntegral_one)
  have hy' : IsIntegral ℤ y := IsIntegral.of_pow hm (hy ▸ isIntegral_one)
  exact ⟨ht ▸ hx'.add hy', hd ▸ hx'.mul hy'⟩

/-- A ring reduction is injective on the `m`th roots of unity when `m` survives reduction.
The argument does not require a local ring or a chosen primitive root. -/
theorem root_reduction_injective {A k : Type*} [CommRing A] [IsDomain A] [CommRing k]
    (red : A →+* k) {m : ℕ} (hm : (m : k) ≠ 0) {x y : A}
    (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : red x = red y) : x = y := by
  have hm' : m ≠ 0 := by rintro rfl; simp at hm
  let u : Aˣ := Units.ofPowEqOne x m hx hm'
  let v : Aˣ := Units.ofPowEqOne y m hy hm'
  have hu : u ^ m = 1 := Units.ext hx
  have hv : v ^ m = 1 := Units.ext hy
  let z : A := ↑(u / v)
  have hz : z ^ m = 1 := by
    change (↑(u / v) : A) ^ m = 1
    rw [← Units.val_pow_eq_pow_val, div_pow, hu, hv, div_one, Units.val_one]
  have hzred : red z = 1 := by
    have huv : Units.map red.toMonoidHom u = Units.map red.toMonoidHom v := Units.ext hxy
    change (↑(Units.map red.toMonoidHom (u / v)) : k) = 1
    rw [_root_.map_div, huv]
    simp
  have hz1 : z = 1 := by
    by_contra hne
    have hgeom := geom_sum_mul z m
    rw [hz, sub_self] at hgeom
    have hsum := (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
    have h := congrArg red hsum
    exact hm (by simpa [map_sum, hzred] using h)
  exact congrArg Units.val (div_eq_one.mp (Units.ext hz1))

/-- The images of a common integral lattice in characteristic zero and in characteristic `ℓ`
have characteristic polynomials obtained by applying the specified reduction to the roots,
with multiplicities. `R` can be the ring of integers of the original number field, and `A`
the valuation ring of its completed local extension. -/
theorem common_lattice_factors {R A F k : Type*} [CommRing R] [CommRing A] [Field F]
    [Field k] (j : R →+* F) (i : A →+* F) (hi : Function.Injective i)
    (red : R →+* k) (res : A →+* k) (B : Matrix (Fin 2) (Fin 2) A)
    {x y : R} (hx : ∃ a : A, i a = j x ∧ res a = red x)
    (hy : ∃ a : A, i a = j y ∧ res a = red y)
    (hchar : (B.map i).charpoly = (X - C (j x)) * (X - C (j y))) :
    (B.map res).charpoly = (X - C (red x)) * (X - C (red y)) := by
  obtain ⟨a, hai, har⟩ := hx
  obtain ⟨b, hbi, hbr⟩ := hy
  have hA : B.charpoly = (X - C a) * (X - C b) :=
    Polynomial.map_injective i hi (by simpa [Matrix.charpoly_map, hai, hbi] using hchar)
  rw [Matrix.charpoly_map, hA]
  simp [har, hbr]

/-- To transport a finite-order matrix through a common lattice, it suffices that the original
coefficient ring contain the roots of unity of the chosen exponent. The actual coefficients
are sums and products of the same two roots in both characteristics. -/
theorem common_lattice_trace_det {R A F k : Type*} [CommRing R] [CommRing A] [Field F]
    [Field k] (a : R →+* A) (i : A →+* F) (hi : Function.Injective i)
    (ha : Function.Injective a) (res : A →+* k) (B : Matrix (Fin 2) (Fin 2) A)
    {m : ℕ} (hB : (B.map i) ^ m = 1) (hs : (B.map i).charpoly.Splits)
    (hroots : ∀ x : F, x ^ m = 1 → ∃ r : R, i (a r) = x) :
    ∃ x y : R, x ^ m = 1 ∧ y ^ m = 1 ∧
      (B.map i).trace = i (a (x + y)) ∧ (B.map i).det = i (a (x * y)) ∧
      (B.map res).trace = res (a (x + y)) ∧ (B.map res).det = res (a (x * y)) := by
  obtain ⟨z, w, hfac⟩ := charpoly_eq_two_factors (B.map i) hs
  have hz : z ^ m = 1 := root_pow_eq_one hB (by rw [hfac]; simp [Polynomial.IsRoot])
  have hw : w ^ m = 1 := root_pow_eq_one hB (by rw [hfac]; simp [Polynomial.IsRoot])
  obtain ⟨x, hx⟩ := hroots z hz
  obtain ⟨y, hy⟩ := hroots w hw
  have hpow (r : R) (hr : i (a r) ^ m = 1) : r ^ m = 1 := by
    apply ha
    apply hi
    simpa using hr
  have hf : (B.map i).charpoly = (X - C ((i.comp a) x)) * (X - C ((i.comp a) y)) := by
    simpa only [RingHom.comp_apply, hx, hy] using hfac
  have hk := common_lattice_factors (i.comp a) i hi (res.comp a) res B
    ⟨a x, rfl, rfl⟩ ⟨a y, rfl, rfl⟩ hf
  obtain ⟨ht, hd⟩ := trace_det_of_factors hf
  obtain ⟨ht', hd'⟩ := trace_det_of_factors hk
  exact ⟨x, y, hpow x (hx ▸ hz), hpow y (hy ▸ hw), by simpa using ht, by simpa using hd,
    by simpa using ht', by simpa using hd'⟩

/-- Precomposing any lift with the fixed finite quotient preserves finiteness and kills its
kernel. For inertia, apply the last component to each inertia element in the residual kernel. -/
theorem same_quotient {G H P : Type*} [Group G] [Group H] [Finite H] [Group P]
    (q : G →* H) (lift : H →* P) :
    (Set.range (lift.comp q)).Finite ∧ ∀ g, q g = 1 → (lift.comp q) g = 1 := by
  refine ⟨(Set.finite_range lift).subset ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨q g, rfl⟩
  · intro g hg
    simp [hg]

end DS966Lifting
