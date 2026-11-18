import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-!
# The final companion, part 1: `disc ℚ(√k) = k` and the splitting of the level primes

Manuscript `diophantine_zq.tex`, the final companion `k` (tex L2595–2613) with the conditions of
the rough companion (tex L2349–2352): `k` a negative odd fundamental discriminant (squarefree,
`k ≡ 1 mod 4`), a unit square at every prime of `2N`, prime to `h_*`. Cai–Shu–Tian (`CST.lean`)
needs every level prime split in `K = ℚ(√k)`.

* `discr_mul_sq_int`: for a generator `θ ∈ 𝓞_K` with `minpoly ℚ θ = X² + uX + v`,
  `u² − 4v = disc K · i²` with `i ∈ ℤ` (the coordinates of `1, θ` in an integral basis are integers);
* `discr_eq_of_sq`: **`disc K = k`** for a quadratic field `K` containing a square root of a
  squarefree `k ≡ 1 (mod 4)`, `k ≠ 1` (the generator `(1 + √k)/2` has discriminant `k`, and `k`
  squarefree forces the index to be `1`);
* `levelPrimes_split`, `levelPrimes_split_of_disc`: under exactly the conditions on `kfin` that
  GenusOdd's `gzComparison_of_RC19` takes (`kfin < 0`, `kfin % 4 = 1`, `Squarefree kfin`,
  `SquareAt p kfin` at every prime `p ∣ 2N`), every prime of the level splits in `ℚ(√kfin)` (from
  `splittingCriterion_proof`).

All statements are PROVED.
-/

noncomputable section

open Polynomial NumberField

namespace ZInQ.Contrib.CloudB3RC53.Companion

open ZInQ.Contrib.CloudB3RC53.Splitting

variable {K : Type} [Field K] [NumberField K]

/-- **`u² − 4v = disc K · i²`** with `i ∈ ℤ`, for a generator `θ ∈ 𝓞_K` with
`minpoly ℚ θ = X² + uX + v`. -/
theorem discr_mul_sq_int (hK : Module.finrank ℚ K = 2) {θ : 𝓞 K} {u v : ℤ}
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    ∃ i : ℤ, u ^ 2 - 4 * v = discr K * i ^ 2 := by
  classical
  set pb := pbOf hK hmin
  set b := pb.basis
  set b' := integralBasis K
  have hcard : Fintype.card (Fin pb.dim) =
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := by
    rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis b']
  let e := Fintype.equivOfCardEq hcard
  set c := b.reindex e
  -- integer coordinates of `θ^j` in the integral basis
  let Mint : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ :=
    fun i j => (RingOfIntegers.basis K).repr (θ ^ ((e.symm j : Fin pb.dim) : ℕ)) i
  have hc_apply : ∀ j, c j = algebraMap (𝓞 K) K (θ ^ ((e.symm j : Fin pb.dim) : ℕ)) := by
    intro j
    rw [Module.Basis.reindex_apply, PowerBasis.coe_basis, pbOf_gen, map_pow]
  have hM : b'.toMatrix c = Mint.map (Int.cast : ℤ → ℚ) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hc_apply, integralBasis_repr_apply]
    rfl
  have hc : (⇑c) = Matrix.vecMul (⇑b') ((b'.toMatrix c).map (algebraMap ℚ K)) := by
    funext j
    rw [Matrix.vecMul, dotProduct]
    simp only [Matrix.map_apply]
    rw [← b'.sum_toMatrix_smul_self c j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hdc : Algebra.discr ℚ ⇑c = Algebra.discr ℚ ⇑b := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex]
  have key : Algebra.discr ℚ ⇑c = (Mint.det : ℚ) ^ 2 * (discr K : ℚ) := by
    rw [hc, Algebra.discr_of_matrix_vecMul, hM, coe_discr]
    congr 2
    exact (RingHom.map_det (Int.castRingHom ℚ) Mint).symm
  rw [hdc, discr_pbOf] at key
  refine ⟨Mint.det, ?_⟩
  have : ((u ^ 2 - 4 * v : ℤ) : ℚ) = ((discr K * Mint.det ^ 2 : ℤ) : ℚ) := by
    rw [key]; push_cast; ring
  exact_mod_cast this

/-- A squarefree integer that is a square is `1`. -/
theorem eq_one_of_isSquare_of_squarefree {k : ℤ} (hk : Squarefree k) (h : IsSquare k)
    (h0 : 0 ≤ k) : k = 1 := by
  obtain ⟨n, rfl⟩ := h
  have hu := hk n (dvd_refl _)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num

/-- **`disc ℚ(√k) = k`**: for a quadratic field `K` containing `s` with `s² = k`, `k` a squarefree
integer `≡ 1 (mod 4)`, `k ≠ 1`, the discriminant of `K` is `k`. -/
theorem discr_eq_of_sq (hK : Module.finrank ℚ K = 2) {k : ℤ} (hk : Squarefree k)
    (hk4 : k % 4 = 1) (hk1 : k ≠ 1) {s : K} (hs : s ^ 2 = k) : discr K = k := by
  -- `s` is irrational
  have hsr : s ∉ (algebraMap ℚ K).range := by
    rintro ⟨r, hr⟩
    have hsq : IsSquare (k : ℚ) := by
      refine ⟨r, (algebraMap ℚ K).injective ?_⟩
      rw [map_mul, hr, ← sq, hs]; simp
    rw [Rat.isSquare_intCast_iff] at hsq
    have h0 : 0 ≤ k := by obtain ⟨n, rfl⟩ := hsq; nlinarith
    exact hk1 (eq_one_of_isSquare_of_squarefree hk hsq h0)
  set t := k / 4
  have hkt : k = 4 * t + 1 := by omega
  set θ : K := (1 + s) / 2
  have hθ2 : θ ^ 2 + ((-1 : ℤ) : K) * θ + ((-t : ℤ) : K) = 0 := by
    simp only [θ]
    push_cast
    have : s ^ 2 = 4 * (t : K) + 1 := by rw [hs, hkt]; push_cast; ring
    field_simp
    linear_combination this
  have hθint : IsIntegral ℤ θ := by
    refine ⟨X ^ 2 + C (-1 : ℤ) * X + C (-t : ℤ), by monicity!, ?_⟩
    rw [← aeval_def]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq]
    convert hθ2 using 2
  have hθr : θ ∉ (algebraMap ℚ K).range := by
    rintro ⟨r, hr⟩
    apply hsr
    refine ⟨2 * r - 1, ?_⟩
    rw [map_sub, map_mul, hr, map_ofNat, map_one]
    simp only [θ]
    field_simp
    ring
  let θ' : 𝓞 K := ⟨θ, hθint⟩
  have hmin : minpoly ℚ (θ' : K) = X ^ 2 + C ((-1 : ℤ) : ℚ) * X + C ((-t : ℤ) : ℚ) :=
    minpoly_eq_of_aeval hK hθr (-1) (-t) hθ2
  obtain ⟨i, hi⟩ := discr_mul_sq_int hK hmin
  have hik : (-1 : ℤ) ^ 2 - 4 * (-t) = k := by rw [hkt]; ring
  rw [hik] at hi
  -- `k` squarefree forces `i = ±1`
  have hiu : IsUnit i := hk i ⟨discr K, by rw [hi]; ring⟩
  have hi2 : i ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hiu with rfl | rfl <;> norm_num
  rw [hi, hi2, mul_one]

/-- **The level primes split in `ℚ(√kfin)`** (PROVED from `splittingCriterion_proof`), for a
quadratic field `K` of discriminant `kfin`, under the conditions on `kfin` that GenusOdd's
`gzComparison_of_RC19` takes: `kfin` a unit square at every prime of `2N`. -/
theorem levelPrimes_split_of_disc (hK : Module.finrank ℚ K = 2) {kfin : ℤ} (hD : discr K = kfin)
    {N : ℕ} (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * N → GenusOdd.SquareAt p kfin) :
    ∀ p : ℕ, p.Prime → p ∣ N → CST.SplitsIn K p := fun p hp hpN =>
  splittingCriterion_proof K hK p hp (hD ▸ hk2N p hp (dvd_mul_of_dvd_right hpN 2))

/-- **The level primes split in `ℚ(√kfin)`**, for any quadratic field `K` containing a square root
of `kfin`, under exactly the `kfin` hypotheses of GenusOdd's `gzComparison_of_RC19` (`kfin < 0`,
`kfin % 4 = 1`, `Squarefree kfin`, `SquareAt p kfin` at the primes of `2N`); also
`disc K = kfin`. -/
theorem levelPrimes_split (hK : Module.finrank ℚ K = 2) {kfin : ℤ} (hk0 : kfin < 0)
    (hk4 : kfin % 4 = 1) (hksq : Squarefree kfin) {N : ℕ}
    (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * N → GenusOdd.SquareAt p kfin) {s : K}
    (hs : s ^ 2 = kfin) :
    discr K = kfin ∧ ∀ p : ℕ, p.Prime → p ∣ N → CST.SplitsIn K p := by
  have hD := discr_eq_of_sq hK hksq hk4 (by omega) hs
  exact ⟨hD, levelPrimes_split_of_disc hK hD hk2N⟩

end ZInQ.Contrib.CloudB3RC53.Companion
