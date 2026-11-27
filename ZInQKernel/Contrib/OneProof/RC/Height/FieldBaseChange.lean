import Mathlib.NumberTheory.Height.NumberField

/-!
# Heights of rational numbers viewed in a number field

Let `K` be a number field. With Mathlib's normalization of heights on `K` (built from all places
of `K`, each infinite place counted with its multiplicity), the height of a rational number `q`
viewed in `K` is the `[K : ℚ]`-th power of its height over `ℚ`:

* `ZInQ.Manuscript.RC.Height.mulHeight₁_algebraMap_rat`:
  `mulHeight₁ (algebraMap ℚ K q) = mulHeight₁ q ^ [K : ℚ]`;
* `ZInQ.Manuscript.RC.Height.logHeight₁_algebraMap_rat`:
  `logHeight₁ (algebraMap ℚ K q) = [K : ℚ] * logHeight₁ q`.

Proof sketch: write `q = num / den` with coprime integers `num, den`, so that the height of `q`
in `K` is the height of the pair `(num, den)`. Every finite place of `K` takes the value `1` on
this pair (Bezout and the ultrametric inequality), every infinite place of `K` restricts to the
usual absolute value on `ℚ`, and the multiplicities of the infinite places sum to `[K : ℚ]`.
-/

namespace ZInQ.Manuscript.RC.Height

open NumberField

/-- For a tuple of integers with `gcd = 1`, every finite place of a number field `K` has
supremum `1` on the tuple (viewed in `K`). PROVED. -/
lemma iSup_finitePlace_intCast_eq_one_of_gcd_eq_one {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ} (v : FinitePlace K)
    (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i : K) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v (n : K) ≤ 1 := hv.apply_intCast_le_one (map_zero_le v 1) (map_one v)
    (map_neg_eq_map v)
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul .univ x
  apply_fun (fun n : ℤ ↦ v (n : K)) at hf
  simp_rw [hx, Int.cast_one, map_one, Int.cast_sum, Int.cast_mul] at hf
  replace hf := hf.trans_le hv.apply_sum_univ_le
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v ((x i : K) * f i))
  rw [← hi, map_mul] at hf
  replace hf : 1 ≤ v (x i : K) := hf.trans <| mul_le_of_le_one_right (apply_nonneg v _) (H _)
  exact le_antisymm (ciSup_le (H <| x ·)) <| Finite.le_ciSup_of_le i hf

/-- The height (relative to `K`) of a rational number `q` viewed in `K` equals the height of
the pair `(num q, den q)` in `K`. PROVED. -/
lemma mulHeight₁_algebraMap_rat_eq_mulHeight_num_den {K : Type*} [Field K] [NumberField K]
    (q : ℚ) :
    Height.mulHeight₁ (algebraMap ℚ K q) = Height.mulHeight ![(q.num : K), (q.den : K)] := by
  have hden : (q.den : K) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  rw [Height.mulHeight₁_eq_mulHeight, ← Height.mulHeight_smul_eq_mulHeight _ hden]
  congr 1
  ext i
  fin_cases i
  · simp [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ hden]
  · simp

/-- The height (relative to the number field `K`, Mathlib's normalization) of a rational number
viewed in `K` is the `[K : ℚ]`-th power of its height over `ℚ`. PROVED. -/
theorem mulHeight₁_algebraMap_rat {K : Type*} [Field K] [NumberField K] (q : ℚ) :
    Height.mulHeight₁ (algebraMap ℚ K q) = Height.mulHeight₁ q ^ Module.finrank ℚ K := by
  have hden : (q.den : K) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hx : ![(q.num : K), (q.den : K)] ≠ 0 := by
    intro h
    exact hden (by simpa using congr_fun h 1)
  rw [mulHeight₁_algebraMap_rat_eq_mulHeight_num_den, NumberField.mulHeight_eq hx,
    Rat.mulHeight₁_eq_max]
  -- the finite places contribute `1`
  have hgcd : (Finset.univ : Finset (Fin 2)).gcd ![q.num, (q.den : ℤ)] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
      Int.isCoprime_iff_gcd_eq_one.mp <| Rat.isCoprime_num_den q
  have hfin (v : FinitePlace K) : ⨆ i, v (![(q.num : K), (q.den : K)] i) = 1 := by
    rw [← iSup_finitePlace_intCast_eq_one_of_gcd_eq_one v hgcd]
    congr 1
    ext i
    fin_cases i <;> simp
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one]
  -- every infinite place restricts to the usual absolute value on `ℚ`
  have hinf (w : InfinitePlace K) :
      ⨆ i, w (![(q.num : K), (q.den : K)] i) = ((max q.num.natAbs q.den : ℕ) : ℝ) := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
    · fin_cases i
      · simp [Int.norm_eq_abs, Nat.cast_natAbs]
      · simp
    · rw [Nat.cast_max]
      refine max_le (Finite.le_ciSup_of_le 0 ?_) (Finite.le_ciSup_of_le 1 ?_)
      · simp [Int.norm_eq_abs, Nat.cast_natAbs]
      · simp
  simp_rw [hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

/-- The logarithmic height (relative to the number field `K`, Mathlib's normalization) of a
rational number viewed in `K` is `[K : ℚ]` times its logarithmic height over `ℚ`. PROVED. -/
theorem logHeight₁_algebraMap_rat {K : Type*} [Field K] [NumberField K] (q : ℚ) :
    Height.logHeight₁ (algebraMap ℚ K q) = (Module.finrank ℚ K : ℝ) * Height.logHeight₁ q := by
  rw [Height.logHeight₁_eq_log_mulHeight₁, mulHeight₁_algebraMap_rat, Real.log_pow,
    Height.logHeight₁_eq_log_mulHeight₁]

/-- Variant of `mulHeight₁_algebraMap_rat` for the coercion `ℚ → K`. PROVED. -/
theorem mulHeight₁_ratCast {K : Type*} [Field K] [NumberField K] (q : ℚ) :
    Height.mulHeight₁ (q : K) = Height.mulHeight₁ q ^ Module.finrank ℚ K := by
  rw [← eq_ratCast (algebraMap ℚ K) q, mulHeight₁_algebraMap_rat]

/-- Variant of `logHeight₁_algebraMap_rat` for the coercion `ℚ → K`. PROVED. -/
theorem logHeight₁_ratCast {K : Type*} [Field K] [NumberField K] (q : ℚ) :
    Height.logHeight₁ (q : K) = (Module.finrank ℚ K : ℝ) * Height.logHeight₁ q := by
  rw [← eq_ratCast (algebraMap ℚ K) q, logHeight₁_algebraMap_rat]

/-- The height (relative to `K`) of a positive natural number `n` viewed in `K` is
`n ^ [K : ℚ]`. PROVED. -/
theorem mulHeight₁_natCast {K : Type*} [Field K] [NumberField K] (n : ℕ) [NeZero n] :
    Height.mulHeight₁ (n : K) = (n : ℝ) ^ Module.finrank ℚ K := by
  rw [← map_natCast (algebraMap ℚ K) n, mulHeight₁_algebraMap_rat, Rat.mulHeight₁_natCast]

/-- The logarithmic height (relative to `K`) of a positive natural number `n` viewed in `K` is
`[K : ℚ] * log n`. PROVED. -/
theorem logHeight₁_natCast {K : Type*} [Field K] [NumberField K] (n : ℕ) [NeZero n] :
    Height.logHeight₁ (n : K) = (Module.finrank ℚ K : ℝ) * Real.log n := by
  rw [← map_natCast (algebraMap ℚ K) n, logHeight₁_algebraMap_rat, Rat.logHeight₁_natCast]

end ZInQ.Manuscript.RC.Height
