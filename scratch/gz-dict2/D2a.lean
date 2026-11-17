import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic

noncomputable section

open UpperHalfPlane Filter Topology

namespace ZInQ.GZDict2

open ZInQ.GZAlg

/-! ## §1. Algebra of `q`-expansions -/

theorem hasQExp_add {X Y : ℍ → ℂ} {x y : LaurentSeries ℚ} (hX : HasQExp X x) (hY : HasQExp Y y) :
    HasQExp (fun τ => X τ + Y τ) (x + y) := by
  obtain ⟨T1, h1⟩ := hX
  obtain ⟨T2, h2⟩ := hY
  refine ⟨max T1 T2, fun τ hτ => ?_⟩
  have := (h1 τ (lt_of_le_of_lt (le_max_left _ _) hτ)).add
    (h2 τ (lt_of_le_of_lt (le_max_right _ _) hτ))
  convert this using 1
  funext m
  simp [HahnSeries.coeff_add, add_mul]

theorem algebraMap_laurent (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c :=
  (RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries ℚ)) HahnSeries.C) c).trans rfl

theorem hasQExp_const (c : ℚ) :
    HasQExp (fun _ => (c : ℂ)) (algebraMap ℚ (LaurentSeries ℚ) c) := by
  refine ⟨0, fun τ _ => ?_⟩
  rw [algebraMap_laurent]
  have h := hasSum_single (f := fun m : ℤ => (((HahnSeries.single (0 : ℤ) c).coeff m : ℚ) : ℂ) *
    qPar τ ^ m) 0 (fun b hb => by simp [HahnSeries.coeff_single_of_ne hb])
  simpa using h

/-- The coefficient of a product of Laurent series, as a (finite) convergent sum in `ℂ`. -/
theorem hasSum_coeff_mul (x y : LaurentSeries ℚ) (m : ℤ) :
    HasSum (fun a : ℤ => ((x.coeff a : ℚ) : ℂ) * ((y.coeff (m - a) : ℚ) : ℂ))
      (((x * y).coeff m : ℚ) : ℂ) := by
  classical
  set A := Finset.antidiagonal x.isPWO_support y.isPWO_support m
  have hmem : ∀ ij : ℤ × ℤ, ij ∈ A ↔ x.coeff ij.1 ≠ 0 ∧ y.coeff ij.2 ≠ 0 ∧ ij.1 + ij.2 = m := by
    intro ij
    simp [A, HahnSeries.mem_support]
  have hsum : HasSum (fun a : ℤ => ((x.coeff a : ℚ) : ℂ) * ((y.coeff (m - a) : ℚ) : ℂ))
      (∑ a ∈ A.image Prod.fst, ((x.coeff a : ℚ) : ℂ) * ((y.coeff (m - a) : ℚ) : ℂ)) :=
    hasSum_sum_of_ne_finset_zero (fun a ha => by
      by_contra h0
      apply ha
      have h0' : x.coeff a * y.coeff (m - a) ≠ 0 := by exact_mod_cast h0
      refine Finset.mem_image.2 ⟨(a, m - a), (hmem _).2 ⟨left_ne_zero_of_mul h0',
        right_ne_zero_of_mul h0', by ring⟩, rfl⟩)
  convert hsum using 1
  rw [HahnSeries.coeff_mul, Finset.sum_image]
  · push_cast
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, h⟩ := (hmem ij).1 hij
    rw [show m - ij.1 = ij.2 by omega]
  · intro ij hij ij' hij' he
    obtain ⟨-, -, h⟩ := (hmem ij).1 hij
    obtain ⟨-, -, h'⟩ := (hmem ij').1 hij'
    exact Prod.ext he (by omega)

theorem hasQExp_mul {X Y : ℍ → ℂ} {x y : LaurentSeries ℚ} (hX : HasQExp X x) (hY : HasQExp Y y) :
    HasQExp (fun τ => X τ * Y τ) (x * y) := by
  obtain ⟨T1, h1⟩ := hX
  obtain ⟨T2, h2⟩ := hY
  refine ⟨max T1 T2, fun τ hτ => ?_⟩
  have hs1 := h1 τ (lt_of_le_of_lt (le_max_left _ _) hτ)
  have hs2 := h2 τ (lt_of_le_of_lt (le_max_right _ _) hτ)
  have hq := qPar_ne_zero τ
  set f : ℤ → ℂ := fun m => (x.coeff m : ℂ) * qPar τ ^ m
  set g : ℤ → ℂ := fun m => (y.coeff m : ℂ) * qPar τ ^ m
  have hf : Summable fun m => ‖f m‖ := summable_norm_iff.2 hs1.summable
  have hg : Summable fun m => ‖g m‖ := summable_norm_iff.2 hs2.summable
  have hprod := hs1.mul hs2 (summable_mul_of_summable_norm hf hg)
  -- reindex `(a, b) ↦ (a + b, a)`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have he := (e.hasSum_iff (f := fun p : ℤ × ℤ => f p.1 * g p.2)).2 hprod
  refine he.prod_fiberwise fun m => ?_
  have hc := (hasSum_coeff_mul x y m).mul_right (qPar τ ^ m)
  convert hc using 1
  funext a
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk, f, g]
  rw [show m = a + (m - a) by ring, zpow_add₀ hq]
  simp only [add_sub_cancel_left]
  ring

theorem hasQExp_congr {X X' : ℍ → ℂ} {x : LaurentSeries ℚ} (h : HasQExp X x) (hXX : ∀ τ, X τ = X' τ) :
    HasQExp X' x := by
  have : X = X' := funext hXX
  exact this ▸ h

/-- A function with `q`-expansion `0` vanishes high up. -/
theorem HasQExp.eq_zero {X : ℍ → ℂ} (h : HasQExp X 0) : ∃ T : ℝ, ∀ τ : ℍ, T < τ.im → X τ = 0 := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun τ hτ => ((hT τ hτ).unique (by simp only [HahnSeries.coeff_zero, Rat.cast_zero, zero_mul]; exact hasSum_zero))⟩


/-! ## §2. Nonvanishing high up -/

open FormalMultilinearSeries in
/-- **A function with a nonzero `q`-expansion has no zeros high up.** -/
theorem HasQExp.exists_ne_zero {X : ℍ → ℂ} {x : LaurentSeries ℚ} (h : HasQExp X x) (hx : x ≠ 0) :
    ∃ T : ℝ, ∀ τ : ℍ, T < τ.im → X τ ≠ 0 := by
  obtain ⟨T1, hT1⟩ := h
  set k : ℤ := x.order
  set T0 : ℝ := max T1 0
  set c : ℕ → ℂ := fun n => (x.coeff ((n : ℤ) + k) : ℂ)
  have hsum : ∀ τ : ℍ, T0 < τ.im →
      HasSum (fun n : ℕ => c n * qPar τ ^ n) (qPar τ ^ (-k) * X τ) := by
    intro τ hτ
    have hq := qPar_ne_zero τ
    have h0 := hT1 τ (lt_of_le_of_lt (le_max_left _ _) hτ)
    set g : ℕ → ℤ := fun n => (n : ℤ) + k
    have hg : Function.Injective g := fun a b e => by simp only [g] at e; omega
    have h1 := (hg.hasSum_iff (f := fun m : ℤ => (x.coeff m : ℂ) * qPar τ ^ m) (fun m hm => by
      have : m < k := by
        by_contra hk
        exact hm ⟨(m - k).toNat, by simp only [g]; omega⟩
      simp [HahnSeries.coeff_eq_zero_of_lt_order this])).2 h0
    convert h1.mul_left (qPar τ ^ (-k)) using 1
    funext n
    simp only [Function.comp_apply, g, c]
    rw [zpow_add₀ hq, zpow_natCast, zpow_neg]
    field_simp
  have hrad := le_radius (le_max_right T1 0) hsum
  have han := analyticAt_sum hrad (w := 0) (by simpa using R0_pos T0)
  have hc0 : (ofScalars ℂ c).sum 0 ≠ 0 := by
    rw [← ofScalarsSum, ofScalarsSum_zero]
    simp only [c, CharP.cast_eq_zero, zero_add, smul_eq_mul, mul_one, k]
    exact_mod_cast (mt HahnSeries.coeff_order_eq_zero.1 hx)
  obtain ⟨δ, hδ, hδne⟩ := Metric.eventually_nhds_iff.1 (han.continuousAt.eventually_ne hc0)
  -- choose `T ≥ T0` with `R0 T ≤ δ`
  obtain ⟨T, hTT0, hTδ⟩ : ∃ T : ℝ, T0 ≤ T ∧ R0 T ≤ δ := by
    refine ⟨max T0 (-Real.log δ / (2 * Real.pi)), le_max_left _ _, ?_⟩
    rw [R0]
    calc Real.exp (-(2 * Real.pi * max T0 (-Real.log δ / (2 * Real.pi))))
        ≤ Real.exp (-(2 * Real.pi * (-Real.log δ / (2 * Real.pi)))) := by
          apply Real.exp_le_exp.2
          have := Real.pi_pos
          nlinarith [le_max_right T0 (-Real.log δ / (2 * Real.pi))]
      _ = δ := by
          rw [show -(2 * Real.pi * (-Real.log δ / (2 * Real.pi))) = Real.log δ by
            field_simp]
          exact Real.exp_log hδ
  refine ⟨T, fun τ hτ hX => ?_⟩
  have hτ0 : T0 < τ.im := lt_of_le_of_lt hTT0 hτ
  have hq : ‖qPar τ‖ < δ := lt_of_lt_of_le (norm_qPar_lt hτ) hTδ
  apply hδne (y := qPar τ) (by simpa using hq)
  rw [sum_eq hsum τ hτ0, hX, mul_zero]

/-! ## §3. The functions `j(τ)`, `j(Nτ)` and the plane model -/

/-- `j(τ) = E₄(τ)³/Δ(τ)`. -/
def jFun (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- The point `(j(τ), j(Nτ))` of the plane model `Φ_N(X, Y) = 0` of `X₀(N)`. -/
def pt2 (N : ℕ) [NeZero N] (τ : ℍ) : Fin 2 → ℂ := ![jFun τ, jFun (scaleN N τ)]

/-- The generators `(jq, jq(q^N))` of `ℚ(X₀(N)) = X0Field N`. -/
def ptQ (N : ℕ) [NeZero N] : Fin 2 → LaurentSeries ℚ :=
  ![ModularCurve.jq, ModularCurve.qExpand ℚ N ModularCurve.jq]

/-- `P(j(τ), j(Nτ))`. -/
def polyFn (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ℚ) (τ : ℍ) : ℂ :=
  MvPolynomial.aeval (pt2 N τ) P

/-- `P(jq, jq(q^N)) ∈ ℚ((q))`. -/
def polyQ (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ℚ) : LaurentSeries ℚ :=
  MvPolynomial.aeval (ptQ N) P

/-- **The value at `τ` of the rational function `P/Q` on the plane model**: `P(j(τ), j(Nτ)) / Q(j(τ), j(Nτ))`. -/
def ratFn (N : ℕ) [NeZero N] (P Q : MvPolynomial (Fin 2) ℚ) (τ : ℍ) : ℂ :=
  polyFn N P τ / polyFn N Q τ

/-- **`x = P(j, j_N)/Q(j, j_N)` in `ℚ((q))`**, with `Q(j, j_N) ≠ 0`: `P/Q` represents `x ∈ ℚ(j, j_N)`. -/
def IsRatRep (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) (P Q : MvPolynomial (Fin 2) ℚ) : Prop :=
  polyQ N Q ≠ 0 ∧ x = polyQ N P / polyQ N Q

theorem hasQExp_coord (N : ℕ) [NeZero N] (i : Fin 2) :
    HasQExp (fun τ => pt2 N τ i) (ptQ N i) := by
  fin_cases i
  · exact hasQExp_j
  · exact hasQExp_jN N

theorem hasQExp_polyFn (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ℚ) :
    HasQExp (polyFn N P) (polyQ N P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine hasQExp_congr (by simpa [polyQ] using hasQExp_const a) fun τ => ?_
    simp [polyFn]
  | add p q hp hq =>
    refine hasQExp_congr (by simpa [polyQ] using hasQExp_add hp hq) fun τ => ?_
    simp [polyFn]
  | mul_X p i hp =>
    refine hasQExp_congr (by simpa [polyQ] using hasQExp_mul hp (hasQExp_coord N i)) fun τ => ?_
    simp [polyFn]

/-- Every element of `ℚ(j, j_N)` has a representation `P/Q`. -/
theorem exists_isRatRep (N : ℕ) [NeZero N] (x : X0Field N) :
    ∃ P Q : MvPolynomial (Fin 2) ℚ, IsRatRep N (x : LaurentSeries ℚ) P Q := by
  have hx : (x : LaurentSeries ℚ) ∈ IntermediateField.adjoin ℚ
      ({ModularCurve.jq, ModularCurve.qExpand ℚ N ModularCurve.jq} : Set (LaurentSeries ℚ)) := x.2
  obtain ⟨r, hr, s, hs, he⟩ := IntermediateField.mem_adjoin_iff_div.1 hx
  have hset : ({ModularCurve.jq, ModularCurve.qExpand ℚ N ModularCurve.jq} : Set (LaurentSeries ℚ)) =
      Set.range (ptQ N) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two, ptQ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  rw [hset, Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨P, rfl⟩ := hr
  obtain ⟨Q, rfl⟩ := hs
  by_cases hQ : MvPolynomial.aeval (ptQ N) Q = 0
  · refine ⟨0, 1, by simp [polyQ], ?_⟩
    simp only [polyQ, map_zero, map_one, div_one]
    rw [he]
    simp [hQ]
  · exact ⟨P, Q, hQ, he⟩

end ZInQ.GZDict2
