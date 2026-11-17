import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic
import ZInQKernel.Contrib.OneProof.Gamma0QExpansion
import ZInQKernel.Contrib.OneProof.EtaW32Character

/-!
# gz-dict2: the Gross–Zagier leaf with `φ` read on the plane model of `X₀(N)` (dictionary step D2)

Task gz-dict2 (2026-11-16/17). Report: `docs/research/gz-dict2.md`; scratch and log: `scratch/gz-dict2/`.

gzopt-dict's leaf `GZAlg.GrossZagierAlgOptCd` gives the modular parametrization `φ : X₀(N) → E` by its
pull-back `φ^* : ℚ(E) →ₐ[ℚ] ℚ(X₀(N)) = ℚ(j, j_N)`, but reads the values of `φ` at Heegner points
through auxiliary functions `X, Y : ℍ → ℂ` (meromorphic, with `q`-expansions `φ^*(x), φ^*(y)`).
fold33-review called the identification of `modPt E X Y τ` with the value of `φ` at the point `τ`
step **D2**. This file proves it in Lean and restates the leaf without `X, Y`:

* §1–§2: `q`-expansions form a ring (`hasQExp_add`, `hasQExp_mul`: Cauchy product over `ℤ × ℤ`), and a
  function with a nonzero `q`-expansion has no zeros high up (`HasQExp.exists_ne_zero`).
* §3: the plane model: `pt2 N τ = (j(τ), j(Nτ))`, `polyFn N P τ = P(j(τ), j(Nτ))`,
  `ratFn N P Q = P(j, j_N)/Q(j, j_N)`, `IsRatRep N x P Q` (`x = P(jq, jq(q^N))/Q(jq, jq(q^N))`);
  every `x ∈ ℚ(j, j_N)` has a representation (`exists_isRatRep`).
* §4: holomorphy of `j`, `j(N·)` and of `P(j, j_N)` on `ℍ`; the identity theorem on `ℍ`.
* §5: **D2** (`eventuallyEq_ratFn`): a meromorphic `X` on `ℍ` with `q`-expansion `x = P/Q` equals
  `P(j, j_N)/Q(j, j_N)` on a punctured neighbourhood of every point; hence
  `modPt E X Y τ = modPt E (ratFn Px Qx) (ratFn Py Qy) τ` for all `τ` (`modPt_eq_ratFn`), and the
  optimality hypothesis transfers (`isOptimalParam_congr`).
* §6: the leaf `GrossZagierPlaneOptAt`/`GrossZagierPlaneOptCd` (values of `φ` read on the plane model)
  and the bridge `grossZagierAlgOptCd_of_plane : GrossZagierPlaneOptCd → GZAlg.GrossZagierAlgOptCd`.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 Filter Topology
open scoped Manifold

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


/-! ## §4. Holomorphy on `ℍ` and the identity theorem -/

/-- `F : ℍ → ℂ` is holomorphic: `F ∘ ofComplex` is analytic at every point of `ℍ`. -/
def HoloH (F : ℍ → ℂ) : Prop := ∀ τ : ℍ, AnalyticAt ℂ (F ∘ ofComplex) (τ : ℂ)

theorem holoH_of_mdiff {F : ℍ → ℂ} (h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : HoloH F := fun τ =>
  (UpperHalfPlane.mdifferentiable_iff.1 h).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.2)

theorem HoloH.comp_scaleN {F : ℍ → ℂ} (h : HoloH F) (N : ℕ) [NeZero N] :
    HoloH (fun τ => F (GZAlg.scaleN N τ)) := by
  intro τ
  have hN : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) * z) (τ : ℂ) := by fun_prop
  have h1 := (h (GZAlg.scaleN N τ)).comp_of_eq hN (by simp [GZAlg.scaleN])
  apply h1.congr
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
  have hz' : 0 < z.im := hz
  have hNz : 0 < ((N : ℂ) * z).im := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    simpa using mul_pos this hz'
  simp only [Function.comp_apply]
  congr 1
  apply UpperHalfPlane.ext
  simp [GZAlg.scaleN, ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hNz]

theorem holoH_jFun : HoloH jFun := by
  intro τ
  have h4 := holoH_of_mdiff (ModularFormClass.holo ModularForm.E₄) τ
  have hD := holoH_of_mdiff (CuspFormClass.holo CuspForm.discriminant) τ
  rw [CuspForm.coe_discriminant] at hD
  have hne : (ModularForm.discriminant ∘ ofComplex) (τ : ℂ) ≠ 0 := by
    simpa using ModularForm.discriminant_ne_zero _
  exact (h4.pow 3).div hD hne

theorem holoH_polyFn (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ℚ) : HoloH (polyFn N P) := by
  have hc : ∀ i : Fin 2, HoloH (fun τ => pt2 N τ i) := by
    intro i; fin_cases i
    · exact holoH_jFun
    · exact holoH_jFun.comp_scaleN N
  induction P using MvPolynomial.induction_on with
  | C a => intro τ; simpa [polyFn, Function.comp_def] using analyticAt_const
  | add p q hp hq =>
    intro τ
    exact ((hp τ).add (hq τ)).congr (Filter.Eventually.of_forall fun z => by simp [polyFn])
  | mul_X p i hp =>
    intro τ
    exact ((hp τ).mul (hc i τ)).congr (Filter.Eventually.of_forall fun z => by simp [polyFn])

theorem meromorphic_ratFn (N : ℕ) [NeZero N] (P Q : MvPolynomial (Fin 2) ℚ) (τ : ℍ) :
    MeromorphicAt (ratFn N P Q ∘ ofComplex) (τ : ℂ) :=
  (holoH_polyFn N P τ).meromorphicAt.div (holoH_polyFn N Q τ).meromorphicAt

theorem meromorphicOn_upper {F : ℍ → ℂ} (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) :
    MeromorphicOn (F ∘ ofComplex) {z : ℂ | 0 < z.im} := fun z hz => hF ⟨z, hz⟩

theorem isPreconnected_upper : IsPreconnected {z : ℂ | 0 < z.im} :=
  (convex_halfSpace_im_gt 0).isPreconnected

/-- **Identity theorem on `ℍ`**: a meromorphic function on `ℍ` vanishing on a punctured
neighbourhood of one point vanishes on a punctured neighbourhood of every point. -/
theorem eventuallyEq_zero_transfer {F : ℍ → ℂ} (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    {τ₀ : ℍ} (h₀ : F ∘ ofComplex =ᶠ[𝓝[≠] (τ₀ : ℂ)] 0) (τ : ℍ) :
    F ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] 0 := by
  have := (meromorphicOn_upper hF).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_upper
    τ₀.2 τ.2 (meromorphicOrderAt_eq_top_iff.2 h₀)
  exact meromorphicOrderAt_eq_top_iff.1 this

/-- The point `i t ∈ ℍ`, `t > 0`. -/
def iPt (t : ℝ) (ht : 0 < t) : ℍ := ⟨Complex.I * t, by simpa using ht⟩

theorem iPt_im (t : ℝ) (ht : 0 < t) : (iPt t ht).im = t := by simp [iPt, UpperHalfPlane.im]

/-- Points of a punctured neighbourhood of `i t`, `t > T`, lie in `Im > T`. -/
theorem eventually_im_gt {T t : ℝ} (ht : 0 < t) (hT : T < t) :
    ∀ᶠ z in 𝓝[≠] ((iPt t ht : ℍ) : ℂ), T < z.im ∧ 0 < z.im := by
  have hopen : IsOpen {z : ℂ | max T 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hmem : ((iPt t ht : ℍ) : ℂ) ∈ {z : ℂ | max T 0 < z.im} := by
    change max T 0 < (iPt t ht).im
    rw [iPt_im]; exact max_lt hT ht
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem)] with z hz
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hz, lt_of_le_of_lt (le_max_right _ _) hz⟩

/-- A meromorphic function on `ℍ` vanishing on `Im τ > T` vanishes on a punctured neighbourhood of
every point. -/
theorem eventuallyEq_zero_of_im_gt {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) {T : ℝ}
    (h0 : ∀ τ : ℍ, T < τ.im → F τ = 0) (τ : ℍ) : F ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] 0 := by
  have ht : (0 : ℝ) < max T 0 + 1 := by linarith [le_max_right T 0]
  refine eventuallyEq_zero_transfer hF (τ₀ := iPt _ ht) ?_ τ
  filter_upwards [eventually_im_gt ht (show T < max T 0 + 1 by linarith [le_max_left T 0])]
    with z hz
  simp only [Function.comp_apply, Pi.zero_apply]
  apply h0
  change T < (ofComplex z : ℂ).im
  rw [ofComplex_apply_of_im_pos hz.2]; exact hz.1

/-- A meromorphic function on `ℍ` with no zeros on `Im τ > T` is nonzero on a punctured
neighbourhood of every point. -/
theorem eventually_ne_zero_of_im_gt {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) {T : ℝ}
    (h0 : ∀ τ : ℍ, T < τ.im → F τ ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), F (ofComplex z) ≠ 0 := by
  rcases (hF τ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have ht : (0 : ℝ) < max T 0 + 1 := by linarith [le_max_right T 0]
    have h1 := eventuallyEq_zero_transfer hF (τ₀ := τ) h (iPt _ ht)
    obtain ⟨z, hz1, hz2⟩ := (h1.and (eventually_im_gt ht
      (show T < max T 0 + 1 by linarith [le_max_left T 0]))).exists
    apply h0 (ofComplex z) (by
      change T < (ofComplex z : ℂ).im
      rw [ofComplex_apply_of_im_pos hz2.2]; exact hz2.1)
    simpa using hz1
  · exact h

/-! ## §5. D2: the meromorphic function with `q`-expansion `x` is `P(j, j_N)/Q(j, j_N)` -/

/-- **D2 (values of `φ` through `q`-expansions = values on the plane model).** Let `X` be meromorphic
on `ℍ` with `q`-expansion `x`, and `x = P(j, j_N)/Q(j, j_N)` in `ℚ((q))`. Then
`X(τ') = P(j(τ'), j(Nτ'))/Q(j(τ'), j(Nτ'))` for all `τ' ≠ τ` near any `τ ∈ ℍ`. -/
theorem eventuallyEq_ratFn {N : ℕ} [NeZero N] {X : ℍ → ℂ} {x : LaurentSeries ℚ}
    (hm : ∀ τ : ℍ, MeromorphicAt (X ∘ ofComplex) (τ : ℂ)) (hq : HasQExp X x)
    {P Q : MvPolynomial (Fin 2) ℚ} (hr : IsRatRep N x P Q) (τ : ℍ) :
    X ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] ratFn N P Q ∘ ofComplex := by
  obtain ⟨hQ0, hx⟩ := hr
  have h1 := hasQExp_add (hasQExp_mul hq (hasQExp_polyFn N Q))
    (hasQExp_mul (hasQExp_const (-1)) (hasQExp_polyFn N P))
  have h2 : x * polyQ N Q + algebraMap ℚ (LaurentSeries ℚ) (-1) * polyQ N P = 0 := by
    rw [hx, div_mul_cancel₀ _ hQ0, map_neg, map_one]; ring
  obtain ⟨T, hT⟩ := HasQExp.eq_zero (h2 ▸ h1)
  have hmF : ∀ τ : ℍ, MeromorphicAt ((fun τ => X τ * polyFn N Q τ +
      ((-1 : ℚ) : ℂ) * polyFn N P τ) ∘ ofComplex) (τ : ℂ) := fun τ =>
    ((hm τ).mul (holoH_polyFn N Q τ).meromorphicAt).add
      ((MeromorphicAt.const _ _).mul (holoH_polyFn N P τ).meromorphicAt)
  have hz := eventuallyEq_zero_of_im_gt hmF hT τ
  obtain ⟨T', hT'⟩ := HasQExp.exists_ne_zero (hasQExp_polyFn N Q) hQ0
  have hQne := eventually_ne_zero_of_im_gt (fun τ => (holoH_polyFn N Q τ).meromorphicAt) hT' τ
  filter_upwards [hz, hQne] with z h1 h2
  simp only [Function.comp_apply, Pi.zero_apply, ratFn] at h1 ⊢
  field_simp
  push_cast at h1
  linear_combination h1

/-- **`modPt` depends only on the germs of `X, Y` on punctured neighbourhoods.** -/
theorem modPt_congr (E : WeierstrassCurve ℚ) {X Y X' Y' : ℍ → ℂ} {τ : ℍ}
    (hX : X ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] X' ∘ ofComplex)
    (hY : Y ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] Y' ∘ ofComplex) :
    ZInQ.GZModuli.modPt E X Y τ = ZInQ.GZModuli.modPt E X' Y' τ := by
  have hX' : ∀ a : ℂ, Tendsto (X ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 a) ↔
      Tendsto (X' ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 a) := fun a => tendsto_congr' hX
  have hY' : ∀ a : ℂ, Tendsto (Y ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 a) ↔
      Tendsto (Y' ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 a) := fun a => tendsto_congr' hY
  unfold ZInQ.GZModuli.modPt
  split_ifs
  next h h' =>
    have e1 := tendsto_nhds_unique ((hX' _).1 h.choose_spec.2.1) h'.choose_spec.2.1
    have e2 := tendsto_nhds_unique ((hY' _).1 h.choose_spec.2.2) h'.choose_spec.2.2
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨e1, e2⟩
  next h h' => exact absurd (let ⟨p, hp⟩ := h; ⟨p, hp.1, (hX' _).1 hp.2.1, (hY' _).1 hp.2.2⟩) h'
  next h h' => exact absurd (let ⟨p, hp⟩ := h'; ⟨p, hp.1, (hX' _).2 hp.2.1, (hY' _).2 hp.2.2⟩) h
  next => rfl

/-- **D2, pointwise form**: for `X, Y` meromorphic with `q`-expansions `x, y`, and representations
`x = Px/Qx`, `y = Py/Qy`, the point `modPt E X Y τ` is the value at `τ` of the rational map
`(Px/Qx, Py/Qy)` on the plane model. -/
theorem modPt_eq_ratFn (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] {X Y : ℍ → ℂ}
    {x y : LaurentSeries ℚ}
    (hmX : ∀ τ : ℍ, MeromorphicAt (X ∘ ofComplex) (τ : ℂ))
    (hmY : ∀ τ : ℍ, MeromorphicAt (Y ∘ ofComplex) (τ : ℂ))
    (hqX : HasQExp X x) (hqY : HasQExp Y y) {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N x Px Qx) (hry : IsRatRep N y Py Qy) (τ : ℍ) :
    ZInQ.GZModuli.modPt E X Y τ = ZInQ.GZModuli.modPt E (ratFn N Px Qx) (ratFn N Py Qy) τ :=
  modPt_congr E (eventuallyEq_ratFn hmX hqX hrx τ) (eventuallyEq_ratFn hmY hqY hry τ)

/-- `IsOptimalParam` reads `φ = (X, Y)` only through `modPt`. -/
theorem isOptimalParam_congr {N : ℕ} [NeZero N] {f : Newform N 2} {E : WeierstrassCurve ℚ}
    {X Y X' Y' : ℍ → ℂ} (h : ∀ τ, ZInQ.GZModuli.modPt E X Y τ = ZInQ.GZModuli.modPt E X' Y' τ) :
    ZInQ.GZOptimal.IsOptimalParam N f E X Y ↔ ZInQ.GZOptimal.IsOptimalParam N f E X' Y' := by
  simp only [ZInQ.GZOptimal.IsOptimalParam, h]


/-! ## §6. The leaf with `φ` read on the plane model, and the bridge -/

open scoped WeierstrassCurve.Affine in
/-- **The Gross–Zagier formula for the strong Weil parametrization, `φ` over `ℚ(X₀(N)) = ℚ(j, j_N)`
and its values read on the plane model (Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1; positive
constant forgotten).** As `GZAlg.GrossZagierAlgOptAt E`, except that the auxiliary functions `X, Y`
on `ℍ` are gone: the value of `φ` at `τ ∈ ℍ` is that of the rational map `(Px/Qx, Py/Qy)`
representing `φ^*(x), φ^*(y) ∈ ℚ(j, j_N)` at the point `(j(τ), j(Nτ))` of the plane model
`Φ_N(X, Y) = 0` (with limits at the finitely many points of indeterminacy near `τ`: `modPt`). Every
representation is allowed (they give the same point: `modPt_eq_ratFn`).

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V Thm 2.1 (locators and the exact hypotheses on `φ` UNVERIFIED:
no copy on this host). -/
def GrossZagierPlaneOptAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∀ φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N,
    ((φ (genX E) : LaurentSeries ℚ)).order < 0 →
    ∀ Px Qx Py Qy : MvPolynomial (Fin 2) ℚ,
    IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx →
    IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy →
    ZInQ.GZOptimal.IsOptimalParam N f E (ratFn N Px Qx) (ratFn N Py Qy) →
    ∀ D β : ℤ, ZInQ.GZDecomp.IsOddImagFundDisc D → D < -4 → ZInQ.GZDecomp.HeegnerHyp N D →
    (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, WeierstrassCurve.Affine.Point.map ι y =
      n • ∑ r, ZInQ.GZModuli.modPt E (ratFn N Px Qx) (ratFn N Py Qy) (τ r) →
    ∀ F G : ℂ → ℂ, ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.coeff f) 2 F →
      ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- **The leaf of the `C_d` route, plane-model form**: `GrossZagierPlaneOptAt E'` for every short
model `E'` in the isogeny class of `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierPlaneOptCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], ZInQ.GZOptimal.IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n =
        (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierPlaneOptAt E'

/-- **The bridge (D2 in Lean)**: gzopt-dict's leaf from the plane-model leaf. Given `X, Y`
meromorphic with `q`-expansions `φ^*(x), φ^*(y)`, pick representations `P/Q` (`exists_isRatRep`);
then `modPt E X Y = modPt E (ratFn Px Qx) (ratFn Py Qy)` everywhere (`modPt_eq_ratFn`), so the
optimality hypothesis and the Heegner point transfer. -/
theorem grossZagierAlgOptAt_of_plane {E : WeierstrassCurve ℚ} (h : GrossZagierPlaneOptAt E) :
    GZAlg.GrossZagierAlgOptAt E := by
  intro N _ f hχ hf φ hord X Y hmX hmY hqX hqY hopt D β hD hD4 hH hβ R _ τ hτ K _ _ _ hK δ hδ ι hι
    n hn y hy F G hF hG
  obtain ⟨Px, Qx, hrx⟩ := exists_isRatRep N (φ (genX E))
  obtain ⟨Py, Qy, hry⟩ := exists_isRatRep N (φ (genY E))
  have hpt := modPt_eq_ratFn E hmX hmY hqX hqY hrx hry
  refine h N f hχ hf φ hord Px Qx Py Qy hrx hry ((isOptimalParam_congr hpt).1 hopt) D β hD hD4 hH
    hβ R τ hτ K hK δ hδ ι hι n hn y ?_ F G hF hG
  rw [hy]
  simp only [hpt]

/-- The `C_d` form of the bridge. -/
theorem grossZagierAlgOptCd_of_plane (h : GrossZagierPlaneOptCd) : GZAlg.GrossZagierAlgOptCd :=
  fun d hd hsq E' _ hE' hL => grossZagierAlgOptAt_of_plane (h d hd hsq E' hE' hL)

/-- **What the chain reads** (`grossZagierFormulaCd_of_alg`'s input), from the plane-model leaf. -/
theorem grossZagierFormulaCd_of_plane (h : GrossZagierPlaneOptCd) : ZInQ.GZHL3.GrossZagierFormulaCd :=
  GZAlg.grossZagierFormulaCd_of_alg (grossZagierAlgOptCd_of_plane h)
    ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
    ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof

end ZInQ.GZDict2
