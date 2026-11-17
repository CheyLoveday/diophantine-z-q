import ZInQKernel.Contrib.OneProof.GrossZagierPlane.Extension
import Mathlib.Analysis.Meromorphic.Order

/-!
# hgz-steps: the place `ord_τ` of `ℚ(X₀(N))` and the evaluation at `τ`

For `τ ∈ ℍ`, `O_τ = {g ∈ ℚ(j, j_N) : the modular function with q-expansion g has no pole at τ}` is a
valuation subring of `ℚ(X₀(N))`, and `ev_τ : O_τ → ℂ` (the value at `τ`) is a local ring map.
The modular function of `g = P(jq, jq(q^N))/Q(jq, jq(q^N))` is `ratFn N P Q = P(j, j_N)/Q(j, j_N)`,
independent of the representation off a discrete set (`ratFn_rep_congr`).
-/

noncomputable section

open UpperHalfPlane Filter Topology

namespace ZInQ.GZSch

open ZInQ.GZAlg ZInQ.GZDict2

variable {N : ℕ} [NeZero N]

theorem eventually_polyFn_ne_zero {P : MvPolynomial (Fin 2) ℚ}
    (hP : polyQ N P ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), polyFn N P (ofComplex z) ≠ 0 := by
  obtain ⟨T, hT⟩ := HasQExp.exists_ne_zero (hasQExp_polyFn N P) hP
  exact eventually_ne_zero_of_im_gt (fun τ => (holoH_polyFn N P τ).meromorphicAt) hT τ

/-- **Two representations give the same function off a discrete set.** -/
theorem ratFn_rep_congr {g : LaurentSeries ℚ} {P Q P' Q' : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) (h' : IsRatRep N g P' Q') (τ : ℍ) :
    ratFn N P Q ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] ratFn N P' Q' ∘ ofComplex := by
  have e0 : polyQ N P / polyQ N Q = polyQ N P' / polyQ N Q' := h.2.symm.trans h'.2
  rw [div_eq_div_iff h.1 h'.1] at e0
  have hz : polyQ N (P * Q' - P' * Q) = 0 := by
    simp only [polyQ] at e0 ⊢
    rw [map_sub, map_mul, map_mul, e0, sub_self]
  have hq := hasQExp_polyFn N (P * Q' - P' * Q)
  rw [hz] at hq
  obtain ⟨T, hT⟩ := HasQExp.eq_zero hq
  have h0 := eventuallyEq_zero_of_im_gt (fun τ => (holoH_polyFn N _ τ).meromorphicAt) hT τ
  filter_upwards [h0, eventually_polyFn_ne_zero h.1 τ, eventually_polyFn_ne_zero h'.1 τ]
    with z hz1 hz2 hz3
  simp only [Function.comp_apply, Pi.zero_apply, polyFn, map_sub, map_mul] at hz1 hz2 hz3 ⊢
  simp only [ratFn, polyFn]
  rw [div_eq_div_iff hz2 hz3]
  linear_combination hz1

/-! ## Representations of sums, products, inverses -/

theorem isRatRep_add {g g' : LaurentSeries ℚ} {P Q P' Q' : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) (h' : IsRatRep N g' P' Q') :
    IsRatRep N (g + g') (P * Q' + Q * P') (Q * Q') := by
  refine ⟨?_, ?_⟩
  · simp only [polyQ, map_mul] at h ⊢; exact mul_ne_zero h.1 h'.1
  · rw [h.2, h'.2, div_add_div _ _ h.1 h'.1]
    simp only [polyQ, map_add, map_mul]

theorem isRatRep_mul {g g' : LaurentSeries ℚ} {P Q P' Q' : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) (h' : IsRatRep N g' P' Q') :
    IsRatRep N (g * g') (P * P') (Q * Q') := by
  refine ⟨?_, ?_⟩
  · simp only [polyQ, map_mul] at h ⊢; exact mul_ne_zero h.1 h'.1
  · rw [h.2, h'.2, div_mul_div_comm]
    simp only [polyQ, map_mul]

theorem isRatRep_neg {g : LaurentSeries ℚ} {P Q : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) : IsRatRep N (-g) (-P) Q :=
  ⟨h.1, by rw [h.2, ← neg_div]; simp only [polyQ, map_neg]⟩

theorem isRatRep_inv' {g : LaurentSeries ℚ} {P Q : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) (hg : g ≠ 0) : IsRatRep N g⁻¹ Q P := by
  have hP : polyQ N P ≠ 0 := by intro h0; apply hg; rw [h.2, h0, zero_div]
  exact ⟨hP, by rw [h.2, inv_div]⟩

theorem isRatRep_const (c : ℚ) :
    IsRatRep N (algebraMap ℚ (LaurentSeries ℚ) c) (MvPolynomial.C c) 1 :=
  ⟨by simp [polyQ], by simp [polyQ]⟩

/-! ## The canonical function of `g ∈ ℚ(X₀(N))` -/

/-- A chosen representation. -/
def repOf (g : X0Field N) : MvPolynomial (Fin 2) ℚ × MvPolynomial (Fin 2) ℚ :=
  ((exists_isRatRep N g).choose, (exists_isRatRep N g).choose_spec.choose)

theorem repOf_spec (g : X0Field N) : IsRatRep N (g : LaurentSeries ℚ) (repOf g).1 (repOf g).2 :=
  (exists_isRatRep N g).choose_spec.choose_spec

/-- **The modular function of `g` on `ℍ`, as a function on `ℂ`.** -/
def mfun (g : X0Field N) : ℂ → ℂ := ratFn N (repOf g).1 (repOf g).2 ∘ ofComplex

theorem mfun_mero (g : X0Field N) (τ : ℍ) : MeromorphicAt (mfun g) (τ : ℂ) :=
  meromorphic_ratFn N _ _ τ

theorem mfun_congr {g : X0Field N} {P Q : MvPolynomial (Fin 2) ℚ}
    (hr : IsRatRep N (g : LaurentSeries ℚ) P Q) (τ : ℍ) :
    mfun g =ᶠ[𝓝[≠] (τ : ℂ)] ratFn N P Q ∘ ofComplex :=
  ratFn_rep_congr (repOf_spec g) hr τ

theorem mfun_add (g h : X0Field N) (τ : ℍ) :
    mfun (g + h) =ᶠ[𝓝[≠] (τ : ℂ)] mfun g + mfun h := by
  have hr := isRatRep_add (repOf_spec g) (repOf_spec h)
  rw [← IntermediateField.coe_add] at hr
  filter_upwards [mfun_congr hr τ, eventually_polyFn_ne_zero (repOf_spec g).1 τ,
    eventually_polyFn_ne_zero (repOf_spec h).1 τ] with z h1 h2 h3
  rw [h1]
  simp only [mfun, Function.comp_apply, Pi.add_apply, ratFn, polyFn, map_add, map_mul] at h2 h3 ⊢
  rw [div_add_div _ _ h2 h3]

theorem mfun_mul (g h : X0Field N) (τ : ℍ) :
    mfun (g * h) =ᶠ[𝓝[≠] (τ : ℂ)] mfun g * mfun h := by
  have hr := isRatRep_mul (repOf_spec g) (repOf_spec h)
  rw [← IntermediateField.coe_mul] at hr
  filter_upwards [mfun_congr hr τ] with z h1
  rw [h1]
  simp only [mfun, Function.comp_apply, Pi.mul_apply, ratFn, polyFn, map_mul]
  rw [div_mul_div_comm]

theorem mfun_neg (g : X0Field N) (τ : ℍ) : mfun (-g) =ᶠ[𝓝[≠] (τ : ℂ)] -mfun g := by
  have hr := isRatRep_neg (repOf_spec g)
  rw [← IntermediateField.coe_neg] at hr
  filter_upwards [mfun_congr hr τ] with z h1
  rw [h1]
  simp only [mfun, Function.comp_apply, Pi.neg_apply, ratFn, polyFn, map_neg, neg_div]

theorem mfun_inv {g : X0Field N} (hg : g ≠ 0) (τ : ℍ) :
    mfun g⁻¹ =ᶠ[𝓝[≠] (τ : ℂ)] (mfun g)⁻¹ := by
  have hr := isRatRep_inv' (repOf_spec g) (by simpa using hg)
  rw [← IntermediateField.coe_inv] at hr
  filter_upwards [mfun_congr hr τ] with z h1
  rw [h1]
  simp only [mfun, Function.comp_apply, Pi.inv_apply, ratFn, inv_div]

theorem mfun_const (c : ℚ) (τ : ℍ) :
    mfun (algebraMap ℚ (X0Field N) c) =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => (c : ℂ) := by
  have hr : IsRatRep N ((algebraMap ℚ (X0Field N) c : X0Field N) : LaurentSeries ℚ)
      (MvPolynomial.C c) 1 := by
    have e1 : ((algebraMap ℚ (X0Field N) c : X0Field N) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) c :=
      RingHom.congr_fun (Subsingleton.elim (((X0Field N).val : X0Field N →+* LaurentSeries ℚ).comp
        (algebraMap ℚ (X0Field N))) (algebraMap ℚ (LaurentSeries ℚ))) c
    rw [e1]; exact isRatRep_const c
  filter_upwards [mfun_congr hr τ] with z h1
  rw [h1]
  simp [ratFn, polyFn]

theorem withTop_nonneg_or_neg_nonneg (a : WithTop ℤ) : 0 ≤ a ∨ 0 ≤ -a := by
  induction a with
  | top => left; exact le_top
  | coe n =>
    rcases le_total 0 n with h | h
    · left; exact_mod_cast h
    · right
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
      exact_mod_cast (show (0 : ℤ) ≤ -n by omega)

/-! ## The valuation ring `O_τ` and the evaluation at `τ` -/

/-- **`O_τ`**: the functions with no pole at `τ`. -/
def Otau (τ : ℍ) : ValuationSubring (X0Field N) where
  carrier := {g | 0 ≤ meromorphicOrderAt (mfun g) (τ : ℂ)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [meromorphicOrderAt_congr (mfun_mul a b τ), meromorphicOrderAt_mul (mfun_mero a τ)
      (mfun_mero b τ)]
    exact add_nonneg ha hb
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    have h := mfun_const (N := N) 1 τ
    rw [map_one] at h
    rw [meromorphicOrderAt_congr h]
    exact analyticAt_const.meromorphicOrderAt_nonneg
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [meromorphicOrderAt_congr (mfun_add a b τ)]
    exact le_trans (le_min ha hb) (meromorphicOrderAt_add (mfun_mero a τ) (mfun_mero b τ))
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have h := mfun_const (N := N) 0 τ
    rw [map_zero] at h
    rw [meromorphicOrderAt_congr h]
    exact analyticAt_const.meromorphicOrderAt_nonneg
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [meromorphicOrderAt_congr (mfun_neg a τ), ← meromorphicOrderAt_neg]
    exact ha
  mem_or_inv_mem' a := by
    by_cases ha : a = 0
    · left
      subst ha
      show 0 ≤ meromorphicOrderAt (mfun (0 : X0Field N)) (τ : ℂ)
      have h := mfun_const (N := N) 0 τ
      rw [map_zero] at h
      rw [meromorphicOrderAt_congr h]
      exact analyticAt_const.meromorphicOrderAt_nonneg
    · show 0 ≤ meromorphicOrderAt (mfun a) (τ : ℂ) ∨ 0 ≤ meromorphicOrderAt (mfun a⁻¹) (τ : ℂ)
      rw [meromorphicOrderAt_congr (mfun_inv ha τ), meromorphicOrderAt_inv]
      exact withTop_nonneg_or_neg_nonneg _

theorem mem_Otau {τ : ℍ} {g : X0Field N} :
    g ∈ Otau τ ↔ 0 ≤ meromorphicOrderAt (mfun g) (τ : ℂ) := Iff.rfl

theorem rat_mem_Otau (τ : ℍ) (c : ℚ) : algebraMap ℚ (X0Field N) c ∈ Otau τ := by
  rw [mem_Otau, meromorphicOrderAt_congr (mfun_const c τ)]
  exact analyticAt_const.meromorphicOrderAt_nonneg

theorem tendsto_lim (τ : ℍ) (g : Otau (N := N) τ) :
    Tendsto (mfun (g : X0Field N)) (𝓝[≠] (τ : ℂ))
      (𝓝 (limUnder (𝓝[≠] (τ : ℂ)) (mfun (g : X0Field N)))) := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg (mfun_mero (g : X0Field N) τ) g.2
  rwa [hc.limUnder_eq]

/-- **`ev_τ : O_τ → ℂ`, the value at `τ`.** -/
def evTau (τ : ℍ) : Otau (N := N) τ →+* ℂ where
  toFun g := limUnder (𝓝[≠] (τ : ℂ)) (mfun (g : X0Field N))
  map_one' := by
    have h := mfun_const (N := N) 1 τ
    rw [map_one] at h
    exact tendsto_nhds_unique ((tendsto_lim τ 1).congr' h) (by simp)
  map_mul' a b := tendsto_nhds_unique ((tendsto_lim τ (a * b)).congr' (mfun_mul a.1 b.1 τ))
    ((tendsto_lim τ a).mul (tendsto_lim τ b))
  map_zero' := by
    have h := mfun_const (N := N) 0 τ
    rw [map_zero] at h
    exact tendsto_nhds_unique ((tendsto_lim τ 0).congr' h) (by simp)
  map_add' a b := tendsto_nhds_unique ((tendsto_lim τ (a + b)).congr' (mfun_add a.1 b.1 τ))
    ((tendsto_lim τ a).add (tendsto_lim τ b))

/-- **The value at `τ` is the limit of `P(j, j_N)/Q(j, j_N)` for every representation.** -/
theorem tendsto_evTau (τ : ℍ) (g : Otau (N := N) τ) {P Q : MvPolynomial (Fin 2) ℚ}
    (hr : IsRatRep N ((g : X0Field N) : LaurentSeries ℚ) P Q) :
    Tendsto (ratFn N P Q ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 (evTau τ g)) :=
  (tendsto_lim τ g).congr' (mfun_congr hr τ)

instance isLocalHom_evTau (τ : ℍ) : IsLocalHom (evTau (N := N) τ) where
  map_nonunit g hg := by
    have hne : evTau τ g ≠ 0 := hg.ne_zero
    have h0 : meromorphicOrderAt (mfun (g : X0Field N)) (τ : ℂ) = 0 :=
      (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (mfun_mero (g : X0Field N) τ)).mp
        ⟨_, hne, tendsto_lim τ g⟩
    have hg0 : (g : X0Field N) ≠ 0 := by
      intro h
      apply hne
      have h1 := mfun_const (N := N) 0 τ
      rw [map_zero, ← h] at h1
      have h2 : Tendsto (fun _ : ℂ => ((0 : ℚ) : ℂ)) (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
        simp only [Rat.cast_zero]; exact tendsto_const_nhds
      exact tendsto_nhds_unique (tendsto_lim τ g) (h2.congr' h1.symm)
    have hinv : (g : X0Field N)⁻¹ ∈ Otau τ := by
      rw [mem_Otau, meromorphicOrderAt_congr (mfun_inv hg0 τ), meromorphicOrderAt_inv, h0]
      simp
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : Otau (N := N) τ) (Subtype.ext ?_)
    simp [hg0]

end ZInQ.GZSch
