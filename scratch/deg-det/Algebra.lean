import Mathlib

/-!
# deg-det, pure algebra (Mathlib only)

Mumford's argument for `deg φ = det T_ℓ φ` (*Abelian varieties*, §19, Thm 4), the algebraic part.
-/

open Polynomial

noncomputable section

namespace DegDet

/-! ## 1. Products over roots -/

section Roots
set_option linter.unusedSectionVars false

variable {L : Type*} [Field L] [IsAlgClosed L]

/-- `Rs P F = ∏_{P(a) = 0} F(a)`, the roots of `P` counted with multiplicity. -/
def Rs (P F : L[X]) : L := (P.roots.map (fun a => F.eval a)).prod

theorem Rs_mul_left {P P' : L[X]} (hP : P ≠ 0) (hP' : P' ≠ 0) (F : L[X]) :
    Rs (P * P') F = Rs P F * Rs P' F := by
  unfold Rs
  rw [roots_mul (mul_ne_zero hP hP'), Multiset.map_add, Multiset.prod_add]

theorem Rs_pow_left (P : L[X]) (e : ℕ) (F : L[X]) : Rs (P ^ e) F = Rs P F ^ e := by
  unfold Rs
  rw [roots_pow, Multiset.map_nsmul, Multiset.prod_nsmul]

theorem prod_map_neg' {ι : Type*} (s : Multiset ι) (f : ι → L) :
    (s.map (fun x => -f x)).prod = (-1) ^ Multiset.card s * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.map_cons, Multiset.prod_cons,
      Multiset.card_cons, pow_succ]
    ring

/-- **Abstract lemma.** A multiplicative `φ : L[X] → L` with `φ(c) = c^n` and
`φ(X - r) = (-1)^n P(r)` for a monic `P` of degree `n` is `F ↦ ∏_{P(a)=0} F(a)`. -/
theorem eq_Rs_of_mul (φ : L[X] →* L) (n : ℕ) (P : L[X]) (hPm : P.Monic) (hPd : P.natDegree = n)
    (hC : ∀ c, φ (C c) = c ^ n) (hlin : ∀ r, φ (X - C r) = (-1) ^ n * P.eval r) (F : L[X]) :
    φ F = Rs P F := by
  have hF := (IsAlgClosed.splits F).eq_prod_roots
  have hcard : Multiset.card P.roots = n := by
    rw [← hPd, (IsAlgClosed.splits P).natDegree_eq_card_roots]
  have hPev : ∀ r, P.eval r = (P.roots.map (r - ·)).prod :=
    (IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hPm
  have hFev : ∀ a, F.eval a = F.leadingCoeff * (F.roots.map (a - ·)).prod :=
    (IsAlgClosed.splits F).eval_eq_prod_roots
  have lhs : φ F = F.leadingCoeff ^ n *
      (F.roots.map (fun r => (P.roots.map (fun a => a - r)).prod)).prod := by
    conv_lhs => rw [hF]
    rw [map_mul, hC, map_multiset_prod, Multiset.map_map]
    congr 2
    apply Multiset.map_congr rfl
    intro r _
    simp only [Function.comp_apply]
    rw [hlin, hPev, ← hcard, ← prod_map_neg']
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    ring
  rw [lhs]
  unfold Rs
  simp_rw [hFev]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard,
    Multiset.prod_map_prod_map]

end Roots

/-! ## 2. Determinants of polynomials in a matrix -/

section Matrix

variable {L : Type*} [Field L] [IsAlgClosed L] {I : Type*} [Fintype I] [DecidableEq I]

/-- `det F(M) = ∏_{χ_M(a) = 0} F(a)`. -/
theorem det_aeval_eq_Rs (M : Matrix I I L) (F : L[X]) :
    (aeval M F).det = Rs M.charpoly F := by
  let φ : L[X] →* L := (Matrix.detMonoidHom).comp (aeval M).toRingHom.toMonoidHom
  have hφ : ∀ G, φ G = (aeval M G).det := fun G => rfl
  rw [← hφ]
  refine eq_Rs_of_mul φ (Fintype.card I) M.charpoly (Matrix.charpoly_monic M)
    (Matrix.charpoly_natDegree_eq_dim M) ?_ ?_ F
  · intro c
    rw [hφ, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one]
  · intro r
    rw [hφ, map_sub, aeval_X, aeval_C, Matrix.eval_charpoly, Algebra.algebraMap_eq_smul_one,
      ← Matrix.det_neg, neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Matrix

/-! ## 3. The ℓ-adic comparison lemma -/

section Compare

open Filter Topology

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `∏_{P(a) = 0} F(a)` for `P` over `ℚ_ℓ` and `F` over `ℤ`, computed in `PadicAlgCl ℓ`. -/
def RsZ (P : ℚ_[ℓ][X]) (F : ℤ[X]) : PadicAlgCl ℓ :=
  Rs (P.map (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))) (F.map (Int.castRingHom (PadicAlgCl ℓ)))

omit hℓ in
theorem norm_sum_range_le {L : Type*} [NormedField L] [IsUltrametricDist L] (d : ℕ) (a : ℕ → L)
    (w : L) (ε B : ℝ) (hε : 0 ≤ ε) (hB : 1 ≤ B) (hw : ‖w‖ ≤ B)
    (ha : ∀ i ∈ Finset.range (d + 1), ‖a i‖ ≤ ε) :
    ‖∑ i ∈ Finset.range (d + 1), a i * w ^ i‖ ≤ ε * B ^ d := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hε (pow_nonneg (zero_le_one.trans hB) _)) fun i hi => ?_
  rw [norm_mul, norm_pow]
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc ‖a i‖ * ‖w‖ ^ i ≤ ε * B ^ i :=
        mul_le_mul (ha i hi) (pow_le_pow_left₀ (norm_nonneg _) hw i) (by positivity) hε
    _ ≤ ε * B ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hid) hε

theorem norm_natCast_prime_pow (n : ℕ) : ‖((ℓ : PadicAlgCl ℓ)) ^ n‖ = ((ℓ : ℝ)⁻¹) ^ n := by
  have h := PadicAlgCl.norm_extends ℓ (ℓ : ℚ_[ℓ])
  rw [map_natCast, Padic.norm_p] at h
  rw [norm_pow, h]

theorem norm_multiset_prod_map {L : Type*} [NormedField L] {ι : Type*} (s : Multiset ι)
    (f : ι → L) : ‖(s.map f).prod‖ = (s.map (fun i => ‖f i‖)).prod := by
  have := map_multiset_prod (normHom : L →*₀ ℝ) (s.map f)
  rw [Multiset.map_map] at this
  exact this

/-- **Key estimate.** If `P = μ^e P₁`, `Q = μ^f Q₁` with `μ` irreducible monic not dividing `P₁, Q₁`, and
`|∏_{P(a)=0} F(a)| = |∏_{Q(b)=0} F(b)|` whenever the left side is nonzero, for all `F ∈ ℤ[X]`, then
`e = f`. -/
theorem mult_eq_of_norm_Rs {μ P1 Q1 : ℚ_[ℓ][X]} (hμ : Irreducible μ) (hμm : μ.Monic)
    (hP1 : P1 ≠ 0) (hQ1 : Q1 ≠ 0) (hPμ : ¬ μ ∣ P1) (hQμ : ¬ μ ∣ Q1) (e f : ℕ)
    (h : ∀ F : ℤ[X], RsZ (μ ^ e * P1) F ≠ 0 → ‖RsZ (μ ^ e * P1) F‖ = ‖RsZ (μ ^ f * Q1) F‖) :
    e = f := by
  classical
  set ι := algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) with hι
  set d := μ.natDegree with hd_def
  have hd : 0 < d := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hμ)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  set a : ℝ := (ℓ : ℝ)⁻¹ with ha_def
  have ha0 : 0 < a := inv_pos.mpr (zero_lt_one.trans hℓ1)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hℓ1
  -- scaling `μ` into `ℤ_ℓ[X]`
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ i, ‖(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i‖ ≤ 1 := by
    obtain ⟨s, hsM⟩ := pow_unbounded_of_one_lt (∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖) hℓ1
    refine ⟨s, fun i => ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hci : ‖μ.coeff i‖ ≤ ∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖ := by
      by_cases hi : i ≤ d
      · exact Finset.single_le_sum (f := fun i => ‖μ.coeff i‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), norm_zero]
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ s := pow_pos (zero_lt_one.trans hℓ1) s
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hci.trans hsM.le
  set c : ℕ → ℤ_[ℓ] := fun i => ⟨(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i, hs i⟩ with hc
  set μ0 : ℚ_[ℓ][X] := C ((ℓ : ℚ_[ℓ]) ^ s) * μ with hμ0
  have hμ0nd : (μ0.map ι).natDegree < d + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_map_le).trans ?_)
    exact (natDegree_C_mul_le _ _).trans le_rfl
  have hμ0ev : ∀ w, (μ0.map ι).eval w = ∑ i ∈ Finset.range (d + 1), ι (c i) * w ^ i := by
    intro w
    rw [eval_eq_sum_range' hμ0nd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, hμ0, coeff_C_mul]
  have hμ0μ : ∀ w, (μ0.map ι).eval w = ι ((ℓ : ℚ_[ℓ]) ^ s) * (μ.map ι).eval w := by
    intro w
    rw [hμ0, Polynomial.map_mul, map_C, eval_mul, eval_C]
  -- the test polynomials
  set Fn : ℕ → ℤ[X] := fun n => ∑ i ∈ Finset.range (d + 1),
    C ((PadicInt.appr (c i) (2 * n) : ℕ) : ℤ) * X ^ i + C ((ℓ : ℤ) ^ n) with hFn
  have hFev : ∀ n w, ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
      ∑ i ∈ Finset.range (d + 1), ((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) * w ^ i +
        (ℓ : PadicAlgCl ℓ) ^ n := by
    intro n w
    simp [hFn, Polynomial.map_sum, eval_finsetSum]
  have happr : ∀ n i, ‖((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)‖ ≤
      a ^ (2 * n) := by
    intro n i
    have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (PadicInt.appr_spec (2 * n) (c i))
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h1
    rw [← map_natCast ι, ← map_sub, hι, PadicAlgCl.norm_extends ℓ, norm_sub_rev]
    convert h1 using 1
    rw [ha_def, zpow_neg, zpow_natCast, inv_pow]
  have herr : ∀ n w (B : ℝ), 1 ≤ B → ‖w‖ ≤ B →
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n‖ ≤ a ^ (2 * n) * B ^ d := by
    intro n w B hB hw
    have hrw : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n = ∑ i ∈ Finset.range (d + 1),
          (((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)) * w ^ i := by
      rw [hFev, hμ0ev]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [hrw]
    exact norm_sum_range_le d _ w _ B (pow_nonneg ha0.le _) hB hw fun i _ => happr n i
  -- roots
  have hμmap : μ.map ι ≠ 0 := (hμm.map ι).ne_zero
  have hP1map : P1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hP1
  have hQ1map : Q1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ1
  have hcardμ : Multiset.card (μ.map ι).roots = d := by
    rw [← (IsAlgClosed.splits (μ.map ι)).natDegree_eq_card_roots, natDegree_map]
  have hμroot : ∀ w ∈ (μ.map ι).roots, (μ.map ι).eval w = 0 := fun w hw =>
    (mem_roots hμmap).mp hw
  have hnotroot : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      (μ.map ι).eval w ≠ 0 := by
    intro R hR hRμ w hw hμw
    have hRw : aeval w R = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots ((Polynomial.map_ne_zero_iff ι.injective).mpr hR)).mp hw
    have hμw' : aeval w μ = 0 := by rw [aeval_def, eval₂_eq_eval_map]; exact hμw
    have hmin := minpoly.eq_of_irreducible_of_monic hμ hμw' hμm
    exact hRμ (hmin ▸ minpoly.dvd ℚ_[ℓ] w hRw)
  have hℓs : ι ((ℓ : ℚ_[ℓ]) ^ s) ≠ 0 := by
    rw [map_ne_zero_iff _ ι.injective]
    exact pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hμ0ne : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      0 < ‖(μ0.map ι).eval w‖ := by
    intro R hR hRμ w hw
    rw [norm_pos_iff, hμ0μ]
    exact mul_ne_zero hℓs (hnotroot R hR hRμ w hw)
  -- the bound `B`
  set Z : Finset (PadicAlgCl ℓ) :=
    ((μ.map ι).roots + (P1.map ι).roots + (Q1.map ι).roots).toFinset with hZ
  set B : ℝ := 1 + ∑ w ∈ Z, ‖w‖ with hB
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hBw : ∀ w ∈ Z, ‖w‖ ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => ‖w‖) (fun _ _ => norm_nonneg _) hw).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmemZ1 : ∀ w ∈ (μ.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hw)))
  have hmemZ2 : ∀ w ∈ (P1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hw)))
  have hmemZ3 : ∀ w ∈ (Q1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inr hw)
  -- eventually
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1
  have ev1 : ∀ᶠ n in atTop, a ^ n * B ^ d < 1 := by
    have hBd : 0 < B ^ d := pow_pos (zero_lt_one.trans_le hB1) d
    filter_upwards [hlim.eventually (gt_mem_nhds (inv_pos.mpr hBd))] with n hn
    calc a ^ n * B ^ d < (B ^ d)⁻¹ * B ^ d := mul_lt_mul_of_pos_right hn hBd
      _ = 1 := inv_mul_cancel₀ hBd.ne'
  set S : Finset (PadicAlgCl ℓ) := (P1.map ι).roots.toFinset ∪ (Q1.map ι).roots.toFinset with hS
  have hSpos : ∀ w ∈ S, 0 < ‖(μ0.map ι).eval w‖ := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hμ0ne P1 hP1 hPμ w (Multiset.mem_toFinset.mp hw)
    · exact hμ0ne Q1 hQ1 hQμ w (Multiset.mem_toFinset.mp hw)
  have ev2 : ∀ᶠ n in atTop, ∀ w ∈ S, a ^ n < ‖(μ0.map ι).eval w‖ := by
    rw [eventually_all_finset]
    intro w hw
    exact hlim.eventually (gt_mem_nhds (hSpos w hw))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and ev2)
  -- values of `F_n` at the roots
  have hsmall : ∀ n, N ≤ n → ∀ w ∈ Z, ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w -
      (μ0.map ι).eval w - (ℓ : PadicAlgCl ℓ) ^ n‖ < a ^ n := by
    intro n hn w hw
    refine (herr n w B hB1 (hBw w hw)).trans_lt ?_
    have := (hN n hn).1
    calc a ^ (2 * n) * B ^ d = a ^ n * (a ^ n * B ^ d) := by rw [two_mul, pow_add]; ring
      _ < a ^ n * 1 := mul_lt_mul_of_pos_left this (pow_pos ha0 n)
      _ = a ^ n := mul_one _
  have V1 : ∀ n, N ≤ n → ∀ w ∈ (μ.map ι).roots,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = a ^ n := by
    intro n hn w hw
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (ℓ : PadicAlgCl ℓ) ^ n + E := by
      rw [hE, hμ0μ, hμroot w hw, mul_zero]; ring
    have hEl := hsmall n hn w (hmemZ1 w hw)
    rw [← hE] at hEl
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_natCast_prime_pow]
    · exact max_eq_left hEl.le
    · rw [norm_natCast_prime_pow]; exact hEl.ne'
  have V2 : ∀ n, N ≤ n → ∀ w ∈ S,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = ‖(μ0.map ι).eval w‖ := by
    intro n hn w hw
    have hwZ : w ∈ Z := by
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hmemZ2 w (Multiset.mem_toFinset.mp hw)
      · exact hmemZ3 w (Multiset.mem_toFinset.mp hw)
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (μ0.map ι).eval w + ((ℓ : PadicAlgCl ℓ) ^ n + E) := by
      rw [hE]; ring
    have hEl := hsmall n hn w hwZ
    rw [← hE] at hEl
    have hsm : ‖(ℓ : PadicAlgCl ℓ) ^ n + E‖ < ‖(μ0.map ι).eval w‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
      rw [norm_natCast_prime_pow]
      exact max_lt ((hN n hn).2 w hw) (hEl.trans ((hN n hn).2 w hw))
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsm.ne', max_eq_left hsm.le]
  -- the norms of the products
  have hRsP : ∀ (R : ℚ_[ℓ][X]) (k : ℕ), R ≠ 0 → ¬ μ ∣ R →
      (∀ w ∈ (R.map ι).roots, w ∈ S) → ∀ n, N ≤ n →
      ‖RsZ (μ ^ k * R) (Fn n)‖ = ((a ^ n) ^ d) ^ k *
        ((R.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod := by
    intro R k hR hRμ hRS n hn
    have hRmap : R.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hR
    unfold RsZ
    rw [Polynomial.map_mul, Polynomial.map_pow, Rs_mul_left (pow_ne_zero _ hμmap) hRmap,
      Rs_pow_left, norm_mul, norm_pow]
    unfold Rs
    rw [norm_multiset_prod_map, norm_multiset_prod_map]
    congr 2
    · rw [Multiset.map_congr rfl (V1 n hn), Multiset.map_const', Multiset.prod_replicate, hcardμ]
    · exact Multiset.map_congr rfl fun w hw => V2 n hn w (hRS w hw)
  have hP1S : ∀ w ∈ (P1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr hw))
  have hQ1S : ∀ w ∈ (Q1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hw))
  set CP := ((P1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCP
  set CQ := ((Q1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCQ
  have hCPpos : 0 < CP := Multiset.prod_pos fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact hμ0ne P1 hP1 hPμ w hw
  have key : ∀ n, N ≤ n → ((a ^ n) ^ d) ^ e * CP = ((a ^ n) ^ d) ^ f * CQ := by
    intro n hn
    have h1 := hRsP P1 e hP1 hPμ hP1S n hn
    have h2 := hRsP Q1 f hQ1 hQμ hQ1S n hn
    rw [← h1, ← h2]
    refine h _ ?_
    rw [← norm_pos_iff, h1]
    exact mul_pos (pow_pos (pow_pos (pow_pos ha0 n) d) e) hCPpos
  have k1 := key N le_rfl
  have k2 := key (N + 1) (Nat.le_succ N)
  set x := (a ^ N) ^ d with hx
  set y := a ^ d with hy
  have hxpos : 0 < x := pow_pos (pow_pos ha0 N) d
  have hy0 : 0 < y := pow_pos ha0 d
  have hy1 : y < 1 := pow_lt_one₀ ha0.le ha1 hd.ne'
  have hk2 : (a ^ (N + 1)) ^ d = x * y := by rw [hx, hy, pow_succ, mul_pow]
  rw [hk2, mul_pow, mul_pow] at k2
  have hye : y ^ e = y ^ f := by
    have hne : x ^ e * CP ≠ 0 := (mul_pos (pow_pos hxpos e) hCPpos).ne'
    have : x ^ e * CP * y ^ e = x ^ e * CP * y ^ f := by
      calc x ^ e * CP * y ^ e = x ^ e * y ^ e * CP := by ring
        _ = x ^ f * y ^ f * CQ := k2
        _ = x ^ f * CQ * y ^ f := by ring
        _ = x ^ e * CP * y ^ f := by rw [k1]
    exact mul_left_cancel₀ hne this
  exact pow_right_injective₀ hy0 hy1.ne hye

/-- **Comparison lemma** (Mumford §19, the lemma in the proof of Thm 4; here over `ℚ_ℓ`): two monic
polynomials over `ℚ_ℓ` with `|∏_{P(a)=0} F(a)|_ℓ = |∏_{Q(b)=0} F(b)|_ℓ` for every `F ∈ ℤ[X]` with nonzero
left side are equal. -/
theorem eq_of_norm_RsZ {P Q : ℚ_[ℓ][X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ F : ℤ[X], RsZ P F ≠ 0 → ‖RsZ P F‖ = ‖RsZ Q F‖) : P = Q := by
  classical
  have hP0 := hP.ne_zero
  have hQ0 := hQ.ne_zero
  have hcount : ∀ μ : ℚ_[ℓ][X], Irreducible μ → μ.Monic →
      (UniqueFactorizationMonoid.normalizedFactors P).count μ =
        (UniqueFactorizationMonoid.normalizedFactors Q).count μ := by
    intro μ hμ hμm
    obtain ⟨e, P1, hP1μ, hPe⟩ := WfDvdMonoid.max_power_factor hP0 hμ
    obtain ⟨f, Q1, hQ1μ, hQf⟩ := WfDvdMonoid.max_power_factor hQ0 hμ
    have hP1 : P1 ≠ 0 := by rintro rfl; rw [mul_zero] at hPe; exact hP0 hPe
    have hQ1 : Q1 ≠ 0 := by rintro rfl; rw [mul_zero] at hQf; exact hQ0 hQf
    have hef : e = f := mult_eq_of_norm_Rs hμ hμm hP1 hQ1 hP1μ hQ1μ e f (by
      rw [← hPe, ← hQf]; exact h)
    have hnd : ∀ (k : ℕ) (R : ℚ_[ℓ][X]), ¬ μ ∣ R → ¬ μ ^ (k + 1) ∣ μ ^ k * R := by
      intro k R hR hdvd
      rw [pow_succ] at hdvd
      exact hR ((mul_dvd_mul_iff_left (pow_ne_zero k hμ.ne_zero)).mp hdvd)
    rw [UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨P1, hPe⟩ (hPe ▸ hnd e P1 hP1μ),
      UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨Q1, hQf⟩ (hQf ▸ hnd f Q1 hQ1μ), hef]
  have hnf : UniqueFactorizationMonoid.normalizedFactors P =
      UniqueFactorizationMonoid.normalizedFactors Q := by
    ext μ
    by_cases hμ : μ ∈ UniqueFactorizationMonoid.normalizedFactors P ∨
        μ ∈ UniqueFactorizationMonoid.normalizedFactors Q
    · have hirr : Irreducible μ := by
        rcases hμ with hμ | hμ <;>
          exact UniqueFactorizationMonoid.irreducible_of_normalized_factor μ hμ
      have hnorm : normalize μ = μ := by
        rcases hμ with hμ | hμ <;>
          exact UniqueFactorizationMonoid.normalize_normalized_factor μ hμ
      have hmon : μ.Monic := by
        rw [← hnorm]; exact Polynomial.monic_normalize hirr.ne_zero
      exact hcount μ hirr hmon
    · push Not at hμ
      rw [Multiset.count_eq_zero.mpr hμ.1, Multiset.count_eq_zero.mpr hμ.2]
  have hPa := UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hQa := UniqueFactorizationMonoid.prod_normalizedFactors hQ0
  rw [hnf] at hPa
  exact eq_of_monic_of_associated hP hQ (hPa.symm.trans hQa)

end Compare

end DegDet
