import ZInQKernel.Contrib.CloudB3RC53.Calibration.Bookkeeping

/-!
# Calibration (4.6): the local quotient lengths and the degree-two disks of the coordinate

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex L4051–4078). The input `hδ`
of `hvprim_of_support_triangle` is the central valuation `v₂ det_W(0) = 2 v₂N_i + 4ω(h)` of the
full/Kummer quotient blocks:

> At either place above the split moving prime `r_i`, the central full/Kummer quotient has
> degree-two length `v₂(N_i)`, `N_i = r_i + 1 − χ_h(r_i) a_{r_i}`. [...] At each active split place
> the corresponding quotient has only degree-two cohomology `E[2]`, of length two. The two places
> above each active prime therefore contribute `−4`.

* `det_moving_block`: at the centre the moving character is trivial, so at either place the
  Frobenius scalar is `χ = χ_h(r_i) = ±1` and the singular block of (4.4) at augmentation is
  `χ Fr_r − r`, with `det(χ Fr_r − r) = r N_i`.
* `v2_det_moving` (`r` odd): the two-place block has `v₂ det = 2 v₂ N_i`.
* `v2_det_active`: an active place with degree-two cohomology `E[2] ≅ (ℤ/2)²` has minimal two-term
  model `2 · 1₂` (`MinimalComplexes`); `2ω` such places have `v₂ det = 4ω`.
* `v2_det_quotient`: the whole quotient block `diag(moving, active)` has
  `v₂ det = 2 v₂N_i + 4ω` — the input `hδ`, in the exact form of RC0's `hvprim`.
* `coord_diag_valuation` (the degree-two disks of the coordinate, tex L4058–4062): on a two-term
  model `diag(0, 2^{e_1}, …)` (the free part carrying the class and functional, torsion disks with
  cokernel length `e_i` in degree two), `v₂ u = v₂ z₀ + v₂ w₀ − Σ e_i`: a degree-two disk contributes
  `(−1)^{2+1} e = −e`.

**Scope.** The degree-one and degree-three torsion disks (lengths `g_A`) of the ordinary Kummer
complex lie outside any two-term model (they are not unit disks and cannot be cancelled), and the
project's class-functional coordinate is defined only on two-term models (RC15's
`IsClassFunctionalCoord`). Their sign `(−1)^{i+1}` is a convention of the determinant-line
coordinate of a graded complex, which is not defined in the project; that part of input (i)
therefore stays an input. See the lane notes.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Calibration

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-! ### The moving prime -/

/-- **`det(χ Fr_r − r) = r N`** with `N = r + 1 − χ a_r`, for `χ² = 1`, `tr Fr_r = a_r`,
`det Fr_r = r` (tex L4066–4071). -/
theorem det_moving_block {R : Type*} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R) (r a χ : R)
    (hχ : χ ^ 2 = 1) (ha : F.trace = a) (hd : F.det = r) :
    (χ • F - r • (1 : Matrix (Fin 2) (Fin 2) R)).det = r * (r + 1 - χ * a) := by
  rw [det_smul_sub_smul_one, ha, hd]
  linear_combination r * hχ

theorem v2_natCast_odd {r : ℕ} (hr : Odd r) : v2 (r : ℚ_[2]) = 0 := by
  have hr0 : (r : ℚ_[2]) ≠ 0 := by exact_mod_cast hr.pos.ne'
  rw [v2, Padic.addValuation.apply hr0, Padic.valuation_natCast]
  have : padicValNat 2 r = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h))
  rw [this]; rfl

theorem v2_intCast {n : ℤ} (hn : n ≠ 0) :
    v2 (n : ℚ_[2]) = ((padicValInt 2 n : ℕ) : ℤ) := by
  have hn0 : (n : ℚ_[2]) ≠ 0 := by exact_mod_cast hn
  rw [v2, Padic.addValuation.apply hn0, Padic.valuation_intCast]

/-- **The two places above the moving prime** (tex L4066–4074): at the centre the two-place
singular block is `twoPlaceBlock Fr_r r χ χ` and its determinant has `v₂ = 2 v₂ N_i`. -/
theorem v2_det_moving (F : Matrix (Fin 2) (Fin 2) ℚ_[2]) (r : ℕ) (hr : Odd r) (a χ : ℤ)
    (hχ : χ = 1 ∨ χ = -1) (ha : F.trace = a) (hd : F.det = r) (hN : (r : ℤ) + 1 - χ * a ≠ 0) :
    v2 (twoPlaceBlock F (r : ℚ_[2]) (χ : ℚ_[2]) (χ : ℚ_[2])).det =
      ((2 * ((padicValInt 2 ((r : ℤ) + 1 - χ * a) : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hχ2 : ((χ : ℚ_[2])) ^ 2 = 1 := by rcases hχ with rfl | rfl <;> norm_num
  rw [det_twoPlaceBlock, quotientDet, det_moving_block F _ _ _ hχ2 ha hd]
  have hcast : ((r : ℚ_[2]) + 1 - (χ : ℚ_[2]) * (a : ℚ_[2])) = (((r : ℤ) + 1 - χ * a : ℤ) : ℚ_[2]) := by
    push_cast; ring
  rw [hcast, v2_mul, v2_mul, v2_natCast_odd hr, v2_intCast hN, zero_add, ← WithTop.coe_add,
    two_mul]

/-! ### The active places -/

/-- **`2ω` active places** (tex L4076–4078): each has degree-two cohomology `E[2] ≅ (ℤ/2)²`,
minimal two-term model `2 · 1₂`; together the block `2 · 1` of size `4ω` has `v₂ det = 4ω`. -/
theorem v2_det_active (ω : ℕ) :
    v2 ((2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2])).det =
      ((4 * ω : ℤ) : WithTop ℤ) := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin]
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  rw [v2, Padic.addValuation.apply (pow_ne_zero _ h2), Padic.valuation_pow]
  have : Padic.valuation (2 : ℚ_[2]) = 1 := by
    have := Padic.valuation_p (p := 2)
    exact_mod_cast this
  rw [this]
  push_cast
  simp

/-- **The total length of the full/Kummer quotients** (tex L4066–4078): the quotient block
`diag(twoPlaceBlock Fr_r r χ χ, 2 · 1_{4ω})` has `v₂ det = 2 v₂N_i + 4ω` — the input `hδ` of
`hvprim_of_support_triangle`, with `v₂N_i` as in RC0's `hvprim`. -/
theorem v2_det_quotient (F : Matrix (Fin 2) (Fin 2) ℚ_[2]) (r : ℕ) (hr : Odd r) (a χ : ℤ)
    (hχ : χ = 1 ∨ χ = -1) (ha : F.trace = a) (hd : F.det = r) (hN : (r : ℤ) + 1 - χ * a ≠ 0)
    (ω : ℕ) :
    v2 (fromBlocks (twoPlaceBlock F (r : ℚ_[2]) (χ : ℚ_[2]) (χ : ℚ_[2])) 0 0
        ((2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2]))).det =
      ((2 * ((padicValInt 2 ((r : ℤ) + 1 - χ * a) : ℕ) : ℤ) + 4 * (ω : ℤ) : ℤ) : WithTop ℤ) := by
  rw [det_fromBlocks_zero₂₁, v2_mul, v2_det_moving F r hr a χ hχ ha hd hN, v2_det_active]
  push_cast
  rfl

/-! ### The degree-two disks of the coordinate -/

theorem v2_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ_[2]) : v2 (∏ i ∈ s, f i) = ∑ i ∈ s, v2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v2]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, v2_mul, ih]

/-- **Degree-two torsion disks in the coordinate** (tex L4058–4062). On the two-term model
`D = diag(0, d_1, …, d_m)` (the free summand carrying the class and functional, and torsion disks
with differentials `d_i`, cokernel length `v₂ d_i` in degree two), the coordinate is `u = z₀ w₀ / ∏ d_i`, so
`v₂ u + Σ v₂ d_i = v₂ z₀ + v₂ w₀`: each degree-two disk contributes `−v₂ d_i`. -/
theorem coord_diag_valuation {m : ℕ} (d : Fin m → ℚ_[2]) (z w : Fin (m + 1) → ℚ_[2]) (u : ℚ_[2])
    (hu : IsClassFunctionalCoord (Matrix.diagonal (Fin.cons 0 d : Fin (m + 1) → ℚ_[2])) z w u) :
    v2 u + ∑ i, v2 (d i) = v2 (z 0) + v2 (w 0) := by
  have h00 := congrFun (congrFun hu 0) 0
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul] at h00
  rw [adjugate_diagonal, diagonal_apply_eq] at h00
  have hset : (Finset.univ : Finset (Fin m)).map (Fin.succEmb m) = Finset.univ.erase 0 := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [Fin.succ_ne_zero]
  have hprod : ∏ j ∈ Finset.univ.erase (0 : Fin (m + 1)), (Fin.cons 0 d : Fin (m + 1) → ℚ_[2]) j =
      ∏ i, d i := by
    rw [← hset, Finset.prod_map]
    simp [Fin.cons_succ]
  rw [hprod] at h00
  have := congrArg v2 h00
  rw [v2_mul, v2_mul] at this
  rw [this, v2_prod]

/-- **`hvprim` with the local lengths computed** (tex L4051–4078): the triangular model of the
support triangle from the Kummer complex to the primitive complex, whose quotient block
specializes at the centre to `diag(twoPlaceBlock Fr_r r χ χ, 2 · 1_{4ω})` (the moving prime and
the `2ω` active places), gives RC0's field `hvprim` from the Kummer coordinate's valuation alone. -/
theorem hvprim_of_model_and_lengths {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])) (X : Matrix (Fin n) κ (PowerSeries ℚ_[2]))
    (DW : Matrix κ κ (PowerSeries ℚ_[2])) (zK wK : Fin n → PowerSeries ℚ_[2])
    (zP wP : Fin n ⊕ κ → PowerSeries ℚ_[2]) (uK uprim : PowerSeries ℚ_[2])
    (hz : ∀ i, zP (Sum.inl i) = zK i) (hw : ∀ i, wP (Sum.inl i) = wK i)
    (hP : IsCoordOn (fromBlocks DK X 0 DW) zP wP uprim)
    (hKc : IsClassFunctionalCoord DK zK wK uK) (hadj : DK.adjugate ≠ 0) (j vL vm gA sA : ℤ)
    (hK : v2 (central uK) = (((j + vL + vm) + (j + vL + vm) +
      (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
        Central.diskContribution 3 gA) : ℤ) : WithTop ℤ))
    (F : Matrix (Fin 2) (Fin 2) ℚ_[2]) (r : ℕ) (hr : Odd r) (a χ : ℤ) (hχ : χ = 1 ∨ χ = -1)
    (ha : F.trace = a) (hd : F.det = r) (hN : (r : ℤ) + 1 - χ * a ≠ 0) (ω : ℕ)
    (hcentral : central DW.det = (fromBlocks (twoPlaceBlock F (r : ℚ_[2]) (χ : ℚ_[2]) (χ : ℚ_[2])) 0 0
        ((2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2]))).det) :
    v2 (central uprim) = ((ZInQ.Manuscript.RC.Wiring.primValuation j vL vm gA sA
      ((padicValInt 2 ((r : ℤ) + 1 - χ * a) : ℕ) : ℤ) (ω : ℤ) : ℤ) : WithTop ℤ) := by
  refine hvprim_of_triangular_model DK X DW zK wK zP wP uK uprim hz hw hP hKc hadj j vL vm gA sA
    _ _ hK ?_
  rw [hcentral, v2_det_quotient F r hr a χ hχ ha hd hN ω]

end ZInQ.Contrib.CloudB3RC53.Calibration
