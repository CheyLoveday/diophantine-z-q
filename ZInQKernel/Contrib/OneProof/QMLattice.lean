import ZInQKernel.OneProof.H.TailZ26

/-! # gt-qm: `QMCentralizerCMC` by the complex lattice

Task gt-qm (docs/research/gt-qm.md; gap-triage A5). The added-bundle field
`HDec.QMSplit.Aut.QMCentralizerCMC` (TailU, the centralizer `End_𝒪(A)` of the QM of an abelian surface over
`ℂ` is `ℤ` or `Φ⁻¹(𝒪)` for an imaginary quadratic `k` and `Φ : k → B`) is proved here from three textbook
fields of the bundle (`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`) and the chain's
proved glue (`qmLatticeFree_of`, `qmSkolemNoetherC_proof`, `qmClassNumberOne_proof`, `unif_ring_hom`,
`lift_unique`).

* §1 (pure algebra in `B = (2, −3)`): the commutant of `ι(𝒪)` in `End_ℂ(ℂ²)` is `ℂ`; the eigen-subring
  `S_v = {x ∈ B : ι(x)v ∈ ℂv}` is commutative and closed under inverses; for `v = (τ, 1)ᵀ`, `Im τ ≠ 0`, a
  pure quaternion in `S_v` is zero or squares to a negative rational, and `S_v ⊆ ℚ + ℚy₀`.
* §2 (`alg_core`): a ring `R` embedded in `B` with image `𝒪 ∩ S_v` is `ℤ` or `Φ⁻¹(𝒪)` with `k = S_v`
  imaginary quadratic.
* §3 (`com_embed`): by the uniformization `A(ℂ) = ℂ²/ι(𝒪)(τ, 1)ᵀ` (T35 + T11a + `QMLatticeAlgebra`),
  `End_𝒪(A)` embeds in `B` with image `𝒪 ∩ S_{(τ,1)}`.
* §4 the theorem `qmCentralizerCMC_of`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMLattice

open HDec.QMSplit.CNO (act act_add act_mul act_one act_smul act_eq_zero act_sub act_zero act_neg
  mem_qmOrbit_iff oBasis_mem)

abbrev B := LeafQM.B

/-! ## §1 Algebra in `B` -/

theorem act_smul_vec (x : B) (c : ℂ) (w : Fin 2 → ℂ) : act x (c • w) = c • act x w := by
  simp [act, Matrix.mulVec_smul]

theorem act_algebraMap (r : ℚ) (w : Fin 2 → ℂ) : act (algebraMap ℚ B r) w = (r : ℂ) • w := by
  rw [Algebra.algebraMap_eq_smul_one, act_smul, act_one]

theorem act_inj {v : Fin 2 → ℂ} (hv : v ≠ 0) {x y : B} (h : act x v = act y v) : x = y :=
  sub_eq_zero.mp (act_eq_zero hv (by rw [act_sub, h, sub_self]))

/-- The explicit action of a quaternion on `ℂ²`. -/
theorem act_apply0 (x : B) (w : Fin 2 → ℂ) : act x w 0 =
    ((x.re : ℂ) + (x.imI : ℂ) * √2) * w 0 + (-3 * (x.imJ : ℂ) - 3 * √2 * (x.imK : ℂ)) * w 1 := by
  simp [act, FibreQMNorm.qmMatB, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.mul_apply, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
  ring

theorem act_apply1 (x : B) (w : Fin 2 → ℂ) : act x w 1 =
    ((x.imJ : ℂ) - √2 * (x.imK : ℂ)) * w 0 + ((x.re : ℂ) - (x.imI : ℂ) * √2) * w 1 := by
  simp [act, FibreQMNorm.qmMatB, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.mul_apply, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
  ring

/-- **The commutant of `ι(𝒪)` in `End_ℂ(ℂ²)` is `ℂ`** (explicit: commuting with `ι(i) = diag(√2, −√2)`
makes `T` diagonal, commuting with `ι((1+j)/2)` makes the two entries equal). -/
theorem commutant (T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (h : ∀ x ∈ LeafQM.O, ∀ z, T (act x z) = act x (T z)) : ∃ c : ℂ, ∀ z, T z = c • z := by
  have s2 : (√2 : ℂ) ≠ 0 := BPAnalytic.QM.sqrt2_ne_zero
  let e0 : Fin 2 → ℂ := ![1, 0]
  let e1 : Fin 2 → ℂ := ![0, 1]
  have hz : ∀ z : Fin 2 → ℂ, z = z 0 • e0 + z 1 • e1 := by
    intro z; funext i; fin_cases i <;> simp [e0, e1]
  have hi0 : act (BPAnalytic.QM.oBasis 1) e0 = (√2 : ℂ) • e0 := by
    funext i; fin_cases i <;> simp [act_apply0, act_apply1, e0, BPAnalytic.QM.oBasis]
  have hi1 : act (BPAnalytic.QM.oBasis 1) e1 = (-√2 : ℂ) • e1 := by
    funext i; fin_cases i <;> simp [act_apply0, act_apply1, e1, BPAnalytic.QM.oBasis]
  have hj0 : act (BPAnalytic.QM.oBasis 2) e0 = (1 / 2 : ℂ) • (e0 + e1) := by
    funext i; fin_cases i <;> simp [act_apply0, act_apply1, e0, e1, BPAnalytic.QM.oBasis]
  have E1 := congrFun (h _ (oBasis_mem 1) e0) 1
  rw [hi0, map_smul, act_apply1] at E1
  have E2 := congrFun (h _ (oBasis_mem 1) e1) 0
  rw [hi1, map_smul, act_apply0] at E2
  have E3 := congrFun (h _ (oBasis_mem 2) e0) 1
  rw [hj0, map_smul, map_add, act_apply1] at E3
  simp [BPAnalytic.QM.oBasis] at E1 E2 E3
  have r0 : T e0 1 = 0 := by
    have : (2 * √2 : ℂ) * T e0 1 = 0 := by linear_combination E1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero s2)
  have r1 : T e1 0 = 0 := by
    have : (2 * √2 : ℂ) * T e1 0 = 0 := by linear_combination -E2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero s2)
  have r2 : T e1 1 = T e0 0 := by linear_combination 2 * E3
  refine ⟨T e0 0, fun z => ?_⟩
  rw [hz z, map_add, map_smul, map_smul]
  funext i; fin_cases i <;> simp [r0, r1, r2, e0, e1] <;> ring

/-- The eigen-subring `S_v = {x ∈ B : ι(x)v ∈ ℂv}`. -/
def S (v : Fin 2 → ℂ) : Subring B where
  carrier := {x | ∃ c : ℂ, act x v = c • v}
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [act_mul, hd, act_smul_vec, hc, smul_smul]⟩
  one_mem' := ⟨1, by rw [act_one, one_smul]⟩
  add_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [act_add, hc, hd, add_smul]⟩
  zero_mem' := ⟨0, by rw [act_zero, zero_smul]⟩
  neg_mem' := by
    rintro x ⟨c, hc⟩
    exact ⟨-c, by rw [act_neg, hc, neg_smul]⟩

theorem mem_S {v : Fin 2 → ℂ} {x : B} : x ∈ S v ↔ ∃ c : ℂ, act x v = c • v := Iff.rfl

theorem algebraMap_mem_S (v : Fin 2 → ℂ) (r : ℚ) : algebraMap ℚ B r ∈ S v :=
  ⟨r, act_algebraMap r v⟩

theorem S_comm {v : Fin 2 → ℂ} (hv : v ≠ 0) {x y : B} (hx : x ∈ S v) (hy : y ∈ S v) : x * y = y * x := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨d, hd⟩ := hy
  apply act_inj hv
  rw [act_mul, act_mul, hd, hc, act_smul_vec, act_smul_vec, hc, hd, smul_smul, smul_smul, mul_comm]

theorem star_eq (x : B) : star x = algebraMap ℚ B (2 * x.re) - x := by
  ext <;> simp [Algebra.algebraMap_eq_smul_one] <;> ring

theorem star_mem_S {v : Fin 2 → ℂ} {x : B} (hx : x ∈ S v) : star x ∈ S v := by
  rw [star_eq]; exact (S v).sub_mem (algebraMap_mem_S v _) hx

/-- The inverse `x⁻¹ = nrd(x)⁻¹ x̄` stays in `S_v`. -/
theorem inv_mem_S {v : Fin 2 → ℂ} (hv : v ≠ 0) {x : B} (hx : x ∈ S v) (hx0 : x ≠ 0) :
    ∃ y ∈ S v, x * y = 1 := by
  refine ⟨(QMSplit.CNO.nrd x)⁻¹ • star x, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (S v).mul_mem (algebraMap_mem_S v _) (star_mem_S hx)
  · have e := QMSplit.CNO.div_mul_cancel' 1 x hx0
    rw [one_mul] at e
    rw [S_comm hv hx (by rw [Algebra.smul_def]; exact (S v).mul_mem (algebraMap_mem_S v _) (star_mem_S hx))]
    exact e

/-- **A pure quaternion with a real eigenvalue on `(τ, 1)ᵀ`, `Im τ ≠ 0`, is zero** (`ι(y)` is a real
matrix; taking real and imaginary parts of the two rows). -/
theorem pure_zero_of_real {τ : ℂ} (hτ : τ.im ≠ 0) {y : B} (hy : y.re = 0) {c : ℂ} (hc : c.im = 0)
    (h : act y ![τ, 1] = c • ![τ, 1]) : y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [act_apply0] at h0
  rw [act_apply1] at h1
  simp [hy] at h0 h1
  have r0 := congrArg Complex.re h0
  have i0 := congrArg Complex.im h0
  have r1 := congrArg Complex.re h1
  have i1 := congrArg Complex.im h1
  simp [hc] at r0 i0 r1 i1
  have s2 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have e1' : (y.imJ : ℝ) - √2 * y.imK = 0 := i1.resolve_right hτ
  have e0' : (y.imI : ℝ) * √2 = c.re := i0.resolve_right hτ
  have ha : (y.imI : ℝ) * √2 = 0 := by linear_combination (e0' - r1 + e1' * τ.re) / 2
  have hb : (y.imJ : ℝ) + √2 * y.imK = 0 := by linear_combination (r0 - e0' * τ.re) / (-3)
  have hc' : (y.imK : ℝ) * √2 = 0 := by linear_combination (hb - e1') / 2
  have a0 : (y.imI : ℝ) = 0 := (mul_eq_zero.mp ha).resolve_right s2
  have c0 : (y.imK : ℝ) = 0 := (mul_eq_zero.mp hc').resolve_right s2
  have b0 : (y.imJ : ℝ) = 0 := by rw [c0] at e1'; simpa using e1'
  exact ⟨by exact_mod_cast a0, by exact_mod_cast b0, by exact_mod_cast c0⟩

end HDec.QMLattice
