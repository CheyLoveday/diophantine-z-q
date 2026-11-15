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

/-- The square of a pure quaternion of `(2, −3)`. -/
def sqForm (y : B) : ℚ := 2 * y.imI ^ 2 - 3 * y.imJ ^ 2 + 6 * y.imK ^ 2

theorem pure_sq {y : B} (hy : y.re = 0) : y * y = algebraMap ℚ B (sqForm y) := by
  ext <;> simp [sqForm, hy, Algebra.algebraMap_eq_smul_one] <;> ring

/-- **A nonzero pure quaternion in `S_{(τ,1)}` squares to a negative rational**: its eigenvalue `c`
satisfies `c² = y²`, and `c` is not real (`pure_zero_of_real`). -/
theorem sqForm_neg {τ : ℂ} (hτ : τ.im ≠ 0) {y : B} (hy : y.re = 0) (hyS : y ∈ S ![τ, 1])
    (hy0 : ¬ (y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0)) : sqForm y < 0 := by
  obtain ⟨c, hc⟩ := hyS
  have hsq : act (y * y) ![τ, 1] = (c * c) • ![τ, 1] := by
    rw [act_mul, hc, act_smul_vec, hc, smul_smul]
  rw [pure_sq hy, act_algebraMap] at hsq
  have h1 := congrFun hsq 1
  simp at h1
  -- h1 : (sqForm y : ℂ) = c * c
  by_contra hn
  push Not at hn
  apply hy0
  refine pure_zero_of_real hτ hy ?_ hc
  have hr := congrArg Complex.re h1
  have hi := congrArg Complex.im h1
  simp at hr hi
  have hn' : (0 : ℝ) ≤ (sqForm y : ℝ) := by exact_mod_cast hn
  by_contra hci
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp (show c.re * c.im = 0 by linarith) with h | h
    · exact h
    · exact absurd h hci
  have : c.im * c.im ≤ 0 := by nlinarith
  exact hci (by nlinarith [mul_self_nonneg c.im])

/-- **The centralizer of a nonzero pure quaternion `y₀` is `ℚ + ℚy₀`** (in `(2, −3)`; the commutator
of pure parts is a twisted cross product). -/
theorem comm_span {y0 y : B} (h0 : y0.re = 0) (hy0 : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0))
    (h : y * y0 = y0 * y) : ∃ α β : ℚ, y = algebraMap ℚ B α + β • y0 := by
  have e1 := congrArg QuaternionAlgebra.imI h
  have e2 := congrArg QuaternionAlgebra.imJ h
  have e3 := congrArg QuaternionAlgebra.imK h
  simp [h0] at e1 e2 e3
  have E1 : y.imJ * y0.imK = y.imK * y0.imJ := by linarith
  have E2 : y.imI * y0.imK = y.imK * y0.imI := by linarith
  have E3 : y.imI * y0.imJ = y.imJ * y0.imI := by linarith
  have key : ∃ β : ℚ, y.imI = β * y0.imI ∧ y.imJ = β * y0.imJ ∧ y.imK = β * y0.imK := by
    by_cases a1 : y0.imI = 0
    · by_cases a2 : y0.imJ = 0
      · have a3 : y0.imK ≠ 0 := fun a3 => hy0 ⟨a1, a2, a3⟩
        rw [a1] at E2; rw [a2] at E1
        refine ⟨y.imK / y0.imK, ?_, ?_, ?_⟩
        · rw [a1, mul_zero]; simpa [a3] using E2
        · rw [a2, mul_zero]; simpa [a3] using E1
        · field_simp
      · rw [a1] at E3
        refine ⟨y.imJ / y0.imJ, ?_, ?_, ?_⟩
        · rw [a1, mul_zero]; simpa [a2] using E3
        · field_simp
        · rw [div_mul_eq_mul_div, eq_div_iff a2]; linarith
    · refine ⟨y.imI / y0.imI, ?_, ?_, ?_⟩
      · field_simp
      · rw [div_mul_eq_mul_div, eq_div_iff a1]; linarith
      · rw [div_mul_eq_mul_div, eq_div_iff a1]; linarith
  obtain ⟨β, b1, b2, b3⟩ := key
  refine ⟨y.re, β, ?_⟩
  ext <;> simp [h0, Algebra.algebraMap_eq_smul_one, b1, b2, b3]

/-! ## §2 The algebraic core: a subring of `B` cut out by `𝒪 ∩ S_{(τ,1)}` -/

theorem int_of_O {x : B} (hx : x ∈ LeafQM.O) (h1 : x.imI = 0) (h2 : x.imJ = 0) (h3 : x.imK = 0) :
    ∃ n : ℤ, x = (n : B) := by
  obtain ⟨n, rfl⟩ := hx
  simp [LeafQM.ofInt] at h1 h2 h3
  simp [h3] at h1
  refine ⟨n 0, ?_⟩
  ext <;> simp [LeafQM.ofInt, h1, h2, h3]

/-- **The algebraic core.** A ring `R` embedded in `B` with image exactly `𝒪 ∩ S_{(τ,1)}` (`Im τ > 0`) is
`ℤ`, or `Φ⁻¹(𝒪)` for the imaginary quadratic field `k = S_{(τ,1)}` and its inclusion `Φ : k → B`. -/
theorem alg_core {R : Type} [Ring R] {τ : ℂ} (hτ : 0 < τ.im) (F : R →+* B) (hF : Function.Injective F)
    (hR : ∀ x, x ∈ Set.range F ↔ (x ∈ LeafQM.O ∧ x ∈ S ![τ, 1])) :
    Nonempty (R ≃+* ℤ) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k), NumberField.IsTotallyComplex k ∧
      Module.finrank ℚ k = 2 ∧
      ∃ Φ : k →ₐ[ℚ] QMSplit.Aut.B, Nonempty (R ≃+* LeafQM.O.comap Φ.toRingHom) := by
  set v : Fin 2 → ℂ := ![τ, 1] with hvdef
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 1
  have hτ' : τ.im ≠ 0 := hτ.ne'
  have hFO : ∀ r, F r ∈ LeafQM.O := fun r => ((hR (F r)).1 ⟨r, rfl⟩).1
  have hFS : ∀ r, F r ∈ S v := fun r => ((hR (F r)).1 ⟨r, rfl⟩).2
  by_cases hall : ∀ x ∈ S v, x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · left
    have hsurj : Function.Surjective (Int.castRingHom R) := by
      intro r
      obtain ⟨h1, h2, h3⟩ := hall _ (hFS r)
      obtain ⟨n, hn⟩ := int_of_O (hFO r) h1 h2 h3
      exact ⟨n, hF (by simp [hn])⟩
    have hinj : Function.Injective (Int.castRingHom R) := by
      rw [injective_iff_map_eq_zero]
      intro n hn
      have h1 := congrArg F hn
      simp at h1
      have h2 := congrArg QuaternionAlgebra.re h1
      simpa using h2
    exact ⟨(RingEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm⟩
  · right
    obtain ⟨x0, hx0S, hx0⟩ : ∃ x ∈ S v, ¬ (x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0) := by
      by_contra hc
      exact hall (fun x hx => by
        by_contra h
        exact hc ⟨x, hx, h⟩)
    set y0 := x0 - algebraMap ℚ B x0.re with hy0def
    have hy0re : y0.re = 0 := by simp [y0, Algebra.algebraMap_eq_smul_one]
    have hy0S : y0 ∈ S v := (S v).sub_mem hx0S (algebraMap_mem_S v _)
    have hy0nz : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0) := by
      simpa [y0, Algebra.algebraMap_eq_smul_one] using hx0
    have hneg := sqForm_neg hτ' hy0re hy0S hy0nz
    have hfield : IsField (S v) :=
      { exists_pair_ne := ⟨0, 1, fun h => by
          have := congrArg (fun z : S v => (z : B).re) h
          simp at this⟩
        mul_comm := fun a b => Subtype.ext (S_comm hv a.2 b.2)
        mul_inv_cancel := fun {a} ha => by
          obtain ⟨y, hy, hxy⟩ := inv_mem_S hv a.2 (fun h => ha (Subtype.ext h))
          exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩ }
    letI : Field (S v) := hfield.toField
    haveI hcz : CharZero (S v) := ⟨fun m n h => by
      have := congrArg (fun z : S v => (z : B).re) h
      simpa using this⟩
    let Φ : S v →ₐ[ℚ] QMSplit.Aut.B := RingHom.toRatAlgHom (S v).subtype
    have hΦ : ∀ x : S v, Φ x = (x : B) := fun x => rfl
    have hΦinj : Function.Injective Φ := fun a b h => Subtype.ext (by rwa [hΦ, hΦ] at h)
    haveI hfd : FiniteDimensional ℚ (S v) := Module.Finite.of_injective Φ.toLinearMap hΦinj
    haveI : NumberField (S v) := ⟨⟩
    have htc : NumberField.IsTotallyComplex (S v) := by
      refine NumberField.isTotallyComplex_of_sq_ratCast_of_neg (x := ⟨y0, hy0S⟩) (r := sqForm y0) ?_ hneg
      apply hΦinj
      rw [map_pow, AlgHom.commutes, hΦ]
      show y0 ^ 2 = _
      rw [pow_two, pure_sq hy0re]
    have hrange : LinearMap.range Φ.toLinearMap = Submodule.span ℚ (Set.range ![(1 : B), y0]) := by
      apply le_antisymm
      · rintro _ ⟨s, rfl⟩
        obtain ⟨α, β, hαβ⟩ := comm_span hy0re hy0nz (S_comm hv s.2 hy0S)
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨![α, β], ?_⟩
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [AlgHom.toLinearMap_apply, hΦ, hαβ, Algebra.algebraMap_eq_smul_one]
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨1, by simp⟩
        · exact ⟨⟨y0, hy0S⟩, rfl⟩
    have hli : LinearIndependent ℚ ![(1 : B), y0] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e0 := congrArg QuaternionAlgebra.re hst
      have e1 := congrArg QuaternionAlgebra.imI hst
      have e2 := congrArg QuaternionAlgebra.imJ hst
      have e3 := congrArg QuaternionAlgebra.imK hst
      simp [hy0re] at e0 e1 e2 e3
      refine ⟨e0, ?_⟩
      by_contra ht
      exact hy0nz ⟨e1.resolve_left ht, e2.resolve_left ht, e3.resolve_left ht⟩
    have hfr : Module.finrank ℚ (S v) = 2 := by
      rw [← LinearMap.finrank_range_of_inj (f := Φ.toLinearMap) hΦinj, hrange, finrank_span_eq_card hli]
      simp
    refine ⟨S v, inferInstance, inferInstance, htc, hfr, Φ, ⟨?_⟩⟩
    let G : R →+* LeafQM.O.comap Φ.toRingHom :=
      (F.codRestrict (S v) hFS).codRestrict _ (fun r => hFO r)
    refine RingEquiv.ofBijective G ⟨fun a b h => hF ?_, fun s => ?_⟩
    · have := congrArg (fun z : LeafQM.O.comap Φ.toRingHom => ((z : S v) : B)) h
      exact this
    · obtain ⟨r, hr⟩ := (hR ((s : S v) : B)).2 ⟨s.2, (s : S v).2⟩
      exact ⟨r, Subtype.ext (Subtype.ext hr)⟩

end HDec.QMLattice
