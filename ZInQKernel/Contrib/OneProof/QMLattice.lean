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

theorem act_add_vec (x : B) (u u' : Fin 2 → ℂ) : act x (u + u') = act x u + act x u' := by
  simp [act, Matrix.mulVec_add]

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

/-! ## §3 The centralizer through the uniformization `A(ℂ) = ℂ²/ι(𝒪)(τ, 1)ᵀ` -/

open HSyn.G0Split.FibreQM in
/-- **`End_𝒪(A)` embeds in `B` with image `𝒪 ∩ S_{(τ,1)}`.** By T35 (`h38`), T11a (`h69`) and the proved
`QMLatticeAlgebra`, `A(ℂ) = ℂ²/Λ` with `Λ` carried by `F` onto `ι(𝒪)(τ, 1)ᵀ`, `ι`-compatibly. An element `e` of
the centralizer acts on `ℂ²` by a map commuting with `ι(𝒪)`, hence by a scalar `c(e)` (`commutant`); since
`c(e)(τ, 1)ᵀ ∈ ι(𝒪)(τ, 1)ᵀ`, `c(e)(τ, 1)ᵀ = ι(x)(τ, 1)ᵀ` for a unique `x ∈ 𝒪`; `e ↦ x` is the embedding.
Conversely each such `x` gives the scalar `c`, which preserves `Λ` and so comes from an endomorphism (T11a),
central because `ρ` is injective. -/
theorem com_embed (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : LeafQM.AV.QMStr A) :
    ∃ (τ : ℂ) (_ : 0 < τ.im) (F : LeafQM.AV.com q →+* B), Function.Injective F ∧
      ∀ x : B, x ∈ Set.range F ↔ (x ∈ LeafQM.O ∧ x ∈ S ![τ, 1]) := by
  have hE : UniformizationExistsT35 := AvSplit.Final.h38 hU hM
  have hR : T11aRiemannEnd := ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hU hG)
  have hL : QMLatticeAlgebra :=
    qmLatticeAlgebra_of_free (qmLatticeFree_of qmSkolemNoetherC_proof QMSplit.CNO.qmClassNumberOne_proof)
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ A (RingHom.id ℂ) 2 hA
  haveI := hd
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR A hA Λ Φu hΦ
  obtain ⟨τ, hτ, Fl, hF, hFρ⟩ := hL Λ hlat (ρ.comp q.iota) (fun a z hz => hpres (q.iota a) z hz)
  set v : Fin 2 → ℂ := ![τ, 1] with hvdef
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 1
  have hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ FibreQMNorm.qmOrbit v := by
    intro z
    rw [← FibreQMNorm.qmLattice_eq_orbit hτ.ne', ← hF]
    constructor
    · intro h; exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      have : w = z := Fl.injective he
      rw [← this]; exact hw
  have hι : ∀ (a : LeafQM.O) z, Fl (ρ (q.iota a) z) = act (a : B) (Fl z) := fun a z => hFρ a z
  have hT11 := hR A 2 Λ Φu hA hΦ
  have hρinj : Function.Injective ρ := fun e e' h =>
    (hT11.1 (ρ e) (hpres e)).unique (hρ e) (fun z => by rw [h]; exact hρ e' z)
  have hρsurj : ∀ N : Module.End ℂ (Fin 2 → ℂ), (∀ z ∈ Λ, N z ∈ Λ) → ∃ e, ρ e = N := by
    intro N hN
    obtain ⟨f, hf, -⟩ := hT11.1 N hN
    exact ⟨f, lift_unique hΦ (fun z => by rw [hρ, hf])⟩
  -- elements of the centralizer act by scalars
  have hcomm : ∀ e ∈ LeafQM.AV.com q, ∃ c : ℂ, ∀ w, ρ e w = c • w := by
    intro e he
    obtain ⟨c, hc⟩ := commutant (Fl.toLinearMap ∘ₗ ρ e ∘ₗ Fl.symm.toLinearMap) (fun x hx z => by
      have hcm : q.iota ⟨x, hx⟩ * e = e * q.iota ⟨x, hx⟩ := by
        rw [LeafQM.AV.com, Subring.mem_centralizer_iff] at he
        exact he _ ⟨⟨x, hx⟩, rfl⟩
      have h1 : Fl.symm (act x z) = ρ (q.iota ⟨x, hx⟩) (Fl.symm z) := by
        rw [LinearEquiv.symm_apply_eq, hι, LinearEquiv.apply_symm_apply]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, ← Module.End.mul_apply, ← map_mul, ← hcm, map_mul, Module.End.mul_apply, hι])
    refine ⟨c, fun w => ?_⟩
    have := hc (Fl w)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
    rw [← Fl.symm_apply_apply (ρ e w), this, map_smul, LinearEquiv.symm_apply_apply]
  let w0 : Fin 2 → ℂ := Fl.symm v
  have hw0 : w0 ≠ 0 := fun h => hv (by rw [← Fl.apply_symm_apply v]; show Fl w0 = 0; rw [h, map_zero])
  have hcinj : ∀ a b : ℂ, a • w0 = b • w0 → a = b := fun a b h => smul_left_injective ℂ hw0 h
  let c : LeafQM.AV.com q → ℂ := fun e => Fl (ρ e w0) 1
  have hscal : ∀ e : LeafQM.AV.com q, ∀ w, ρ e w = c e • w := by
    intro e w
    obtain ⟨c0, h0⟩ := hcomm e e.2
    have : c e = c0 := by
      show Fl (ρ e w0) 1 = c0
      rw [h0, map_smul, LinearEquiv.apply_symm_apply]
      simp [v]
    rw [this, h0]
  have c_one : c 1 = 1 := hcinj _ _ (by rw [← hscal, OneMemClass.coe_one, map_one, one_smul]; rfl)
  have c_zero : c 0 = 0 := hcinj _ _ (by rw [← hscal, ZeroMemClass.coe_zero, map_zero, zero_smul]; rfl)
  have c_mul : ∀ e e', c (e * e') = c e * c e' := fun e e' => hcinj _ _ (by
    rw [← hscal, MulMemClass.coe_mul, map_mul, Module.End.mul_apply, hscal e', map_smul, hscal e,
      smul_smul, mul_comm])
  have c_add : ∀ e e', c (e + e') = c e + c e' := fun e e' => hcinj _ _ (by
    rw [← hscal, AddMemClass.coe_add, map_add, LinearMap.add_apply, hscal e, hscal e', add_smul])
  have hvO : ∀ e : LeafQM.AV.com q, ∃ x ∈ LeafQM.O, act x v = c e • v := by
    intro e
    have h1 : w0 ∈ Λ := (hΛ w0).2 (by
      show Fl (Fl.symm v) ∈ _
      rw [LinearEquiv.apply_symm_apply, mem_qmOrbit_iff]
      exact ⟨1, LeafQM.O.one_mem, (act_one v).symm⟩)
    have h2 := (hΛ _).1 (hpres e w0 h1)
    rw [hscal, map_smul, LinearEquiv.apply_symm_apply, mem_qmOrbit_iff] at h2
    obtain ⟨x, hx, hxe⟩ := h2
    exact ⟨x, hx, hxe.symm⟩
  choose X hXO hX using hvO
  let F : LeafQM.AV.com q →+* B :=
    { toFun := X
      map_one' := act_inj hv (by rw [hX, act_one, c_one, one_smul])
      map_mul' := fun e e' => act_inj hv (by
        rw [hX, act_mul, hX, act_smul_vec, hX, smul_smul, c_mul, mul_comm])
      map_zero' := act_inj hv (by rw [hX, act_zero, c_zero, zero_smul])
      map_add' := fun e e' => act_inj hv (by rw [hX, act_add, hX, hX, c_add, add_smul]) }
  have hFX : ∀ e, F e = X e := fun e => rfl
  refine ⟨τ, hτ, F, fun e e' h => ?_, fun x => ⟨?_, ?_⟩⟩
  · have h1 : c e • v = c e' • v := by rw [← hX, ← hX]; exact congrArg (fun y => act y v) h
    have h2 : c e = c e' := smul_left_injective ℂ hv h1
    apply Subtype.ext
    apply hρinj
    refine LinearMap.ext fun w => ?_
    rw [hscal e, hscal e', h2]
  · rintro ⟨e, rfl⟩
    exact ⟨hXO e, c e, hX e⟩
  · rintro ⟨hxO, c0, hc0⟩
    let N : Module.End ℂ (Fin 2 → ℂ) := c0 • LinearMap.id
    have hN : ∀ z ∈ Λ, N z ∈ Λ := by
      intro z hz
      have h1 := (hΛ z).1 hz
      rw [mem_qmOrbit_iff] at h1
      obtain ⟨y, hy, hyz⟩ := h1
      apply (hΛ _).2
      rw [mem_qmOrbit_iff]
      refine ⟨y * x, LeafQM.O.mul_mem hy hxO, ?_⟩
      show Fl (c0 • z) = _
      rw [map_smul, hyz, act_mul, hc0, act_smul_vec]
    obtain ⟨e0, he0⟩ := hρsurj N hN
    have he0com : e0 ∈ LeafQM.AV.com q := by
      rw [LeafQM.AV.com, Subring.mem_centralizer_iff]
      rintro _ ⟨a, rfl⟩
      apply hρinj
      rw [map_mul, map_mul, he0]
      refine LinearMap.ext fun w => ?_
      simp [N]
    have hce : c ⟨e0, he0com⟩ = c0 := hcinj _ _ (by rw [← hscal]; show ρ e0 w0 = _; rw [he0]; rfl)
    refine ⟨⟨e0, he0com⟩, act_inj hv ?_⟩
    rw [hFX, hX, hce, hc0]

/-! ## §4 `QMCentralizerCMC` -/

/-- **`QMCentralizerCMC` (added-bundle field `qmCentralizerCMC`) from the textbook fields
`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`.** -/
theorem qmCentralizerCMC_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    HDec.QMSplit.Aut.QMCentralizerCMC := by
  intro A hA q
  obtain ⟨τ, hτ, F, hF, hR⟩ := com_embed hU hG hM A hA q
  exact alg_core hτ F hF hR

/-! ## §5 Toward `YuThm11` (gap-triage A9): generic lemmas -/

/-- Lifting a ring hom through an injective ring hom containing its range. -/
theorem exists_lift {X Y Z : Type} [Ring X] [Ring Y] [Ring Z] (g : X →+* Z) (θ : Y →+* Z)
    (hθ : Function.Injective θ) (h : ∀ x, g x ∈ Set.range θ) : ∃ Ψ : X →+* Y, ∀ x, θ (Ψ x) = g x := by
  let e : Y ≃+* θ.range := RingEquiv.ofBijective θ.rangeRestrict
    ⟨fun a b hab => hθ (congrArg Subtype.val hab), θ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (g.codRestrict θ.range (fun x => h x)), fun x => ?_⟩
  have : θ.rangeRestrict (e.symm (g.codRestrict θ.range (fun x => h x) x)) =
      g.codRestrict θ.range (fun x => h x) x := e.apply_symm_apply _
  exact congrArg Subtype.val this

/-- **`ℚ ⊗_ℤ M ≅ C`** for a ring embedding `Ψ : M → C` into a `ℚ`-algebra whose image spans `C` up to
denominators. -/
theorem end0_equiv {M C : Type} [Ring M] [Ring C] [Algebra ℚ C] (Ψ : M →+* C)
    (hinj : Function.Injective Ψ)
    (hspan : ∀ c : C, ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • c ∈ Set.range Ψ) :
    Nonempty (TensorProduct ℤ ℚ M ≃ₐ[ℚ] C) := by
  let f : M →ₗ[ℤ] C := Ψ.toAddMonoidHom.toIntLinearMap
  have hf : ∀ m, f m = Ψ m := fun m => rfl
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f := by
    refine ⟨fun x => ?_, fun c => ?_, fun {x₁ x₂} h => ⟨1, by simpa using hinj h⟩⟩
    · have hx : (x : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero x
      have hxq : ((x : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hx
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ] at hab
        exact smul_right_injective C hxq hab
      · intro c
        refine ⟨(((x : ℤ) : ℚ)⁻¹) • c, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_inv_cancel₀ hxq, one_smul]
    · obtain ⟨n, hn, m, hm⟩ := hspan c
      refine ⟨(m, ⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩), ?_⟩
      show ((n : ℤ)) • c = f m
      rw [hf, hm, ← Int.cast_smul_eq_zsmul ℚ]
      simp
  have hbc : IsBaseChange ℚ f := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mp hloc
  let e := hbc.equiv
  have he : ∀ (s : ℚ) (m : M), e (s ⊗ₜ m) = s • Ψ m := fun s m => hbc.equiv_tmul s m
  refine ⟨AlgEquiv.ofLinearEquiv e ?_ ?_⟩
  · show e (1 ⊗ₜ 1) = 1
    rw [he, map_one, one_smul]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
    | tmul s m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, mul_add]
      | tmul t n =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, he, he, he, map_mul, smul_mul_smul_comm]

open HSyn.G0Split.FibreQM in
/-- **The analytic representation, normalized** (from the same inputs as `com_embed`): a ring embedding
`ρ : End(A) → End_ℂ(ℂ²)` with `ρ(ι(a)) = ι(a)` and image exactly the maps preserving
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`. -/
theorem unif_conj (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : LeafQM.AV.QMStr A) :
    ∃ (τ : ℂ) (_ : 0 < τ.im) (ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ)),
      Function.Injective ρ ∧ (∀ a z, ρ (q.iota a) z = act (a : B) z) ∧
      ∀ N : Module.End ℂ (Fin 2 → ℂ),
        (∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1]) ↔ ∃ e, ρ e = N := by
  have hE : UniformizationExistsT35 := AvSplit.Final.h38 hU hM
  have hR : T11aRiemannEnd := ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hU hG)
  have hL : QMLatticeAlgebra :=
    qmLatticeAlgebra_of_free (qmLatticeFree_of qmSkolemNoetherC_proof QMSplit.CNO.qmClassNumberOne_proof)
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ A (RingHom.id ℂ) 2 hA
  haveI := hd
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR A hA Λ Φu hΦ
  obtain ⟨τ, hτ, Fl, hF, hFρ⟩ := hL Λ hlat (ρ.comp q.iota) (fun a z hz => hpres (q.iota a) z hz)
  have hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ FibreQMNorm.qmOrbit ![τ, 1] := by
    intro z
    rw [← FibreQMNorm.qmLattice_eq_orbit hτ.ne', ← hF]
    constructor
    · intro h; exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      have : w = z := Fl.injective he
      rw [← this]; exact hw
  have hT11 := hR A 2 Λ Φu hA hΦ
  have hρinj : Function.Injective ρ := fun e e' h =>
    (hT11.1 (ρ e) (hpres e)).unique (hρ e) (fun z => by rw [h]; exact hρ e' z)
  have hρsurj : ∀ N : Module.End ℂ (Fin 2 → ℂ), (∀ z ∈ Λ, N z ∈ Λ) → ∃ e, ρ e = N := by
    intro N hN
    obtain ⟨f, hf, -⟩ := hT11.1 N hN
    exact ⟨f, lift_unique hΦ (fun z => by rw [hρ, hf])⟩
  let ρ' : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ) :=
    { toFun := fun e => Fl.toLinearMap ∘ₗ ρ e ∘ₗ Fl.symm.toLinearMap
      map_one' := LinearMap.ext fun z => by simp
      map_mul' := fun e e' => LinearMap.ext fun z => by simp [map_mul]
      map_zero' := LinearMap.ext fun z => by simp
      map_add' := fun e e' => LinearMap.ext fun z => by simp [map_add] }
  have hρ' : ∀ e z, ρ' e z = Fl (ρ e (Fl.symm z)) := fun e z => rfl
  refine ⟨τ, hτ, ρ', fun e e' h => hρinj ?_, fun a z => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · refine LinearMap.ext fun w => ?_
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => Fl.symm (T (Fl w))) h
    simpa [hρ'] using this
  · rw [hρ']
    have := hFρ a (Fl.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  · obtain ⟨e, he⟩ := hρsurj (Fl.symm.toLinearMap ∘ₗ N ∘ₗ Fl.toLinearMap) (fun z hz => by
      rw [hΛ]
      simpa using hN _ ((hΛ z).1 hz))
    refine ⟨e, LinearMap.ext fun z => ?_⟩
    rw [hρ', he]
    simp
  · rintro ⟨e, rfl⟩ z hz
    rw [hρ']
    rw [← hΛ]
    apply hpres
    rw [hΛ]
    simpa using hz

/-! ## §6 The lattice algebra of `ℂ²/Λ_τ` -/

/-- `w = ι(i)(τ, 1)ᵀ`. -/
def wvec (τ : ℂ) : Fin 2 → ℂ := act (BPAnalytic.QM.oBasis 1) ![τ, 1]

theorem wvec_eq (τ : ℂ) : wvec τ = ![√2 * τ, -√2] := by
  funext i; fin_cases i <;> simp [wvec, act_apply0, act_apply1, BPAnalytic.QM.oBasis]

theorem vw_li {τ : ℂ} (hτ : τ.im ≠ 0) : LinearIndependent ℂ ![![τ, 1], wvec τ] := by
  have hτ0 : τ ≠ 0 := fun h => hτ (by rw [h, Complex.zero_im])
  have s2 : (√2 : ℂ) ≠ 0 := BPAnalytic.QM.sqrt2_ne_zero
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [wvec_eq] at h0 h1
  have ht : (2 * √2 * τ : ℂ) * t = 0 := by linear_combination h0 - τ * h1
  have ht' : t = 0 := (mul_eq_zero.mp ht).resolve_left (by simp [hτ0, s2])
  refine ⟨?_, ht'⟩
  rw [ht'] at h1; simpa using h1

/-- The `ℂ`-basis `(v, w)` of `ℂ²`. -/
def bvw {τ : ℂ} (hτ : τ.im ≠ 0) : Module.Basis (Fin 2) ℂ (Fin 2 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (vw_li hτ) (by simp)

theorem bvw_zero {τ : ℂ} (hτ : τ.im ≠ 0) : bvw hτ 0 = ![τ, 1] := by
  simp [bvw, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem bvw_one {τ : ℂ} (hτ : τ.im ≠ 0) : bvw hτ 1 = wvec τ := by
  simp [bvw, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem decomp {τ : ℂ} (hτ : τ.im ≠ 0) (u : Fin 2 → ℂ) :
    u = (bvw hτ).repr u 0 • ![τ, 1] + (bvw hτ).repr u 1 • wvec τ := by
  conv_lhs => rw [← (bvw hτ).sum_repr u]
  rw [Fin.sum_univ_two, bvw_zero, bvw_one]

theorem repr_comb {τ : ℂ} (hτ : τ.im ≠ 0) (α β : ℂ) :
    (bvw hτ).repr (α • ![τ, 1] + β • wvec τ) 0 = α ∧ (bvw hτ).repr (α • ![τ, 1] + β • wvec τ) 1 = β := by
  rw [← bvw_zero hτ, ← bvw_one hτ]
  simp [Finsupp.single_apply]

/-- `x ↦ ι(x)v`, `ℚ`-linearly. -/
def actV (v : Fin 2 → ℂ) : B →ₗ[ℚ] (Fin 2 → ℂ) where
  toFun b := act b v
  map_add' a b := act_add a b v
  map_smul' r b := by
    rw [act_smul, RingHom.id_apply, Rat.cast_smul_eq_qsmul]

/-- **If `S_{(τ,1)} = ℚ`, every `ℂ`-linear map preserving `ι(B)(τ, 1)ᵀ` is some `ι(x)`.** With
`N' = N − ι(x)` killing `v` and `N'w = ι(y)v`, `y ≠ 0` would force the `w`-coordinate of `ι(b)v` to be
rational for all `b ∈ B`; that `ℚ`-linear functional has kernel `S_v = ℚ`, so `4 ≤ 1 + 1`. -/
theorem eq_act_of_trivial {τ : ℂ} (hτ : τ.im ≠ 0)
    (hall : ∀ x ∈ S ![τ, 1], x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0)
    (N : Module.End ℂ (Fin 2 → ℂ)) (hN : ∀ x : B, ∃ y : B, N (act x ![τ, 1]) = act y ![τ, 1]) :
    ∃ x : B, ∀ z, N z = act x z := by
  obtain ⟨x, hx⟩ := hN 1
  rw [act_one] at hx
  obtain ⟨y1, hy1⟩ := hN (BPAnalytic.QM.oBasis 1)
  set y := y1 - x * BPAnalytic.QM.oBasis 1 with hydef
  have hNw : N (wvec τ) - act x (wvec τ) = act y ![τ, 1] := by
    rw [hydef, act_sub, act_mul, ← hy1]; rfl
  refine ⟨x, ?_⟩
  by_cases hy : y = 0
  · intro z
    have hw : N (wvec τ) = act x (wvec τ) := by
      rw [hy, act_zero] at hNw; exact sub_eq_zero.mp hNw
    rw [decomp hτ z, map_add, map_smul, map_smul, act_add_vec, act_smul_vec, act_smul_vec, hx, hw]
  · exfalso
    obtain ⟨yi, hyi⟩ : ∃ yi : B, yi * y = 1 :=
      ⟨(QMSplit.CNO.nrd y)⁻¹ • star y, by simpa using QMSplit.CNO.div_mul_cancel' 1 y hy⟩
    let β : B →ₗ[ℚ] ℂ := ((bvw hτ).coord 1).restrictScalars ℚ ∘ₗ actV ![τ, 1]
    have hβ : ∀ b, β b = (bvw hτ).repr (act b ![τ, 1]) 1 := fun b => rfl
    have hβrat : ∀ b, ∃ r : ℚ, β b = r := by
      intro b
      obtain ⟨z, hz⟩ := hN b
      have e1 : N (act b ![τ, 1]) - act x (act b ![τ, 1]) = β b • act y ![τ, 1] := by
        conv_lhs => rw [decomp hτ (act b ![τ, 1])]
        rw [map_add, map_smul, map_smul, act_add_vec, act_smul_vec, act_smul_vec, hx, hβ, ← hNw]
        module
      have e2 : act (yi * (z - x * b)) ![τ, 1] = β b • ![τ, 1] := by
        rw [act_mul, act_sub, act_mul, ← hz, e1, act_smul_vec, ← act_mul, hyi, act_one]
      obtain ⟨h1, h2, h3⟩ := hall _ ⟨β b, e2⟩
      set u := yi * (z - x * b)
      have hu : u = algebraMap ℚ B u.re := by
        ext <;> simp [h1, h2, h3, Algebra.algebraMap_eq_smul_one]
      refine ⟨u.re, ?_⟩
      rw [hu, act_algebraMap] at e2
      have := congrFun e2 1
      simpa using this.symm
    have hker : ∀ b, β b = 0 → b ∈ Submodule.span ℚ {(1 : B)} := by
      intro b hb
      have : act b ![τ, 1] = (bvw hτ).repr (act b ![τ, 1]) 0 • ![τ, 1] := by
        conv_lhs => rw [decomp hτ (act b ![τ, 1])]
        rw [← hβ, hb, zero_smul, add_zero]
      obtain ⟨h1, h2, h3⟩ := hall b ⟨_, this⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨b.re, by ext <;> simp [h1, h2, h3]⟩
    have hr : Module.finrank ℚ (LinearMap.range β) ≤ 1 := by
      have hle : LinearMap.range β ≤ Submodule.span ℚ {(1 : ℂ)} := by
        rintro _ ⟨b, rfl⟩
        obtain ⟨r, hr⟩ := hβrat b
        rw [hr, Submodule.mem_span_singleton]
        exact ⟨r, by simp [Rat.cast_smul_eq_qsmul]⟩
      exact (Submodule.finrank_mono hle).trans ((finrank_span_le_card ({(1 : ℂ)} : Set ℂ)).trans (by simp))
    have hk : Module.finrank ℚ (LinearMap.ker β) ≤ 1 :=
      (Submodule.finrank_mono (fun b hb => hker b hb)).trans ((finrank_span_le_card ({(1 : B)} : Set B)).trans (by simp))
    have := LinearMap.finrank_range_add_finrank_ker β
    rw [QuaternionAlgebra.finrank_eq_four] at this
    omega

end HDec.QMLattice

