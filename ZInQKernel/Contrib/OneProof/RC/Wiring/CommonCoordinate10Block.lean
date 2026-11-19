import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Retract

/-!
# The minimal block model `F --0--> F` and the zero cases of the coordinate

Manuscript `diophantine_zq.tex`, the support triangle of Lemma `ex:arith-common-coordinate`
(tex 4157–4194: "over a field, splitting gives a minimal model"), the class-functional coordinate
of Definition `ex:arith-coordinate` (tex 3877–3892: generic cohomology of dimensions `(1, 1)` in
degrees one and two, and "For a generically acyclic constituent set `u = 0`"), and the minimal
models of tex 4636–4640 ("a minimal model obtained by cancelling unit entries; its ranks are the
dimensions of the cohomology").

* `minBlock F`: the block complex with `m₀ = m₁ = m₂ = 0` and zero differentials, the minimal
  model `F --0--> F` in degrees one and two (`minBlock_ddL`, `minBlock_toGCx_d`: its
  differentials vanish).
* `minBlockIdxEquiv`, `minBlockModelEquiv`, `minBlockModelEquiv_comm`: for ranks `1, 1` in
  degrees one and two and `0` elsewhere, `minBlock F` is degreewise isomorphic to the matrix
  complex `matCx rank dC`, compatibly with the differentials when `dC = 0`
  (`minBlockModelEquiv_apply`: the isomorphism reindexes coordinates).
* `exists_minBlock_retract`: over a field, a complex whose cohomology has dimension one in
  degrees one and two and vanishes otherwise has a normalized graded deformation retract onto
  `minBlock F` (the minimal graded model of `exists_minimalGradedModel_field_cohomology`,
  transported by `retractOfModelEquiv`).
* `kmCoord_minBlock`: on `minBlock F` every vector is a cycle and every functional is closed
  (`minBlock_toFour_cycle`, `minBlock_toFour_closed`), and the Knudsen–Mumford coordinate of
  `[z] ⊗ [λ]` is `−z_H λ_H` (Elliot's block computation `kmCoord_block`, tex 5577–5595).
* `kmCoord_eq_zero_of_indep_z`, `kmCoord_eq_zero_of_indep_lam`: if two cycles are linearly
  independent modulo boundaries (two closed functionals modulo `im (d²)ᵀ`), every
  Knudsen–Mumford coordinate vanishes.
* `singularBlockFull`, `kmStep_zero`: the pre-cancellation complex made of the two-place
  singular block alone, and the zero case `KmStep Fr q a zq zqi 0 0` of a step.
* Non-vacuity: `minBlockCohomologyEquiv` (`Hⁿ(minBlock F) ≅ F^{minRank n}`) and
  `nonempty_minBlock_retract_self` (`minBlock F` meets the hypotheses of
  `exists_minBlock_retract`); `zeroFour_indep_z`, `zeroFour_indep_lam` (two independent classes
  and functionals exist); `kmCoord_minBlock_example` (the coordinate on `minBlock ℚ` at
  `z = λ = 1` is `−1`); `kmStep_zero_example` (the singular block can be invertible).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)

/-! ### The minimal block model -/

section MinBlock

/-- **The minimal block model** `F --0--> F` in degrees one and two (tex 4157–4194, 4636–4640:
over a field, splitting gives a minimal model; the block form of tex 5522–5530): the block
complex with `m₀ = m₁ = m₂ = 0`, so `D¹ = H₁ ≅ F`, `D² = H₂ ≅ F`, `D⁰ = D³ = 0`, and all three
differentials zero. Kind: definition. -/
def minBlock (F : Type) [Field F] : BlockComplex F where
  m0 := 0
  m1 := 0
  m2 := 0
  d0 := 0
  d1 := 0
  d2 := 0
  d1_d0 := Matrix.zero_mul 0
  d2_d1 := Matrix.zero_mul 0

variable {F : Type} [Field F]

/-- The differentials of `minBlock F` vanish in every degree. (tex 4157–4194, 4636–4640)
Kind: PROVED. -/
theorem minBlock_ddL (i : ℤ) (x : (minBlock F).idx i → F) : (minBlock F).ddL i x = 0 := by
  match i with
  | 0 =>
    have h : ∀ y : Fin 0 → F, (0 : Matrix (Fin 0 ⊕ Unit ⊕ Fin 0) (Fin 0) F) *ᵥ y = 0 :=
      fun y => Matrix.zero_mulVec y
    exact h x
  | 1 =>
    have h : ∀ y : Fin 0 ⊕ Unit ⊕ Fin 0 → F,
        (0 : Matrix (Fin 0 ⊕ Unit ⊕ Fin 0) (Fin 0 ⊕ Unit ⊕ Fin 0) F) *ᵥ y = 0 :=
      fun y => Matrix.zero_mulVec y
    exact h x
  | 2 =>
    have h : ∀ y : Fin 0 ⊕ Unit ⊕ Fin 0 → F,
        (0 : Matrix (Fin 0) (Fin 0 ⊕ Unit ⊕ Fin 0) F) *ᵥ y = 0 :=
      fun y => Matrix.zero_mulVec y
    exact h x
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n => rfl

/-- The differentials of the complex `(minBlock F).toGCx` vanish. (tex 4157–4194, 4636–4640)
Kind: PROVED. -/
theorem minBlock_toGCx_d (a b : ℤ) (h : a + 1 = b) (x : (minBlock F).toGCx.X a) :
    (minBlock F).toGCx.d a b h x = 0 := by
  subst h
  exact minBlock_ddL a x

/-- **The bases of `minBlock F` against prescribed ranks** (tex 3877–3892, 4636–4640): for ranks
`1` in degrees one and two and `0` elsewhere, the basis index of `minBlock F` in degree `n` is
equivalent to `Fin (rank n)`. Kind: definition. -/
def minBlockIdxEquiv (rank : ℤ → ℕ) (h1 : rank 1 = 1) (h2 : rank 2 = 1)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → rank n = 0) : (n : ℤ) → (minBlock F).idx n ≃ Fin (rank n)
  | 0 => (finCongr (h0 0 (by omega) (by omega)).symm : Fin 0 ≃ Fin (rank 0))
  | 1 => (Fintype.equivOfCardEq (by simp [h1]) : Fin 0 ⊕ Unit ⊕ Fin 0 ≃ Fin (rank 1))
  | 2 => (Fintype.equivOfCardEq (by simp [h2]) : Fin 0 ⊕ Unit ⊕ Fin 0 ≃ Fin (rank 2))
  | 3 => (finCongr (h0 3 (by omega) (by omega)).symm : Fin 0 ≃ Fin (rank 3))
  | Int.ofNat (n + 4) =>
    (Equiv.equivOfIsEmpty Empty (Fin 0)).trans (finCongr (h0 (Int.ofNat (n + 4))
      (by intro h; injection h with h; omega) (by intro h; injection h with h; omega)).symm)
  | Int.negSucc n =>
    (Equiv.equivOfIsEmpty Empty (Fin 0)).trans
      (finCongr (h0 (Int.negSucc n) (by intro h; cases h) (by intro h; cases h)).symm)

/-- **The degreewise isomorphism of `minBlock F` with a matrix model** of ranks `1, 1` in degrees
one and two and `0` elsewhere (tex 4423–4437, 4636–4640): reindexing the coordinates along
`minBlockIdxEquiv`. Kind: definition. -/
def minBlockModelEquiv (rank : ℤ → ℕ) (h1 : rank 1 = 1) (h2 : rank 2 = 1)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → rank n = 0)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) F)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0) (n : ℤ) :
    (minBlock F).toGCx.X n ≃ₗ[F] (matCx rank dC hsq).X n :=
  LinearEquiv.funCongrLeft F F (minBlockIdxEquiv rank h1 h2 h0 n).symm

/-- `minBlockModelEquiv` reindexes coordinates: `y ↦ y ∘ (minBlockIdxEquiv n)⁻¹`.
(tex 4423–4437, 4636–4640) Kind: PROVED (definitional). -/
theorem minBlockModelEquiv_apply (rank : ℤ → ℕ) (h1 : rank 1 = 1) (h2 : rank 2 = 1)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → rank n = 0)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) F)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0) (n : ℤ)
    (y : (minBlock F).idx n → F) :
    minBlockModelEquiv rank h1 h2 h0 dC hsq n y = y ∘ (minBlockIdxEquiv rank h1 h2 h0 n).symm :=
  rfl

/-- **For a zero model differential the degreewise isomorphism commutes with the differentials**
(both sides vanish). (tex 4423–4437, 4636–4640) Kind: PROVED. -/
theorem minBlockModelEquiv_comm (rank : ℤ → ℕ) (h1 : rank 1 = 1) (h2 : rank 2 = 1)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → rank n = 0)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) F)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0)
    (hdC : ∀ a b (h : a + 1 = b), dC a b h = 0) (a b : ℤ) (h : a + 1 = b)
    (y : (minBlock F).toGCx.X a) :
    (matCx rank dC hsq).d a b h (minBlockModelEquiv rank h1 h2 h0 dC hsq a y) =
      minBlockModelEquiv rank h1 h2 h0 dC hsq b ((minBlock F).toGCx.d a b h y) := by
  have hd0 : (matCx rank dC hsq).d a b h = 0 := by
    change Matrix.toLin' (dC a b h) = 0
    rw [hdC, map_zero]
  rw [minBlock_toGCx_d, map_zero, hd0, LinearMap.zero_apply]

/-- **A complex over a field with cohomology of dimensions `(1, 1)` in degrees one and two
retracts onto the minimal block model** (Lemma `ex:arith-common-coordinate`, tex 4157–4194:
"over a field, splitting gives a minimal model"; Definition `ex:arith-coordinate`,
tex 3877–3892; Lemma `ex:limits-inner-limit`, tex 4391–4451; tex 4636–4640): if `Hⁿ(X)` is
finite-dimensional, of dimension one for `n = 1, 2` and zero otherwise, then `X` has a
normalized graded deformation retract onto `minBlock F`. The minimal graded model of
`exists_minimalGradedModel_field_cohomology` has these ranks and zero differential, and
`retractOfModelEquiv` transports it along `minBlockModelEquiv`. Kind: PROVED. -/
theorem exists_minBlock_retract (X : GCx F)
    (hfin : ∀ n, Module.Finite F (fieldCohomologyAt X n))
    (h1 : Module.finrank F (fieldCohomologyAt X 1) = 1)
    (h2 : Module.finrank F (fieldCohomologyAt X 2) = 1)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → Module.finrank F (fieldCohomologyAt X n) = 0) :
    Nonempty (GRetract X (minBlock F).toGCx) := by
  obtain ⟨R, hR, hd⟩ := exists_minimalGradedModel_field_cohomology X hfin
  have r1 : R.rank 1 = 1 := (hR 1).trans h1
  have r2 : R.rank 2 = 1 := (hR 2).trans h2
  have r0 : ∀ n, n ≠ 1 → n ≠ 2 → R.rank n = 0 := fun n hn1 hn2 => (hR n).trans (h0 n hn1 hn2)
  exact ⟨retractOfModelEquiv R.retract (minBlockModelEquiv R.rank r1 r2 r0 R.dC R.dC_sq)
    (minBlockModelEquiv_comm R.rank r1 r2 r0 R.dC R.dC_sq hd)⟩

/-- Every vector of degree one of the minimal block model is a cycle. (tex 3877–3892)
Kind: PROVED. -/
theorem minBlock_toFour_cycle (z : Fin (minBlock F).m0 ⊕ Unit ⊕ Fin (minBlock F).m1 → F) :
    (minBlock F).toFour.d1 *ᵥ z = 0 :=
  Matrix.zero_mulVec z

/-- Every functional on degree two of the minimal block model is closed. (tex 3877–3892)
Kind: PROVED. -/
theorem minBlock_toFour_closed (μ : Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2 → F) :
    μ ᵥ* (minBlock F).toFour.d1 = 0 :=
  Matrix.vecMul_zero μ

/-- **The coordinate on the minimal block model** (tex 3877–3892, 5577–5595): the
Knudsen–Mumford coordinate of `[z] ⊗ [λ]` on `minBlock F` is `−z_H λ_H`. There are no Smith
disks, the remaining map `H₁ → H₂` is zero, and `α = z_H`, `β = λ_H` (`kmCoord_block`; the sign
is the convention `kmCoord = −τ`). Kind: PROVED. -/
theorem kmCoord_minBlock (z : Fin (minBlock F).m0 ⊕ Unit ⊕ Fin (minBlock F).m1 → F)
    (μ : Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2 → F)
    (hz : (minBlock F).toFour.d1 *ᵥ z = 0) (hμ : μ ᵥ* (minBlock F).toFour.d1 = 0) :
    kmCoord (minBlock F).toFour z μ hz hμ
        (σBlock (minBlock F).m0 (minBlock F).m1 (minBlock F).m2) =
      -(z (Sum.inr (Sum.inl ())) * μ (Sum.inr (Sum.inl ()))) := by
  have e0 : IsEmpty (Fin (minBlock F).m0) := inferInstanceAs (IsEmpty (Fin 0))
  have e1 : IsEmpty (Fin (minBlock F).m1) := inferInstanceAs (IsEmpty (Fin 0))
  have e2 : IsEmpty (Fin (minBlock F).m2) := inferInstanceAs (IsEmpty (Fin 0))
  have h0 : IsUnit (minBlock F).A0.det := by
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  have h1 : IsUnit (minBlock F).A1.det := by
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  have h2 : IsUnit (minBlock F).A2.det := by
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  refine (kmCoord_block (D := minBlock F) z μ hz hμ h0 h1 h2).trans ?_
  have hR : (minBlock F).hRem = 0 := by
    simp [BlockComplex.hRem, minBlock, dotProduct]
  have hα : (minBlock F).alphaB z = z (Sum.inr (Sum.inl ())) := by
    simp [BlockComplex.alphaB, dotProduct]
  have hβ : (minBlock F).betaB μ = μ (Sum.inr (Sum.inl ())) := by
    simp [BlockComplex.betaB, dotProduct]
  simp only [hR, ite_true, hα, hβ, Matrix.det_isEmpty]
  ring

end MinBlock

/-! ### The coordinate vanishes off the rank-one pattern -/

section ZeroCoord

variable {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  (C : FourCx K ι0 ι1 ι2 ι3)

/-- **Two independent classes make the coordinate vanish** (tex 3877–3892: the coordinate of
`[z] ⊗ [λ]` in `det⁻¹ C ≅ H¹ ⊗ (H²)^*` needs `dim H¹ = 1`; tex 5612–5617, the generic patterns):
if two cycles `z₁, z₂` are linearly independent modulo the boundaries `im d⁰`, then
`kmCoord C z λ = 0` for every cycle `z` and closed functional `λ`. One of `z₁, z₂` lies outside
`K z + im d⁰` (else `s z₁ − t z₂ ∈ im d⁰` forces `s = t = 0` and `z₁ ∈ im d⁰`), so the augmented
complex has no contraction (`not_contraction_of_independent_z`). Kind: PROVED. -/
theorem kmCoord_eq_zero_of_indep_z {z₁ z₂ : ι1 → K} (h₁ : C.d1 *ᵥ z₁ = 0)
    (h₂ : C.d1 *ᵥ z₂ = 0)
    (hind : ∀ (a b : K) (w : ι0 → K), a • z₁ + b • z₂ = C.d0 *ᵥ w → a = 0 ∧ b = 0)
    {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) : kmCoord C z lam hz hlam σ = 0 := by
  apply kmCoord_eq_zero_of_not C σ hz hlam
  by_cases hA : ∃ (t : K) (w : ι0 → K), z₁ = t • z + C.d0 *ᵥ w
  · by_cases hB : ∃ (s : K) (w : ι0 → K), z₂ = s • z + C.d0 *ᵥ w
    · exfalso
      obtain ⟨t, w, hw⟩ := hA
      obtain ⟨s, w', hw'⟩ := hB
      have key : s • z₁ + (-t) • z₂ = C.d0 *ᵥ (s • w - t • w') := by
        rw [hw, hw', mulVec_sub, mulVec_smul, mulVec_smul]
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      have ht : t = 0 := neg_eq_zero.mp (hind s (-t) _ key).2
      have hz₁ : (1 : K) • z₁ + (0 : K) • z₂ = C.d0 *ᵥ w := by
        rw [one_smul, zero_smul, add_zero, hw, ht, zero_smul, zero_add]
      exact one_ne_zero (hind 1 0 w hz₁).1
    · exact not_contraction_of_independent_z C hz hlam h₂ (fun s w h => hB ⟨s, w, h⟩)
  · exact not_contraction_of_independent_z C hz hlam h₁ (fun t w h => hA ⟨t, w, h⟩)

/-- **Two independent closed functionals make the coordinate vanish** (tex 3877–3892, 5612–5617;
dual to `kmCoord_eq_zero_of_indep_z`): if two closed functionals `λ₁, λ₂` are linearly
independent modulo `im (d²)ᵀ`, then `kmCoord C z λ = 0` for every cycle `z` and closed
functional `λ` (`not_contraction_of_independent_lam`). Kind: PROVED. -/
theorem kmCoord_eq_zero_of_indep_lam {lam₁ lam₂ : ι2 → K} (h₁ : lam₁ ᵥ* C.d1 = 0)
    (h₂ : lam₂ ᵥ* C.d1 = 0)
    (hind : ∀ (a b : K) (μ : ι3 → K), a • lam₁ + b • lam₂ = μ ᵥ* C.d2 → a = 0 ∧ b = 0)
    {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) : kmCoord C z lam hz hlam σ = 0 := by
  apply kmCoord_eq_zero_of_not C σ hz hlam
  by_cases hA : ∃ (t : K) (μ : ι3 → K), lam₁ = t • lam + μ ᵥ* C.d2
  · by_cases hB : ∃ (s : K) (μ : ι3 → K), lam₂ = s • lam + μ ᵥ* C.d2
    · exfalso
      obtain ⟨t, μ, hμ⟩ := hA
      obtain ⟨s, μ', hμ'⟩ := hB
      have key : s • lam₁ + (-t) • lam₂ = (s • μ - t • μ') ᵥ* C.d2 := by
        rw [hμ, hμ', sub_vecMul, smul_vecMul, smul_vecMul]
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      have ht : t = 0 := neg_eq_zero.mp (hind s (-t) _ key).2
      have hl₁ : (1 : K) • lam₁ + (0 : K) • lam₂ = μ ᵥ* C.d2 := by
        rw [one_smul, zero_smul, add_zero, hμ, ht, zero_smul, zero_add]
      exact one_ne_zero (hind 1 0 μ hl₁).1
    · exact not_contraction_of_independent_lam C hz hlam h₂ (fun s μ h => hB ⟨s, μ, h⟩)
  · exact not_contraction_of_independent_lam C hz hlam h₁ (fun t μ h => hA ⟨t, μ, h⟩)

end ZeroCoord

/-! ### The zero case of a step -/

section StepZero

variable {K : Type} [Field K]

/-- **The pre-cancellation complex of the singular block alone** (tex 5398–5424, 4178–4184):
`m₀ = m₁ = m₂ = 0`, new summands `N = Fin 2 ⊕ Fin 2`, and all blocks zero except the two-place
singular block `B = diag(z Fr_q − q, z⁻¹ Fr_q − q)` (`twoPlaceBlock`). Kind: definition. -/
def singularBlockFull (Fr : Matrix (Fin 2) (Fin 2) K) (q zq zqi : K) : FullPreComplex K where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Fin 2 ⊕ Fin 2
  c0 := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := twoPlaceBlock Fr q zq zqi
  U := 0
  V := 0
  c1_c0 := by
    ext _ j
    exact j.elim0
  c2_c1 := by
    ext i _
    exact i.elim0

/-- **The zero case of a step of the support triangle** (tex 4157–4194, 5398–5424): if the
two-place singular block is invertible, `singularBlockFull` with zero cycles and zero
functionals is a torsion-level step with `u_R = u_P = 0` (`kmCoord_zero_z`). Kind: PROVED. -/
theorem kmStep_zero (Fr : Matrix (Fin 2) (Fin 2) K) (q a zq zqi : K)
    (hB : IsUnit (twoPlaceBlock Fr q zq zqi).det) : KmStep Fr q a zq zqi 0 0 :=
  ⟨singularBlockFull Fr q zq zqi, hB, ⟨Equiv.refl _, rfl⟩, 0, 0, mulVec_zero _, zero_vecMul _,
    0, 0, mulVec_zero _, zero_vecMul _, (smul_zero _).symm, (smul_zero _).symm,
    (kmCoord_zero_z _ _ _ _).symm, (kmCoord_zero_z _ _ _ _).symm⟩

end StepZero

/-! ### Non-vacuity -/

section NonVacuity

variable {F : Type} [Field F]

/-- The ranks `1` in degrees one and two and `0` elsewhere (tex 3877–3892: dimensions `(1, 1)`
in degrees one and two, zero otherwise). Kind: definition. -/
def minRank (n : ℤ) : ℕ := if n = 1 ∨ n = 2 then 1 else 0

/-- `minRank 1 = 1`. (tex 3877–3892) Kind: PROVED. -/
theorem minRank_one : minRank 1 = 1 := by simp [minRank]

/-- `minRank 2 = 1`. (tex 3877–3892) Kind: PROVED. -/
theorem minRank_two : minRank 2 = 1 := by simp [minRank]

/-- `minRank n = 0` outside degrees one and two. (tex 3877–3892) Kind: PROVED. -/
theorem minRank_zero (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : minRank n = 0 := by
  simp [minRank, h1, h2]

/-- The subquotient `ker g / im f` of two zero maps is the middle module.
(tex 4157–4194, 4636–4640) Kind: definition. -/
def subquotientEquivOfZero {k V W Z : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup Z] [Module k Z] (f : V →ₗ[k] W)
    (g : W →ₗ[k] Z) (hf : f = 0) (hg : g = 0) : subquotientOf f g ≃ₗ[k] W :=
  (Submodule.quotEquivOfEqBot _ (by
      rw [hf, LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype])).trans
    (LinearEquiv.ofTop _ (by rw [hg, LinearMap.ker_zero]))

/-- **The cohomology of the minimal block model** (tex 4157–4194, 4636–4640): its differentials
vanish, so `Hⁿ(minBlock F) ≅ F^{minRank n}`. Kind: definition. -/
def minBlockCohomologyEquiv (n : ℤ) :
    fieldCohomologyAt (minBlock F).toGCx n ≃ₗ[F] (Fin (minRank n) → F) :=
  (subquotientEquivOfZero _ _ (LinearMap.ext (minBlock_toGCx_d _ _ _))
      (LinearMap.ext (minBlock_toGCx_d _ _ _))).trans
    (LinearEquiv.funCongrLeft F F
      (minBlockIdxEquiv minRank minRank_one minRank_two minRank_zero n).symm)

/-- The cohomology of the minimal block model is finite-dimensional in every degree.
(tex 4157–4194, 4636–4640) Kind: PROVED. -/
theorem minBlock_cohomology_finite (n : ℤ) :
    Module.Finite F (fieldCohomologyAt (minBlock F).toGCx n) :=
  Module.Finite.equiv (minBlockCohomologyEquiv n).symm

/-- `dim Hⁿ(minBlock F) = minRank n`. (tex 3877–3892, 4636–4640) Kind: PROVED. -/
theorem minBlock_finrank_cohomology (n : ℤ) :
    Module.finrank F (fieldCohomologyAt (minBlock F).toGCx n) = minRank n :=
  (minBlockCohomologyEquiv n).finrank_eq.trans (Module.finrank_fin_fun F)

/-- **Non-vacuity of `exists_minBlock_retract`** (tex 4157–4194, 3877–3892): the minimal block
model itself has cohomology of dimensions `(1, 1)` in degrees one and two and zero otherwise,
so the theorem applies to it. Kind: PROVED. -/
theorem nonempty_minBlock_retract_self :
    Nonempty (GRetract (minBlock F).toGCx (minBlock F).toGCx) :=
  exists_minBlock_retract _ minBlock_cohomology_finite
    ((minBlock_finrank_cohomology 1).trans minRank_one)
    ((minBlock_finrank_cohomology 2).trans minRank_two)
    (fun n h1 h2 => (minBlock_finrank_cohomology n).trans (minRank_zero n h1 h2))

/-- The four-term complex `0 → F² --0--> F² → 0` in degrees one and two (tex 3877–3892).
Kind: definition. -/
def zeroFour (F : Type) [Field F] : FourCx F Empty (Fin 2) (Fin 2) Empty where
  d0 := 0
  d1 := 0
  d2 := 0
  d10 := Matrix.zero_mul 0
  d21 := Matrix.zero_mul 0

/-- **Non-vacuity of `kmCoord_eq_zero_of_indep_z`** (tex 3877–3892): the two basis cycles of
`zeroFour F` are linearly independent modulo boundaries. Kind: PROVED. -/
theorem zeroFour_indep_z (a b : F) (w : Empty → F)
    (h : a • (Pi.single 0 1 : Fin 2 → F) + b • Pi.single 1 1 = (zeroFour F).d0 *ᵥ w) :
    a = 0 ∧ b = 0 := by
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  simp [zeroFour] at e0 e1
  exact ⟨e0, e1⟩

/-- **Non-vacuity of `kmCoord_eq_zero_of_indep_lam`** (tex 3877–3892): the two basis functionals
of `zeroFour F` are linearly independent modulo `im (d²)ᵀ`. Kind: PROVED. -/
theorem zeroFour_indep_lam (a b : F) (μ : Empty → F)
    (h : a • (Pi.single 0 1 : Fin 2 → F) + b • Pi.single 1 1 = μ ᵥ* (zeroFour F).d2) :
    a = 0 ∧ b = 0 := by
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  simp [zeroFour] at e0 e1
  exact ⟨e0, e1⟩

/-- **The coordinate on the minimal block model is not identically zero** (tex 3877–3892):
at `z = λ = 1` over `ℚ` it is `−1`. Kind: PROVED. -/
theorem kmCoord_minBlock_example :
    kmCoord (minBlock ℚ).toFour 1 1 (minBlock_toFour_cycle 1) (minBlock_toFour_closed 1)
      (σBlock (minBlock ℚ).m0 (minBlock ℚ).m1 (minBlock ℚ).m2) = -1 := by
  rw [kmCoord_minBlock]
  simp

/-- **Non-vacuity of `kmStep_zero`** (tex 4178–4184, 5398–5424): for `Fr = 1`, `q = 1`,
`z = z⁻¹ = 2` the two-place singular block has determinant one (`exB_det`). Kind: PROVED. -/
theorem kmStep_zero_example : KmStep (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 2 0 0 :=
  kmStep_zero 1 1 2 2 2 (by
    change IsUnit exB.det
    rw [exB_det]
    exact isUnit_one)

end NonVacuity

end ZInQ.Manuscript.RC.Wiring
