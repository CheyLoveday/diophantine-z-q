import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Step

/-!
# Non-vacuity of the support-triangle step, with nonzero coordinates

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194):

> Let `i : C_P → C_R` be the primitive-to-relaxed map […] The actual norm identity is
> `z_R = e_q i(z_P)`, with its retained boundary. […] Consequently `λ_R ∘ i = e_q λ_P`. […]
> The two quotient determinants satisfy `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q) = q⁴ l_q`.
> In the original integral determinant bases, the support triangle therefore gives
> `l_q u_rel = e_q² ε_q u_prim` (4.7).

This file gives an explicit `SupportTriangle ℚ` (`exS`) that satisfies the three arithmetic
hypotheses of `SupportTriangle.kmStep_of_supportTriangle` and whose step coordinates are both
nonzero. The Frobenius data are `Fr = 1`, `q = q⁻¹ = 1`, `a = tr Fr = 2` and `z = z⁻¹ = 2`, so
that `e_q = a − z − z⁻¹ = −2` and `l_q = 1`:

* the primitive complex `C_P` is the block complex `D = exFull.cancel exFull_hB` (`F --0--> F`
  in degrees one and two, all Smith blocks empty), with its identity retract;
* the quotient `Q` is the singular disk `N --B--> N` of `exFull` in degrees one and two
  (`N = Fin 2 ⊕ Fin 2`, `B = exB` the two-place block `diag(z Fr − q, z⁻¹ Fr − q)`,
  `det B = 1`), zero in the other degrees, with the standard bases of `Q¹, Q²`;
* the relaxed complex is the direct sum `C_R = C_P ⊕ Q` (`triCx` with zero off-diagonal map),
  and `i : C_P → C_R` is its split inclusion `triIncl`; the quotient model is the quotient
  complex itself with the identity retract (`Q' = Q`, `R_Q = 1`);
* the cycles are `z_P = 1` and `z_R = e_q i(z_P)`, the functionals are `λ_P = ⟨1, ·⟩` and
  `λ_R = e_q λ_P ∘ pr₁`; `λ_R` is closed because it reads only the `C_P`-component of
  `d¹_R (x, y) = (d¹_D x + 0, B y)`, and `d¹_D = 0`.

Results (PROVED): the hypotheses `exS_hBe` (identity relabelling), `exS_hzR` (retained boundary
`b = 0`), `exS_hlamR` and the unit condition `exS_hl` (`l_q = 1`); **`exS_kmStep`**, the step
from `kmStep_of_supportTriangle`; its (4.7) `exS_h47`; the coordinates `exS_primCoord`
(`u_prim = −1`, from `exFull_uP`) and `exS_relCoord` (`u_rel = −4`, from (4.7)); and
**`supportTriangle_nonvacuous`**.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)

/-! ### The objects of the example -/

/-- **The primitive block complex** `D` of the example (tex 5398–5425): the cancellation of
`exFull`, i.e. `F --0--> F` in degrees one and two (`m₀ = m₁ = m₂ = 0`). Kind: definition. -/
abbrev exSD : BlockComplex ℚ := exFull.cancel exFull_hB

/-- The differential `d¹ = P − Q B⁻¹ T` of the primitive block complex vanishes.
(tex 5424–5425) Kind: PROVED. -/
theorem exSD_d1 : exSD.d1 = 0 := by
  change (0 : Matrix exFull.D2 exFull.D1 ℚ) - (0 : Matrix exFull.D2 exFull.N ℚ) * exFull.B⁻¹ *
    (0 : Matrix exFull.N exFull.D1 ℚ) = 0
  simp

/-- **The local quotient** `Q` of the example (tex 5398–5403, 5420–5424, 4178–4182): the
singular disk `N --B--> N` of `exFull` in degrees one and two, with `N = Fin 2 ⊕ Fin 2` and
`B = exB` the two-place block for `Fr = 1`, `q = 1`, `z = z⁻¹ = 2`; zero in the other degrees.
Kind: definition. -/
abbrev exSQ : GCx ℚ := exFull.disk

/-- The quotient vanishes outside degrees one and two. (tex 5398–5403) Kind: PROVED. -/
theorem exSQ_subsingleton (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : Subsingleton (exSQ.X n) := by
  have := exFull.isEmpty_kidx n h1 h2
  change Subsingleton (exFull.kidx n → ℚ)
  infer_instance

/-- **The relaxed complex** of the example, the direct sum `C_R = C_P ⊕ Q`: the triangular
extension with zero off-diagonal map. (tex 5398–5403) Kind: definition. -/
abbrev exSCR : GCx ℚ :=
  triCx exSD.toGCx exSQ (zeroOffDiag exSD.toGCx exSQ) (zeroOffDiag_sq exSD.toGCx exSQ)

/-- **The primitive-to-relaxed map** `i : C_P → C_R`, `x ↦ (x, 0)`, a split inclusion with
complement `0 ⊕ Q`. (tex 4160, 5398–5403) Kind: definition. -/
abbrev exSE : SplitInclusion exSD.toGCx exSCR :=
  triIncl exSD.toGCx exSQ (zeroOffDiag exSD.toGCx exSQ) (zeroOffDiag_sq exSD.toGCx exSQ)

/-- The complement of `i` vanishes outside degrees one and two. (tex 5398–5424)
Kind: PROVED. -/
theorem exSE_hQ (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : exSE.Qc n = ⊥ :=
  triIncl_Qc_eq_bot _ _ _ _ n (exSQ_subsingleton n h1 h2)

/-- The standard basis of `Q¹ = F^N`. (tex 5398–5424) Kind: definition. -/
def exSb1 : Basis (Fin 2 ⊕ Fin 2) ℚ (exSQ.X 1) := Pi.basisFun ℚ (Fin 2 ⊕ Fin 2)

/-- The standard basis of `Q² = F^N`. (tex 5398–5424) Kind: definition. -/
def exSb2 : Basis (Fin 2 ⊕ Fin 2) ℚ (exSQ.X 2) := Pi.basisFun ℚ (Fin 2 ⊕ Fin 2)

/-- **The primitive cycle** `z_P = 1` on `D¹ = F`. (tex 4166–4170, 3877–3892)
Kind: definition. -/
def exSzP : exSD.toGCx.X 1 := (1 : Fin exSD.m0 ⊕ Unit ⊕ Fin exSD.m1 → ℚ)

/-- `d z_P = 0`. (tex 4166–4170) Kind: PROVED. -/
theorem exSzP_cycle : exSD.toGCx.d 1 2 rfl exSzP = 0 :=
  exFull_hzP

/-- **The primitive functional** `λ_P = ⟨1, ·⟩` on `D² = F`. (tex 4166–4175, 3877–3892)
Kind: definition. -/
def exSlamP : exSD.toGCx.X 2 →ₗ[ℚ] ℚ where
  toFun v := (1 : Fin exSD.m1 ⊕ Unit ⊕ Fin exSD.m2 → ℚ) ⬝ᵥ v
  map_add' v w := dotProduct_add (1 : Fin exSD.m1 ⊕ Unit ⊕ Fin exSD.m2 → ℚ) v w
  map_smul' c v := dotProduct_smul c (1 : Fin exSD.m1 ⊕ Unit ⊕ Fin exSD.m2 → ℚ) v

/-- `λ_P ∘ d = 0`, since `d¹_D = 0`. (tex 4166–4175) Kind: PROVED. -/
theorem exSlamP_closed : exSlamP ∘ₗ exSD.toGCx.d 1 2 rfl = 0 := by
  apply LinearMap.ext
  intro (v : Fin exSD.m0 ⊕ Unit ⊕ Fin exSD.m1 → ℚ)
  change (1 : Fin exSD.m1 ⊕ Unit ⊕ Fin exSD.m2 → ℚ) ⬝ᵥ (exSD.d1 *ᵥ v) = 0
  rw [exSD_d1, zero_mulVec, dotProduct_zero]

/-- **The relaxed cycle** `z_R = e_q i(z_P)` with `e_q = a − z − z⁻¹ = −2`: the norm identity
with zero retained boundary. (tex 4158, 4169–4170) Kind: definition. -/
def exSzR : exSCR.X 1 :=
  pointFactor (2 : ℚ) 2 2 • exSE.i.f 1 1 rfl exSzP

/-- `d z_R = 0`. (tex 4169–4170) Kind: PROVED. -/
theorem exSzR_cycle : exSCR.d 1 2 rfl exSzR = 0 := by
  unfold exSzR
  rw [map_smul, ← exSE.i_d 1 2 rfl exSzP, exSzP_cycle, map_zero, smul_zero]

/-- **The relaxed functional** `λ_R = e_q λ_P ∘ pr₁` on `C²_R = D² × Q²`. (tex 4173–4175)
Kind: definition. -/
def exSlamR : exSCR.X 2 →ₗ[ℚ] ℚ :=
  pointFactor (2 : ℚ) 2 2 • (exSlamP ∘ₗ LinearMap.fst ℚ (exSD.toGCx.X 2) (exSQ.X 2))

/-- `λ_R ∘ d = 0`: `λ_R` reads only the `D`-component of `d¹_R (x, y) = (d¹_D x + 0, B y)`, and
`d¹_D = 0`. (tex 4173–4175, 5398–5403) Kind: PROVED. -/
theorem exSlamR_closed : exSlamR ∘ₗ exSCR.d 1 2 rfl = 0 := by
  apply LinearMap.ext
  intro (x : (Fin exSD.m0 ⊕ Unit ⊕ Fin exSD.m1 → ℚ) × exSQ.X 1)
  change pointFactor (2 : ℚ) 2 2 • ((1 : Fin exSD.m1 ⊕ Unit ⊕ Fin exSD.m2 → ℚ) ⬝ᵥ
    (exSD.d1 *ᵥ x.1 + 0)) = 0
  rw [exSD_d1, zero_mulVec, add_zero, dotProduct_zero, smul_zero]

/-! ### The support triangle and the hypotheses of the step -/

/-- **An explicit support triangle over `ℚ`** (tex 4157–4194, 5398–5424): `C_P = D` and
`C_R = D ⊕ Q` with the split inclusion `i`, the identity retract of `D`, the standard bases of
`Q¹, Q²`, the cycles `z_P = 1`, `z_R = e_q i(z_P)` and the closed functionals `λ_P = ⟨1, ·⟩`,
`λ_R = e_q λ_P ∘ pr₁`. Kind: definition. -/
def exS : SupportTriangle ℚ where
  CP := exSD.toGCx
  CR := exSCR
  E := exSE
  D := exSD
  R := GRetract.refl exSD.toGCx
  Q' := exSE.quotientCx
  RQ := GRetract.refl exSE.quotientCx
  hQ' := fun n h1 h2 => by
    change Subsingleton (exSE.Qc n)
    rw [exSE_hQ n h1 h2]
    infer_instance
  N := Fin 2 ⊕ Fin 2
  b1 := triQBasis exSD.toGCx exSQ _ _ 1 exSb1
  b2 := triQBasis exSD.toGCx exSQ _ _ 2 exSb2
  zR := exSzR
  hzR := exSzR_cycle
  zP := exSzP
  hzP := exSzP_cycle
  lamR := exSlamR
  hlamR := exSlamR_closed
  lamP := exSlamP
  hlamP := exSlamP_closed

/-- **The new block of the example is the two-place block `exB`**: the matrix of the quotient
differential `d_Q : Q¹ → Q²` in the bases. (tex 5420–5424, 4178–4182) Kind: PROVED. -/
theorem exS_dQ_matrix : LinearMap.toMatrix exS.b1 exS.b2 (exS.Q'.d 1 2 rfl) = exB :=
  (toMatrix_triIncl_dQ exSD.toGCx exSQ _ _ exSb1 exSb2).trans (toMatrix_basisFun_mulVecLin exB)

/-- **The hypothesis `hBe` of the step** for `Fr = 1`, `q = 1`, `z = z⁻¹ = 2`, with the identity
relabelling. (tex 4178–4182, 5420–5424) Kind: PROVED. -/
theorem exS_hBe : ∃ e : exS.N ≃ Fin 2 ⊕ Fin 2,
    LinearMap.toMatrix exS.b1 exS.b2 (exS.Q'.d 1 2 rfl) =
      (twoPlaceBlock (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2).submatrix e e :=
  ⟨Equiv.refl _, exS_dQ_matrix⟩

/-- **The hypothesis `hzR` of the step**: the norm identity `z_R = e_q i(z_P) + d b` with
retained boundary `b = 0`. (tex 4169–4170) Kind: PROVED. -/
theorem exS_hzR : ∃ b : exS.CR.X 0,
    exS.zR = pointFactor (2 : ℚ) 2 2 • exS.E.i.f 1 1 rfl exS.zP + exS.CR.d 0 1 rfl b :=
  ⟨0, by rw [map_zero, add_zero]; rfl⟩

/-- **The hypothesis `hlamR` of the step**: the functional relation `λ_R ∘ i = e_q λ_P`.
(tex 4173–4175) Kind: PROVED. -/
theorem exS_hlamR : exS.lamR ∘ₗ exS.E.i.f 2 2 rfl = pointFactor (2 : ℚ) 2 2 • exS.lamP :=
  LinearMap.ext fun _ => rfl

/-- The point factor of the example: `e_q = a − z − z⁻¹ = 2 − 2 − 2 = −2`. (tex 4158)
Kind: PROVED. -/
theorem exS_pointFactor : pointFactor (2 : ℚ) 2 2 = -2 := by
  norm_num [pointFactor]

/-- The quotient factor of the example: `l_q = det(1 − 2 Fr) det(1 − 2 Fr) = 1` for `Fr = 1`,
`q = 1` (consistent with `det B = q⁴ l_q = 1`, `exB_det`). (tex 4208–4211, 4178–4182)
Kind: PROVED. -/
theorem exS_quotientFactor : quotientFactor (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 = 1 := by
  rw [quotientFactor_eq_poly (a := 2) (q := 1) (by simp) (by simp)]
  norm_num

/-- **The unit condition `l_q ≠ 0` of the step** for the example. (tex 4178–4182, 4208–4211)
Kind: PROVED. -/
theorem exS_hl : quotientFactor (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 ≠ 0 := by
  rw [exS_quotientFactor]
  exact one_ne_zero

/-! ### The step and its coordinates -/

/-- **The step of the explicit support triangle** (tex 4157–4194, 5398–5424): by
`kmStep_of_supportTriangle`, a `KmStep` for `Fr = 1`, `q = 1`, `a = 2`, `z = z⁻¹ = 2` at the
torsion coordinates `(u_rel, u_prim)` of its models. Kind: PROVED. -/
theorem exS_kmStep :
    KmStep (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 2 exS.relCoord exS.primCoord :=
  exS.kmStep_of_supportTriangle (qi := 1) (by norm_num) (by simp) (by simp) exS_hl exS_hBe
    exS_hzR exS_hlamR

/-- **(4.7) for the explicit support triangle**: `l_q u_rel = e_q² q⁻⁴ u_prim`, from
`h47_of_supportTriangle`. (tex 4185–4188) Kind: PROVED. -/
theorem exS_h47 : quotientFactor (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 * exS.relCoord =
    pointFactor (2 : ℚ) 2 2 ^ 2 * 1 ^ 4 * exS.primCoord :=
  exS.h47_of_supportTriangle (Fr := 1) (q := 1) (qi := 1) (a := 2) (zq := 2) (zqi := 2)
    (by norm_num) (by simp) (by simp) exS_hl exS_hBe exS_hzR exS_hlamR

/-- **The primitive coordinate of the example is `u_prim = −1`** (tex 3877–3892, 5545–5595): the
model of `z_P` is `1`, the coordinate vector of `λ_P` is `1`, and the coordinate is `exFull_uP`
(Elliot's block computation `kmCoord_block`). Kind: PROVED. -/
theorem exS_primCoord : exS.primCoord = -1 := by
  have h1 : exS.zPv = (1 : exFull.D1 → ℚ) := rfl
  have h2 : exS.lamPv = (1 : exFull.D2 → ℚ) := by
    funext k
    change (1 : Fin exS.D.m1 ⊕ Unit ⊕ Fin exS.D.m2 → ℚ) ⬝ᵥ Pi.single k 1 = 1
    rw [dotProduct_single, mul_one]
    rfl
  exact (kmCoord_congr exS.D.toFour exS.zPv_cycle exFull_hzP exS.lamPv_closed exFull_hlamP h1 h2
    _).trans exFull_uP

/-- **The relaxed coordinate of the example is `u_rel = −4`**: (4.7) with `l_q = 1`,
`e_q = −2`, `q = 1` and `u_prim = −1`; the step is not degenerate. (tex 4185–4188)
Kind: PROVED. -/
theorem exS_relCoord : exS.relCoord = -4 := by
  have h := exS_h47
  rw [exS_quotientFactor, one_mul, exS_pointFactor, exS_primCoord] at h
  rw [h]
  norm_num

/-- **Non-vacuity of the support-triangle step, with nonzero coordinates** (tex 4157–4194):
there is a support triangle over `ℚ` whose coordinates form a `KmStep` for `Fr = 1`, `q = 1`,
`a = 2`, `z = z⁻¹ = 2` (through `kmStep_of_supportTriangle`), with `u_rel = −4` and
`u_prim = −1`. Kind: PROVED. -/
theorem supportTriangle_nonvacuous : ∃ S : SupportTriangle ℚ,
    KmStep (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 2 S.relCoord S.primCoord ∧ S.relCoord = -4 ∧
      S.primCoord = -1 :=
  ⟨exS, exS_kmStep, exS_relCoord, exS_primCoord⟩

end ZInQ.Manuscript.RC.Wiring
