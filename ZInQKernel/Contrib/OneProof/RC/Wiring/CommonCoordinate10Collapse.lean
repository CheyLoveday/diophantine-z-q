import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Block

/-!
# The support triangle at a step collapses to (4.7) at the step

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194):

> The actual norm identity is `z_R = e_q i(z_P)`, with its retained boundary. […]
> Consequently `λ_R ∘ i = e_q λ_P`. […] The two quotient determinants satisfy
> `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q) = q⁴ l_q`. In the original integral determinant
> bases, the support triangle therefore gives `l_q u_rel = e_q² ε_q u_prim` (4.7).

A `SupportTriangle` (`CommonCoordinate10Step.lean`) is existential over the complexes: its three
hypotheses `hBe`, `hzR`, `hlamR` do not tie `C_P` and `C_R` to the Selmer complexes. This file
generalizes the example `exS` (`CommonCoordinate10NonVacuity.lean`) to show that, at a step, a
support triangle with prescribed coordinates exists exactly when (4.7) holds at the step:

* `SupportTriangle.relCoord_eq_of_isUnit`: for any support triangle whose new block is an
  invertible matrix `B` up to relabelling, with the norm identity and the functional relation
  for one factor `c`, `u_rel = det(B)⁻¹ c² u_prim` (`kmCoord_fullCancel_step`; no Frobenius
  arithmetic is used).
* `abstractTriangle Fr q zq zqi a uP`, over any field: `C_P = minBlock K` (`F --0--> F` in
  degrees one and two) with its identity retract, the quotient `Q` the singular disk
  `N --B--> N` of `singularBlockFull` (`B` the two-place block `diag(z Fr − q, z⁻¹ Fr − q)`),
  `C_R = C_P ⊕ Q` with its split inclusion, the cycles `z_P = −u_P · 1`, `z_R = e i(z_P)` and the
  functionals `λ_P = ⟨1, ·⟩`, `λ_R = e λ_P ∘ pr₁` for `e = pointFactor a zq zqi`. It satisfies
  `hBe` (identity relabelling), `hzR` (`b = 0`) and `hlamR`; `u_prim = u_P`
  (`kmCoord_minBlock`), and `u_rel = det(B)⁻¹ e² u_P` when `B` is invertible.
* `kmStep_of_h47`, `kmStep_iff_h47`: under the unit conditions, `KmStep Fr q a zq zqi u_R u_P`
  holds if and only if `l_q u_R = e_q² q⁻⁴ u_P`.
* **`supportTriangleAt_of_h47`**, **`supportTriangleAt_iff_h47`**: at the leaf's values (a good
  odd prime `p`, `Fr = ρ_T(Fr_p)` over `Frac Λ`, `z = z_p(x)`, `e_p(x)`),
  `SupportTriangleAt C Fam x p u_R u_P` holds if and only if `l_p u_R = e_p² p⁻⁴ u_P`.

So the step field of `CommonCoordinateTrianglesST` constrains the coordinates `u T` exactly
through (4.7) at each step, and through nothing else.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

section Abstract

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor)

/-- **The relaxed coordinate of a support triangle with an invertible new block**
(tex 4157–4194, 5509–5516): if the matrix of `d_{Q'} : Q'¹ → Q'²` is an invertible `B` up to a
relabelling, `z_R = c i(z_P) + d b` and `λ_R ∘ i = c λ_P`, then `u_rel = det(B)⁻¹ c² u_prim`.
Kind: PROVED. -/
theorem SupportTriangle.relCoord_eq_of_isUnit {F : Type} [Field F] (S : SupportTriangle F)
    {B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hB : IsUnit B.det) (c : F)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2,
      LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) = B.submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = c • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamR : S.lamR ∘ₗ S.E.i.f 2 2 rfl = c • S.lamP) :
    S.relCoord = B.det⁻¹ * c ^ 2 * S.primCoord := by
  obtain ⟨e, he⟩ := hBe
  obtain ⟨b, hb⟩ := hzR
  have h1 : S.model.B.det = (B.submatrix e e).det :=
    congrArg Matrix.det ((relModel_B S.E S.R S.RQ S.b1 S.b2).trans he)
  have hdet : S.model.B.det = B.det := h1.trans (det_submatrix_equiv_self e B)
  have hB' : IsUnit S.model.B.det := hdet ▸ hB
  have hz' := S.cycle_smul_zPext c
  have hzRv := S.zRv_eq c b hb
  have hcoordR : S.relCoord = kmCoord S.model.toFour (c • S.zPext) S.lamRv hz' S.lamRv_closed
      (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) := by
    unfold SupportTriangle.relCoord
    rw [kmCoord_congr S.model.toFour S.zRv_cycle
      (cycle_add_boundary S.model.toFour hz' (S.retract.p.f 0 0 rfl b)) S.lamRv_closed
      S.lamRv_closed hzRv rfl]
    exact kmCoord_add_boundary S.model.toFour hz' S.lamRv_closed
      (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) _
  have h4 : (S.model.cancel hB').toFour = S.D.toFour :=
    cancel_relModel_toFour S.E S.R S.RQ S.b1 S.b2 hB'
  have hzP' : (S.model.cancel hB').toFour.d1 *ᵥ S.zPv = 0 := by
    rw [h4]
    exact S.zPv_cycle
  have hlamP' : S.lamPv ᵥ* (S.model.cancel hB').toFour.d1 = 0 := by
    rw [h4]
    exact S.lamPv_closed
  have hstep := kmCoord_fullCancel_step hB' hz' S.lamRv_closed hzP' hlamP' c rfl
    (S.lamRv_inl c hlamR)
  rw [hcoordR, hstep, ← S.primCoord_eq_cancel hB' hzP' hlamP', hdet]
  ring

variable {K : Type} [Field K] (Fr : Matrix (Fin 2) (Fin 2) K) (q zq zqi a uP : K)

/-- **The local quotient of the abstract triangle** (tex 5398–5403, 5420–5424, 4178–4182): the
singular disk `N --B--> N` of `singularBlockFull Fr q zq zqi` in degrees one and two, with
`N = Fin 2 ⊕ Fin 2` and `B` the two-place block; zero in the other degrees.
Kind: definition. -/
abbrev absTQ : GCx K := (singularBlockFull Fr q zq zqi).disk

/-- The quotient vanishes outside degrees one and two. (tex 5398–5403) Kind: PROVED. -/
theorem absTQ_subsingleton (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((absTQ Fr q zq zqi).X n) := by
  have := (singularBlockFull Fr q zq zqi).isEmpty_kidx n h1 h2
  change Subsingleton ((singularBlockFull Fr q zq zqi).kidx n → K)
  infer_instance

/-- **The relaxed complex of the abstract triangle**, the direct sum `C_R = C_P ⊕ Q` of
`C_P = minBlock K` and the quotient (zero off-diagonal map). (tex 5398–5403)
Kind: definition. -/
abbrev absTCR : GCx K :=
  triCx (minBlock K).toGCx (absTQ Fr q zq zqi)
    (zeroOffDiag (minBlock K).toGCx (absTQ Fr q zq zqi))
    (zeroOffDiag_sq (minBlock K).toGCx (absTQ Fr q zq zqi))

/-- **The primitive-to-relaxed map** `i : C_P → C_R`, `x ↦ (x, 0)`, a split inclusion with
complement `0 ⊕ Q`. (tex 4160, 5398–5403) Kind: definition. -/
abbrev absTE : SplitInclusion (minBlock K).toGCx (absTCR Fr q zq zqi) :=
  triIncl (minBlock K).toGCx (absTQ Fr q zq zqi)
    (zeroOffDiag (minBlock K).toGCx (absTQ Fr q zq zqi))
    (zeroOffDiag_sq (minBlock K).toGCx (absTQ Fr q zq zqi))

/-- The complement of `i` vanishes outside degrees one and two. (tex 5398–5424)
Kind: PROVED. -/
theorem absTE_Qc (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : (absTE Fr q zq zqi).Qc n = ⊥ :=
  triIncl_Qc_eq_bot _ _ _ _ n (absTQ_subsingleton Fr q zq zqi n h1 h2)

/-- The standard basis of `Q¹ = K^N`. (tex 5398–5424) Kind: definition. -/
def absTb1 : Basis (Fin 2 ⊕ Fin 2) K ((absTQ Fr q zq zqi).X 1) :=
  Pi.basisFun K (Fin 2 ⊕ Fin 2)

/-- The standard basis of `Q² = K^N`. (tex 5398–5424) Kind: definition. -/
def absTb2 : Basis (Fin 2 ⊕ Fin 2) K ((absTQ Fr q zq zqi).X 2) :=
  Pi.basisFun K (Fin 2 ⊕ Fin 2)

/-- **The primitive cycle** `z_P = −u_P · 1` on `D¹ = K`. (tex 4166–4170, 3877–3892)
Kind: definition. -/
def absTzP : (minBlock K).toGCx.X 1 :=
  (-uP) • (1 : Fin (minBlock K).m0 ⊕ Unit ⊕ Fin (minBlock K).m1 → K)

/-- `d z_P = 0` (the differentials of `minBlock K` vanish). (tex 4166–4170) Kind: PROVED. -/
theorem absTzP_cycle : (minBlock K).toGCx.d 1 2 rfl (absTzP uP) = 0 :=
  minBlock_toGCx_d 1 2 rfl _

/-- **The primitive functional** `λ_P = ⟨1, ·⟩` on `D² = K`. (tex 4166–4175, 3877–3892)
Kind: definition. -/
def absTlamP : (minBlock K).toGCx.X 2 →ₗ[K] K where
  toFun v := (1 : Fin (minBlock K).m1 ⊕ Unit ⊕ Fin (minBlock K).m2 → K) ⬝ᵥ v
  map_add' v w :=
    dotProduct_add (1 : Fin (minBlock K).m1 ⊕ Unit ⊕ Fin (minBlock K).m2 → K) v w
  map_smul' c v :=
    dotProduct_smul c (1 : Fin (minBlock K).m1 ⊕ Unit ⊕ Fin (minBlock K).m2 → K) v

/-- `λ_P ∘ d = 0` (the differentials of `minBlock K` vanish). (tex 4166–4175)
Kind: PROVED. -/
theorem absTlamP_closed : absTlamP (K := K) ∘ₗ (minBlock K).toGCx.d 1 2 rfl = 0 := by
  apply LinearMap.ext
  intro v
  change absTlamP (K := K) ((minBlock K).toGCx.d 1 2 rfl v) = 0
  rw [minBlock_toGCx_d, map_zero]

/-- **The relaxed cycle** `z_R = e i(z_P)`, `e = pointFactor a zq zqi`: the norm identity with
zero retained boundary. (tex 4158, 4169–4170) Kind: definition. -/
def absTzR : (absTCR Fr q zq zqi).X 1 :=
  pointFactor a zq zqi • (absTE Fr q zq zqi).i.f 1 1 rfl (absTzP uP)

/-- `d z_R = 0`. (tex 4169–4170) Kind: PROVED. -/
theorem absTzR_cycle : (absTCR Fr q zq zqi).d 1 2 rfl (absTzR Fr q zq zqi a uP) = 0 := by
  unfold absTzR
  rw [map_smul, ← (absTE Fr q zq zqi).i_d 1 2 rfl (absTzP uP), absTzP_cycle, map_zero,
    smul_zero]

/-- **The relaxed functional** `λ_R = e λ_P ∘ pr₁` on `C²_R = D² × Q²`, `e = pointFactor a zq zqi`.
(tex 4173–4175) Kind: definition. -/
def absTlamR : (absTCR Fr q zq zqi).X 2 →ₗ[K] K :=
  pointFactor a zq zqi •
    (absTlamP ∘ₗ LinearMap.fst K ((minBlock K).toGCx.X 2) ((absTQ Fr q zq zqi).X 2))

/-- `λ_R ∘ d = 0`: `λ_R` reads only the `C_P`-component of `d¹_R (x, y) = (d¹_D x + 0, B y)`,
and `d¹_D = 0`. (tex 4173–4175, 5398–5403) Kind: PROVED. -/
theorem absTlamR_closed : absTlamR Fr q zq zqi a ∘ₗ (absTCR Fr q zq zqi).d 1 2 rfl = 0 := by
  apply LinearMap.ext
  intro (x : (minBlock K).toGCx.X 1 × (absTQ Fr q zq zqi).X 1)
  change pointFactor a zq zqi • absTlamP (K := K) ((minBlock K).toGCx.d 1 2 rfl x.1 + 0) = 0
  rw [minBlock_toGCx_d, add_zero, map_zero, smul_zero]

/-- **The abstract support triangle** (tex 4157–4194, 5398–5424): over any field `K`, for any
`Fr, q, zq, zqi, a` and any `u_P`, the support triangle with `C_P = minBlock K` and its identity
retract, `C_R = C_P ⊕ Q` (`Q` the singular disk of the two-place block, with the identity
retract of the quotient complex and the standard bases), the cycles `z_P = −u_P · 1`,
`z_R = e i(z_P)` and the closed functionals `λ_P = ⟨1, ·⟩`, `λ_R = e λ_P ∘ pr₁`, where
`e = pointFactor a zq zqi`. Kind: definition. -/
def abstractTriangle : SupportTriangle K where
  CP := (minBlock K).toGCx
  CR := absTCR Fr q zq zqi
  E := absTE Fr q zq zqi
  D := minBlock K
  R := GRetract.refl (minBlock K).toGCx
  Q' := (absTE Fr q zq zqi).quotientCx
  RQ := GRetract.refl (absTE Fr q zq zqi).quotientCx
  hQ' := fun n h1 h2 => by
    change Subsingleton ((absTE Fr q zq zqi).Qc n)
    rw [absTE_Qc Fr q zq zqi n h1 h2]
    infer_instance
  N := Fin 2 ⊕ Fin 2
  b1 := triQBasis (minBlock K).toGCx (absTQ Fr q zq zqi) _ _ 1 (absTb1 Fr q zq zqi)
  b2 := triQBasis (minBlock K).toGCx (absTQ Fr q zq zqi) _ _ 2 (absTb2 Fr q zq zqi)
  zR := absTzR Fr q zq zqi a uP
  hzR := absTzR_cycle Fr q zq zqi a uP
  zP := absTzP uP
  hzP := absTzP_cycle uP
  lamR := absTlamR Fr q zq zqi a
  hlamR := absTlamR_closed Fr q zq zqi a
  lamP := absTlamP
  hlamP := absTlamP_closed

/-- **The new block of the abstract triangle is the two-place block**: the matrix of
`d_{Q'} : Q'¹ → Q'²` in the bases. (tex 5420–5424, 4178–4182) Kind: PROVED. -/
theorem abstractTriangle_dQ_matrix :
    LinearMap.toMatrix (abstractTriangle Fr q zq zqi a uP).b1
        (abstractTriangle Fr q zq zqi a uP).b2
        ((abstractTriangle Fr q zq zqi a uP).Q'.d 1 2 rfl) =
      twoPlaceBlock Fr q zq zqi :=
  (toMatrix_triIncl_dQ (minBlock K).toGCx (absTQ Fr q zq zqi) _ _ (absTb1 Fr q zq zqi)
    (absTb2 Fr q zq zqi)).trans (toMatrix_basisFun_mulVecLin (twoPlaceBlock Fr q zq zqi))

/-- **The hypothesis `hBe`** for the abstract triangle, with the identity relabelling.
(tex 4178–4182, 5420–5424) Kind: PROVED. -/
theorem abstractTriangle_hBe : ∃ e : (abstractTriangle Fr q zq zqi a uP).N ≃ Fin 2 ⊕ Fin 2,
    LinearMap.toMatrix (abstractTriangle Fr q zq zqi a uP).b1
        (abstractTriangle Fr q zq zqi a uP).b2
        ((abstractTriangle Fr q zq zqi a uP).Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e :=
  ⟨Equiv.refl _, abstractTriangle_dQ_matrix Fr q zq zqi a uP⟩

/-- **The hypothesis `hzR`** for the abstract triangle, with retained boundary `b = 0`.
(tex 4169–4170) Kind: PROVED. -/
theorem abstractTriangle_hzR : ∃ b : (abstractTriangle Fr q zq zqi a uP).CR.X 0,
    (abstractTriangle Fr q zq zqi a uP).zR = pointFactor a zq zqi •
      (abstractTriangle Fr q zq zqi a uP).E.i.f 1 1 rfl (abstractTriangle Fr q zq zqi a uP).zP +
        (abstractTriangle Fr q zq zqi a uP).CR.d 0 1 rfl b :=
  ⟨0, by rw [map_zero, add_zero]; rfl⟩

/-- **The hypothesis `hlamR`** for the abstract triangle: `λ_R ∘ i = e λ_P`.
(tex 4173–4175) Kind: PROVED. -/
theorem abstractTriangle_hlamR :
    (abstractTriangle Fr q zq zqi a uP).lamR ∘ₗ
        (abstractTriangle Fr q zq zqi a uP).E.i.f 2 2 rfl =
      pointFactor a zq zqi • (abstractTriangle Fr q zq zqi a uP).lamP :=
  LinearMap.ext fun _ => rfl

/-- **The primitive coordinate of the abstract triangle is `u_P`** (tex 3877–3892, 5577–5595):
on `minBlock K` the coordinate is `−z_H λ_H = −(−u_P · 1)` (`kmCoord_minBlock`).
Kind: PROVED. -/
theorem abstractTriangle_primCoord : (abstractTriangle Fr q zq zqi a uP).primCoord = uP := by
  have h1 : (abstractTriangle Fr q zq zqi a uP).zPv =
      ((-uP) • 1 : Fin (minBlock K).m0 ⊕ Unit ⊕ Fin (minBlock K).m1 → K) := rfl
  have h2 : (abstractTriangle Fr q zq zqi a uP).lamPv =
      (1 : Fin (minBlock K).m1 ⊕ Unit ⊕ Fin (minBlock K).m2 → K) := by
    funext k
    change (1 : Fin (abstractTriangle Fr q zq zqi a uP).D.m1 ⊕ Unit ⊕
      Fin (abstractTriangle Fr q zq zqi a uP).D.m2 → K) ⬝ᵥ Pi.single k 1 = 1
    rw [dotProduct_single, mul_one]
    rfl
  refine (kmCoord_congr (minBlock K).toFour _ (minBlock_toFour_cycle _) _
    (minBlock_toFour_closed _) h1 h2 _).trans ((kmCoord_minBlock _ _ _ _).trans ?_)
  simp

/-- **The relaxed coordinate of the abstract triangle** (tex 4157–4194, 5509–5516): when the
two-place block `B` is invertible, `u_rel = det(B)⁻¹ e² u_P` with `e = pointFactor a zq zqi`
(`SupportTriangle.relCoord_eq_of_isUnit`). Kind: PROVED. -/
theorem abstractTriangle_relCoord (hB : IsUnit (twoPlaceBlock Fr q zq zqi).det) :
    (abstractTriangle Fr q zq zqi a uP).relCoord =
      (twoPlaceBlock Fr q zq zqi).det⁻¹ * pointFactor a zq zqi ^ 2 * uP := by
  rw [(abstractTriangle Fr q zq zqi a uP).relCoord_eq_of_isUnit hB _
    (abstractTriangle_hBe Fr q zq zqi a uP) (abstractTriangle_hzR Fr q zq zqi a uP)
    (abstractTriangle_hlamR Fr q zq zqi a uP), abstractTriangle_primCoord]

end Abstract

/-! ### The collapse of the torsion-level step -/

section Collapse

open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock det_twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor quotientDet_eq)

variable {K : Type} [Field K]

/-- **(4.7) at a step gives a `KmStep`** (tex 4157–4194, 4185–4188): under the unit conditions
(`q q⁻¹ = 1`, `tr Fr = a`, `det Fr = q`, `l_q ≠ 0`), every pair `(u_R, u_P)` with
`l_q u_R = e_q² q⁻⁴ u_P` is a torsion-level step, through the abstract triangle with
`u_prim = u_P` (`det B = q⁴ l_q`). Kind: PROVED. -/
theorem kmStep_of_h47 {Fr : Matrix (Fin 2) (Fin 2) K} {q qi a zq zqi uR uP : K}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (h : quotientFactor Fr qi zq zqi * uR = pointFactor a zq zqi ^ 2 * qi ^ 4 * uP) :
    KmStep Fr q a zq zqi uR uP := by
  have hdet : (twoPlaceBlock Fr q zq zqi).det = q ^ 4 * quotientFactor Fr qi zq zqi := by
    rw [det_twoPlaceBlock, quotientDet_eq zq zqi hq ha hd]
  have hq0 : q ≠ 0 := left_ne_zero_of_mul_eq_one hq
  have hB : IsUnit (twoPlaceBlock Fr q zq zqi).det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero 4 hq0) hl)
  have hS := (abstractTriangle Fr q zq zqi a uP).kmStep_of_supportTriangle hq ha hd hl
    (abstractTriangle_hBe Fr q zq zqi a uP) (abstractTriangle_hzR Fr q zq zqi a uP)
    (abstractTriangle_hlamR Fr q zq zqi a uP)
  rw [abstractTriangle_relCoord Fr q zq zqi a uP hB, abstractTriangle_primCoord] at hS
  have hqi4 : qi ^ 4 = (q ^ 4)⁻¹ := by rw [eq_inv_of_mul_eq_one_right hq, inv_pow]
  have hcoord : (twoPlaceBlock Fr q zq zqi).det⁻¹ * pointFactor a zq zqi ^ 2 * uP = uR := by
    rw [(eq_inv_mul_iff_mul_eq₀ hl).2 h, hdet]
    linear_combination
      (-((quotientFactor Fr qi zq zqi)⁻¹ * pointFactor a zq zqi ^ 2 * uP)) * hqi4
  rwa [hcoord] at hS

/-- **A torsion-level step is exactly (4.7) at the step** (tex 4157–4194, 4185–4188): under the
unit conditions, `KmStep Fr q a zq zqi u_R u_P ↔ l_q u_R = e_q² q⁻⁴ u_P` (`KmStep.h47` and
`kmStep_of_h47`). Kind: PROVED. -/
theorem kmStep_iff_h47 {Fr : Matrix (Fin 2) (Fin 2) K} {q qi a zq zqi uR uP : K}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0) :
    KmStep Fr q a zq zqi uR uP ↔
      quotientFactor Fr qi zq zqi * uR = pointFactor a zq zqi ^ 2 * qi ^ 4 * uP :=
  ⟨fun h => h.h47 hq ha hd, kmStep_of_h47 hq ha hd hl⟩

end Collapse

/-! ### The collapse at the leaf's values -/

section Leaf

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)

/-- **(4.7) at the step gives an actual support triangle at `p`** (tex 4157–4194, 4185–4188):
at a good odd prime `p`, for any `u_R, u_P` over `Frac Λ` with `l_p u_R = e_p² p⁻⁴ u_P` (at
`Fr = ρ_T(Fr_p)`, `z = z_p(x)`), the abstract triangle with `u_prim = u_P` is a support triangle
at `p` with coordinates `(u_R, u_P)`: `e_p(x) = a_p − z − z⁻¹` (`eF_eq_pointFactor`) and
`u_rel = det(B)⁻¹ e_p² u_P = (p⁴ l_p)⁻¹ e_p² u_P = u_R`. Kind: PROVED. -/
theorem supportTriangleAt_of_h47 {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) {uR uP : FracLam}
    (h : quotientFactor ((frobMat C p).map zTwoToF) (p : FracLam)⁻¹
        (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) * uR =
      pointFactor (apE ℓ p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) ^ 2 * (p : FracLam)⁻¹ ^ 4 * uP) :
    SupportTriangleAt C Fam x p uR uP := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  have hl := leaf_quotientFactor_ne_zero C Fam x hpr hp2 hgood
  have hB := isUnit_iff_ne_zero.2 (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2 hgood)
  refine ⟨abstractTriangle ((frobMat C p).map zTwoToF) (p : FracLam)
    (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) (apE ℓ p : FracLam) uP,
    abstractTriangle_hBe _ _ _ _ _ _, ?_, ?_, ?_, abstractTriangle_primCoord _ _ _ _ _ _⟩
  · rw [eF_eq_pointFactor]
    exact abstractTriangle_hzR _ _ _ _ _ _
  · rw [eF_eq_pointFactor]
    exact abstractTriangle_hlamR _ _ _ _ _ _
  · rw [abstractTriangle_relCoord _ _ _ _ _ _ hB, det_twoPlaceBlock,
      quotientDet_eq _ _ (mul_inv_cancel₀ hp0) ha hd, (eq_inv_mul_iff_mul_eq₀ hl).2 h]
    ring

/-- **The collapse of the support triangle at a step** (tex 4157–4194, 4185–4188): at a good odd
prime `p`, `SupportTriangleAt C Fam x p u_R u_P` holds if and only if (4.7) holds at the step,
`l_p u_R = e_p² p⁻⁴ u_P` (`SupportTriangleAt.kmStep` with `KmStep.h47`, and
`supportTriangleAt_of_h47`). Kind: PROVED. -/
theorem supportTriangleAt_iff_h47 {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) {uR uP : FracLam} :
    SupportTriangleAt C Fam x p uR uP ↔
      quotientFactor ((frobMat C p).map zTwoToF) (p : FracLam)⁻¹
          (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) * uR =
        pointFactor (apE ℓ p : FracLam) (lamToF (zAt Fam x p : Lambda))
          (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) ^ 2 * (p : FracLam)⁻¹ ^ 4 * uP := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  exact ⟨fun h => (h.kmStep C Fam x hpr hp2 hgood).h47 (mul_inv_cancel₀ hp0) ha hd,
    supportTriangleAt_of_h47 C Fam x hpr hp2 hgood⟩

end Leaf

end ZInQ.Manuscript.RC.Wiring
