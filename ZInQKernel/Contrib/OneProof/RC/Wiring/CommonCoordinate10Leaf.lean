import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10TwoSing
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate9
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6NonVacuity

/-!
# The common-coordinate leaf from the actual support triangles

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): each
relaxation `T → T ∪ {q}` at an unused prime is the support triangle `C_P → C_R → Q_q`, and gives
(4.7) at the step, `l_q u_rel = e_q² ε_q u_prim`.

The current leaf `CommonCoordinateInputsNF` (`CommonCoordinate9.lean`) takes each step as batch
three's `NaturalStep` with the actual Frobenius `frobMat C p`. This file ties it to the actual
support triangles of `CommonCoordinate10Step.lean`:

* `naturalStep_of_kmStep`: a torsion-level step gives the leaf's `NaturalStep` with step unit
  `ε_q = q⁻⁴` (through (4.7) at the step and round one's `naturalStepF_of`);
* `kmStep_leaf_of_supportTriangle`: at the leaf's values (`Fr = ρ_T(Fr_p)` over `F`, `q = p`,
  `a = a_p`, `z = z_p(x)`), an actual support triangle over `F = Frac Λ` with the new block
  `hBe`, the norm identity `hzR` and the functional relation `hlamR` is a `KmStep` at its torsion
  coordinates; the units (`p p⁻¹ = 1`, `tr = a_p`, `det = p`, `l_p(x) ≠ 0`) are PROVED here;
  `naturalStep_leaf_of_supportTriangle`: the leaf's step field at those coordinates;
* `SupportTriangleAt C Fam x p u_R u_P`: an actual support triangle at `p` with the three
  hypotheses whose coordinates are `u_R, u_P`;
* `supportTriangleAt_of_twoSing`: with the quotient retracted onto the tame model `twoSingCx`
  the block hypothesis is PROVED, so a step needs only the actual complexes, that retraction,
  `hzR` and `hlamR`;
* `CommonCoordinateTrianglesST`: the leaf with each step an actual support triangle;
  `CommonCoordinateTrianglesST.toLF` and `commonCoordinateInputsNF_of_ST`: it gives the current
  leaf, hence (4.7) (`commonCoordinateTarget_of_ST`).

What still differs from the text is recorded in the docstring of `CommonCoordinateTrianglesST`:
the coordinates `u T` are one number per support `T`, so the model of `C_T` used as the primitive
complex of the step `(T, p)` and the model used as the relaxed complex of a step into `T` must give
the same coordinate (the text's "original integral determinant bases" and its unit-disk argument,
tex 4185–4193).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx)

/-- **A torsion-level step gives the leaf's `NaturalStep`** with step unit `q⁻⁴` (tex 4185–4193):
(4.7) at the step, `l_q u_R = e_q² q⁻⁴ u_P`, gives `det B · u_R = e_q² u_P` (`det B = q⁴ l_q`),
and round one's `naturalStepF_of` builds the triangular model. Kind: PROVED. -/
theorem naturalStep_of_kmStep {Fr : Matrix (Fin 2) (Fin 2) FracLam} {q qi a z zi uR uP : FracLam}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hB : (twoPlaceBlock Fr q z zi).det ≠ 0) (h : KmStep Fr q a z zi uR uP) :
    NaturalStep Fr q qi a z zi uP uR (qi ^ 4 * 1) LamUnitF LamUnitF := by
  refine naturalStepF_of lamUnitF_one hB ?_
  have h47 := h.h47 hq ha hd
  rw [det_twoPlaceBlock, quotientDet_eq z zi hq ha hd]
  have hq4 : q ^ 4 * qi ^ 4 = 1 := by rw [← mul_pow, hq, one_pow]
  linear_combination q ^ 4 * h47 + (pointFactor a z zi ^ 2 * uP) * hq4

section Leaf

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)

/-- The actual Frobenius over `F` has trace `a_p` and determinant `p` at a good odd prime
(tex 4157–4194; `FrobeniusTrace` is PROVED, `frobeniusTrace_proved`). Kind: PROVED. -/
theorem leafFr_trace_det {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) :
    ((frobMat C p).map zTwoToF).trace = (apE ℓ p : FracLam) ∧
      ((frobMat C p).map zTwoToF).det = (p : FracLam) :=
  trace_det_map_zTwoToF
    (trace_det_frobMat C (frobeniusTrace_proved (Ecurve ℓ)) hpr hp2 hgood).1
    (det_frobMat C hpr hp2)

/-- **The unit condition at the leaf's values** (tex 4178–4182, 4185–4188): the two-place factor
`l_p(x)` is nonzero. Kind: PROVED. -/
theorem leaf_quotientFactor_ne_zero {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) :
    quotientFactor ((frobMat C p).map zTwoToF) (p : FracLam)⁻¹ (lamToF (zAt Fam x p : Lambda))
      (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) ≠ 0 := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hpo : Odd p := hpr.odd_of_ne_two hp2
  rw [quotientFactor_eq_quotPoly _ _ _ ha hd, ← lF_eq_quotPoly hpo]
  exact lF_ne_zero ℓ Fam x hpo

/-- The new block at the leaf's values is invertible (`det = p⁴ l_p(x)`). (tex 4178–4182)
Kind: PROVED. -/
theorem leaf_det_twoPlaceBlock_ne_zero {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) :
    (twoPlaceBlock ((frobMat C p).map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
      (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).det ≠ 0 := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  rw [det_twoPlaceBlock, quotientDet_eq _ _ (mul_inv_cancel₀ hp0) ha hd]
  exact mul_ne_zero (pow_ne_zero 4 hp0) (leaf_quotientFactor_ne_zero C Fam x hpr hp2 hgood)

/-- **The relaxation step at the leaf's values from an actual support triangle**
(tex 4157–4194): with the new block `hBe` (the two-place block of `ρ_T(Fr_p)` at `z_p(x)`), the
norm identity `hzR` and the functional relation `hlamR` (with `e_p(x)`), the step is a `KmStep`
at the torsion coordinates of the models; the units are PROVED. Kind: PROVED. -/
theorem kmStep_leaf_of_supportTriangle {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) (S : SupportTriangle FracLam)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock ((frobMat C p).map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = eF ℓ Fam x p • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamR : S.lamR ∘ₗ S.E.i.f 2 2 rfl = eF ℓ Fam x p • S.lamP) :
    KmStep ((frobMat C p).map zTwoToF) (p : FracLam) (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) S.relCoord
      S.primCoord := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  rw [eF_eq_pointFactor] at hzR hlamR
  exact S.kmStep_of_supportTriangle (mul_inv_cancel₀ hp0) ha hd
    (leaf_quotientFactor_ne_zero C Fam x hpr hp2 hgood) hBe hzR hlamR

/-- **The leaf's step field from an actual support triangle** (tex 4157–4194, 4185–4193): the
`NaturalStep` of the leaf at the torsion coordinates of the models, with step unit `p⁻⁴`.
Kind: PROVED. -/
theorem naturalStep_leaf_of_supportTriangle {p : ℕ} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) (S : SupportTriangle FracLam)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock ((frobMat C p).map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = eF ℓ Fam x p • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamR : S.lamR ∘ₗ S.E.i.f 2 2 rfl = eF ℓ Fam x p • S.lamP) :
    NaturalStep ((frobMat C p).map zTwoToF) (p : FracLam) (p : FracLam)⁻¹ (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) S.primCoord
      S.relCoord ((p : FracLam)⁻¹ ^ 4 * 1) LamUnitF LamUnitF := by
  obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 hgood
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpr.ne_zero
  exact naturalStep_of_kmStep (mul_inv_cancel₀ hp0) ha hd
    (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2 hgood)
    (kmStep_leaf_of_supportTriangle C Fam x hpr hp2 hgood S hBe hzR hlamR)

/-- **An actual support triangle at `p` with coordinates `u_R, u_P`** (tex 4157–4194): a
`SupportTriangle` over `F = Frac Λ` satisfying the three hypotheses at the leaf's values
(`hBe`: the new block; `hzR`: the norm identity with its retained boundary; `hlamR`: the
functional relation), whose torsion coordinates are `u_R` and `u_P`. Kind: definition. -/
def SupportTriangleAt (p : ℕ) (uR uP : FracLam) : Prop :=
  ∃ S : SupportTriangle FracLam,
    (∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock ((frobMat C p).map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
        (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).submatrix e e) ∧
    (∃ b : S.CR.X 0, S.zR = eF ℓ Fam x p • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b) ∧
    S.lamR ∘ₗ S.E.i.f 2 2 rfl = eF ℓ Fam x p • S.lamP ∧ S.relCoord = uR ∧ S.primCoord = uP

/-- An actual support triangle at `p` is a `KmStep` at its coordinates. (tex 4157–4194)
Kind: PROVED. -/
theorem SupportTriangleAt.kmStep {p : ℕ} {uR uP : FracLam} (hpr : p.Prime) (hp2 : p ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) p) (h : SupportTriangleAt C Fam x p uR uP) :
    KmStep ((frobMat C p).map zTwoToF) (p : FracLam) (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) uR uP := by
  obtain ⟨S, hBe, hzR, hlamR, rfl, rfl⟩ := h
  exact kmStep_leaf_of_supportTriangle C Fam x hpr hp2 hgood S hBe hzR hlamR

/-- **An actual support triangle at `p` from the tame quotient model** (tex 4157–4194,
4176–4184): for the actual complexes, a block-complex model of `C_P`, a retraction of the quotient
complex onto the two singular blocks at the leaf's values (from the tame local model, lane RC31's
PRINT `TameLocalModelPrint`), the norm identity `hzR` and the functional relation `hlamR`, the
support triangle `SupportTriangle.ofTwoSing` is a `SupportTriangleAt` at its coordinates; the
block hypothesis is PROVED (`toMatrix_twoSing`). Kind: PROVED. -/
theorem supportTriangleAt_of_twoSing {p : ℕ} {CP CR : GCx FracLam}
    (E : ZInQ.Manuscript.RC.Limits.SplitInclusion CP CR) (D : ClearingComplex.BlockComplex FracLam)
    (R : ZInQ.Manuscript.RC.Limits.GRetract CP D.toGCx)
    (RQ : ZInQ.Manuscript.RC.Limits.GRetract E.quotientCx
      (ZInQ.Manuscript.RC.Local.twoSingCx ((frobMat C p).map zTwoToF) p
        (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))))
    (zR : CR.X 1) (hzR0 : CR.d 1 2 rfl zR = 0) (zP : CP.X 1) (hzP0 : CP.d 1 2 rfl zP = 0)
    (lamR : CR.X 2 →ₗ[FracLam] FracLam) (hlamR0 : lamR ∘ₗ CR.d 1 2 rfl = 0)
    (lamP : CP.X 2 →ₗ[FracLam] FracLam) (hlamP0 : lamP ∘ₗ CP.d 1 2 rfl = 0)
    (hzR : ∃ b : CR.X 0, zR = eF ℓ Fam x p • E.i.f 1 1 rfl zP + CR.d 0 1 rfl b)
    (hlamR : lamR ∘ₗ E.i.f 2 2 rfl = eF ℓ Fam x p • lamP) :
    SupportTriangleAt C Fam x p
      (SupportTriangle.ofTwoSing _ p _ _ E D R RQ zR hzR0 zP hzP0 lamR hlamR0 lamP
        hlamP0).relCoord
      (SupportTriangle.ofTwoSing _ p _ _ E D R RQ zR hzR0 zP hzP0 lamR hlamR0 lamP
        hlamP0).primCoord :=
  ⟨_, ⟨Equiv.refl _, (toMatrix_twoSing _ p _ _).trans (submatrix_id_id _).symm⟩, hzR, hlamR,
    rfl, rfl⟩

end Leaf

/-- **The common-coordinate triangles from the actual support triangles** (tex 4142–4194):
the graph primes are good odd primes, one coordinate `u T ∈ F` per support `T ⊆ U_x` with the
primitive and corrected expansions of the leaf, and each relaxation `T → T ∪ {p}` an actual
support triangle (`SupportTriangleAt`) whose coordinates are `u (T ∪ {p})` and `u T`.

What still differs from the text (DEPARTURE, stated exactly):
* the complexes of each step are existential: `SupportTriangleAt` does not pin `C_P, C_R` to the
  genuine Selmer complexes of supports `T, T ∪ {p}` (base-changed to `F`), and abstract
  triangles realize any coordinates satisfying (4.7) at the step (`supportTriangleAt_iff_h47`,
  `CommonCoordinate10Collapse.lean`); the content of the step is in that identification;
* `u` is one number per support, so the coordinate of `C_T` in the model used as the primitive
  complex of a step out of `T` must equal its coordinate in the model used as the relaxed
  complex of a step into `T`; in the text both are the coordinate in "the original integral
  determinant bases", and the comparison of the retained models is a product of unit-disk
  determinants (tex 4185–4193);
* the arithmetic inputs of each step are explicit: `hBe` (the new block, PROVED for the tame
  quotient model, `supportTriangleAt_of_twoSing`), `hzR` (the norm identity with its retained
  boundary, the Kummer image of the split norm relation (4.1)) and `hlamR` (the functional
  relation, from the retained pairing). Kind: definition (data). -/
structure CommonCoordinateTrianglesST {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ))
    (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) : Type where
  /-- the graph primes are odd primes (tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are primes of good reduction of `E_ℓ` (tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the coordinates `u T ∈ F` relaxed at `T ⊆ U` (tex 3877–3892, 4159–4188) -/
  u : Finset ℕ → FracLam
  /-- the primitive coordinate is regular with `t`-expansion `u_{prim,x}` (tex 4153) -/
  hprim : IsTExpansion (u ∅) (D.uPrim Fam x)
  /-- each relaxation is an actual support triangle (tex 4157–4194) -/
  hstep : ∀ T ⊆ unusedAt Fam x, ∀ p ∈ unusedAt Fam x, p ∉ T →
    SupportTriangleAt C Fam x p (u (insert p T)) (u T)
  /-- the corrected coordinate `η_x u_{rel,x}` has `t`-expansion `ũ_x` (tex 4150–4151) -/
  htilde : IsTExpansion (etaF ℓ Fam x * u (unusedAt Fam x)) (D.uTilde Fam x)

/-- **The current leaf's triangles from the actual support triangles** (tex 4142–4194): the step
field is `naturalStep_leaf_of_supportTriangle`, with step units `ε_p = p⁻⁴`. Kind: PROVED
(definition with PROVED fields). -/
def CommonCoordinateTrianglesST.toLF {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)}
    {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b} (h : CommonCoordinateTrianglesST C D Fam x) :
    CommonCoordinateTrianglesLF C D Fam x where
  hgood := h.hgood
  u := h.u
  hprim := h.hprim
  eps := fun _ p => (p : FracLam)⁻¹ ^ 4 * 1
  hstep := fun T hT p hp hpT => by
    have hpQ : p ∈ Fam.Q := (mem_unusedAt.mp hp).1
    obtain ⟨hpr, hp2⟩ := h.hprime p hpQ
    obtain ⟨ha, hd⟩ := leafFr_trace_det C hpr hp2 (h.hgood p hpQ)
    exact naturalStep_of_kmStep (mul_inv_cancel₀ (natCast_ne_zero_F hpr.ne_zero)) ha hd
      (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2 (h.hgood p hpQ))
      ((h.hstep T hT p hp hpT).kmStep C Fam x hpr hp2 (h.hgood p hpQ))
  htilde := h.htilde

/-- **The common-coordinate inputs from the actual support triangles** (definition): `E_ℓ`
elliptic, a coefficient datum, and at every address of every final family the triangles of
`CommonCoordinateTrianglesST`. -/
def CommonCoordinateInputsST {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateTrianglesST ℓ hE C D F x)

/-- **The current leaf from the actual support triangles** (PROVED). -/
theorem commonCoordinateInputsNF_of_ST {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsST D) :
    CommonCoordinateInputsNF D := by
  obtain ⟨hE, C, hT⟩ := h
  exact ⟨hE, C, fun Co Ce F hF x => (hT Co Ce F hF x).map fun t => t.toLF⟩

/-- **(4.7) from the actual support triangles** (PROVED). -/
theorem commonCoordinateTarget_of_ST {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsST D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_ST h)

end ZInQ.Manuscript.RC.Wiring
