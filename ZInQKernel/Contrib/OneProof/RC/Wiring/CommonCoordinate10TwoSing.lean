import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Step
import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModel

/-!
# The new block from the tame local model: `hBe` is a theorem for `Q' = twoSingCx`

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4176–4184: the
singular quotient `[Φ − q]` in degrees one and two at the two conjugate places above an unused
split prime, `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q)`), with the tame local model (4.4).

When the quotient complex of the support triangle is retracted onto lane RC31's two singular
blocks `twoSingCx Fr q z z⁻¹` (`[M --zFr−q--> M] ⊕ [M --z⁻¹Fr−q--> M]`, `M = F²`, in degrees one
and two), the block hypothesis `hBe` of `kmStep_of_supportTriangle` holds in the coordinates of
the two places:

* `twoSingB1`, `twoSingB2`: the bases of degrees one and two, the standard bases carried by
  `twoPlaceCoord`;
* `toMatrix_twoSing`: the matrix of the differential in these bases is `twoPlaceBlock`
  (from lane RC31's `twoSingD12_eq` and `twoSing_matrix`);
* `SupportTriangle.ofTwoSing`: the support triangle with `Q' = twoSingCx`;
* **`kmStep_of_twoSing`**: the step is a `KmStep` at the coordinates of the models, from the
  actual complexes, the retraction `R_Q` of the quotient onto `twoSingCx` (supplied by the tame
  local model, lane RC31's PRINT `TameLocalModelPrint`), the norm identity `hzR`, the functional
  relation `hlamR` and the unit condition; `hBe` is PROVED.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)
open ZInQ.Manuscript.RC.Local (twoSingCx twoSingD12 twoPlaceCoord twoSingD12_eq twoSing_matrix)

section TwoSing

variable {F : Type} [Field F] (Fr : Matrix (Fin 2) (Fin 2) F) (q : ℕ) (z zi : F)

/-- The basis of degree one of the two singular blocks: the coordinates of the two places
(tex 4176–4184). Kind: definition. -/
abbrev twoSingB1 : Basis (Fin 2 ⊕ Fin 2) F ((twoSingCx Fr q z zi).X 1) :=
  (Pi.basisFun F (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := F))

/-- The basis of degree two of the two singular blocks (tex 4176–4184). Kind: definition. -/
abbrev twoSingB2 : Basis (Fin 2 ⊕ Fin 2) F ((twoSingCx Fr q z zi).X 2) :=
  (Pi.basisFun F (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := F))

/-- **The matrix of the two singular blocks is the two-place block** (tex 4176–4184): in the
coordinates of the two places, the differential of `twoSingCx Fr q z z⁻¹` from degree one to
degree two has matrix `twoPlaceBlock Fr q z z⁻¹ = diag(z Fr − q, z⁻¹ Fr − q)`. Kind: PROVED. -/
theorem toMatrix_twoSing :
    LinearMap.toMatrix (twoSingB1 Fr q z zi) (twoSingB2 Fr q z zi)
        ((twoSingCx Fr q z zi).d 1 2 rfl) = twoPlaceBlock Fr (q : F) z zi := by
  rw [← twoSing_matrix Fr q z zi]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply]
  have hb1 : (twoSingB1 Fr q z zi) j =
      (twoPlaceCoord (A := F) (Pi.single j 1) : (twoSingCx Fr q z zi).X 1) := by
    change ((Pi.basisFun F (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := F))) j = _
    rw [Basis.map_apply, Pi.basisFun_apply]
  have hrepr : ∀ x : (Fin 2 → F) × (Fin 2 → F),
      ((Pi.basisFun F (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := F))).repr x i =
        (twoPlaceCoord (A := F)).symm x i := fun x => by
    rw [Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr]
  rw [hb1]
  refine (hrepr _).trans ?_
  have e2 := congrArg (twoPlaceCoord (A := F)).symm (twoSingD12_eq Fr q z zi (Pi.single j 1))
  rw [LinearEquiv.symm_apply_apply] at e2
  exact congrFun e2.symm i

/-- The two singular blocks vanish outside degrees one and two (tex 4176–4184).
Kind: PROVED. -/
theorem twoSing_subsingleton (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((twoSingCx Fr q z zi).X n) := by
  have h : ∀ (Φ : (Fin 2 → F) →ₗ[F] (Fin 2 → F)),
      Subsingleton ((ZInQ.Manuscript.RC.Local.singCx Φ q).X n) := fun Φ => by
    rcases n with (_ | _ | _ | n) | n
    · exact inferInstanceAs (Subsingleton PUnit)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact inferInstanceAs (Subsingleton PUnit)
    · exact inferInstanceAs (Subsingleton PUnit)
  change Subsingleton ((ZInQ.Manuscript.RC.Local.singCx (Matrix.toLin' (z • Fr)) q).X n ×
    (ZInQ.Manuscript.RC.Local.singCx (Matrix.toLin' (zi • Fr)) q).X n)
  infer_instance

end TwoSing

/-- **The support triangle with the tame quotient model** (tex 4157–4194, 4176–4184): the actual
complexes, the block-complex model of `C_P`, the actual classes, and a retraction of the quotient
complex onto the two singular blocks `twoSingCx Fr q z z⁻¹` with the bases of the two places.
Kind: definition. -/
def SupportTriangle.ofTwoSing {F : Type} [Field F] (Fr : Matrix (Fin 2) (Fin 2) F) (q : ℕ)
    (z zi : F) {CP CR : GCx F} (E : SplitInclusion CP CR) (D : BlockComplex F)
    (R : GRetract CP D.toGCx) (RQ : GRetract E.quotientCx (twoSingCx Fr q z zi))
    (zR : CR.X 1) (hzR : CR.d 1 2 rfl zR = 0) (zP : CP.X 1) (hzP : CP.d 1 2 rfl zP = 0)
    (lamR : CR.X 2 →ₗ[F] F) (hlamR : lamR ∘ₗ CR.d 1 2 rfl = 0) (lamP : CP.X 2 →ₗ[F] F)
    (hlamP : lamP ∘ₗ CP.d 1 2 rfl = 0) : SupportTriangle F where
  CP := CP
  CR := CR
  E := E
  D := D
  R := R
  Q' := twoSingCx Fr q z zi
  RQ := RQ
  hQ' := twoSing_subsingleton Fr q z zi
  N := Fin 2 ⊕ Fin 2
  b1 := twoSingB1 Fr q z zi
  b2 := twoSingB2 Fr q z zi
  zR := zR
  hzR := hzR
  zP := zP
  hzP := hzP
  lamR := lamR
  hlamR := hlamR
  lamP := lamP
  hlamP := hlamP

/-- **The relaxation step from the actual complexes and the tame quotient model**
(tex 4157–4194, 4176–4184, 5398–5424): for the actual primitive and relaxed complexes, a
block-complex model of `C_P`, a retraction of the quotient complex onto the two singular blocks
(supplied by the tame local model, lane RC31's PRINT `TameLocalModelPrint`), the norm identity
`hzR`, the functional relation `hlamR` and `l_q ≠ 0`, the step is a `KmStep` at the torsion
coordinates of the models; the block hypothesis `hBe` is PROVED (`toMatrix_twoSing`).
Kind: PROVED. -/
theorem kmStep_of_twoSing {F : Type} [Field F] {Fr : Matrix (Fin 2) (Fin 2) F} {q : ℕ}
    {qi a z zi : F} {CP CR : GCx F} (E : SplitInclusion CP CR) (D : BlockComplex F)
    (R : GRetract CP D.toGCx) (RQ : GRetract E.quotientCx (twoSingCx Fr q z zi))
    (zR : CR.X 1) (hzR0 : CR.d 1 2 rfl zR = 0) (zP : CP.X 1) (hzP0 : CP.d 1 2 rfl zP = 0)
    (lamR : CR.X 2 →ₗ[F] F) (hlamR0 : lamR ∘ₗ CR.d 1 2 rfl = 0) (lamP : CP.X 2 →ₗ[F] F)
    (hlamP0 : lamP ∘ₗ CP.d 1 2 rfl = 0) (hq : (q : F) * qi = 1) (ha : Fr.trace = a)
    (hd : Fr.det = q) (hl : quotientFactor Fr qi z zi ≠ 0)
    (hzR : ∃ b : CR.X 0, zR = pointFactor a z zi • E.i.f 1 1 rfl zP + CR.d 0 1 rfl b)
    (hlamR : lamR ∘ₗ E.i.f 2 2 rfl = pointFactor a z zi • lamP) :
    KmStep Fr (q : F) a z zi
      (SupportTriangle.ofTwoSing Fr q z zi E D R RQ zR hzR0 zP hzP0 lamR hlamR0 lamP
        hlamP0).relCoord
      (SupportTriangle.ofTwoSing Fr q z zi E D R RQ zR hzR0 zP hzP0 lamR hlamR0 lamP
        hlamP0).primCoord :=
  SupportTriangle.kmStep_of_supportTriangle _ hq ha hd hl
    ⟨Equiv.refl _, (toMatrix_twoSing Fr q z zi).trans (submatrix_id_id _).symm⟩ hzR hlamR

end ZInQ.Manuscript.RC.Wiring
