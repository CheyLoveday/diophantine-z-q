import ZInQKernel.Contrib.OneProof.RC.Local.TwoPlaceSplitBlock
import ZInQKernel.Contrib.OneProof.RC.Limits.TriangularModel2
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionOld
import ZInQKernel.Contrib.OneProof.RC.Limits.SDRRetract
import ZInQKernel.Contrib.OneProof.RC.Local.TameUnramifiedSquare

/-!
# Lane RC31, round 6: the two-place block is an integral invariant, not a field invariant

Manuscript `diophantine_zq.tex`, tex 4176–4184 ((4.7): the quotient determinants
`δ_q = det(zFr_q − q) · det(z⁻¹Fr_q − q)`), tex 3478–3480 (the singular quotient `[Φ − q]`),
tex 5398–5424 (the triangular model).

The block `B` of the new summands enters the support triangle only through its class up to
changes of basis in degrees one and two: a retract onto `[N --B--> N]` and an equivalence
`[N --B--> N] ≅ [N --B'--> N]` (that is `B' = e₂ B e₁⁻¹`) give a retract onto `[N --B'--> N]`
(`GRetract.ofEquivTarget`, `retract_blockCx_change`). Consequently:

* over a FIELD every invertible block is equivalent to every other (`blockCx_equiv_of_isUnit`,
  `retract_blockCx_of_isUnit`): when `l_q ≠ 0` the two-place block is invertible over `Frac Λ`,
  so a retract onto the two singular blocks with block `twoPlaceBlock F q z z⁻¹` exists as soon as
  one onto ANY invertible block does, and the block hypothesis `hBe` read over the field alone
  carries no arithmetic content;
* over the INTEGRAL coefficients only the class of `B` under `B ↦ e₂ B e₁⁻¹` is determined, so
  `det B` is determined up to a unit (`det_eq_unit_mul_of_equiv`), which is exactly the
  precision of (4.7) (`δ_q = q⁴ l_q` up to `Λ^×`).

So the consumer of `twoPiece_hBe` (the torsion-level step `KmStep`, through the support triangle)
must take the full-condition complex as the base change to the field of an integral triangular
model whose quotient block is the two singular blocks of the tame models at `w`, `w̄`
(`fullPre_map_hBe`: the block hypothesis passes to the base change, through
`twoPlaceBlock_map`).

The normalization at one place, over a field (`exists_retract_tameModel_field`): if the
comparison `tameCochainMap` is a quasi-isomorphism and surjective in every degree, the genuine
local complex retracts onto the tame model with projection the comparison
(`exists_retract_of_surjective_quasiIso_field`: a strict section and the Lambe–Stasheff
normalization `GRetract.ofDeformation`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.Limits

variable {A : Type} [CommRing A]

/-! ### Retracts along an equivalence of the target -/

/-- **A retract transported along an equivalence of its target** (tex 4423–4437): from
`R : X → Y` and a degreewise equivalence `e : Y ≅ Y'` of complexes, the retract `X → Y'` with
inclusion `i e⁻¹`, projection `e p` and the same homotopy. Kind: definition (PROVED identities). -/
def GRetract.ofEquivTarget {X Y Y' : GCx A} (R : GRetract X Y) (e : ∀ n, Y.X n ≃ₗ[A] Y'.X n)
    (he : ∀ a b (h : a + 1 = b) (y : Y.X a), Y'.d a b h (e a y) = e b (Y.d a b h y)) :
    GRetract X Y' where
  i :=
    { f := fun a b h => by
        subst h
        exact R.i.f a a rfl ∘ₗ (e a).symm.toLinearMap
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj y
        subst hij hj h₁
        have hs : (e (i + 1)).symm (Y'.d i (i + 1) rfl y) = Y.d i (i + 1) rfl ((e i).symm y) := by
          rw [LinearEquiv.symm_apply_eq, ← he, LinearEquiv.apply_symm_apply]
        change R.i.f (i + 1) (i + 1) rfl ((e (i + 1)).symm (Y'.d i (i + 1) rfl y)) =
          X.d i (i + 1) rfl (R.i.f i i rfl ((e i).symm y))
        rw [hs, R.i_d] }
  p :=
    { f := fun a b h => by
        subst h
        exact (e a).toLinearMap ∘ₗ R.p.f a a rfl
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj x
        subst hij hj h₁
        change e (i + 1) (R.p.f (i + 1) (i + 1) rfl (X.d i (i + 1) rfl x)) =
          Y'.d i (i + 1) rfl (e i (R.p.f i i rfl x))
        rw [he, R.p_d] }
  h := R.h
  p_i n y := by
    change e n (R.p.f n n rfl (R.i.f n n rfl ((e n).symm y))) = y
    rw [R.p_i, LinearEquiv.apply_symm_apply]
  homotopy n x := by
    change x - R.i.f n n rfl ((e n).symm (e n (R.p.f n n rfl x))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact R.homotopy n x
  h_h := R.h_h
  h_i a b hab y := R.h_i a b hab _
  p_h a b hab x := by
    change e b (R.p.f b b rfl (R.h a b hab x)) = 0
    rw [R.p_h, map_zero]

/-! ### Two-term blocks -/

variable {M : Type} [AddCommGroup M] [Module A M]

/-- **The block complex** `[M --B--> M]` in degrees one and two (tex 3478–3480; the singular
quotient `singCx Φ q` is `blockCx (Φ − q)`). Kind: definition. -/
def blockCx (B : M →ₗ[A] M) : GCx A :=
  cx3 (0 : PUnit →ₗ[A] M) B (fun _ => by simp)

/-- The singular block is the block complex of `Φ − q`. Kind: PROVED (definitional). -/
theorem singCx_eq_blockCx (Φ : M →ₗ[A] M) (q : ℕ) : singCx Φ q = blockCx (frobQ Φ q) :=
  rfl

/-- The degreewise equivalence of two block complexes given by `e₁`, `e₂` in degrees one and
two (and the identity elsewhere). Kind: definition. -/
def blockEquivF (e₁ e₂ : M ≃ₗ[A] M) :
    ∀ n : ℤ, cx3X (A := A) PUnit M M n ≃ₗ[A] cx3X (A := A) PUnit M M n
  | .ofNat 1 => e₁
  | .ofNat 2 => e₂
  | _ => LinearEquiv.refl A _

/-- **Equivalent blocks give equivalent complexes** (tex 3478–3480): if `B' e₁ = e₂ B`, then
`e₁`, `e₂` form an equivalence `[M --B--> M] ≅ [M --B'--> M]`. Kind: PROVED. -/
theorem blockEquivF_comm (B B' : M →ₗ[A] M) (e₁ e₂ : M ≃ₗ[A] M)
    (hB : ∀ x, B' (e₁ x) = e₂ (B x)) (a b : ℤ) (h : a + 1 = b) (y : (blockCx B).X a) :
    (blockCx B').d a b h (blockEquivF e₁ e₂ a y) = blockEquivF e₁ e₂ b ((blockCx B).d a b h y) := by
  by_cases h0 : a = 0
  · subst h0
    obtain rfl : b = 1 := by omega
    change (0 : M) = e₁ 0
    rw [map_zero]
  · by_cases h1 : a = 1
    · subst h1
      obtain rfl : b = 2 := by omega
      exact hB y
    · have z1 : cx3D (0 : PUnit →ₗ[A] M) B' a b h = 0 := cx3D_eq_zero _ _ a b h h0 h1
      have z2 : cx3D (0 : PUnit →ₗ[A] M) B a b h = 0 := cx3D_eq_zero _ _ a b h h0 h1
      change cx3D (0 : PUnit →ₗ[A] M) B' a b h (blockEquivF e₁ e₂ a y) =
        blockEquivF e₁ e₂ b (cx3D (0 : PUnit →ₗ[A] M) B a b h y)
      rw [z1, z2]
      exact (map_zero (blockEquivF e₁ e₂ b)).symm

/-- **Changing the block of a retract** (tex 4423–4437, 5398–5424): a retract onto
`[M --B--> M]` gives a retract onto `[M --B'--> M]` whenever `B' = e₂ B e₁⁻¹`. Kind: PROVED. -/
theorem retract_blockCx_change {X : GCx A} (B B' : M →ₗ[A] M) (R : GRetract X (blockCx B))
    (e₁ e₂ : M ≃ₗ[A] M) (hB : ∀ x, B' (e₁ x) = e₂ (B x)) : Nonempty (GRetract X (blockCx B')) :=
  ⟨GRetract.ofEquivTarget R (blockEquivF e₁ e₂) (blockEquivF_comm B B' e₁ e₂ hB)⟩

/-- **Over a field all invertible blocks are equivalent** (tex 4176–4184): for invertible
`B`, `B'`, `B' ∘ 1 = (B' B⁻¹) ∘ B`. Kind: PROVED. -/
theorem blockCx_equiv_of_isUnit (B B' : M ≃ₗ[A] M) :
    ∀ x, B'.toLinearMap (LinearEquiv.refl A M x) = (B.symm.trans B') (B.toLinearMap x) := by
  intro x
  change B' x = B' (B.symm (B x))
  rw [LinearEquiv.symm_apply_apply]

/-- **The integral caveat, over a field** (tex 4176–4184): a retract onto a block complex with
an invertible block gives one onto the block complex of ANY invertible block. In particular, when
`l_q ≠ 0` the two-place block `twoPlaceBlock F q z z⁻¹` is invertible over `Frac Λ`, and a retract
onto it is no more information than a retract onto any other invertible block. Kind: PROVED. -/
theorem retract_blockCx_of_isUnit {X : GCx A} (B B' : M ≃ₗ[A] M)
    (R : GRetract X (blockCx B.toLinearMap)) : Nonempty (GRetract X (blockCx B'.toLinearMap)) :=
  retract_blockCx_change B.toLinearMap B'.toLinearMap R (LinearEquiv.refl A M) (B.symm.trans B')
    (blockCx_equiv_of_isUnit B B')

/-- **The integral invariant** (tex 4176–4184): equivalent blocks over the integral coefficients
have the same determinant up to a unit, `det B' = det e₂ · det B · (det e₁)⁻¹`. Kind: PROVED. -/
theorem det_eq_unit_mul_of_equiv {N : Type} [Fintype N] [DecidableEq N]
    (B B' : Matrix N N A) (e₁ e₂ : (Matrix N N A)ˣ)
    (hB : B' * (e₁ : Matrix N N A) = (e₂ : Matrix N N A) * B) :
    ∃ u : Aˣ, B'.det = (u : A) * B.det := by
  refine ⟨(Matrix.GeneralLinearGroup.det e₂) * (Matrix.GeneralLinearGroup.det e₁)⁻¹, ?_⟩
  have h := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hu : (e₁ : Matrix N N A).det * ((Matrix.GeneralLinearGroup.det e₁)⁻¹ : Aˣ) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]
  calc B'.det =
        B'.det * ((e₁ : Matrix N N A).det * ((Matrix.GeneralLinearGroup.det e₁)⁻¹ : Aˣ)) := by
        rw [hu, mul_one]
    _ = (e₂ : Matrix N N A).det * B.det * ((Matrix.GeneralLinearGroup.det e₁)⁻¹ : Aˣ) := by
        rw [← mul_assoc, h]
    _ = _ := by
        rw [Units.val_mul, ← Matrix.GeneralLinearGroup.val_det_apply]
        ring

/-! ### The integral reading of the block hypothesis -/

/-- **The block hypothesis is read on the integral model** (tex 4176–4184): the block hypothesis
`hBe` of an integral full-condition complex (for instance the one of `twoPiece_hBe` over `Λ` or a
stage ring) passes to its base change along any ring map, with the block `twoPlaceBlock` of the
images (`twoPlaceBlock_map`). Kind: PROVED. -/
theorem fullPre_map_hBe {S S' : Type} [CommRing S] [CommRing S']
    (C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex S) (f : S →+* S')
    (F : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S)
    (h : ∃ e : C.N ≃ Fin 2 ⊕ Fin 2,
      C.B = (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F (q : S) z zi).submatrix e
        e) :
    ∃ e : (C.map f).N ≃ Fin 2 ⊕ Fin 2, (C.map f).B =
      (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock (F.map f) (q : S') (f z)
        (f zi)).submatrix e e := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  change C.B.map f = _
  rw [he, ← Matrix.submatrix_map, twoPlaceBlock_map]
  rfl

/-! ### The normalization at one place, over a field -/

section Normalize

open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- **A retract of the genuine local complex onto the tame model, over a field**
(tex 3470–3480, 4423–4437): if the comparison `tameCochainMap` (at `g = 1`) is a
quasi-isomorphism and surjective in every degree, the genuine local complex retracts onto the
tame free model with projection the comparison itself (strict section and Lambe–Stasheff
normalization, `exists_retract_of_surjective_quasiIso_field`). Kind: PROVED. -/
theorem exists_retract_tameModel_field (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ id_invol
      (comm_id Φ) hrel)))
    (hsurj : ∀ n, Function.Surjective ((tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ id_invol
      (comm_id Φ) hrel).f n n rfl)) :
    ∃ R : GRetract (natCx (contCochains k G M)) (tameFreeModel1 Φ q hq),
      ∀ n x, R.p.f n n rfl x =
        (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ id_invol (comm_id Φ) hrel).f n n rfl x := by
  have : (natCx (contCochains k G M)).toCC.IsStrictlyGE 0 :=
    ZInQ.Manuscript.RC.Limits.natCx_toCC_isStrictlyGE _
  have : (tameFreeModel1 Φ q hq).toCC.IsStrictlyGE 0 :=
    cx3_toCC_isStrictlyGE _ _ (freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq))
  exact exists_retract_of_surjective_quasiIso_field 0 _ hsurj

end Normalize

end ZInQ.Manuscript.RC.Local
