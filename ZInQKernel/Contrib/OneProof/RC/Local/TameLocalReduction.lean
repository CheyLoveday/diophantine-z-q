import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalPrint
import ZInQKernel.Contrib.OneProof.RC.Limits.FieldQuasiIso

/-!
# Lane RC31, round 5: from two quasi-isomorphisms to a tame local model, over a field

Manuscript `diophantine_zq.tex`, tex 3470–3480 ((4.4)), consumed at tex 4176–4184 and 5317–5322.

Over a field `k`, a tame local model `TameLocalModelAt Lq Uq ιq T` (`TameLocalPrint.lean`)
follows from two QUASI-isomorphisms `φL : L_q → T.L_q`, `φU : U_q → T.U_q` from the genuine
complexes to the model, strictly compatible with the inclusions: bounded-below complexes of
vector spaces are K-injective, so quasi-isomorphisms between them are homotopy equivalences
(`homotopyEquiv_of_quasiIso_field`). The same data gives the reverse form, model to genuine:
quasi-isomorphisms `T.L_q → L_q`, `T.U_q → U_q` with a homotopy between the two composites.

* `cx3_toCC_isStrictlyGE`, `tameNewPlace_Lq_isStrictlyGE`, `tameNewPlace_Uq_isStrictlyGE`: the
  model complexes vanish in negative degrees.
* `tameLocalModelAt_of_quasiIso`: the reduction (PROVED).
* `tameLocalModel_reverse_of_quasiIso`: the reverse form (PROVED).

So over a field the remaining content of `TameLocalModelPrint` is: the comparison of the genuine
cochains with the model is a quasi-isomorphism, compatibly with the unramified condition.
`TameFreeModelCochains.lean` builds the comparison map for Iwasawa generators and proves the
bijections in degrees zero and one; degrees two and higher remain the literature input.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Limits

variable {A : Type} [CommRing A]

/-- **The three-term complexes vanish in negative degrees** (tex 3470–3474). Kind: PROVED. -/
theorem cx3_toCC_isStrictlyGE {X0 X1 X2 : Type} [AddCommGroup X0] [Module A X0]
    [AddCommGroup X1] [Module A X1] [AddCommGroup X2] [Module A X2] (d0 : X0 →ₗ[A] X1)
    (d1 : X1 →ₗ[A] X2) (h : ∀ x, d1 (d0 x) = 0) : (cx3 d0 d1 h).toCC.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rcases i with n | m
  · rw [Int.ofNat_eq_natCast] at hi
    omega
  · have : Subsingleton ((cx3 d0 d1 h).toCC.X (Int.negSucc m)) :=
      inferInstanceAs (Subsingleton PUnit)
    exact ModuleCat.isZero_of_subsingleton _

/-- The full complex of the tame model vanishes in negative degrees (tex 3470–3480). Kind:
PROVED. -/
theorem tameNewPlace_Lq_isStrictlyGE (Mq : ModuleCat.{0} A) (Φ : Mq →ₗ[A] Mq) (q : ℕ)
    (hq : Odd q) : (tameNewPlace Mq Φ q hq).Lq.toCC.IsStrictlyGE 0 :=
  cx3_toCC_isStrictlyGE _ _ (freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq))

/-- The unramified complex of the tame model vanishes in negative degrees (tex 3478–3480). Kind:
PROVED. -/
theorem tameNewPlace_Uq_isStrictlyGE (Mq : ModuleCat.{0} A) (Φ : Mq →ₗ[A] Mq) (q : ℕ)
    (hq : Odd q) : (tameNewPlace Mq Φ q hq).Uq.toCC.IsStrictlyGE 0 :=
  cx3_toCC_isStrictlyGE (frobOne Φ) (0 : Mq →ₗ[A] PUnit) (fun _ => rfl)

/-- **A tame local model from two quasi-isomorphisms, over a field** (tex 3470–3480): chain maps
`φL : L_q → T.L_q` and `φU : U_q → T.U_q` that are quasi-isomorphisms and strictly compatible
with the inclusions `ι_q`, `T.ι_q` give a `TameLocalModelAt` with `eL.hom = φL`, `eU.hom = φU`,
when all four complexes vanish in negative degrees. Kind: PROVED. -/
theorem tameLocalModelAt_of_quasiIso {k : Type} [Field k] {Lq Uq : GCx k} {ιq : GHom Uq Lq}
    {T : UnramifiedNewPlace k} [Lq.toCC.IsStrictlyGE 0] [Uq.toCC.IsStrictlyGE 0]
    [T.Lq.toCC.IsStrictlyGE 0] [T.Uq.toCC.IsStrictlyGE 0]
    (φL : Lq.toCC ⟶ T.Lq.toCC) (φU : Uq.toCC ⟶ T.Uq.toCC) [QuasiIso φL] [QuasiIso φU]
    (hsq : GHom.toCC ιq ≫ φL = φU ≫ GHom.toCC T.ιq) :
    ∃ m : TameLocalModelAt Lq Uq ιq T, m.eL.hom = φL ∧ m.eU.hom = φU := by
  obtain ⟨eL, heL⟩ := homotopyEquiv_of_quasiIso_field 0 φL
  obtain ⟨eU, heU⟩ := homotopyEquiv_of_quasiIso_field 0 φU
  refine ⟨⟨eL, eU, Homotopy.ofEq ?_⟩, heL, heU⟩
  rw [heL, heU]
  exact hsq

/-- **The reverse form, model to genuine** (tex 3470–3480): under the hypotheses of
`tameLocalModelAt_of_quasiIso`, there are quasi-isomorphisms `ψL : T.L_q → L_q`,
`ψU : T.U_q → U_q` with a homotopy `T.ι_q ≫ ψL ∼ ψU ≫ ι_q`. Kind: PROVED. -/
theorem tameLocalModel_reverse_of_quasiIso {k : Type} [Field k] {Lq Uq : GCx k}
    {ιq : GHom Uq Lq} {T : UnramifiedNewPlace k} [Lq.toCC.IsStrictlyGE 0]
    [Uq.toCC.IsStrictlyGE 0] [T.Lq.toCC.IsStrictlyGE 0] [T.Uq.toCC.IsStrictlyGE 0]
    (φL : Lq.toCC ⟶ T.Lq.toCC) (φU : Uq.toCC ⟶ T.Uq.toCC) [QuasiIso φL] [QuasiIso φU]
    (hsq : GHom.toCC ιq ≫ φL = φU ≫ GHom.toCC T.ιq) :
    ∃ (ψL : T.Lq.toCC ⟶ Lq.toCC) (ψU : T.Uq.toCC ⟶ Uq.toCC), QuasiIso ψL ∧ QuasiIso ψU ∧
      Nonempty (Homotopy (GHom.toCC T.ιq ≫ ψL) (ψU ≫ GHom.toCC ιq)) := by
  obtain ⟨eL, heL⟩ := homotopyEquiv_of_quasiIso_field 0 φL
  obtain ⟨eU, heU⟩ := homotopyEquiv_of_quasiIso_field 0 φU
  have hsq' : GHom.toCC ιq ≫ eL.hom = eU.hom ≫ GHom.toCC T.ιq := by
    rw [heL, heU]
    exact hsq
  exact ⟨eL.inv, eU.inv, inferInstance, inferInstance,
    ⟨(HomotopyEquiv.inv_comp_homotopy eL eU (GHom.toCC ιq) (GHom.toCC T.ιq) hsq').symm⟩⟩

end ZInQ.Manuscript.RC.Local
