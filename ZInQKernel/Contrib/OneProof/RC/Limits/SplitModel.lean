import ZInQKernel.Contrib.OneProof.RC.Limits.FieldModel
import ZInQKernel.Contrib.OneProof.RC.Limits.TriangularModel

/-!
# Lane RC31, round 4: the model of the relaxed complex from a split inclusion

Manuscript `diophantine_zq.tex`, the graded model of the support triangle (5.6) (tex 5398–5403:
"the graded model of (5.6) is `C_old ⊕ ⊕_q Q_q` with an upper triangular differential").

For a degreewise split inclusion `E : C_P ⊂ C_R` (with complements `Q`, `SplitInclusion`) and a
normalized graded deformation retract `R` of `C_P` onto a model `Y`, the relaxed complex `C_R`
retracts onto the triangular extension `Y ⊕ Q` with differential `(y, q) ↦ (d y + p (∗ q), d_Q q)`
(`splitRetract`): the triangular extension's retract (`GRetract.triExt`) transported along the
block coordinates `C_P ⊕ Q ≃ C_R` (`GRetract.ofEquiv`). In particular `C_R` is homotopy equivalent
to the model (`GRetract.homotopyEquiv`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable {A : Type} [CommRing A]

/-- The inverse of a degreewise equivalence of complexes commutes with the differentials.
(tex 5398–5403) Kind: PROVED. -/
theorem equiv_symm_d {X X' : GCx A} (e : ∀ n, X.X n ≃ₗ[A] X'.X n)
    (he : ∀ a b (h : a + 1 = b) (x : X.X a), X'.d a b h (e a x) = e b (X.d a b h x))
    (a b : ℤ) (h : a + 1 = b) (x' : X'.X a) :
    (e b).symm (X'.d a b h x') = X.d a b h ((e a).symm x') := by
  rw [LinearEquiv.symm_apply_eq, ← he, LinearEquiv.apply_symm_apply]

/-- **Transport of a retract along a degreewise equivalence of complexes** (tex 5398–5403):
inclusion `e ∘ i`, projection `p ∘ e⁻¹`, homotopy `e ∘ h ∘ e⁻¹`. Kind: definition (PROVED
identities). -/
def GRetract.ofEquiv {X X' Y : GCx A} (R : GRetract X Y) (e : ∀ n, X.X n ≃ₗ[A] X'.X n)
    (he : ∀ a b (h : a + 1 = b) (x : X.X a), X'.d a b h (e a x) = e b (X.d a b h x)) :
    GRetract X' Y where
  i :=
    { f := fun a b h => by
        subst h
        exact (e a).toLinearMap ∘ₗ R.i.f a a rfl
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj y
        subst hij hj h₁
        change e (i + 1) (R.i.f (i + 1) (i + 1) rfl (Y.d i (i + 1) rfl y)) =
          X'.d i (i + 1) rfl (e i (R.i.f i i rfl y))
        rw [he, R.i_d] }
  p :=
    { f := fun a b h => by
        subst h
        exact R.p.f a a rfl ∘ₗ (e a).symm.toLinearMap
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj x'
        subst hij hj h₁
        change R.p.f (i + 1) (i + 1) rfl ((e (i + 1)).symm (X'.d i (i + 1) rfl x')) =
          Y.d i (i + 1) rfl (R.p.f i i rfl ((e i).symm x'))
        rw [equiv_symm_d e he, R.p_d] }
  h a b hab := (e b).toLinearMap ∘ₗ R.h a b hab ∘ₗ (e a).symm.toLinearMap
  p_i n y := by
    change R.p.f n n rfl ((e n).symm (e n (R.i.f n n rfl y))) = y
    rw [LinearEquiv.symm_apply_apply, R.p_i]
  homotopy n x' := by
    change x' - e n (R.i.f n n rfl (R.p.f n n rfl ((e n).symm x'))) =
      X'.d (n - 1) n (by omega) (e (n - 1) (R.h n (n - 1) (by omega) ((e n).symm x'))) +
        e n (R.h (n + 1) n rfl ((e (n + 1)).symm (X'.d n (n + 1) rfl x')))
    have hx := R.homotopy n ((e n).symm x')
    rw [he, equiv_symm_d e he, ← map_add, ← hx, map_sub, LinearEquiv.apply_symm_apply]
  h_h a b c hab hbc x' := by
    change e c (R.h b c hbc ((e b).symm (e b (R.h a b hab ((e a).symm x'))))) = 0
    rw [LinearEquiv.symm_apply_apply, R.h_h, map_zero]
  h_i a b hab y := by
    change e b (R.h a b hab ((e a).symm (e a (R.i.f a a rfl y)))) = 0
    rw [LinearEquiv.symm_apply_apply, R.h_i, map_zero]
  p_h a b hab x' := by
    change R.p.f b b rfl ((e b).symm (e b (R.h a b hab ((e a).symm x')))) = 0
    rw [LinearEquiv.symm_apply_apply, R.p_h]

variable {CP CR Y : GCx A} (E : SplitInclusion CP CR) (R : GRetract CP Y)

/-- The off-diagonal block of a split inclusion satisfies `d ∗ + ∗ d_Q = 0`. (tex 5398–5403)
Kind: PROVED. -/
theorem SplitInclusion.offDiag_sq (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c)
    (q : E.quotientCx.X a) :
    CP.d b c hbc (E.offDiag a b hab q) + E.offDiag b c hbc (E.quotientCx.d a b hab q) = 0 :=
  E.d_offDiag_add_offDiag_dQ a b c hab hbc q

/-- **The model of the relaxed complex** (tex 5398–5403): a split inclusion `C_P ⊂ C_R` and a
retract of `C_P` onto `Y` give a normalized graded deformation retract of `C_R` onto the
triangular extension `Y ⊕ Q` with differential `(y, q) ↦ (d y + p (∗ q), d_Q q)`.
Kind: definition (PROVED identities). -/
def splitRetract :
    GRetract CR (triCx Y E.quotientCx (R.pδ (Q := E.quotientCx) E.offDiag)
      (R.pδ_sq (Q := E.quotientCx) E.offDiag E.offDiag_sq)) :=
  (R.triExt (Q := E.quotientCx) E.offDiag E.offDiag_sq).ofEquiv (fun n => E.blockEquiv n)
    (fun a b h z => by
      obtain ⟨x, q⟩ := z
      exact E.d_blockEquiv a b h x q)

/-- The relaxed complex is homotopy equivalent to its triangular model. (tex 5398–5403)
Kind: definition. -/
def splitHomotopyEquiv :
    HomotopyEquiv (triCx Y E.quotientCx (R.pδ (Q := E.quotientCx) E.offDiag)
      (R.pδ_sq (Q := E.quotientCx) E.offDiag E.offDiag_sq)).toCC CR.toCC :=
  (splitRetract E R).homotopyEquiv

/-- **Non-vacuity**: over a field every complex has a split inclusion into itself and the
corresponding triangular model retract (tex 5398–5403). Kind: PROVED. -/
theorem splitRetract_nonvacuous {F : Type} [Field F] (X : GCx F) :
    ∃ E : SplitInclusion X X, Nonempty (GRetract X (triCx X E.quotientCx
      ((GRetract.refl X).pδ (Q := E.quotientCx) E.offDiag)
      ((GRetract.refl X).pδ_sq (Q := E.quotientCx) E.offDiag E.offDiag_sq))) := by
  obtain ⟨E, -⟩ := exists_splitInclusion (gHomId X) (fun n => Function.injective_id)
  exact ⟨E, ⟨splitRetract E (GRetract.refl X)⟩⟩

end ZInQ.Manuscript.RC.Limits
