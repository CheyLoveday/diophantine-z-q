import ZInQKernel.Contrib.OneProof.RC.Limits.GradedTransport

/-!
# Lane RC31, round 4: the model of a triangular extension

Manuscript `diophantine_zq.tex`, the graded model of the support triangle (5.6) (tex 5398–5403:
"the graded model of (5.6) is `C_old ⊕ ⊕_q Q_q` with an upper triangular differential") and Lemma
`ex:limits-inner-limit` (tex 4423–4437: the normalized perturbation formulas).

A triangular extension `X ⊕ Q` of a complex `X` by a complex `Q` has differential
`(x, q) ↦ (d x + δ q, d q)` with `d δ + δ d = 0` (`triCx`). For a normalized graded deformation
retract `R` of `X` onto `Y`, the extension retracts onto `Y ⊕ Q` with differential
`(y, q) ↦ (d y + p δ q, d q)` (`GRetract.triExt`): inclusion `(y, q) ↦ (i y − h δ q, q)`, projection
`(x, q) ↦ (p x, q)`, homotopy `(x, q) ↦ (h x, 0)`. This is the perturbation lemma for the
off-diagonal perturbation `δ`, whose series stops after one term (`δ h δ = 0`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable {A : Type} [CommRing A]

/-- **The triangular extension** `X ⊕ Q` with differential `(x, q) ↦ (d x + δ q, d q)`, for an
off-diagonal map `δ : Qᵃ → X^{a+1}` with `d δ + δ d = 0` (tex 5398–5403). Kind: definition. -/
def triCx (X Q : GCx A) (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0) : GCx A where
  X n := ModuleCat.of A (X.X n × Q.X n)
  d a b h := (X.d a b h).coprod (δ a b h) |>.prod ((Q.d a b h).comp (LinearMap.snd A _ _))
  d_d a b c hab hbc z := by
    obtain ⟨x, q⟩ := z
    refine Prod.ext ?_ ?_
    · change X.d b c hbc (X.d a b hab x + δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0
      rw [map_add, X.d_d, zero_add, hδ]
    · exact Q.d_d a b c hab hbc q

/-- The differential of the triangular extension. (tex 5398–5403)
Kind: PROVED (definitional). -/
theorem triCx_d_apply (X Q : GCx A) (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (a b : ℤ) (h : a + 1 = b) (x : X.X a) (q : Q.X a) :
    (triCx X Q δ hδ).d a b h ((x, q) : X.X a × Q.X a) = (X.d a b h x + δ a b h q, Q.d a b h q) :=
  rfl

variable {X Y Q : GCx A} (R : GRetract X Y) (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
  (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)

/-- The projection is a chain map in the relation-indexed form. (tex 5398–5403)
Kind: PROVED. -/
theorem GRetract.p_d (a b : ℤ) (h : a + 1 = b) (x : X.X a) :
    R.p.f b b rfl (X.d a b h x) = Y.d a b h (R.p.f a a rfl x) := by
  subst h
  exact R.p.comm a (a + 1) a (a + 1) rfl rfl rfl rfl x

/-- The inclusion is a chain map in the relation-indexed form. (tex 5398–5403)
Kind: PROVED. -/
theorem GRetract.i_d (a b : ℤ) (h : a + 1 = b) (y : Y.X a) :
    R.i.f b b rfl (Y.d a b h y) = X.d a b h (R.i.f a a rfl y) := by
  subst h
  exact R.i.comm a (a + 1) a (a + 1) rfl rfl rfl rfl y

/-- The transported off-diagonal map `p δ`. (tex 5398–5403)
Kind: definition. -/
def GRetract.pδ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] Y.X b :=
  fun a b h => R.p.f b b rfl ∘ₗ δ a b h

omit hδ in
/-- The transported off-diagonal map satisfies `d (p δ) + (p δ) d = 0`. (tex 5398–5403)
Kind: PROVED. -/
theorem GRetract.pδ_sq (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0) (a b c : ℤ) (hab : a + 1 = b)
    (hbc : b + 1 = c) (q : Q.X a) :
    Y.d b c hbc (R.pδ δ a b hab q) + R.pδ δ b c hbc (Q.d a b hab q) = 0 := by
  change Y.d b c hbc (R.p.f b b rfl (δ a b hab q)) +
    R.p.f c c rfl (δ b c hbc (Q.d a b hab q)) = 0
  rw [← R.p_d b c hbc, ← map_add, hδ, map_zero]

/-- Index congruence for `d h`. (tex 5398–5403)
Kind: PROVED. -/
theorem GRetract.dh_congr {n m m' : ℤ} (hmm : m = m') (h1 : m + 1 = n) (h2 : m' + 1 = n)
    (x : X.X n) : X.d m n h1 (R.h n m h1 x) = X.d m' n h2 (R.h n m' h2 x) := by
  subst hmm
  rfl

omit hδ in
/-- The chain identity of the extended inclusion. (tex 5398–5403)
Kind: PROVED. -/
theorem GRetract.triExt_i_aux (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0) (a : ℤ) (y : Y.X a)
    (q : Q.X a) :
    X.d a (a + 1) rfl (R.i.f a a rfl y - R.h (a + 1) a rfl (δ a (a + 1) rfl q)) +
        δ a (a + 1) rfl q =
      R.i.f (a + 1) (a + 1) rfl (Y.d a (a + 1) rfl y + R.p.f (a + 1) (a + 1) rfl
        (δ a (a + 1) rfl q)) - R.h (a + 1 + 1) (a + 1) rfl (δ (a + 1) (a + 1 + 1) rfl
          (Q.d a (a + 1) rfl q)) := by
  have e := R.homotopy (a + 1) (δ a (a + 1) rfl q)
  rw [R.dh_congr (show a + 1 - 1 = a by omega) _ rfl] at e
  have hdq : X.d (a + 1) (a + 1 + 1) rfl (δ a (a + 1) rfl q) =
      -δ (a + 1) (a + 1 + 1) rfl (Q.d a (a + 1) rfl q) :=
    eq_neg_of_add_eq_zero_left (hδ a (a + 1) (a + 1 + 1) rfl rfl q)
  rw [hdq, map_neg] at e
  rw [map_sub, map_add, R.i_d a (a + 1) rfl y]
  linear_combination (norm := abel) e

omit hδ in
/-- **The model of a triangular extension** (tex 5398–5403, 4423–4437): a normalized graded
deformation retract `R` of `X` onto `Y` extends to the triangular extensions, from
`X ⊕ Q` (differential `(x, q) ↦ (d x + δ q, d q)`) onto `Y ⊕ Q` (differential
`(y, q) ↦ (d y + p δ q, d q)`), with inclusion `(y, q) ↦ (i y − h δ q, q)`, projection
`(x, q) ↦ (p x, q)` and homotopy `(x, q) ↦ (h x, 0)`. Kind: definition (PROVED identities). -/
def GRetract.triExt (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0) :
    GRetract (triCx X Q δ hδ) (triCx Y Q (R.pδ δ) (R.pδ_sq δ hδ)) where
  i :=
    { f := fun a b h => by
        subst h
        exact ((R.i.f a a rfl).coprod (-(R.h (a + 1) a rfl ∘ₗ δ a (a + 1) rfl))).prod
          (LinearMap.snd A _ _)
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj z
        subst hij hj h₁
        obtain ⟨y, q⟩ := z
        refine Prod.ext ?_ rfl
        change R.i.f (i + 1) (i + 1) rfl (Y.d i (i + 1) rfl y + R.p.f (i + 1) (i + 1) rfl
            (δ i (i + 1) rfl q)) + -(R.h (i + 1 + 1) (i + 1) rfl (δ (i + 1) (i + 1 + 1) rfl
              (Q.d i (i + 1) rfl q))) =
          X.d i (i + 1) rfl (R.i.f i i rfl y + -(R.h (i + 1) i rfl (δ i (i + 1) rfl q))) +
            δ i (i + 1) rfl q
        rw [← sub_eq_add_neg, ← sub_eq_add_neg]
        exact (R.triExt_i_aux δ hδ i y q).symm }
  p :=
    { f := fun a b h => by
        subst h
        exact (R.p.f a a rfl).prodMap LinearMap.id
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj z
        subst hij hj h₁
        obtain ⟨x, q⟩ := z
        refine Prod.ext ?_ rfl
        change R.p.f (i + 1) (i + 1) rfl (X.d i (i + 1) rfl x + δ i (i + 1) rfl q) =
          Y.d i (i + 1) rfl (R.p.f i i rfl x) + R.p.f (i + 1) (i + 1) rfl (δ i (i + 1) rfl q)
        rw [map_add, R.p_d] }
  h a b hab := (R.h a b hab).prodMap 0
  p_i n z := by
    obtain ⟨y, q⟩ := z
    refine Prod.ext ?_ rfl
    change R.p.f n n rfl (R.i.f n n rfl y + -(R.h (n + 1) n rfl (δ n (n + 1) rfl q))) = y
    rw [map_add, map_neg, R.p_i, R.p_h, neg_zero, add_zero]
  homotopy n z := by
    obtain ⟨x, q⟩ := z
    refine Prod.ext ?_ ?_
    · change x - (R.i.f n n rfl (R.p.f n n rfl x) + -(R.h (n + 1) n rfl (δ n (n + 1) rfl q))) =
        (X.d (n - 1) n (by omega) (R.h n (n - 1) (by omega) x) + δ (n - 1) n (by omega) 0) +
          R.h (n + 1) n rfl (X.d n (n + 1) rfl x + δ n (n + 1) rfl q)
      rw [map_zero, add_zero, map_add]
      linear_combination (norm := abel) R.homotopy n x
    · change q - q = Q.d (n - 1) n (by omega) 0 + 0
      rw [sub_self, map_zero, add_zero]
  h_h a b c hab hbc z := by
    obtain ⟨x, q⟩ := z
    refine Prod.ext ?_ rfl
    exact R.h_h a b c hab hbc x
  h_i a b hab z := by
    obtain ⟨y, q⟩ := z
    refine Prod.ext ?_ rfl
    change R.h a b hab (R.i.f a a rfl y + -(R.h (a + 1) a rfl (δ a (a + 1) rfl q))) = 0
    subst hab
    rw [map_add, map_neg, R.h_i, R.h_h, neg_zero, add_zero]
  p_h a b hab z := by
    obtain ⟨x, q⟩ := z
    refine Prod.ext ?_ rfl
    exact R.p_h a b hab x

/-! ### Non-vacuity -/

/-- The zero off-diagonal map. (tex 5398–5403) Kind: definition. -/
def zeroOffDiag (X Q : GCx A) : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b := fun _ _ _ => 0

/-- The zero off-diagonal map satisfies `d δ + δ d = 0` (the direct sum). (tex 5398–5403)
Kind: PROVED. -/
theorem zeroOffDiag_sq (X Q : GCx A) (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c)
    (q : Q.X a) :
    X.d b c hbc (zeroOffDiag X Q a b hab q) + zeroOffDiag X Q b c hbc (Q.d a b hab q) = 0 := by
  simp [zeroOffDiag]

/-- **Non-vacuity**: the direct sum `X ⊕ Q` retracts onto itself through the identity retract of
`X` (tex 5398–5403). Kind: definition. -/
def triExt_refl_example (X Q : GCx A) :
    GRetract (triCx X Q (zeroOffDiag X Q) (zeroOffDiag_sq X Q))
      (triCx X Q ((GRetract.refl X).pδ (zeroOffDiag X Q))
        ((GRetract.refl X).pδ_sq (zeroOffDiag X Q) (zeroOffDiag_sq X Q))) :=
  (GRetract.refl X).triExt (zeroOffDiag X Q) (zeroOffDiag_sq X Q)

/-- The projection of the example is the identity. (tex 5398–5403) Kind: PROVED. -/
theorem triExt_refl_example_p (X Q : GCx A) (n : ℤ) (x : X.X n) (q : Q.X n) :
    (triExt_refl_example X Q).p.f n n rfl ((x, q) : X.X n × Q.X n) = (x, q) :=
  rfl

end ZInQ.Manuscript.RC.Limits
