import ZInQKernel.Contrib.OneProof.RC.Limits.SplitModel

/-!
# Lane RC31, round 5: the two-piece perturbation for triangular extensions

Manuscript `diophantine_zq.tex`, the graded model of the support triangle (5.6) (tex 5398–5424:
"the graded model of (5.6) is `C_old ⊕ ⊕_q Q_q` with an upper triangular differential") and Lemma
`ex:limits-inner-limit` (tex 4423–4437: the normalized perturbation formulas).

For normalized graded deformation retracts `R_X` of `X` onto `Y` and `R_Q` of `Q` onto `Q'`, the
triangular extension `X ⊕ Q` (differential `(x, q) ↦ (d x + δ q, d q)`) retracts onto `Y ⊕ Q'`
with differential `(y, q') ↦ (d y + p δ i q', d q')` (`GRetract.triExt₂`). This is the
perturbation lemma for `H = h_X ⊕ h_Q` and the off-diagonal perturbation `δ`, whose series stops
after one term (`(H δ)² = 0`):

* inclusion `(y, q') ↦ (i y − h δ i q', i q')`,
* projection `(x, q) ↦ (p x − p δ h q, p q)`,
* homotopy `(x, q) ↦ (h x − h δ h q, h q)`.

It is assembled as the composite (`GRetract.comp`) of the retract that only moves `X`
(`GRetract.triExt`) and the retract that only moves `Q` (`GRetract.triExtQ`).

For a split inclusion `C_P ⊂ C_R` with quotient complex `Q`, retracts of `C_P` onto `Y` and of
`Q` onto `Q'` give a retract of `C_R` onto `Y ⊕ Q'` (`splitRetract₂`, `splitHomotopyEquiv₂`).
When `Q'` is a two-term complex `[M --B--> M]` in degrees one and two (`twoTermCx`), the
degree-one-to-two model differential is `(y, q) ↦ (d y + p (∗ (i q)), B q)`
(`splitModel₂_twoTerm_d_one_two`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable {A : Type} [CommRing A]

/-! ### Composition of normalized retracts -/

section Comp

variable {X Y Z : GCx A}

/-- **The composite of two normalized graded deformation retracts** (tex 4423–4437): inclusion
`i₁ i₂`, projection `p₂ p₁`, homotopy `h₁ + i₁ h₂ p₁`. Kind: definition (PROVED identities). -/
def GRetract.comp (R₁ : GRetract X Y) (R₂ : GRetract Y Z) : GRetract X Z where
  i :=
    { f := fun a b h => R₁.i.f a b h ∘ₗ R₂.i.f a a rfl
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj z
        subst hij hj h₁
        change R₁.i.f (i + 1) (i + 1) rfl (R₂.i.f (i + 1) (i + 1) rfl (Z.d i (i + 1) rfl z)) =
          X.d i (i + 1) rfl (R₁.i.f i i rfl (R₂.i.f i i rfl z))
        rw [R₂.i_d, R₁.i_d] }
  p :=
    { f := fun a b h => R₂.p.f a b h ∘ₗ R₁.p.f a a rfl
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj x
        subst hij hj h₁
        change R₂.p.f (i + 1) (i + 1) rfl (R₁.p.f (i + 1) (i + 1) rfl (X.d i (i + 1) rfl x)) =
          Z.d i (i + 1) rfl (R₂.p.f i i rfl (R₁.p.f i i rfl x))
        rw [R₁.p_d, R₂.p_d] }
  h a b hab := R₁.h a b hab + R₁.i.f b b rfl ∘ₗ R₂.h a b hab ∘ₗ R₁.p.f a a rfl
  p_i n z := by
    change R₂.p.f n n rfl (R₁.p.f n n rfl (R₁.i.f n n rfl (R₂.i.f n n rfl z))) = z
    rw [R₁.p_i, R₂.p_i]
  homotopy n x := by
    change x - R₁.i.f n n rfl (R₂.i.f n n rfl (R₂.p.f n n rfl (R₁.p.f n n rfl x))) =
      X.d (n - 1) n (by omega) (R₁.h n (n - 1) (by omega) x + R₁.i.f (n - 1) (n - 1) rfl
        (R₂.h n (n - 1) (by omega) (R₁.p.f n n rfl x))) +
      (R₁.h (n + 1) n rfl (X.d n (n + 1) rfl x) + R₁.i.f n n rfl
        (R₂.h (n + 1) n rfl (R₁.p.f (n + 1) (n + 1) rfl (X.d n (n + 1) rfl x))))
    have e₁ := R₁.homotopy n x
    have e₂ := congrArg (R₁.i.f n n rfl) (R₂.homotopy n (R₁.p.f n n rfl x))
    rw [map_sub, map_add, R₁.i_d (n - 1) n (by omega), ← R₁.p_d n (n + 1) rfl] at e₂
    rw [map_add]
    linear_combination (norm := abel) e₁ + e₂
  h_h a b c hab hbc x := by
    change R₁.h b c hbc (R₁.h a b hab x + R₁.i.f b b rfl (R₂.h a b hab (R₁.p.f a a rfl x))) +
      R₁.i.f c c rfl (R₂.h b c hbc (R₁.p.f b b rfl (R₁.h a b hab x +
        R₁.i.f b b rfl (R₂.h a b hab (R₁.p.f a a rfl x))))) = 0
    rw [map_add, map_add, R₁.h_h, R₁.h_i, R₁.p_h, R₁.p_i]
    simp only [zero_add, R₂.h_h, map_zero]
  h_i a b hab z := by
    change R₁.h a b hab (R₁.i.f a a rfl (R₂.i.f a a rfl z)) + R₁.i.f b b rfl
      (R₂.h a b hab (R₁.p.f a a rfl (R₁.i.f a a rfl (R₂.i.f a a rfl z)))) = 0
    rw [R₁.h_i, R₁.p_i, R₂.h_i, map_zero, add_zero]
  p_h a b hab x := by
    change R₂.p.f b b rfl (R₁.p.f b b rfl (R₁.h a b hab x + R₁.i.f b b rfl
      (R₂.h a b hab (R₁.p.f a a rfl x)))) = 0
    rw [map_add, R₁.p_h, R₁.p_i, zero_add, R₂.p_h]

end Comp

/-! ### The retract that only moves the second block -/

section QSide

variable {Y Q Q' : GCx A}

/-- The off-diagonal map `ε i` of the second-block retract, `ε : Qᵃ → Y^{a+1}` (tex 4423–4437,
5398–5424). Kind: definition. -/
def GRetract.δQ (RQ : GRetract Q Q') (ε : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] Y.X b) :
    ∀ a b : ℤ, a + 1 = b → Q'.X a →ₗ[A] Y.X b :=
  fun a b h => ε a b h ∘ₗ RQ.i.f a a rfl

/-- The map `ε i` satisfies `d (ε i) + (ε i) d = 0` (tex 5398–5424). Kind: PROVED. -/
theorem GRetract.δQ_sq (RQ : GRetract Q Q') (ε : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] Y.X b)
    (hε : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      Y.d b c hbc (ε a b hab q) + ε b c hbc (Q.d a b hab q) = 0)
    (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q'.X a) :
    Y.d b c hbc (RQ.δQ ε a b hab q) + RQ.δQ ε b c hbc (Q'.d a b hab q) = 0 := by
  change Y.d b c hbc (ε a b hab (RQ.i.f a a rfl q)) +
    ε b c hbc (RQ.i.f b b rfl (Q'.d a b hab q)) = 0
  rw [RQ.i_d a b hab, hε]

/-- Index congruence for `ε h` (tex 5398–5424). Kind: PROVED. -/
theorem GRetract.eps_h_congr (RQ : GRetract Q Q') (ε : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] Y.X b)
    {n m m' : ℤ} (hmm : m = m') (h1 : m + 1 = n) (h2 : m' + 1 = n) (q : Q.X n) :
    ε m n h1 (RQ.h n m h1 q) = ε m' n h2 (RQ.h n m' h2 q) := by
  subst hmm
  rfl

/-- **The second-block retract of a triangular extension** (tex 4423–4437, 5398–5424): a
normalized graded deformation retract `R_Q` of `Q` onto `Q'` extends from `Y ⊕ Q` (differential
`(y, q) ↦ (d y + ε q, d q)`) onto `Y ⊕ Q'` (differential `(y, q') ↦ (d y + ε i q', d q')`), with
inclusion `(y, q') ↦ (y, i q')`, projection `(y, q) ↦ (y − ε h q, p q)` and homotopy
`(y, q) ↦ (0, h q)`. Kind: definition (PROVED identities). -/
def GRetract.triExtQ (RQ : GRetract Q Q') (ε : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] Y.X b)
    (hε : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      Y.d b c hbc (ε a b hab q) + ε b c hbc (Q.d a b hab q) = 0) :
    GRetract (triCx Y Q ε hε) (triCx Y Q' (RQ.δQ ε) (RQ.δQ_sq ε hε)) where
  i :=
    { f := fun a b h => by
        subst h
        exact LinearMap.id.prodMap (RQ.i.f a a rfl)
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj z
        subst hij hj h₁
        obtain ⟨y, q⟩ := z
        refine Prod.ext rfl ?_
        exact RQ.i_d i (i + 1) rfl q }
  p :=
    { f := fun a b h => by
        subst h
        exact (LinearMap.id.coprod (-(ε (a - 1) a (by omega) ∘ₗ RQ.h a (a - 1) (by omega)))).prod
          (RQ.p.f a a rfl ∘ₗ LinearMap.snd A _ _)
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj z
        subst hij hj h₁
        obtain ⟨y, q⟩ := z
        refine Prod.ext ?_ ?_
        · change Y.d i (i + 1) rfl y + ε i (i + 1) rfl q + -(ε (i + 1 - 1) (i + 1) (by omega)
              (RQ.h (i + 1) (i + 1 - 1) (by omega) (Q.d i (i + 1) rfl q))) =
            Y.d i (i + 1) rfl (y + -(ε (i - 1) i (by omega) (RQ.h i (i - 1) (by omega) q))) +
              ε i (i + 1) rfl (RQ.i.f i i rfl (RQ.p.f i i rfl q))
          rw [RQ.eps_h_congr ε (show i + 1 - 1 = i by omega) _ rfl]
          have e := congrArg (ε i (i + 1) rfl) (RQ.homotopy i q)
          rw [map_sub, map_add] at e
          have hd := hε (i - 1) i (i + 1) (by omega) rfl (RQ.h i (i - 1) (by omega) q)
          rw [map_add, map_neg]
          linear_combination (norm := abel) e + hd
        · exact RQ.p_d i (i + 1) rfl q }
  h a b hab := (0 : Y.X a →ₗ[A] Y.X b).prodMap (RQ.h a b hab)
  p_i n z := by
    obtain ⟨y, q⟩ := z
    refine Prod.ext ?_ ?_
    · change y + -(ε (n - 1) n (by omega) (RQ.h n (n - 1) (by omega) (RQ.i.f n n rfl q))) = y
      rw [RQ.h_i, map_zero, neg_zero, add_zero]
    · exact RQ.p_i n q
  homotopy n z := by
    obtain ⟨y, q⟩ := z
    refine Prod.ext ?_ ?_
    · change y - (y + -(ε (n - 1) n (by omega) (RQ.h n (n - 1) (by omega) q))) =
        (Y.d (n - 1) n (by omega) 0 + ε (n - 1) n (by omega) (RQ.h n (n - 1) (by omega) q)) + 0
      rw [map_zero]
      abel
    · exact RQ.homotopy n q
  h_h a b c hab hbc z := by
    obtain ⟨y, q⟩ := z
    exact Prod.ext rfl (RQ.h_h a b c hab hbc q)
  h_i a b hab z := by
    obtain ⟨y, q⟩ := z
    exact Prod.ext rfl (RQ.h_i a b hab q)
  p_h a b hab z := by
    obtain ⟨y, q⟩ := z
    refine Prod.ext ?_ ?_
    · change (0 : Y.X b) + -(ε (b - 1) b (by omega)
        (RQ.h b (b - 1) (by omega) (RQ.h a b hab q))) = 0
      rw [RQ.h_h, map_zero, neg_zero, add_zero]
    · exact RQ.p_h a b hab q

end QSide

/-! ### The two-piece perturbation -/

section TwoPiece

variable {X Y Q Q' : GCx A}

/-- **The transported off-diagonal map** `δ' = p δ i : Q'ᵃ → Y^{a+1}` of the two-piece
perturbation (tex 4423–4437, 5398–5424). Kind: definition. -/
def GRetract.triδ₂ (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b) :
    ∀ a b : ℤ, a + 1 = b → Q'.X a →ₗ[A] Y.X b :=
  RQ.δQ (RX.pδ δ)

/-- `δ' q' = p (δ (i q'))` (tex 4423–4437). Kind: PROVED (definitional). -/
theorem GRetract.triδ₂_apply (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b) (a b : ℤ) (h : a + 1 = b) (q : Q'.X a) :
    RX.triδ₂ RQ δ a b h q = RX.p.f b b rfl (δ a b h (RQ.i.f a a rfl q)) :=
  rfl

/-- The transported off-diagonal map satisfies `d δ' + δ' d = 0` (tex 5398–5424).
Kind: PROVED. -/
theorem GRetract.triδ₂_sq (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q'.X a) :
    Y.d b c hbc (RX.triδ₂ RQ δ a b hab q) + RX.triδ₂ RQ δ b c hbc (Q'.d a b hab q) = 0 :=
  RQ.δQ_sq (RX.pδ δ) (RX.pδ_sq δ hδ) a b c hab hbc q

/-- **The two-piece perturbation for triangular extensions** (tex 4423–4437, 5398–5424: "the
graded model of (5.6) is `C_old ⊕ ⊕_q Q_q` with an upper triangular differential"): normalized
graded deformation retracts `R_X` of `X` onto `Y` and `R_Q` of `Q` onto `Q'` give a normalized
graded deformation retract of `X ⊕ Q` (differential `(x, q) ↦ (d x + δ q, d q)`) onto `Y ⊕ Q'`
(differential `(y, q') ↦ (d y + p δ i q', d q')`). The components are computed in
`triExt₂_i_apply`, `triExt₂_p_apply`, `triExt₂_h_apply`. Kind: definition (PROVED identities). -/
def GRetract.triExt₂ (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0) :
    GRetract (triCx X Q δ hδ) (triCx Y Q' (RX.triδ₂ RQ δ) (RX.triδ₂_sq RQ δ hδ)) :=
  (RX.triExt δ hδ).comp (RQ.triExtQ (RX.pδ δ) (RX.pδ_sq δ hδ))

/-- **The inclusion of the two-piece perturbation** is `(y, q') ↦ (i y − h δ i q', i q')`
(tex 4423–4437). Kind: PROVED. -/
theorem GRetract.triExt₂_i_apply (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (n : ℤ) (y : Y.X n) (q : Q'.X n) :
    (RX.triExt₂ RQ δ hδ).i.f n n rfl ((y, q) : Y.X n × Q'.X n) =
      ((RX.i.f n n rfl y - RX.h (n + 1) n rfl (δ n (n + 1) rfl (RQ.i.f n n rfl q)),
        RQ.i.f n n rfl q) : X.X n × Q.X n) :=
  Prod.ext (sub_eq_add_neg _ _).symm rfl

/-- **The projection of the two-piece perturbation** is `(x, q) ↦ (p x − p δ h q, p q)`
(tex 4423–4437). Kind: PROVED. -/
theorem GRetract.triExt₂_p_apply (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (n : ℤ) (x : X.X n) (q : Q.X n) :
    (RX.triExt₂ RQ δ hδ).p.f n n rfl ((x, q) : X.X n × Q.X n) =
      ((RX.p.f n n rfl x - RX.p.f n n rfl (δ (n - 1) n (by omega) (RQ.h n (n - 1) (by omega) q)),
        RQ.p.f n n rfl q) : Y.X n × Q'.X n) :=
  Prod.ext (sub_eq_add_neg _ _).symm rfl

/-- **The homotopy of the two-piece perturbation** is `(x, q) ↦ (h x − h δ h q, h q)`
(tex 4423–4437). Kind: PROVED. -/
theorem GRetract.triExt₂_h_apply (RX : GRetract X Y) (RQ : GRetract Q Q')
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (a b : ℤ) (hab : b + 1 = a) (x : X.X a) (q : Q.X a) :
    (RX.triExt₂ RQ δ hδ).h a b hab ((x, q) : X.X a × Q.X a) =
      ((RX.h a b hab x - RX.h (b + 1) b rfl (δ b (b + 1) rfl (RQ.h a b hab q)),
        RQ.h a b hab q) : X.X b × Q.X b) := by
  refine Prod.ext ?_ ?_
  · change RX.h a b hab x + (RX.i.f b b rfl 0 + -(RX.h (b + 1) b rfl
      (δ b (b + 1) rfl (RQ.h a b hab q)))) = _
    rw [map_zero, zero_add, sub_eq_add_neg]
  · change (0 : Q.X b) + RQ.h a b hab q = _
    rw [zero_add]

/-! ### Reduction to the one-piece extension -/

/-- **Reduction of the target differential**: for `R_Q` the identity retract the transported
off-diagonal map is the one of `triExt`, `p δ` (tex 5398–5424). Kind: PROVED (definitional). -/
theorem GRetract.triδ₂_refl (RX : GRetract X Y) (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b) :
    RX.triδ₂ (GRetract.refl Q) δ = RX.pδ δ :=
  rfl

/-- **Reduction of the target complex**: for `R_Q` the identity retract the target of
`triExt₂` is the target of `triExt` (tex 5398–5424). Kind: PROVED (definitional). -/
theorem GRetract.triExt₂_refl_target (RX : GRetract X Y)
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0) :
    triCx Y Q (RX.triδ₂ (GRetract.refl Q) δ) (RX.triδ₂_sq (GRetract.refl Q) δ hδ) =
      triCx Y Q (RX.pδ δ) (RX.pδ_sq δ hδ) :=
  rfl

/-- **Reduction of the inclusion**: for `R_Q` the identity retract the inclusion of `triExt₂` is
that of `triExt` (tex 5398–5424). Kind: PROVED (definitional). -/
theorem GRetract.triExt₂_refl_i (RX : GRetract X Y)
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (n : ℤ) (z : Y.X n × Q.X n) :
    (RX.triExt₂ (GRetract.refl Q) δ hδ).i.f n n rfl z = (RX.triExt δ hδ).i.f n n rfl z :=
  rfl

/-- **Reduction of the projection**: for `R_Q` the identity retract the projection of `triExt₂`
is that of `triExt` (tex 5398–5424). Kind: PROVED. -/
theorem GRetract.triExt₂_refl_p (RX : GRetract X Y)
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (n : ℤ) (z : X.X n × Q.X n) :
    (RX.triExt₂ (GRetract.refl Q) δ hδ).p.f n n rfl z = (RX.triExt δ hδ).p.f n n rfl z := by
  obtain ⟨x, q⟩ := z
  refine Prod.ext ?_ rfl
  change RX.p.f n n rfl x + -(RX.p.f n n rfl (δ (n - 1) n (by omega) 0)) = RX.p.f n n rfl x
  rw [map_zero, map_zero, neg_zero, add_zero]

/-- **Reduction of the homotopy**: for `R_Q` the identity retract the homotopy of `triExt₂` is
that of `triExt` (tex 5398–5424). Kind: PROVED. -/
theorem GRetract.triExt₂_refl_h (RX : GRetract X Y)
    (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (a b : ℤ) (hab : b + 1 = a) (z : X.X a × Q.X a) :
    (RX.triExt₂ (GRetract.refl Q) δ hδ).h a b hab z = (RX.triExt δ hδ).h a b hab z := by
  obtain ⟨x, q⟩ := z
  rw [GRetract.triExt₂_h_apply]
  refine Prod.ext ?_ rfl
  change RX.h a b hab x - RX.h (b + 1) b rfl (δ b (b + 1) rfl 0) = RX.h a b hab x
  rw [map_zero, map_zero, sub_zero]

end TwoPiece

/-! ### The model of the relaxed complex with a retracted quotient block -/

section Split

variable {CP CR Y Q' : GCx A} (E : SplitInclusion CP CR) (R : GRetract CP Y)
  (RQ : GRetract E.quotientCx Q')

/-- **The model of the relaxed complex, two-piece form** (tex 5398–5424): a split inclusion
`C_P ⊂ C_R` with quotient complex `Q`, a retract of `C_P` onto `Y` and a retract of `Q` onto `Q'`
give a normalized graded deformation retract of `C_R` onto the triangular extension `Y ⊕ Q'`
with differential `(y, q') ↦ (d y + p (∗ (i q')), d q')`. Kind: definition (PROVED identities). -/
def splitRetract₂ :
    GRetract CR (triCx Y Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)) :=
  (R.triExt₂ RQ E.offDiag E.offDiag_sq).ofEquiv (fun n => E.blockEquiv n)
    (fun a b h z => by
      obtain ⟨x, q⟩ := z
      exact E.d_blockEquiv a b h x q)

/-- The relaxed complex is homotopy equivalent to its two-piece triangular model
(tex 5398–5424). Kind: definition. -/
def splitHomotopyEquiv₂ :
    HomotopyEquiv (triCx Y Q' (R.triδ₂ RQ E.offDiag)
      (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)).toCC CR.toCC :=
  (splitRetract₂ E R RQ).homotopyEquiv

/-- **The degree-one-to-two block of the model** (tex 5398–5424): if the degree-one-to-two
differential of `Q'` is `B` (e.g. a two-term block `[M → M]` of the tame local model), the model
differential from degree one to degree two is `(y, q) ↦ (d y + p (∗ (i q)), B q)`.
Kind: PROVED. -/
theorem splitModel₂_d_one_two (B : Q'.X 1 →ₗ[A] Q'.X 2)
    (hB : ∀ q : Q'.X 1, Q'.d 1 2 rfl q = B q) (y : Y.X 1) (q : Q'.X 1) :
    (triCx Y Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)).d 1 2 rfl
        ((y, q) : Y.X 1 × Q'.X 1) =
      ((Y.d 1 2 rfl y + R.p.f 2 2 rfl (E.offDiag 1 2 rfl (RQ.i.f 1 1 rfl q)), B q) :
        Y.X 2 × Q'.X 2) := by
  rw [triCx_d_apply, hB]
  rfl

end Split

/-! ### Two-term blocks -/

section TwoTerm

variable {M : Type} [AddCommGroup M] [Module A M]

variable (M) in
/-- The support of the two-term complex `[M → M]`: all of `M` in degrees one and two, zero
elsewhere (tex 5398–5424). Kind: definition. -/
def twoTermSupp (n : ℤ) : Submodule A M :=
  if n = 1 ∨ n = 2 then ⊤ else ⊥

variable (M) in
/-- The support in degree two is everything (tex 5398–5424). Kind: PROVED. -/
theorem twoTermSupp_two : twoTermSupp (A := A) M 2 = ⊤ := by
  simp [twoTermSupp]

/-- The differential of the two-term complex `[M → M]`: `B` from degree one to degree two, zero
elsewhere (tex 5398–5424). Kind: definition. -/
def twoTermD (B : M →ₗ[A] M) (a b : ℤ) (h : a + 1 = b) :
    twoTermSupp (A := A) M a →ₗ[A] twoTermSupp (A := A) M b :=
  if ha : a = 1 then
    (B ∘ₗ (twoTermSupp (A := A) M a).subtype).codRestrict (twoTermSupp (A := A) M b) (fun _ => by
      have hb : b = 2 := by omega
      subst hb
      rw [twoTermSupp_two]
      exact Submodule.mem_top)
  else 0

/-- **The two-term complex** `[M --B--> M]` in degrees one and two (tex 5398–5424: the singular
blocks of the tame local model). Kind: definition (PROVED identities). -/
def twoTermCx (B : M →ₗ[A] M) : GCx A where
  X n := ModuleCat.of A (twoTermSupp (A := A) M n)
  d := twoTermD B
  d_d a b c hab hbc x := by
    change twoTermD B b c hbc (twoTermD B a b hab x) = 0
    by_cases ha : a = 1
    · have hb : ¬ b = 1 := by omega
      simp only [twoTermD, dite_eq_right hb, LinearMap.zero_apply]
    · simp only [twoTermD, dite_eq_right ha, LinearMap.zero_apply, map_zero]

/-- The two-term complex vanishes outside degrees one and two (tex 5398–5424). Kind: PROVED. -/
theorem twoTermCx_subsingleton (B : M →ₗ[A] M) (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((twoTermCx B).X n) := by
  have hn : ¬ (n = 1 ∨ n = 2) := by omega
  have e : twoTermSupp (A := A) M n = ⊥ := by simp [twoTermSupp, hn]
  change Subsingleton (twoTermSupp (A := A) M n)
  rw [e]
  infer_instance

/-- The degree-one-to-two differential of the two-term complex is `B` (tex 5398–5424).
Kind: PROVED. -/
theorem twoTermCx_d_one_two (B : M →ₗ[A] M) (q : (twoTermCx B).X 1) :
    ((show twoTermSupp (A := A) M 2 from (twoTermCx B).d 1 2 rfl q) : M) =
      B (show twoTermSupp (A := A) M 1 from q) := by
  change ((twoTermD B 1 2 rfl q : twoTermSupp (A := A) M 2) : M) = _
  rw [twoTermD, dite_eq_left rfl]
  rfl

variable {CP CR Y : GCx A} (E : SplitInclusion CP CR) (R : GRetract CP Y)

/-- **The two-term block of the relaxed model** (tex 5398–5424): for a retract of the quotient
complex onto a two-term complex `[M --B--> M]` (e.g. `B = Φ − q` on a singular block of the tame
local model), the differential of the two-piece model from degree one to degree two is
`(y, q) ↦ (d y + p (∗ (i q)), B q)`. Kind: PROVED. -/
theorem splitModel₂_twoTerm_d_one_two (B : M →ₗ[A] M) (RQ : GRetract E.quotientCx (twoTermCx B))
    (y : Y.X 1) (q : (twoTermCx B).X 1) :
    ((triCx Y (twoTermCx B) (R.triδ₂ RQ E.offDiag)
        (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)).d 1 2 rfl ((y, q) : Y.X 1 × (twoTermCx B).X 1)).1 =
      Y.d 1 2 rfl y + R.p.f 2 2 rfl (E.offDiag 1 2 rfl (RQ.i.f 1 1 rfl q)) ∧
    ((show twoTermSupp (A := A) M 2 from ((triCx Y (twoTermCx B) (R.triδ₂ RQ E.offDiag)
        (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)).d 1 2 rfl
          ((y, q) : Y.X 1 × (twoTermCx B).X 1)).2) : M) =
      B (show twoTermSupp (A := A) M 1 from q) :=
  ⟨rfl, twoTermCx_d_one_two B q⟩

end TwoTerm

/-! ### Non-vacuity -/

section NonVacuity

variable {X Q : GCx A}

/-- **Non-vacuity**: with both retracts the identity, the projection of the two-piece
perturbation is the identity (tex 4423–4437, 5398–5424). Kind: PROVED. -/
theorem triExt₂_refl_refl_p (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (n : ℤ) (z : X.X n × Q.X n) :
    ((GRetract.refl X).triExt₂ (GRetract.refl Q) δ hδ).p.f n n rfl z = z := by
  rw [GRetract.triExt₂_refl_p]
  rfl

/-- **Non-vacuity**: with both retracts the identity, the inclusion of the two-piece
perturbation is the identity (tex 4423–4437, 5398–5424). Kind: PROVED. -/
theorem triExt₂_refl_refl_i (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (n : ℤ) (z : X.X n × Q.X n) :
    ((GRetract.refl X).triExt₂ (GRetract.refl Q) δ hδ).i.f n n rfl z = z := by
  obtain ⟨x, q⟩ := z
  refine Prod.ext ?_ rfl
  change x + -((0 : X.X (n + 1) →ₗ[A] X.X n) (δ n (n + 1) rfl q)) = x
  rw [LinearMap.zero_apply, neg_zero, add_zero]

/-- **Non-vacuity**: with both retracts the identity, the homotopy of the two-piece perturbation
vanishes (tex 4423–4437, 5398–5424). Kind: PROVED. -/
theorem triExt₂_refl_refl_h (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (a b : ℤ) (hab : b + 1 = a) (z : X.X a × Q.X a) :
    ((GRetract.refl X).triExt₂ (GRetract.refl Q) δ hδ).h a b hab z = 0 := by
  rw [GRetract.triExt₂_refl_h]
  rfl

/-- **Non-vacuity**: with both retracts the identity, the target differential is the source
differential (tex 4423–4437, 5398–5424). Kind: PROVED. -/
theorem triExt₂_refl_refl_d (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[A] X.X b)
    (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
      X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)
    (a b : ℤ) (h : a + 1 = b) (z : X.X a × Q.X a) :
    (triCx X Q ((GRetract.refl X).triδ₂ (GRetract.refl Q) δ)
      ((GRetract.refl X).triδ₂_sq (GRetract.refl Q) δ hδ)).d a b h z =
      (triCx X Q δ hδ).d a b h z := by
  subst h
  rfl

/-- **Non-vacuity**: over a field every complex has a split inclusion into itself and the
corresponding two-piece model retract, with the identity retract on the quotient block
(tex 5398–5424). Kind: PROVED. -/
theorem splitRetract₂_nonvacuous {F : Type} [Field F] (X : GCx F) :
    ∃ E : SplitInclusion X X, Nonempty (GRetract X (triCx X E.quotientCx
      ((GRetract.refl X).triδ₂ (GRetract.refl E.quotientCx) E.offDiag)
      ((GRetract.refl X).triδ₂_sq (GRetract.refl E.quotientCx) E.offDiag E.offDiag_sq))) := by
  obtain ⟨E, -⟩ := exists_splitInclusion (gHomId X) (fun n => Function.injective_id)
  exact ⟨E, ⟨splitRetract₂ E (GRetract.refl X) (GRetract.refl E.quotientCx)⟩⟩

end NonVacuity

end ZInQ.Manuscript.RC.Limits
