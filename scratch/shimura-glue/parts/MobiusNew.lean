/-! # shimura-glue: Baba–Granath and Elkies leaves without the `j`-normalization; Möbius glue -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

open scoped Classical

/-- **GLUE (standard; not proved here): postcomposing a morphism `X → P¹` with a Möbius
transformation over `ℚ`.** For a `ℚ`-scheme `X`, `π : X → P¹` (by charts) and `g ∈ GL₂(ℚ)` there is
`π' = g ∘ π : X → P¹`, with `π'(x) = g·π(x)` on `ℚ̄`-points (`OnePoint`'s `GL₂`-action from Mathlib).
(The composition of morphisms of schemes `X → P¹_ℚ → P¹_ℚ`; for `ToP1` it needs new charts, glued
along `U ∩ V` for a translation `t ↦ t + b`.) -/
def MobiusCompose : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 X.left) (g : GL (Fin 2) ℚ),
    ∃ π' : ToP1 X.left, ∀ x : fieldPt Qbar ⟶ X,
      π'.val (K := Qbar) x.left =
        Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) g • π.val (K := Qbar) x.left

/-- `!![a, b; c, d]` as an element of `GL₂(ℚ)`. -/
noncomputable def gl2 (a b c d : ℚ) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

theorem gl2_apply (a b c d : ℚ) (h : a * d - b * c ≠ 0) (i j : Fin 2) :
    (gl2 a b c d h) i j = !![a, b; c, d] i j := rfl

theorem gl2_smul_some (a b c d : ℚ) (h : a * d - b * c ≠ 0) (k : ℚ) :
    gl2 a b c d h • (k : OnePoint ℚ) =
      if c * k + d = 0 then OnePoint.infty else ((a * k + b) / (c * k + d) : ℚ) := by
  rw [OnePoint.smul_some_eq_ite]; simp [gl2_apply]

theorem gl2_smul_infty (a b c d : ℚ) (h : a * d - b * c ≠ 0) :
    gl2 a b c d h • (OnePoint.infty : OnePoint ℚ) = if c = 0 then OnePoint.infty else ((a / c : ℚ) : OnePoint ℚ) := by
  rw [OnePoint.smul_infty_eq_ite]; simp [gl2_apply]

/-- **A Möbius transformation over `ℚ` sends three distinct points of `P¹(ℚ)` to `0, ∞, 1`.** -/
theorem exists_mobius01 (a b c : OnePoint ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℚ, g • a = ((0 : ℚ) : OnePoint ℚ) ∧ g • b = OnePoint.infty ∧
      g • c = ((1 : ℚ) : OnePoint ℚ) := by
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => exact absurd rfl hab
    | coe b =>
      induction c using OnePoint.rec with
      | infty => exact absurd rfl hac
      | coe c =>
        have hcb : c - b ≠ 0 := sub_ne_zero.2 fun e => hbc (by rw [e])
        refine ⟨gl2 0 (c - b) 1 (-b) (by intro e; apply hcb; linear_combination -e), ?_, ?_, ?_⟩
        · rw [gl2_smul_infty]; simp
        · rw [gl2_smul_some]; simp
        · rw [gl2_smul_some, if_neg (by intro e; apply hcb; linear_combination e)]
          congr 1
          rw [div_eq_one_iff_eq (by intro e; apply hcb; linear_combination e)]; ring
  | coe a =>
    induction b using OnePoint.rec with
    | infty =>
      induction c using OnePoint.rec with
      | infty => exact absurd rfl hbc
      | coe c =>
        have hca : c - a ≠ 0 := sub_ne_zero.2 fun e => hac (by rw [e])
        refine ⟨gl2 (1 / (c - a)) (-a / (c - a)) 0 1 (by simpa using hca), ?_, ?_, ?_⟩
        · rw [gl2_smul_some, if_neg (by simp)]
          congr 1; field_simp; ring
        · rw [gl2_smul_infty]; simp
        · rw [gl2_smul_some, if_neg (by simp)]
          congr 1; field_simp; try ring
    | coe b =>
      have hab' : a - b ≠ 0 := sub_ne_zero.2 fun e => hab (by rw [e])
      induction c using OnePoint.rec with
      | infty =>
        refine ⟨gl2 1 (-a) 1 (-b) (by intro e; apply hab'; linear_combination e), ?_, ?_, ?_⟩
        · rw [gl2_smul_some, if_neg (by intro e; apply hab'; linear_combination e)]; simp
        · rw [gl2_smul_some]; simp
        · rw [gl2_smul_infty]; simp
      | coe c =>
        have hca : c - a ≠ 0 := sub_ne_zero.2 fun e => hac (by rw [e])
        have hcb : c - b ≠ 0 := sub_ne_zero.2 fun e => hbc (by rw [e])
        set k := (c - b) / (c - a) with hkdef
        have hk : k ≠ 0 := div_ne_zero hcb hca
        have hkc : k * (c - a) = c - b := by rw [hkdef]; field_simp
        refine ⟨gl2 k (-k * a) 1 (-b) (by
          intro e; apply mul_ne_zero hk hab'; linear_combination e), ?_, ?_, ?_⟩
        · rw [gl2_smul_some, if_neg (by intro e; apply hab'; linear_combination e)]
          congr 1; rw [div_eq_zero_iff]; left; ring
        · rw [gl2_smul_some]; simp
        · rw [gl2_smul_some, if_neg (by intro e; apply hcb; linear_combination e)]
          congr 1
          rw [div_eq_one_iff_eq (by intro e; apply hcb; linear_combination e)]
          linear_combination hkc

/-- Three distinct points of `P¹(ℚ)` go to `0, ∞, −16/27`. -/
theorem exists_mobiusBG (a b c : OnePoint ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℚ, g • a = ((0 : ℚ) : OnePoint ℚ) ∧ g • b = OnePoint.infty ∧
      g • c = ((-16 / 27 : ℚ) : OnePoint ℚ) := by
  obtain ⟨g, h0, h1, h2⟩ := exists_mobius01 a b c hab hac hbc
  let s := gl2 (-16 / 27) 0 0 1 (by norm_num)
  refine ⟨s * g, ?_, ?_, ?_⟩
  · rw [mul_smul, h0, gl2_smul_some]; simp
  · rw [mul_smul, h1, gl2_smul_infty]; simp
  · rw [mul_smul, h2, gl2_smul_some]; simp

/-- The value transfer: `G·s = (g·t)` over `ℚ̄` iff `s = t`, for `G` the image of `g`. -/
theorem smul_map_iff (g : GL (Fin 2) ℚ) (t : OnePoint ℚ) (s : OnePoint Qbar) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) g • s = (g • t).map (algebraMap ℚ Qbar) ↔
      s = t.map (algebraMap ℚ Qbar) := by
  rw [OnePoint.map_smul]
  exact (MulAction.injective _).eq_iff

/-- **LEAF (Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 (p. 737), Lemma 3.1 (pp. 739–740) and the
§3.1 elliptic-order table (p. 740); read by the locator audit: YES), without the `j`-normalization.**
Some coarse witness of the moduli clause lists carries `π : X₆ → P¹` with
* the fibre clause (Thm 2.1: the polarized moduli space is `V/W`; two `ℚ̄`-points have the same value
  iff their QM pairs are `Aut(𝒪)`-twists, i.e. `W`-conjugate), and
* three distinct points `t₄, t₃, t₂₄ ∈ P¹(ℚ)` (Lemma 3.1: `V/W ≅ P¹_ℚ` and the three distinguished images
  are rational) such that the CM points of discriminants `−4, −3, −24` are exactly the fibres over them
  (the §3.1 table: each of `CM(−4)`, `CM(−3)`, `CM(−24)` is one `W`-orbit).
Unlike `BabaGranathX6'` it does not fix the coordinate's values `0, ∞, −16/27` (the normalization the
audit did not locate in Thm 2.1/Lemma 3.1); that is the Möbius computation `babaGranathX6'_of_rational`. -/
def BabaGranathRational : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π : ToP1 X.left)
    (t₄ t₃ t₂₄ : OnePoint ℚ),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ t₄ ≠ t₃ ∧ t₄ ≠ t₂₄ ∧ t₃ ≠ t₂₄ ∧
    ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (π.val (K := Qbar) x.left = π.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM4 P.q ↔ π.val (K := Qbar) x.left = t₄.map (algebraMap ℚ Qbar)) ∧
        (HasCM3 P.q ↔ π.val (K := Qbar) x.left = t₃.map (algebraMap ℚ Qbar)) ∧
        (HasCM24 P.q ↔ π.val (K := Qbar) x.left = t₂₄.map (algebraMap ℚ Qbar))

/-- **`BabaGranathX6'` from `BabaGranathRational` and the Möbius glue**: the coordinate sending the
three CM values to `0, ∞, −16/27` (`exists_mobiusBG`). -/
theorem babaGranathX6'_of_rational (h : BabaGranathRational) (hM : MobiusCompose) :
    BabaGranathX6' := by
  obtain ⟨Y, Φ, X, Ψ, fY, π, t₄, t₃, t₂₄, h1, h6, d1, d2, d3, hcl⟩ := h
  obtain ⟨g, hg4, hg3, hg24⟩ := exists_mobiusBG t₄ t₃ t₂₄ d1 d2 d3
  obtain ⟨π', hπ'⟩ := hM X π g
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, π', fun x x' P Q hP hQ => ?_⟩
  obtain ⟨hf, h4, h3, h24⟩ := hcl x x' P Q hP hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hπ', hπ', (MulAction.injective _).eq_iff]; exact hf
  · rw [h4, hπ', show (OnePoint.some (0 : Qbar)) = (g • t₄).map (algebraMap ℚ Qbar) by
      rw [hg4]; simp, smul_map_iff]
  · rw [h3, hπ', show (OnePoint.infty : OnePoint Qbar) = (g • t₃).map (algebraMap ℚ Qbar) by
      rw [hg3]; simp, smul_map_iff]
  · rw [h24, hπ', show (OnePoint.some (-16 / 27 : Qbar)) = (g • t₂₄).map (algebraMap ℚ Qbar) by
      rw [hg24]; simp, smul_map_iff]

/-- The conic model in Elkies' coordinate `t = −X²/Z²` (`t = ∞` at the points at infinity). -/
def ConicModelT (X : Over (Spec (CommRingCat.of ℚ))) (t : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ X6Kummer.ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = X6Kummer.conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      t.val (K := Qbar) x.left = OnePoint.some (-(p.1.1 ^ 2))) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → t.val (K := Qbar) x.left = OnePoint.infty)

/-- **LEAF (Elkies, ANTS-III, LNCS 1423 (1998), §3, in his coordinate; locators UNVERIFIED).** Some
witness of the moduli clause lists carries Elkies' coordinate `t : X₆ → X*(6) = X₆/W ≅ P¹` with
* the fibre clause (`t` is a coordinate on `X₆/W`: equal values iff `W`-conjugate),
* `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`, and
* the Kummer description `X₆ = X*(6)(√−t, √(3(t − 1)))` on `ℚ̄`-points, written in the Kummer coordinates
  `X/Z = √−t`, `Y/Z = √(3(t − 1))` (so `Y² + 3X² + 3Z² = 0` and `t = −X²/Z²`): `ConicModelT`.
Reading (SPECULATIVE): Elkies' statement is about function fields; this is its form on the points of the
smooth projective model. It does not use Baba–Granath's `j` (the relation `j = 16(t − 1)/27` is the
Möbius computation in `elkiesConicX6_of_t`). -/
def ElkiesConicT : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    ConicModelT X t

/-- `j = 16(t − 1)/27`. -/
noncomputable def gJ : GL (Fin 2) ℚ := gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)

theorem gJ_smul (s : OnePoint Qbar) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) gJ • s =
      s.map (fun z : Qbar => 16 * (z - 1) / 27) := by
  induction s using OnePoint.rec with
  | infty => rw [OnePoint.smul_infty_eq_ite]; simp [Matrix.GeneralLinearGroup.map_apply, gJ, gl2_apply]
  | coe z =>
    rw [OnePoint.smul_some_eq_ite]
    simp [Matrix.GeneralLinearGroup.map_apply, gJ, gl2_apply]
    ring

/-- **`ElkiesConicX6` from Elkies' statement in his coordinate and the Möbius glue** (`j = 16(t−1)/27`
sends `0, 1, ∞` to `−16/27, 0, ∞` and `−X²/Z²` to `−16(X² + Z²)/(27Z²)`). -/
theorem elkiesConicX6_of_t (h : ElkiesConicT) (hM : MobiusCompose) : ElkiesConicX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, e, he, hp, hi⟩ := h
  obtain ⟨π', hπ'⟩ := hM X t gJ
  refine ⟨Y, Φ, X, Ψ, fY, π', h1, h6, fun x x' P Q hP hQ => ?_, e, he, fun x p hx => ?_,
    fun x b hx => ?_⟩
  · obtain ⟨hf, h24, h4, h3⟩ := hcl x x' P Q hP hQ
    refine ⟨?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
    · rw [hπ', hπ', (MulAction.injective _).eq_iff]; exact hf
    · rw [hπ', gJ_smul, h4 c]; simp
    · rw [hπ', gJ_smul, h3 c]; rfl
    · rw [hπ', gJ_smul, h24 c]; simp; try ring
  · rw [hπ', gJ_smul, hp x p hx]; simp; try ring
  · rw [hπ', gJ_smul, hi x b hx]; rfl

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.babaGranathX6'_of_rational
#print axioms HDec.QMSplit.Moduli.elkiesConicX6_of_t
