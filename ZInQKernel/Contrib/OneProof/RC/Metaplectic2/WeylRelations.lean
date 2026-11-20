import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Sandwich

/-! The Weyl relations with their actual scalars, tex 8756–8758 and
8779–8787. The specialization to the cubic relation is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex GaussSign Visibility
open scoped BigOperators

variable (a : Fin 3 → ℕ) (p : Place) [∀ i, NeZero (2 * a i)]

theorem fourier_square : fourier a p * fourier a p = dilation p (-1) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (fourier a p (fourier a p f)).1 x = _
  rw [fourier_sq, dilation_neg_one]

private theorem factor_reciprocal (b : ℚ_[p.val]ˣ) :
    (dilationFactor p b : ℂ) * (dilationFactor p (-b⁻¹) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← dilationFactor_mul, show b * -b⁻¹ = (-1 : ℚ_[p.val]ˣ) by simp]
  simp [dilationFactor]

/-- The literal operator formula of tex 8756–8758, using reflection
times Fourier for the inverse Fourier transform. -/
theorem fourier_sandwich (b : ℚ_[p.val]ˣ) :
    fourier a p * upperUnipotent a p (b : ℚ_[p.val]) * fourier a p =
      (scaledIndex a p b : ℂ) •
        (upperUnipotent a p ((-b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * dilation p (-b⁻¹) *
          fourier a p * upperUnipotent a p ((-b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val])) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  have h := factor_reciprocal p b
  apply mul_left_cancel₀ (show (dilationFactor p b : ℂ) ≠ 0 by
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h)
  change (dilationFactor p b : ℂ) * (fourier a p (upperUnipotent a p b (fourier a p f))).1 x = _
  rw [fourier_upper_sandwich]
  let t : ℚ_[p.val]ˣ := -b⁻¹
  let c : ℚ_[p.val] := t
  change (scaledIndex a p b : ℂ) * (localPhase p (c * quad a x) *
    (fourier a p (upperUnipotent a p c f)).1 (c • x)) =
    (dilationFactor p b : ℂ) * ((scaledIndex a p b : ℂ) * (localPhase p (c * quad a x) *
      (dilation p t (fourier a p (upperUnipotent a p c f))).1 x))
  rw [dilation_apply]
  calc
    _ = ((dilationFactor p b : ℂ) * (dilationFactor p t : ℂ)) *
        ((scaledIndex a p b : ℂ) * (localPhase p (c * quad a x) *
          (fourier a p (upperUnipotent a p c f)).1 (c • x))) := by rw [h, one_mul]
    _ = _ := by ring

private theorem root_pow_eight (e : ZMod 8) :
    exponentRoot e ^ (8 : ℕ) = 1 := by
  have h : zetaEight ^ (8 : ℕ) = 1 := by
    rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, zetaEight_pow_four]
    apply Units.ext
    norm_num [Units.val_pow_eq_pow_val]
  rw [exponentRoot, ← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem scaledIndex_eighth (b : ℚ_[p.val]ˣ) : scaledIndex a p b ^ (8 : ℕ) = 1 := by
  rw [scaledIndex, ← Finset.prod_pow]
  simp only [gaussGamma_eq_finiteGamma, finiteGamma, root_pow_eight, Finset.prod_const_one]

/-- With the choice w = (0, 1; -1, 0), the cube projects to the
identity and its operator is the fourth power of the actual index. -/
theorem weyl_upper_cube :
    (Metaplectic.weyl a p * upperUnipotent a p 1) ^ 3 =
      (gaussIndex a p : ℂ) ^ 4 • (1 : Module.End ℂ (SchwartzBruhat p)) := by
  let F := fourier a p
  let U := upperUnipotent a p (1 : ℚ_[p.val])
  let V := upperUnipotent a p (-1 : ℚ_[p.val])
  let D := dilation p (-1)
  let g := (gaussIndex a p : ℂ)
  have hUV : V * U = 1 := by
    dsimp [V, U]
    rw [upper_mul, neg_add_cancel, upper_zero]
  have hFF : F * F = D := fourier_square a p
  have hDD : D * D = 1 := by
    dsimp [D]
    rw [dilation_mul, neg_one_mul, neg_neg, dilation_one]
  have hFUF : F * U * F = g • (V * D * F * V) := by
    simpa [F, U, V, D, g, scaledIndex_one] using fourier_sandwich a p 1
  have h2 : (F * U) ^ 2 = g • (V * D * F) := by
    calc
      _ = (F * U * F) * U := by simp only [pow_two, mul_assoc]
      _ = _ := by rw [hFUF, smul_mul_assoc, mul_assoc (V * D * F), hUV, mul_one]
  have h3 : (F * U) ^ 3 = g • (1 : Module.End ℂ (SchwartzBruhat p)) := by
    rw [pow_succ, h2, smul_mul_assoc]
    congr 1
    calc
      _ = V * (D * (F * F)) * U := by simp only [mul_assoc]
      _ = 1 := by rw [hFF, hDD, mul_one, hUV]
  change ((g • F) * U) ^ 3 = g ^ 4 • (1 : Module.End ℂ (SchwartzBruhat p))
  rw [smul_mul_assoc, smul_pow, h3, smul_smul, ← pow_succ]

theorem weyl_cube_scalar_is_sign :
    ((gaussIndex a p : ℂ) ^ 4) ^ 2 = 1 := by
  have h := scaledIndex_eighth a p 1
  rw [scaledIndex_one] at h
  rw [← pow_mul, show (4 * 2 : ℕ) = 8 by decide]
  have hv := congrArg (fun z : ℂˣ => (z : ℂ)) h
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hv

/-- Exact scalar in the Weyl square before identifying the Hilbert symbol. -/
theorem weyl_square_scalar :
    Metaplectic.weyl a p * Metaplectic.weyl a p =
      ((gaussIndex a p : ℂ) ^ 2 / (diagonalRatio a p (-1) : ℂ)) • diagonal a p (-1) := by
  simp only [Metaplectic.weyl, smul_mul_smul_comm, fourier_square, diagonal, smul_smul, pow_two]
  rw [div_mul_cancel₀ _ (diagonalRatio a p (-1)).ne_zero]

/-- The general Bruhat relation with a literal nonzero scalar from the actual indices. -/
theorem weyl_upper_bruhat (b : ℚ_[p.val]ˣ) :
    Metaplectic.weyl a p * upperUnipotent a p (b : ℚ_[p.val]) * Metaplectic.weyl a p =
      ((gaussIndex a p : ℂ) ^ 2 * (scaledIndex a p b : ℂ) /
        (scaledIndex a p (-b⁻¹) : ℂ)) •
        (upperUnipotent a p ((-b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) *
         diagonal a p (-b⁻¹) * Metaplectic.weyl a p *
         upperUnipotent a p ((-b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val])) := by
  let F := fourier a p
  let U := upperUnipotent a p (b : ℚ_[p.val])
  let g := (gaussIndex a p : ℂ)
  have h : Metaplectic.weyl a p * U * Metaplectic.weyl a p = g ^ 2 • (F * U * F) := by
    simp only [Metaplectic.weyl, smul_mul_assoc, mul_smul_comm, smul_smul, pow_two, F, g]
  change Metaplectic.weyl a p * U * Metaplectic.weyl a p = _
  rw [h, show F * U * F = _ from fourier_sandwich a p b]
  simp only [diagonal, diagonalRatio, Metaplectic.weyl, smul_mul_assoc, mul_smul_comm,
    smul_smul, Units.val_div_eq_div_val]
  congr 1
  field_simp [(gaussIndex a p).ne_zero, (scaledIndex a p (-b⁻¹)).ne_zero]
  rfl

private theorem root_nsmul (e : ZMod 8) (n : ℕ) :
    exponentRoot (n • e) = exponentRoot e ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, exponentRoot_add, ih, pow_succ]

private theorem dyadic_mul_four (u : ZMod 8) (hu : IsUnit u) (e : Bool) :
    4 • dyadicExponent e u = (4 : ZMod 8) := by
  have hn : (ZMod.cast u : ZMod 2) ≠ 0 :=
    (hu.map (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))).ne_zero
  clear hu
  fin_cases u <;> cases e <;> first | decide | exact False.elim (hn (by decide))

private theorem gaussGamma_pow_four (p : Place) (b : ℚ_[p.val]ˣ) :
    gaussGamma p b ^ (4 : ℕ) = if p = dyadicPlace then -1 else 1 := by
  rw [gaussGamma_eq_finiteGamma]
  change exponentRoot (finiteExponent p b) ^ 4 = _
  rw [← root_nsmul]
  by_cases hp : p = dyadicPlace
  · subst p
    rw [finiteExponent_dyadic, dyadic_mul_four _ (dyadicUnitResidue b).isUnit, ite_eq_left rfl]
    exact zetaEight_pow_four
  · rw [finiteExponent_odd _ hp, ite_eq_right hp]
    have he : 4 • oddExponent p b = (0 : ZMod 8) := by
      unfold oddExponent oddBase signExponent
      split_ifs <;> decide
    rw [he, exponentRoot_zero]

/-- The actual ternary fourth power is independent of the form, also at two. -/
theorem scaledIndex_fourth (t : ℚ_[p.val]ˣ) :
    scaledIndex a p t ^ (4 : ℕ) = if p = dyadicPlace then -1 else 1 := by
  rw [scaledIndex, ← Finset.prod_pow]
  simp only [gaussGamma_pow_four, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  split
  · apply Units.ext
    norm_num [Units.val_pow_eq_pow_val, Units.val_neg]
  · exact one_pow _

theorem weyl_upper_cube_at_two :
    (Metaplectic.weyl a dyadicPlace * upperUnipotent a dyadicPlace 1) ^ 3 =
      -(1 : Module.End ℂ (SchwartzBruhat dyadicPlace)) := by
  have h := scaledIndex_fourth a dyadicPlace 1
  rw [scaledIndex_one, ite_eq_left rfl] at h
  have hc := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at hc
  rw [weyl_upper_cube, hc]
  apply LinearMap.ext
  intro f
  change (-1 : ℂ) • f = -f
  exact neg_one_smul ℂ f


end ZInQ.Manuscript.RC.Metaplectic2
