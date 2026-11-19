import ZInQKernel.Contrib.OneProof.RC.Metaplectic.Fourier

/-! The two local generators in the convention of tex 8729–8744.
The same construction works at odd primes and at two. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic

open Intertwine Intertwine2 WeilIndex

variable (a : Fin 3 → ℕ) (p : Place)

/-- The operator for the upper unipotent with upper-right entry `b`. -/
def upperUnipotent (b : ℚ_[p.val]) : SchwartzBruhat p →ₗ[ℂ] SchwartzBruhat p where
  toFun f := ⟨fun x => localPhase p (b * quad a x) * f.1 x, by
    have h : IsLocallyConstant (fun x => localPhase p (b * quad a x)) :=
      (isLocallyConstant_phase p).comp_continuous (continuous_const.mul (continuous_quad p a))
    exact ⟨h.mul f.2.1, f.2.2.mul_left⟩⟩
  map_add' f g := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' z f := Subtype.ext (funext fun x => mul_left_comm _ z _)

def elementaryCoset (c : LocalVectors p) : SchwartzBruhat p :=
  ⟨localCoset p c, rectangleIndicator_one p c ▸ rectangleIndicator_mem p 1 c⟩

/-- The upper factor of `GeneratorTensorAction` is the operator with parameter (-n). -/
theorem upper_elementary (n : ℤ) (c x : LocalVectors p) :
    (upperUnipotent a p (-(n : ℚ_[p.val])) (elementaryCoset p c) : LocalVectors p → ℂ) x =
      localUpper a p n (localCoset p c) x := rfl

variable [∀ i, NeZero (2 * a i)]

/-- The actual ternary index, using the scalar Gauss integral in each coordinate. -/
def gaussIndex : ℂˣ := indexAt gaussGamma (rationalDiagonal a) p

/-- The operator for the Weyl matrix with entries (0, 1; −1, 0). -/
def weyl : SchwartzBruhat p →ₗ[ℂ] SchwartzBruhat p :=
  (gaussIndex a p : ℂ) • fourier a p

/-- The Weyl factor of `GeneratorTensorAction`, with the actual index. -/
theorem weyl_elementary (c y : LocalVectors p) :
    (weyl a p (elementaryCoset p c) : LocalVectors p → ℂ) y =
      (gaussIndex a p : ℂ) * localFourier a p (localCoset p c) y := rfl

open Classical in
theorem weyl_elementary_value (c y : LocalVectors p) :
    (weyl a p (elementaryCoset p c) : LocalVectors p → ℂ) y =
      if localDual a p y then (gaussIndex a p : ℂ) * localPhase p (polar a c y) *
        (Real.sqrt (localNorm (determinant a) p) : ℂ) else 0 := by
  rw [weyl_elementary, localFourier_coset]
  split_ifs <;> simp [mul_assoc]

/-- The square above (-I) is reflection times the square of the actual Weil index. -/
theorem weyl_sq (f : SchwartzBruhat p) (x : LocalVectors p) :
    (weyl a p (weyl a p f) : LocalVectors p → ℂ) x =
      (gaussIndex a p : ℂ) ^ 2 * f.1 (-x) := by
  change (gaussIndex a p : ℂ) *
    (fourier a p ((gaussIndex a p : ℂ) • fourier a p f) : LocalVectors p → ℂ) x = _
  rw [map_smul]
  change (gaussIndex a p : ℂ) * ((gaussIndex a p : ℂ) *
    (fourier a p (fourier a p f) : LocalVectors p → ℂ) x) = _
  rw [fourier_sq, pow_two, mul_assoc]

#print axioms upper_elementary
#print axioms weyl_elementary
#print axioms weyl_elementary_value
#print axioms weyl_sq

end ZInQ.Manuscript.RC.Metaplectic
