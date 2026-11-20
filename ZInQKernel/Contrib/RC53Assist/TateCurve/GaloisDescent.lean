import ZInQKernel.Contrib.RC53Assist.TateCurve.QuadraticDescent
import ZInQKernel.Contrib.RC53Assist.TateCurve.PrintedUniformization
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The quadratic descent character of a Tate uniformization

The sign is derived from the scaling coefficient of an actual Weierstrass
isomorphism. Comparing that isomorphism with each of its Galois conjugates
shows that its sign is quadratic and multiplicative, and that it is the
sign in the transported pointwise uniformization.

Reference: Silverman, AEC, III.1 and III.10; the automorphism classification
needed here is proved by the coefficient comparison, not assumed.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open WeierstrassCurve WeierstrassCurve.Affine Module
open scoped Classical WithZero

section Sign

variable {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F]

/-- **DEFINITION**: the sign read from the conjugate scaling coefficient.
Locator: `isomorphism_scaling_square`. -/
def galoisSign (C : VariableChange F) (σ : F ≃ₐ[K] F) : ℤ :=
  if Units.map σ.toAlgHom.toMonoidHom C.u = C.u then 1 else -1

/-- **PROVED**: the sign takes the two quadratic values.
Locator: its definition. -/
theorem galoisSign_values (C : VariableChange F) (σ : F ≃ₐ[K] F) :
    galoisSign C σ = 1 ∨ galoisSign C σ = -1 := by
  unfold galoisSign
  split_ifs <;> simp

/-- **PROVED**: the descent sign has square one.
Locator: `galoisSign_values`. -/
theorem galoisSign_square (C : VariableChange F) (σ : F ≃ₐ[K] F) :
    galoisSign C σ * galoisSign C σ = 1 := by
  rcases galoisSign_values C σ with h | h <;> rw [h] <;> norm_num

/-- **PROVED**: the identity automorphism has sign one.
Locator: the scaling coefficient is fixed by the identity. -/
theorem galoisSign_one (C : VariableChange F) :
    galoisSign (K := K) C 1 = 1 := by
  simp [galoisSign, Units.ext_iff]

/-- **PROVED**: conjugating a change of variables gives another
isomorphism between the same two curves defined over the base field.
Locator: `map_variableChange` and `map_baseChange`. -/
theorem conjugate_variableChange_isom (E E' : WeierstrassCurve K)
    (C : VariableChange F) (hC : C • E.baseChange F = E'.baseChange F)
    (σ : F ≃ₐ[K] F) :
    C.map σ.toAlgHom.toRingHom • E.baseChange F = E'.baseChange F := by
  have h := congrArg (fun W : WeierstrassCurve F => W.map σ.toAlgHom.toRingHom) hC
  rw [← map_variableChange] at h
  have hE : (E.baseChange F).map σ.toAlgHom.toRingHom = E.baseChange F :=
    E.map_baseChange σ.toAlgHom
  have hE' : (E'.baseChange F).map σ.toAlgHom.toRingHom = E'.baseChange F :=
    E'.map_baseChange σ.toAlgHom
  rw [hE, hE'] at h
  exact h

/-- **PROVED**: the conjugate scaling coefficient is the original one
multiplied by its quadratic sign. Locator: coefficient comparison. -/
theorem galoisSign_scalar (E E' : WeierstrassCurve K) (C : VariableChange F)
    (hC : C • E.baseChange F = E'.baseChange F)
    (h4 : (E.baseChange F).c₄ ≠ 0) (h6 : (E.baseChange F).c₆ ≠ 0)
    (σ : F ≃ₐ[K] F) :
    σ (C.u : F) = (galoisSign C σ : F) * (C.u : F) := by
  let D := C.map σ.toAlgHom.toRingHom
  have hD := conjugate_variableChange_isom E E' C hC σ
  rcases isomorphism_coefficient_alternatives (E.baseChange F) (E'.baseChange F)
    C D hC hD h4 h6 with ⟨hu, _, _, _⟩ | ⟨hu, _, _, _⟩
  · have hf : Units.map σ.toAlgHom.toMonoidHom C.u = C.u := hu
    change (Units.map σ.toAlgHom.toMonoidHom C.u : F) = _
    simp only [galoisSign, hf, ite_true, Int.cast_one, one_mul]
  · have hn : Units.map σ.toAlgHom.toMonoidHom C.u ≠ C.u := by
      intro h
      have hv := congrArg Units.val h
      change (D.u : F) = C.u at hv
      rw [hu] at hv
      have hz : (C.u : F) = 0 := by linear_combination -hv / 2
      exact C.u.ne_zero hz
    change (D.u : F) = _
    rw [hu]
    simp only [galoisSign, hn, ite_false, Int.cast_neg, Int.cast_one, neg_one_mul]

/-- **PROVED**: the sign is multiplicative.
Locator: composition of Galois automorphisms and cancellation of the nonzero
scaling coefficient. -/
theorem galoisSign_mul (E E' : WeierstrassCurve K) (C : VariableChange F)
    (hC : C • E.baseChange F = E'.baseChange F)
    (h4 : (E.baseChange F).c₄ ≠ 0) (h6 : (E.baseChange F).c₆ ≠ 0)
    (σ τ : F ≃ₐ[K] F) :
    galoisSign C (σ * τ) = galoisSign C σ * galoisSign C τ := by
  have h := galoisSign_scalar E E' C hC h4 h6 (σ * τ)
  rw [AlgEquiv.mul_apply, galoisSign_scalar E E' C hC h4 h6 τ,
    map_mul, map_intCast, galoisSign_scalar E E' C hC h4 h6 σ] at h
  have hf : (galoisSign C (σ * τ) : F) =
      (galoisSign C σ : F) * (galoisSign C τ : F) := by
    apply mul_right_cancel₀ C.u.ne_zero
    linear_combination -h
  apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : F)))
  rw [Int.cast_mul]
  exact hf

/-- **PROVED DEFINITION**: the quadratic character valued in integer
units. Locator: `galoisSign_mul` and `galoisSign_square`. -/
def quadraticSignCharacter (E E' : WeierstrassCurve K) (C : VariableChange F)
    (hC : C • E.baseChange F = E'.baseChange F)
    (h4 : (E.baseChange F).c₄ ≠ 0) (h6 : (E.baseChange F).c₆ ≠ 0) :
    (F ≃ₐ[K] F) →* ℤˣ where
  toFun σ := ⟨galoisSign C σ, galoisSign C σ,
    galoisSign_square C σ, galoisSign_square C σ⟩
  map_one' := Units.ext (galoisSign_one C)
  map_mul' σ τ := Units.ext (galoisSign_mul E E' C hC h4 h6 σ τ)

/-- **PROVED**: pointwise naturality for a conjugated isomorphism.
Locator: the two point-coordinate formulas. -/
theorem conjugate_pointsOfVariableChange (E E' : WeierstrassCurve K)
    (C : VariableChange F) (hC : C • E.baseChange F = E'.baseChange F)
    (σ : F ≃ₐ[K] F) (P : (E'.baseChange F).toAffine.Point) :
    Point.map (W' := E) σ.toAlgHom
        (pointsOfVariableChange (E.baseChange F) (E'.baseChange F) C hC P) =
      pointsOfVariableChange (E.baseChange F) (E'.baseChange F)
        (C.map σ.toAlgHom.toRingHom) (conjugate_variableChange_isom E E' C hC σ)
        (Point.map (W' := E') σ.toAlgHom P) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Point.zero_def, map_zero]
  · simp only [pointsOfVariableChange, AddEquiv.trans_apply]
    rw [AddEquiv.cast_apply hC.symm, Point.cast_some hC.symm]
    simp only [Point.coe_addEquivVariableChange, Point.equivVariableChange_some,
      Point.map_some]
    rw [AddEquiv.cast_apply (conjugate_variableChange_isom E E' C hC σ).symm,
      Point.cast_some (conjugate_variableChange_isom E E' C hC σ).symm]
    simp only [Point.coe_addEquivVariableChange, Point.equivVariableChange_some,
      Point.some.injEq, VariableChange.map, Units.coe_map, map_add, map_mul, map_pow]
    rfl

/-- **PROVED**: the derived sign is the sign on the actual point
isomorphism. Locator: the full coefficient alternatives, not an assumed
Tate-module twist formula. -/
theorem galoisSign_points (E E' : WeierstrassCurve K) (C : VariableChange F)
    (hC : C • E.baseChange F = E'.baseChange F)
    (h4 : (E.baseChange F).c₄ ≠ 0) (h6 : (E.baseChange F).c₆ ≠ 0)
    (σ : F ≃ₐ[K] F) (P : (E'.baseChange F).toAffine.Point) :
    pointsOfVariableChange (E.baseChange F) (E'.baseChange F)
        (C.map σ.toAlgHom.toRingHom) (conjugate_variableChange_isom E E' C hC σ) P =
      galoisSign C σ •
        pointsOfVariableChange (E.baseChange F) (E'.baseChange F) C hC P := by
  let D := C.map σ.toAlgHom.toRingHom
  have hD := conjugate_variableChange_isom E E' C hC σ
  rcases isomorphism_coefficient_alternatives (E.baseChange F) (E'.baseChange F)
    C D hC hD h4 h6 with ⟨hu, hr, hs, ht⟩ | ⟨hu, hr, hs, ht⟩
  · have hf : Units.map σ.toAlgHom.toMonoidHom C.u = C.u := hu
    have hDC : D = C := by ext <;> simp only [hu, hr, hs, ht]
    rw [galoisSign, ite_eq_left hf, one_zsmul]
    change pointsOfVariableChange _ _ D hD P = _
    exact pointsOfVariableChange_congr (E.baseChange F) (E'.baseChange F)
      D C hD hC hDC P
  · have hn : Units.map σ.toAlgHom.toMonoidHom C.u ≠ C.u := by
      intro h
      have hv := congrArg Units.val h
      change (D.u : F) = C.u at hv
      rw [hu] at hv
      have hz : (C.u : F) = 0 := by linear_combination -hv / 2
      exact C.u.ne_zero hz
    rw [galoisSign, ite_eq_right hn, neg_one_zsmul]
    exact pointsOfVariableChange_negative (E.baseChange F) (E'.baseChange F)
      C D hC hD hu hr hs ht P

end Sign

section Transport

variable {F P Q : Type*} [Field F] [AddCommGroup P] [AddCommGroup Q] {q : Fˣ}

/-- **PROVED DEFINITION**: transport of a uniformization along an actual
isomorphism of point groups. Its kernel remains exactly `q^ℤ`.
Locator: injectivity and surjectivity of the additive equivalence. -/
def transportUniformization (U : MultiplicativeUniformization (P := P) q)
    (e : P ≃+ Q) : MultiplicativeUniformization (P := Q) q where
  map := e.toAddMonoidHom.comp U.map
  surjective := e.surjective.comp U.surjective
  kernel x := by
    constructor
    · intro h
      change e (U.map (Additive.ofMul x)) = 0 at h
      apply (U.kernel x).mp
      apply e.injective
      simpa only [map_zero] using h
    · intro h
      change e (U.map (Additive.ofMul x)) = 0
      rw [(U.kernel x).mpr h, map_zero]

end Transport

section SignedUniformization

variable {K : Type*} [Field K] [CharZero K] [Valued K ℤᵐ⁰]

/-- **PROVED DEFINITION**: the uniformization transported from the Tate
curve to the given curve via a genuine Weierstrass isomorphism.
Locator: `transportUniformization`. -/
def descendedUniformization (E : WeierstrassCurve K) (q : Kˣ)
    (C : VariableChange (AlgebraicClosure K))
    (hC : C • E.baseChange (AlgebraicClosure K) =
      (tateEquation q).baseChange (AlgebraicClosure K))
    (U : EquivariantTateUniformization q) :
    MultiplicativeUniformization
      (P := (E.baseChange (AlgebraicClosure K)).toAffine.Point) (closureParameter q) :=
  transportUniformization U.uniformization
    (pointsOfVariableChange _ _ C hC)

/-- **PROVED**: the transported uniformization is Galois equivariant
with precisely the derived quadratic sign.
Locator: `conjugate_pointsOfVariableChange`, `galoisSign_points`, and the
literal Galois equivariance of Tate uniformization. -/
theorem descendedUniformization_equivariant (E : WeierstrassCurve K) (q : Kˣ)
    (C : VariableChange (AlgebraicClosure K))
    (hC : C • E.baseChange (AlgebraicClosure K) =
      (tateEquation q).baseChange (AlgebraicClosure K))
    (h4 : (E.baseChange (AlgebraicClosure K)).c₄ ≠ 0)
    (h6 : (E.baseChange (AlgebraicClosure K)).c₆ ≠ 0)
    (U : EquivariantTateUniformization q)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (AlgebraicClosure K)ˣ) :
    Point.map (W' := E) σ.toAlgHom
        ((descendedUniformization E q C hC U).map (Additive.ofMul x)) =
      galoisSign C σ • (descendedUniformization E q C hC U).map
        (Additive.ofMul (Units.map σ.toAlgHom.toMonoidHom x)) := by
  change Point.map (W' := E) σ.toAlgHom
      (pointsOfVariableChange _ _ C hC (U.uniformization.map (Additive.ofMul x))) = _
  rw [conjugate_pointsOfVariableChange E (tateEquation q) C hC σ,
    galoisSign_points E (tateEquation q) C hC h4 h6 σ, U.equivariant]
  rfl

end SignedUniformization

end ZInQ.Contrib.RC53Assist.TateCurve
