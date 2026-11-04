module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Hyperoperation

public section

namespace ZInQ

theorem exists_bounded_integer_polynomial_defining_integers :
  ∃ P : MvPolynomial (Fin 292890231905) Int,
    P.totalDegree < hyperoperation 4 2 7 ∧
    (∀ m : Fin 292890231905 →₀ Nat,
      (P.coeff m).natAbs < hyperoperation 4 2 8) ∧
    ∀ q : Rat,
      (∃ w : Fin 292890231904 → Rat,
        MvPolynomial.eval₂ (Int.castRingHom Rat) (Fin.cons q w) P = 0) ↔
      ∃ z : Int, (z : Rat) = q := by
  sorry

end ZInQ
