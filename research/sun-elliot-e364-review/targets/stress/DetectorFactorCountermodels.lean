import Mathlib

/-! The original unguarded detector-factor statement has an exact adverse case. -/
namespace SunElliotE364.Targets.Stress

abbrev PlaceValue := WithTop ℤ

structure CounterexampleKit (F : Type*) [Field F] [Algebra ℚ F] where
  p : ℕ
  Place : Type*
  val : Place → AddValuation F PlaceValue

variable {F : Type*} [Field F] [Algebra ℚ F]

def scalar (R : ℚ) : F := algebraMap ℚ F R

def detectorFactor' (R : ℚ) (D : F) (k : ℕ) : F :=
  1 + scalar R * (D / (scalar R : F) ^ k) ^ 2

def localTermValue' (kit : CounterexampleKit F) (R : ℚ) (D : F) (k : ℕ)
    (P : kit.Place) : PlaceValue :=
  (padicValRat kit.p R : PlaceValue) +
    2 * (kit.val P D - (k : PlaceValue) * (padicValRat kit.p R : PlaceValue))

/-- The unguarded equality is false: at these values the left side is `⊤` but
its right side is `0`. No `R = 0` exploit is used. -/
theorem detectorFactor_original_statement_fails (kit : CounterexampleKit F)
    [Nonempty kit.Place] (P : kit.Place) :
    kit.val P (detectorFactor' (-1) (1 : F) 0) ≠
      min 0 (localTermValue' kit (-1) (1 : F) 0 P) := by
  simp [detectorFactor', scalar, localTermValue']

#print axioms detectorFactor_original_statement_fails

end SunElliotE364.Targets.Stress
