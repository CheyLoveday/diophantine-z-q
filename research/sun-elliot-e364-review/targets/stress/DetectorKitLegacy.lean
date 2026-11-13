import Mathlib

/-!
Regression countermodel for the first detector skeleton.

The legacy `trace_lower_bound` field below is copied semantically from the
original draft. Its quantification over `a : WithTop ℤ`, including `⊤`, makes
it inconsistent at `x = 0` for every nonempty place type. This is interface
counterevidence, not a counterexample to Sun's detector.
-/

namespace SunElliotE364.Targets.Stress

abbrev PlaceValue := WithTop ℤ

structure LegacyTraceAdapter (F : Type*) [Field F] [Algebra ℚ F] where
  p : ℕ
  Place : Type*
  val : Place → AddValuation F PlaceValue
  trace : F →ₗ[ℚ] ℚ
  trace_lower_bound : ∀ (x : F) (a : PlaceValue),
    (∀ P : Place, a ≤ val P x) → a ≤ (padicValRat p (trace x) : PlaceValue)

/-- The old adapter cannot be instantiated for a nonempty place type. -/
theorem legacy_traceLowerBound_inconsistent {F : Type*} [Field F] [Algebra ℚ F]
    (kit : LegacyTraceAdapter F) [Nonempty kit.Place] : False := by
  have h := kit.trace_lower_bound 0 (⊤ : PlaceValue) (by simp)
  simp at h

#print axioms legacy_traceLowerBound_inconsistent

/-- The original unguarded rational-compatibility field, before the
`q = 0` repair. -/
structure LegacyScalarAdapter (F : Type*) [Field F] [Algebra ℚ F] where
  p : ℕ
  Place : Type*
  val : Place → AddValuation F PlaceValue
  val_algebraMap : ∀ (P : Place) (q : ℚ),
    val P (algebraMap ℚ F q) = (padicValRat p q : PlaceValue)

/-- A second zero-sentinel inconsistency: additive valuations send zero to
`⊤`, whereas `padicValRat p 0` computes to zero. -/
theorem legacy_scalarAdapter_inconsistent {F : Type*} [Field F] [Algebra ℚ F]
    (kit : LegacyScalarAdapter F) [Nonempty kit.Place] : False := by
  let P : kit.Place := Classical.choice (inferInstance : Nonempty kit.Place)
  have h := kit.val_algebraMap P 0
  simp at h

#print axioms legacy_scalarAdapter_inconsistent

end SunElliotE364.Targets.Stress
