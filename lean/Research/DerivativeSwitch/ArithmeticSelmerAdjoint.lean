import Research.DerivativeSwitch.ArithmeticSelmer
import Research.DerivativeSwitch.ContinuousSelmerTrace
import Research.DerivativeSwitch.FiniteSelmerInjective
import Research.DerivativeSwitch.SelmerDualityMap

/-!
# Arithmetic Selmer adjoint with the compact-support normalization

This assembles the continuous cochains over `G_{K,S}` and the local
completions. The inputs identify the local conditions, the cup product and
the local invariant maps. The chain-level adjoint uses the trace derived
from those invariants, including after pullback to finite models.
-/

namespace Research.DerivativeSwitch.ArithmeticSelmer

open CategoryTheory NativeSelmerCone ContinuousSelmer ContinuousSelmerTrace
open NativeBoundaryTrace SelmerDualityMap HomologicalComplex
open scoped BigOperators

universe u
variable {K R : Type u} [Field K] [NumberField K] [CommRing R] [TopologicalSpace R]
  [Module.Injective R R]
  (S : Finset (FinitePrime K))
  (M Mdual TateTwist : TopRep.{u} R (globalGroup K S))
  (e : ∀ v : S, PlaceEmbedding K v.1)
  (U : ∀ v : S, LocalCondition (localCochains M (localizations K S e) v))
  (Uorth : ∀ v : S, LocalCondition (localCochains Mdual (localizations K S e) v))

/-- The normalized map on finite models uses the original cup and one common
trace on the Tate-twist compact-support cone. No inverse duality map or
perfectness of this adjoint is used in its construction. -/
theorem exists_normalized_retained_adjoint {A B : Complex (R := R)}
    (i : A ⟶ arithmeticSelmer K S M e U) (j : B ⟶ arithmeticSelmer K S Mdual e Uorth)
    (P : TraceProduct (arithmeticSelmer K S M e U) (arithmeticSelmer K S Mdual e Uorth)
      (arithmeticCompactSupport K S TateTwist e))
    (inv : ∀ v : S, (localCochains TateTwist (localizations K S e) v).homology 2 →ₗ[R] R)
    (reciprocity : ∀ a : (cochains TateTwist).homology 2,
      ∑ v : S, inv v (homologyMap (restrict TateTwist (localizations K S e v)) 2 a) = 0) :
    ∃ trace : (arithmeticCompactSupport K S TateTwist e).X 2 →ₗ[R] R,
      (∀ b : (arithmeticCompactSupport K S TateTwist e).X 1,
        trace ((arithmeticCompactSupport K S TateTwist e).d 1 2 b) = 0) ∧
      (∀ z : (v : S) → (localCochains TateTwist (localizations K S e) v).cycles 2,
        localTrace (-(localization TateTwist (localizations K S e))) trace
          (fun v => (localCochains TateTwist (localizations K S e) v).iCycles 2 (z v)) =
        ∑ v : S, inv v ((localCochains TateTwist (localizations K S e) v).homologyπ 2 (z v))) ∧
      ∃ f : A ⟶ shiftedDual B, ∀ (n : ℤ) (x : A.X n) (y : B.X (1 - n)),
        (f.f n x) y = trace (P.totalThree n (i.f n x) (j.f (1 - n) y)) := by
  obtain ⟨trace, kills, normalization⟩ := exists_normalized_trace TateTwist
    (localizations K S e) inv reciprocity
  exact ⟨trace, kills, normalization, adjoint (P.pullback i j) trace kills,
    retained_adjoint_apply P i j trace kills⟩

end Research.DerivativeSwitch.ArithmeticSelmer
