# javanpeykar-direct results log

Base wip/leaf-fold33b fe2f0d4a. Build: .lake/build and lean/.lake/build copied (reflink) from ~/dzq-wt/leaf-fold33b
(7c137704, built 11-17 00:40).

## Statements (scratch/javanpeykar-direct/JavanpeykarDirect.lean, namespace JavanpeykarDirect)

* `HasBelyiMapOfDegree X d := 0 < d ∧ ∃ β, IsBelyiMap X β d` (javanpeykar-fix's IsBelyiMap).
* `belyiDegree X hB := Nat.find hB` (deg_B, given one Belyi map hB; Belyi's theorem not used).
* `IsStableHeightBar W x` (W : AbelianVariety Kbar): ∃ number field L, Algebra L Kbar, V : AbelianVariety L,
  V ×_L Kbar ≅ W and height-fix's `IsPrintedStableHeight (ofVendored V) x`.
* NEW LEAF `JavanpeykarThm111`: ∀ Kbar algebraic closure of ℚ (`[Algebra ℚ Kbar] [IsAlgClosure ℚ Kbar]`),
  ∀ X curve over Kbar (IsCurve, IsIntegral), projective, 1 ≤ genusK X, ∀ W Pic⁰-representative with tensor
  group law, ∀ hB, ∀ x, IsStableHeightBar W x → x ≤ javanpeykarBound (genusK X) (belyiDegree X hB).
* Bridges (proved): `belyiDegree_le`, `javanpeykarBound_mono` (bridge (i)); `isStableHeightBar_of_model`
  (bridge (ii), ∃-intro at L = K); `isCurve_baseChange`; `genusK_baseChange` (rfl); `isAlgClosure_rat`.
* `javanpeykarPrintedMap_of_thm111 : JavanpeykarThm111 → JavanpeykarRebase.JavanpeykarPrintedMap`.

## Compile outcomes

* 11-17 00:49 `lake env lean scratch/javanpeykar-direct/JavanpeykarDirect.lean`: OK, 12 s;
  `javanpeykarPrintedMap_of_thm111` axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  (First attempt 00:46: two errors fixed — IsAlgClosure ℚ (AlgebraicClosure K) needed an explicit
  `Algebra.IsAlgebraic.trans`; GeometricallyConnected of the base change via `pullback.snd` instance.)
