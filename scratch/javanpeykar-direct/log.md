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
* 11-17 00:50 autofold dry run (`autofold.json`, temporary copy of the contribution at
  ZInQKernel/Contrib/OneProof/JavanpeykarDirect.lean, removed afterwards): exit 0, strict 16/15 on 31 -> 17/14 on 31
  (raw: autofold counts kind published + flag "pending review" as LEAF; Addendum 1 makes it GLUE -> neutral).
  VERIFIED.
* 11-17 00:50 `lake build +ZInQKernel.Contrib.OneProof.JavanpeykarDirect`: success, 12860 jobs, 61 s. VERIFIED.
* Copied TailZ57-64 oleans were stale for this tree (leaf-fold33b has uncommitted edits): rebuilt
  `lake build +ZInQKernel.OneProof.H.TailZ64` (one run killed at the 10-min background limit, resumed): success,
  15211 jobs (build-tailz64.txt). VERIFIED.
* 11-17 01:13 dry-run module (FoldDryRun.lean.txt) `lake env lean` against the rebuilt TailZ64: OK, 18 s;
  `HDec.HSyn.sixContactMin_of_open58` axioms standard (FoldDryRun-compile.txt). VERIFIED.
* 11-17 01:14 `WellPosed.lean`: OK; `isStableHeightBar_of_iso`, `isPrintedStableHeight_unique` (given N1
  NeronModelExists, SS2 SemistableNeronBaseChange) standard axioms. VERIFIED.

## Findings

* Both theorem steps of the recorded reading gap are Lean proofs: (i) `belyiDegree_le` + `javanpeykarBound_mono`;
  (ii) `isStableHeightBar_of_model` (∃-intro). No further printed theorem needed.
* New leaf = print + one added hypothesis hB (a Belyi map exists; Belyi's theorem). Remaining readings are
  definition-level: IsStableHeightBar is Faltings' stable height (independence of model V not in tree; fixed-model
  uniqueness proved given N1, SS2), height-fix's IsPrintedStableHeight, IsBelyiMap's unramifiedness, projectivity.
