import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.LocalDescentInput

/-!
# Lane RC22 (glue sweep), share Heeg: integral local descent with the genuine local input

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, paragraph 5
"Integral local descent at the old places", tex 3034–3086.

Lane RC10 proves the diagram chase "a class that becomes Kummer over `F'` becomes Kummer over `F`
after multiplication by `m₀ c_B`" as `ZInQ.Manuscript.RC.HeegnerAlgebra.LocalDescentInput.kummer`
(and its unbundled forms `kummer_descent`, `H11_kummer_at_old`), from the interface
`LocalDescentInput` (`PRINT` Lang 1956 and Silverman IV.3.2(a), with the Kummer sequences, the
restriction and inflation maps as fields).  The interface is constructed over genuine continuous
cohomology as `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.localDescentInputGenuine`, from (H10)
hypotheses on a filtration of `B(F')` (Lang's theorem `hLang`, the formal-group quotients, the
component bound `hcB`).  The `CloudB3RC53` layer states the composite for `m₀ = 1`
(`localDescent_kummer`); here is RC10's statement for every `m₀`.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology groupCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- **Integral local descent with multiplier `m₀ c_B`, genuine**, tex 3058–3062 and 3080.  Kind:
`PROVED`, from the remaining hypotheses, which are exactly those of
`localDescentInputGenuine` (the `CloudB3RC53` layer): a topological group `G` (for `G_F`), a
normal subgroup `N` (for `G_{F'}`, `F'/F` unramified), a short exact sequence
`S : 0 → A → B → B → 0` of discrete
`G`-modules (for `0 → E[2^a] → E → E → 0`), and the (H10) data on `B^N` (for `B(F')`) with
`Γ = G ⧸ N` (for `Gal(F'/F)`): a separated complete `Γ`-stable filtration `F i` (identity
component and formal-group levels) with equivariant surjections `π i : F i → Q i` of kernel
`F (i+1)`, `H¹(Γ, Q 0) = 0` (`hLang`, Lang's theorem, `PRINT`), `H¹(Γ, Q i) = 0` for `i ≥ 1`
(`hInd`), and `c_B • B^N ⊆ F 0` (`hcB`, the component bound).  Conclusion: if the restriction of
`v ∈ H¹(G, A)` to `N` is a Kummer class, then `(m₀ c_B) v` is a Kummer class over `G`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.LocalDescentInput.kummer` (lane RC10; the same
hypotheses unbundled are those of `kummer_descent` and `H11_kummer_at_old`).  Discharger:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.localDescentInputGenuine` (the composite
`localDescent_kummer` stated there is the case `m₀ = 1`). -/
theorem localDescentInput_kummer_genuine (N : Subgroup G) [N.Normal]
    (S : DiscreteShortExact G A B B)
    (F : ℕ → AddSubgroup (FixedPoints.addSubgroup N B))
    (hstable : ∀ i (g : G ⧸ N), ∀ x ∈ F i, g • x ∈ F i)
    (hsep : ∀ x, (∀ i, x ∈ F i) → x = 0)
    (hcomplete : ∀ x : ℕ → FixedPoints.addSubgroup N B, (∀ i, x i ∈ F i) →
      ∃ s, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (Q : ℕ → Type*) [∀ i, AddCommGroup (Q i)] [∀ i, DistribMulAction (G ⧸ N) (Q i)]
    (π : ∀ i, F i →+ Q i) (hπs : ∀ i, Function.Surjective (π i))
    (hπk : ∀ i (x : F i), π i x = 0 ↔ (x : FixedPoints.addSubgroup N B) ∈ F (i + 1))
    (hπe : ∀ i (g : G ⧸ N) (x : F i), π i ⟨g • (x : FixedPoints.addSubgroup N B),
      hstable i g x x.2⟩ = g • π i x)
    (hLang : ∀ f : G ⧸ N → Q 0, IsCocycle₁ f → IsCoboundary₁ f)
    (hInd : ∀ i, 1 ≤ i → ∀ f : G ⧸ N → Q i, IsCocycle₁ f → IsCoboundary₁ f)
    (cB : ℤ) (hcB : ∀ x : FixedPoints.addSubgroup N B, cB • x ∈ F 0) (m0 : ℤ)
    (v : H1 G A) (hv : ∃ x' : H0 N B, explicitRes1 G A N v = (S.restrict N).explicitDelta0 x') :
    ∃ x : H0 G B, S.explicitDelta0 x = (m0 * cB) • v :=
  (localDescentInputGenuine N S F hstable hsep hcomplete Q π hπs hπk hπe hLang hInd cB
    hcB).kummer m0 v hv

end ZInQ.Manuscript.RC.GlueSweep.Heeg
