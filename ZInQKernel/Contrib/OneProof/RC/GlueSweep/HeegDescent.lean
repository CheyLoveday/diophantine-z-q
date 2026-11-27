import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes

/-!
# Lane RC22 (glue sweep), share Heeg: the descent `d_a` (H9) on the genuine five-term sequence

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, paragraph 4
"Descend once, before twisting", tex 3017–3024.

Lane RC10 proves the properties of `d_a(c) = 2^e b` (`res b = 2^e c`) for abstract exactness data
`FiveTerm` with the `2^e`-vanishing of the outer groups as hypotheses (`FiveTerm.descend_eq`,
`FiveTerm.res_descend`, `FiveTerm.descend_add`).  The `CloudB3RC53` layer constructs the
sequence over genuine continuous cohomology (`fiveTermGenuine`) and the vanishing from (H2)
(`infResInputGenuine`); its node `H8H9Node` states the lift, the independence and the restriction
for `E[2^a]` over an absolute Galois group, in terms of lifts `b`.  Here RC10's three statements are
given for the genuine `d_a` on any profinite group, with exactly the inputs of `infResInputGenuine`.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (e : ℕ)
  (hH2 : ∀ m : M, (∀ n : N, n • m = m) → ((2 : ℤ) ^ e) • m = 0)

/-- **(H9) is independent of the lift, genuine**, tex 3021–3022.  Kind: `PROVED`, from the
remaining hypotheses: a profinite group `G` (for `G_{H_f}`), a discrete module `M` (for `E[2^a]`),
a closed normal subgroup `N` (for `G_{M_I}`), and (H2) as "`2^e` kills `M^N`".  Conclusion: for
`c ∈ H¹(N, M)^{G/N}` and any `b ∈ H¹(G, M)` with `res b = 2^e c`, `d_a(c) = 2^e b`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm.descend_eq` (lane RC10).  Dischargers:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.fiveTermGenuine`, `.infResInputGenuine`. -/
theorem descend_eq_genuine (c : H1ConjInvariants G M N) (b : H1 G M)
    (hb : explicitResConj1 G M N b = ((2 : ℤ) ^ e) • c) :
    (fiveTermGenuine G M N hN).descend e (infResInputGenuine G M N hN e hH2).killD c =
      ((2 : ℤ) ^ e) • b :=
  (fiveTermGenuine G M N hN).descend_eq e (infResInputGenuine G M N hN e hH2).killA
    (infResInputGenuine G M N hN e hH2).killD c b hb

/-- **The restriction of `d_a(c)` is `2^{2e} c`, genuine**, tex 3024.  Kind: `PROVED`, from the
remaining hypotheses of `descend_eq_genuine`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm.res_descend` (lane RC10).  Dischargers:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.fiveTermGenuine`, `.infResInputGenuine`. -/
theorem res_descend_genuine (c : H1ConjInvariants G M N) :
    explicitResConj1 G M N
        ((fiveTermGenuine G M N hN).descend e (infResInputGenuine G M N hN e hH2).killD c) =
      ((2 : ℤ) ^ (2 * e)) • c :=
  (fiveTermGenuine G M N hN).res_descend e (infResInputGenuine G M N hN e hH2).killD c

/-- **(H9) is additive, genuine**, tex 3022–3023.  Kind: `PROVED`, from the remaining hypotheses of
`descend_eq_genuine`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm.descend_add` (lane RC10).  Dischargers:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.fiveTermGenuine`, `.infResInputGenuine`. -/
theorem descend_add_genuine (c c' : H1ConjInvariants G M N) :
    (fiveTermGenuine G M N hN).descend e (infResInputGenuine G M N hN e hH2).killD (c + c') =
      (fiveTermGenuine G M N hN).descend e (infResInputGenuine G M N hN e hH2).killD c +
        (fiveTermGenuine G M N hN).descend e (infResInputGenuine G M N hN e hH2).killD c' :=
  (fiveTermGenuine G M N hN).descend_add e (infResInputGenuine G M N hN e hH2).killA
    (infResInputGenuine G M N hN e hH2).killD c c'

end ZInQ.Manuscript.RC.GlueSweep.Heeg
