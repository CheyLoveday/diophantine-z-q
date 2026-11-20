import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegKummer
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes

/-!
# Lane RC22 (glue sweep), share Heeg: (H8)–(H11) with the genuine five-term sequence

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, paragraph 4
"Descend once, before twisting" and (H11), tex 3004–3032 and 3064–3086.

Lane RC10 proves (H11) as `ZInQ.Manuscript.RC.HeegnerAlgebra.H11_assembled` from the interface
`InfResInput` (the five-term sequence (H8), `PRINT` Nekovář (4.1.4.1), with the `2^e`-vanishing of
its outer groups from (H2)).  The interface is constructed over genuine continuous cohomology in
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology` (`infResInputGenuine` for a profinite group and a
closed normal subgroup, `infResInputTorsion` for `E[2^a]` over an absolute Galois group), from the
single hypothesis that `2^e` kills the `N`-fixed part of the coefficients ((H2)).  Here:

* `H11_assembled_genuine`, `H11_assembled_torsion`: RC10's (H11) with that input;
* `H7_H11_genuine`: (H7) and (H11) together for the genuine Kummer map: the derivative class
  `c_{I,a} = δ_a(C_π D_I y)` is a genuine `G/N`-invariant class, and
  `b_{I,a} = m₀ C_bad d_a(c_{I,a})` restricts to the genuine Kummer class `δ_a(L D_I y)`,
  `L = m₀ C_π C_bad 2^{2e}`.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

section Genuine

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **(H11) with the genuine five-term sequence**, tex 3004–3032 and 3074–3081.  Kind: `PROVED`,
from the remaining hypotheses: a profinite group `G` (for `G_{H_f}`), a discrete `G`-module `M`
(for `E[2^a]`), a closed normal subgroup `N` (for `G_{M_I}`), (H2) in the form "`2^e` kills every
`N`-fixed element of `M`", and an additive map `δa` into the `G/N`-invariant classes of
`H¹(N, M)`.  Conclusion: the restriction of `m₀ C_bad d_a(δa(C_π x))` is `δa(L x)`,
`L = m₀ C_π C_bad 2^{2e}`, where `d_a` is (H9) on the genuine sequence `fiveTermGenuine`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H11_assembled` (lane RC10, its `InfResInput`
hypothesis).  Discharger: `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.infResInputGenuine`. -/
theorem H11_assembled_genuine (M : Type*) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : N, n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    {P : Type*} [AddCommGroup P] (δa : P →+ H1ConjInvariants G M N) (m0 Cπ Cbad : ℕ) (x : P) :
    explicitResConj1 G M N (((m0 * Cbad : ℕ) : ℤ) •
        (fiveTermGenuine G M N hN).descend e (infResInputGenuine G M N hN e hH2).killD
          (δa ((Cπ : ℤ) • x))) =
      δa (Lmult m0 Cπ Cbad e • x) :=
  H11_assembled e (infResInputGenuine G M N hN e hH2) δa m0 Cπ Cbad x

end Genuine

section Elliptic

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

set_option synthInstance.maxHeartbeats 400000 in
/-- **(H11) for `V_a = E[2^a]`**, tex 3004–3032 and 3074–3081.  Kind: `PROVED`, from the
remaining hypotheses: a Weierstrass curve `E/K` (for `K = H_f`), a closed normal subgroup `N` of
`G_K` (for `G_{M_I}`), (H2) as "`2^e` kills the `N`-fixed points of `E(K^sep)[2^a]`", and an
additive map `δa` into the invariant classes of `H¹(N, E[2^a])`.  Conclusion as in
`H11_assembled_genuine`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H11_assembled` (lane RC10).  Discharger:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.infResInputTorsion`. -/
theorem H11_assembled_torsion (a : ℕ) (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal]
    (hN : IsClosed (N : Set (TauCeti.AbsoluteGaloisGroup K))) (e : ℕ)
    (hH2 : ∀ P : W.TorsionCoeff (2 ^ a), (∀ σ : N, σ • P = P) → ((2 : ℤ) ^ e) • P = 0)
    {P : Type*} [AddCommGroup P]
    (δa : P →+ H1ConjInvariants (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N)
    (m0 Cπ Cbad : ℕ) (x : P) :
    explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N
        (((m0 * Cbad : ℕ) : ℤ) •
          (infResInputTorsion W a N hN e hH2).seq.descend e
            (infResInputTorsion W a N hN e hH2).killD (δa ((Cπ : ℤ) • x))) =
      δa (Lmult m0 Cπ Cbad e • x) :=
  H11_assembled e (infResInputTorsion W a N hN e hH2) δa m0 Cπ Cbad x

end Elliptic

section Composite

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- **(H7) and (H8)–(H11) together over genuine continuous cohomology**, tex 2992–3032 and
3064–3081.  Kind: `PROVED`, from the remaining hypotheses: a profinite group `G` (for `G_{H_f}`), a
short exact sequence `S : 0 → A → B → B → 0` of discrete `G`-modules with second map `2^a` (for
`0 → E[2^a] → E → E → 0`), a closed normal subgroup `N` (for `G_{M_I}`), (H2) as "`2^e` kills the
`N`-fixed elements of `A`", RC10's `DerivativeInput` over `G ⧸ N` acting on `H⁰(N, B)` (for
`E(M_I)`), and (H12) at every prime of `I`.  With `x = D_I y_{f n_I}`:

* `c_{I,a} := δ_a(C_π x)` (the genuine Kummer class) is a `G/N`-invariant class (H7), i.e. an
  element `c` of `H¹(N, A)^{G/N}`, the third term of the genuine five-term sequence;
* `b_{I,a} := m₀ C_bad d_a(c)` (with (H9) on that sequence) restricts to the genuine Kummer class
  `δ_a(L x)`, `L = m₀ C_π C_bad 2^{2e}` (H11).

Consumers: `ZInQ.Manuscript.RC.HeegnerAlgebra.H7_assembled` and `.H11_assembled` (lane RC10:
`KummerSequence`, `InfResInput`, and the abstract map `δa` of `H11_assembled`, here the genuine
Kummer map on the points whose Kummer class is invariant).  Dischargers:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.kummerSequenceGenuine` and `.infResInputGenuine`. -/
theorem H7_H11_genuine (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (a e : ℕ)
    (S : DiscreteShortExact G A B B) (hproj : ∀ b, S.proj b = ((2 : ℤ) ^ a) • b)
    (hH2 : ∀ m : A, (∀ n : N, n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    {ι 𝒜 : Type*} [DecidableEq ι] [CommRing 𝒜] [Module 𝒜 (H0 N B)]
    (I : Finset ι) (Din : DerivativeInput ι 𝒜 (G ⧸ N) (H0 N B) I)
    (hH12 : ∀ i ∈ I, (2 : ℤ) ^ (a + 1) ∣ Din.aℓ i ∧ (2 : ℤ) ^ (a + 1) ∣ Din.ℓnum i + 1)
    (m0 Cπ Cbad : ℕ) :
    ∃ c : H1ConjInvariants G A N,
      (c : H1 N A) = (S.restrict N).explicitDelta0 ((Cπ : ℤ) • ((∏ j ∈ I, Din.D j) • Din.y I)) ∧
      (explicitResConj1 G A N (((m0 * Cbad : ℕ) : ℤ) •
          (fiveTermGenuine G A N hN).descend e (infResInputGenuine G A N hN e hH2).killD c) :
          H1 N A) =
        (S.restrict N).explicitDelta0 (Lmult m0 Cπ Cbad e • ((∏ j ∈ I, Din.D j) • Din.y I)) := by
  set δ := (S.restrict N).explicitDelta0 with hδdef
  -- the points whose genuine Kummer class is `G/N`-invariant
  let Pinv : AddSubgroup (H0 N B) := AddSubgroup.comap δ (H1ConjInvariants G A N)
  -- `x = D_I y` lies there, by (H7) with `C_π = 1`
  have hx : (∏ j ∈ I, Din.D j) • Din.y I ∈ Pinv := by
    show δ ((∏ j ∈ I, Din.D j) • Din.y I) ∈ H1ConjInvariants G A N
    intro g
    have h := H7_assembled_genuine N a S hproj I Din 1 hH12 g
    simpa only [Int.cast_one, one_mul] using h
  let δa : Pinv →+ H1ConjInvariants G A N :=
    AddMonoidHom.codRestrict (δ.comp Pinv.subtype) _ (fun p => p.2)
  have h11 := H11_assembled_genuine G A N hN e hH2 δa m0 Cπ Cbad ⟨_, hx⟩
  refine ⟨δa ((Cπ : ℤ) • ⟨_, hx⟩), rfl, ?_⟩
  rw [h11]
  rfl

end Composite

end ZInQ.Manuscript.RC.GlueSweep.Heeg
