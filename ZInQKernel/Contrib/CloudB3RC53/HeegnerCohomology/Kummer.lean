import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.DeltaNaturality
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.Basic

/-!
# HeegnerCohomology, part 3: the Kummer sequence over `M_I` with its `Gal(M_I/H_f)`-action

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, (H7) and its
uses, tex 2987–3002 (the derivative class `c_{I,a} = δ_a(C_π D_I y_{f n_I})` lies in
`H¹(M_I, E[2^a])^{Gal(M_I/H_f)}`), and the Kummer statements at tex 3058–3062, 3080–3084,
3111–3113.

RC10 records the Kummer map as the interface `KummerSequence Γ P HV HE a` (file
`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Interfaces.lean`): `δ_a : P → HV`,
`j : HV → HE`, `δ_a` equivariant for the group `Γ`, `ker δ_a = 2^a P`, and `ker j = im δ_a`, with
`P = E(F)`, `HV = H¹(F, E[2^a])`, `HE = H¹(F, E)` and `Γ = Gal(M_I/H_f)` (consumed by RC10's
`H7_assembled`).  This file discharges that interface over genuine continuous cohomology:

* `quotientConjAction`: for a normal subgroup `N` of a topological group `G`, the conjugation
  action of `G` on `H¹(N, A)` (Tau Ceti's `explicitConj1`) factors through `G ⧸ N`, because
  inner conjugation is trivial on cohomology (`explicitConj1_eq_id_of_mem`).  For `G = G_{H_f}`,
  `N = G_{M_I}` this is the action of `Γ = Gal(M_I/H_f)` on `H¹(M_I, E[2^a])`.
* `delta0_conj` (`PROVED`): the connecting map `δ⁰` of a short exact sequence of discrete
  `G`-modules, restricted to `N`, intertwines the actions of `G` on `H⁰(N, C)` and `H¹(N, A)`.
* `kummerSequenceGenuine` (`PROVED`): RC10's `KummerSequence (G ⧸ N) (H⁰(N, B)) (H¹(N, A))
  (H¹(N, B)) a` for any short exact sequence `0 → A → B → B → 0` whose second map is
  multiplication by `2^a`.
* `kummerSequenceTorsion` (`PROVED`): the case `G = G_{H_f}` (an absolute Galois group),
  `0 → E[2^a] → E(K^sep) → E(K^sep) → 0` (Tau Ceti's `kummerShortExact`, needing `2 ≠ 0` in the
  field), any normal `N` (for `G_{M_I}`): then `P = E(K^sep)^N = E(M_I)`.

Status: `GLUE` made `PROVED` (Kummer theory and the conjugation action are standard and are now
theorems over genuine objects).
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra (KummerSequence)

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  (N : Subgroup G) [N.Normal]

/-- Conjugation `g ↦ explicitConj1 N g` as a monoid homomorphism `G → End(H¹(N, A))`. -/
noncomputable def conjHom : G →* AddMonoid.End (H1 N A) where
  toFun g := explicitConj1 (M := A) N g
  map_one' := explicitConj1_one N
  map_mul' g h := explicitConj1_mul N g h

/-- The conjugation action factors through `G ⧸ N` (inner conjugation is trivial). -/
noncomputable def quotientConjHom : G ⧸ N →* AddMonoid.End (H1 N A) :=
  QuotientGroup.lift N (conjHom (A := A) N) (fun n hn => by
    rw [MonoidHom.mem_ker]
    exact explicitConj1_eq_id_of_mem N ⟨n, hn⟩)

/-- **The action of `G ⧸ N` on `H¹(N, A)`** (for `G_{H_f} ⧸ G_{M_I} = Gal(M_I/H_f)` acting on
`H¹(M_I, E[2^a])`, tex 2995). -/
noncomputable instance quotientConjAction : DistribMulAction (G ⧸ N) (H1 N A) :=
  DistribMulAction.compHom (H1 N A) (quotientConjHom (A := A) N)

theorem quotient_smul_H1 (g : G) (x : H1 N A) :
    ((g : G ⧸ N) • x : H1 N A) = explicitConj1 N g x := rfl

end Conj

section Delta

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type*} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]
  (S : DiscreteShortExact G A B C) (N : Subgroup G) [N.Normal]

/-- **`δ⁰` intertwines conjugation**, `PROVED`: for `c ∈ H⁰(N, C)` and `g ∈ G`,
`δ⁰(g • c) = g_*(δ⁰ c)` in `H¹(N, A)`, where `g_*` is conjugation by `g`.  (Naturality of `δ⁰` in
the compatible pair `(n ↦ g⁻¹ n g, g•)`.) -/
theorem delta0_conj (g : G) (c : H0 N C) :
    (S.restrict N).explicitDelta0 (g • c) = explicitConj1 N g ((S.restrict N).explicitDelta0 c) := by
  have hfA : ∀ (h : N) (a : A), DistribSMul.toAddMonoidHom A g (Subgroup.inverseConjugationHom N g h • a) =
      h • DistribSMul.toAddMonoidHom A g a := fun h a => Subgroup.inverseConjugationHom_smul N g h a
  have hfB : ∀ (h : N) (b : B), DistribSMul.toAddMonoidHom B g (Subgroup.inverseConjugationHom N g h • b) =
      h • DistribSMul.toAddMonoidHom B g b := fun h b => Subgroup.inverseConjugationHom_smul N g h b
  exact (DiscreteShortExact.explicitDelta0_naturality (S.restrict N) (S.restrict N)
    (Subgroup.inverseConjugationHom N g) (DistribSMul.toAddMonoidHom A g) (DistribSMul.toAddMonoidHom B g)
    (DistribSMul.toAddMonoidHom C g) hfA hfB (fun a => (S.incl_equivariant g a).symm)
    (fun b => (S.proj_equivariant g b).symm) c (g • c) rfl).symm

end Delta

section Kummer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
  (N : Subgroup G) [N.Normal]

/-- **RC10's `KummerSequence` for genuine continuous cohomology** (tex 2995–3002, 3058–3062,
3111–3113), `PROVED`: for a short exact sequence `0 → A → B → B → 0` of discrete `G`-modules
whose second map is multiplication by `2^a` (for `A = E[2^a]`, `B = E(K^sep)`), and a normal
subgroup `N` (for `G_{M_I}`), with `Γ = G ⧸ N`, `P = H⁰(N, B) = B^N` (for `E(M_I)`),
`HV = H¹(N, A)`, `HE = H¹(N, B)`: `δ_a` is the connecting map, `j` is induced by `A → B`. -/
noncomputable def kummerSequenceGenuine (a : ℕ) (S : DiscreteShortExact G A B B)
    (hproj : ∀ b, S.proj b = ((2 : ℤ) ^ a) • b) :
    KummerSequence (G ⧸ N) (H0 N B) (H1 N A) (H1 N B) a where
  δ := (S.restrict N).explicitDelta0
  j := explicitCoeff1 N A (S.restrict N).inclDistribMulActionHom continuous_of_discreteTopology
  equivariant γ x := by
    induction γ using QuotientGroup.induction_on with
    | H g =>
      rw [TauCeti.coe_quotient_smul_fixedPoints_addSubgroup, quotient_smul_H1]
      exact delta0_conj S N g x
  ker_δ x := by
    rw [← AddMonoidHom.mem_ker, ← (S.restrict N).explicitLongExact_H0C]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subtype.ext (by
        rw [coe_explicitCoeff0, DiscreteShortExact.projDistribMulActionHom_apply,
          DiscreteShortExact.restrict_proj, hproj]
        rfl)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subtype.ext (by
        rw [coe_explicitCoeff0, DiscreteShortExact.projDistribMulActionHom_apply,
          DiscreteShortExact.restrict_proj, hproj]
        rfl)⟩
  exact v := by
    rw [← AddMonoidHom.mem_ker, ← (S.restrict N).explicitLongExact_H1A]
    rfl

end Kummer

section Elliptic

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]

set_option synthInstance.maxHeartbeats 400000

/-- **The Kummer sequence of `E` over `M_I` with its `Gal(M_I/H_f)`-action** (tex 2995–3002),
`PROVED`: for an elliptic curve `E` over a field `K` (for `H_f`) in which `2 ≠ 0`, a normal
subgroup `N ≤ G_K` (for `G_{M_I}`), and `a ≥ 0`, RC10's `KummerSequence` holds with
`Γ = G_K ⧸ N`, `P = E(K^sep)^N`, `HV = H¹(N, E[2^a])`, `HE = H¹(N, E(K^sep))`, the Kummer map
being the connecting map of `0 → E[2^a] → E → E → 0`. -/
noncomputable def kummerSequenceTorsion (a : ℕ) (h2 : IsUnit ((2 ^ a : ℕ) : K))
    (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal] :
    KummerSequence (TauCeti.AbsoluteGaloisGroup K ⧸ N) (H0 N W.PointCoeff)
      (H1 N (W.TorsionCoeff (2 ^ a))) (H1 N W.PointCoeff) a :=
  kummerSequenceGenuine N a (W.kummerShortExact (2 ^ a) h2) (fun b => by
    show (2 ^ a : ℕ) • b = _
    rw [← natCast_zsmul]; push_cast; rfl)

/-- **Node: Kummer sequence over `M_I`**, tex 2995–3002, `PROVED`: for every field `K` with
`2 ≠ 0`, elliptic curve `E/K`, `a`, and normal subgroup `N ≤ G_K`, the Kummer map
`δ_a : E(K^sep)^N → H¹(N, E[2^a])` is `G_K/N`-equivariant, has kernel `2^a E(K^sep)^N`, and its
image is the kernel of `H¹(N, E[2^a]) → H¹(N, E)`. -/
def KummerNode : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (a : ℕ)
    (_h2 : IsUnit ((2 ^ a : ℕ) : K)) (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal],
    Nonempty (KummerSequence (TauCeti.AbsoluteGaloisGroup K ⧸ N) (H0 N W.PointCoeff)
      (H1 N (W.TorsionCoeff (2 ^ a))) (H1 N W.PointCoeff) a)

theorem kummerNode_proof : KummerNode := by
  intro K _ _ W _ a h2 N _
  exact ⟨kummerSequenceTorsion W a h2 N⟩

end Elliptic

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
