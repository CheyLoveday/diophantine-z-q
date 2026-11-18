import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegInfRes

/-!
# Lane RC22 (glue sweep), share Heeg: the case `I = ∅` of (H9)–(H11), genuine

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, tex 3030–3032 and
3293–3295: "For `I = ∅` the relative group is trivial and the same definition gives
`d_a(c) = 2^{2e} c`."

Lane RC10 states this as `FiveTerm.descend_trivial` and `H11_empty`, for a five-term sequence
`FiveTerm A B B D` whose third term is the second one and whose restriction is the identity.  The
genuine sequence `fiveTermGenuine G M N` of the `CloudB3RC53` layer has third term
`H¹(N, M)^{G/N}`, a different type from `H¹(G, M)` even for `N = G`, so RC10's statements
cannot be instantiated with it (exact difference: `C = H1ConjInvariants G M ⊤ ≠ B = H1 G M`, and
`res` is not the identity map but the
restriction to `⊤`).  Here the genuine form is proved instead: for `N = ⊤` the inflation term
`H¹(G/⊤, M^⊤)` vanishes, so restriction to `⊤` is injective, and the two statements hold with the
restriction inserted.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

/-- The continuous `H¹` of a group with one element vanishes, `PROVED`: a `1`-cocycle `f` has
`f 1 = f 1 + f 1`, hence `f = 0`. -/
theorem subsingleton_H1_of_subsingleton {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [Subsingleton Γ] {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [DistribMulAction Γ V] [ContinuousSMul Γ V] : Subsingleton (H1 Γ V) := by
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : H1 Γ V, z = 0 by rw [h x, h y]
  intro z
  induction z using QuotientAddGroup.induction_on with
  | H f =>
    show H1pi Γ V f = 0
    refine H1pi_eq_zero_iff.mpr (mem_B1_iff.mpr ⟨0, fun g => ?_⟩)
    have hc := ((mem_Z1_iff (G := Γ) (M := V)).mp f.2).2 1 1
    rw [one_mul, one_smul] at hc
    have h1 : (f : Γ → V) 1 = 0 := by
      have := congrArg (fun t => t - (f : Γ → V) 1) hc
      simpa using this.symm
    rw [Subsingleton.elim g 1, h1, smul_zero, sub_zero]

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- `⊤` is closed, `PROVED`. -/
theorem isClosed_top_subgroup : IsClosed (((⊤ : Subgroup G)) : Set G) := by
  rw [Subgroup.coe_top]; exact isClosed_univ

/-- For `N = ⊤` (the case `I = ∅`: `M_∅ = H_f`), restriction `H¹(G, M) → H¹(⊤, M)^{G/⊤}` of the
genuine five-term sequence is injective, `PROVED`: its kernel is inflated from
`H¹(G/⊤, M^⊤) = 0`. -/
theorem explicitResConj1_top_injective :
    Function.Injective (explicitResConj1 G M (⊤ : Subgroup G)) := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have : Subsingleton (H1 (G ⧸ (⊤ : Subgroup G)) (FixedPoints.addSubgroup (⊤ : Subgroup G) M)) :=
    subsingleton_H1_of_subsingleton
  rw [injective_iff_map_eq_zero]
  intro b hb
  obtain ⟨x, hx⟩ := ((fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).exact_B b).mp hb
  rw [← hx, Subsingleton.elim x 0, map_zero]

/-- **`d_a(c) = 2^{2e} c` for `I = ∅`, genuine**, tex 3030–3032.  Kind: `PROVED`, from the
remaining hypothesis (H2) for `N = ⊤` ("`2^e` kills the `G`-fixed elements of `M`", for
`E(H_f)[2^a]`), on a profinite group `G` (for `G_{H_f}`) and a discrete module `M` (for `E[2^a]`).
Conclusion: for `c ∈ H¹(G, M)`, the descent (H9) on the genuine five-term sequence for `N = ⊤`,
applied to the restriction of `c`, is `2^{2e} c`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm.descend_trivial` (lane RC10).  This is a
genuine reformulation, not an instance: RC10's statement needs `C = B` with `res = id`, while the
genuine sequence has `C = H1ConjInvariants G M ⊤` (see the module docstring).  Dischargers:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.fiveTermGenuine`, `.infResInputGenuine`, with RC10's
`FiveTerm.res_descend` and `explicitResConj1_top_injective`. -/
theorem descend_trivial_genuine (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : (⊤ : Subgroup G), n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    (c : H1 G M) :
    (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).descend e
        (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2).killD
        (explicitResConj1 G M ⊤ c) =
      ((2 : ℤ) ^ (2 * e)) • c := by
  apply explicitResConj1_top_injective G M
  rw [map_zsmul]
  exact (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).res_descend e
    (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2).killD _

/-- **(H8)–(H9) and (H11) for `I = ∅`, genuine**, tex 3030–3032 and 3293–3295.  Kind: `PROVED`,
from the remaining hypotheses: a profinite group `G` (for `G_{H_f}`), a discrete module `M` (for
`E[2^a]`), (H2) for `N = ⊤` (`2^e` kills `M^G`, for `E(H_f)[2^a]`), and an additive map
`κ : P → H¹(G, M)` (for the Kummer map of `E(H_f)`).  Conclusion: `b_{∅,a} = m₀ C_bad d_a(c_{∅,a})`,
with `c_{∅,a}` the restriction of `κ(C_π x)` to `⊤`, is the class `κ(L x)`,
`L = m₀ C_π C_bad 2^{2e}`: the Kummer class of the `L`-multiplied point.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H11_empty` (lane RC10).  A genuine reformulation, not
an instance (RC10 needs `C = B`, `res = id`; see the module docstring).  Dischargers:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.infResInputGenuine` (through `H11_assembled_genuine`)
and `explicitResConj1_top_injective`. -/
theorem H11_empty_genuine (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : (⊤ : Subgroup G), n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    {P : Type*} [AddCommGroup P] (κ : P →+ H1 G M) (m0 Cπ Cbad : ℕ) (x : P) :
    ((m0 * Cbad : ℕ) : ℤ) •
        (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).descend e
          (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2).killD
          (explicitResConj1 G M ⊤ (κ ((Cπ : ℤ) • x))) =
      κ (Lmult m0 Cπ Cbad e • x) := by
  apply explicitResConj1_top_injective G M
  exact H11_assembled_genuine G M ⊤ (isClosed_top_subgroup G) e hH2
    ((explicitResConj1 G M ⊤).comp κ) m0 Cπ Cbad x

end ZInQ.Manuscript.RC.GlueSweep.Heeg
