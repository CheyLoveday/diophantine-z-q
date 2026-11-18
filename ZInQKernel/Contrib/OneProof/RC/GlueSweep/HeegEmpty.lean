import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegInfRes

/-!
# Lane RC22 (glue sweep), share Heeg: the case `I = ∅` of (H9)–(H11), genuine

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, tex 3030–3032 and
3293–3295: "For `I = ∅` the relative group is trivial and the same definition gives
`d_a(c) = 2^{2e} c`."

Lane RC10 first stated this as `FiveTerm.descend_trivial` and `H11_empty` for a five-term sequence
`FiveTerm A B B D` whose third term is the second one and whose restriction is the identity.  The
genuine sequence `fiveTermGenuine G M N` of the `CloudB3RC53` layer has third term
`H¹(N, M)^{G/N}`, a different type from `H¹(G, M)` even for `N = G` (exact difference:
`C = H1ConjInvariants G M ⊤ ≠ B = H1 G M`, and `res` is not the identity map but the restriction
to `⊤`), so those statements could not be instantiated with it.  Lane RC27 restated both over a
general `FiveTerm A B C D` (`InfResInput A B C D e`): `descend_trivial` assumes that restriction
is an isomorphism onto the invariants and reads the invariant class through it; `H11_empty`
assumes that the class over `M_∅` is the restriction of the Kummer class over the base field.
Here the genuine sequence for `N = ⊤` (the case `I = ∅`: `M_∅ = H_f`) is shown to meet these
hypotheses, and the earlier genuine reformulations become corollaries of the restated theorems:

* `subsingleton_H1_of_subsingleton`, `subsingleton_H2_of_subsingleton`: the continuous `H¹` and
  `H²` of a group with one element vanish (the outer terms of (H8) for `N = ⊤`);
* `explicitResConj1_top_injective`, `explicitResConj1_top_surjective`,
  `explicitResConj1_top_bijective`: restriction `H¹(G, M) → H¹(⊤, M)^{G/⊤}` is an isomorphism
  (RC10's `FiveTerm.res_bijective_of_subsingleton`);
* `descend_trivial_top`: RC10's restated `FiveTerm.descend_trivial`, applied directly to the
  genuine sequence; `descend_trivial_torsion_top`: the same for `E[2^a]` over an absolute Galois
  group, where (H2) holds with `e = a` (`hH2_torsion_top`), a non-vacuity witness;
* `descend_trivial_genuine`, `H11_empty_genuine` (statements unchanged): corollaries of the
  restated `FiveTerm.descend_trivial` and `H11_empty`.
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

/-- The continuous `H²` of a group with one element vanishes, `PROVED`: a `2`-cocycle `f` is the
coboundary of the constant (hence continuous) cochain with value `f (1, 1)`. -/
theorem subsingleton_H2_of_subsingleton {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [ContinuousMul Γ] [Subsingleton Γ] {V : Type*} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [DistribMulAction Γ V] [ContinuousSMul Γ V] :
    Subsingleton (H2 Γ V) := by
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : H2 Γ V, z = 0 by rw [h x, h y]
  intro z
  induction z using QuotientAddGroup.induction_on with
  | H f =>
    show H2pi Γ V f = 0
    refine H2pi_eq_zero_iff.mpr (mem_B2_iff'.mpr
      ⟨fun _ => (f : Γ × Γ → V) (1, 1), continuous_const, fun g h => ?_⟩)
    rw [Subsingleton.elim g 1, Subsingleton.elim h 1, one_smul, sub_add_cancel]

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

/-- For `N = ⊤`, restriction `H¹(G, M) → H¹(⊤, M)^{G/⊤}` is an isomorphism, `PROVED`: the two outer
terms `H¹(G/⊤, M^⊤)` and `H²(G/⊤, M^⊤)` of the genuine five-term sequence vanish (the relative
group `G/⊤` is trivial), so RC10's `FiveTerm.res_bijective_of_subsingleton` applies.  This is the
hypothesis `hres` of the restated `FiveTerm.descend_trivial`, met by the genuine sequence (a
non-vacuity witness for it). -/
theorem explicitResConj1_top_bijective :
    Function.Bijective (explicitResConj1 G M (⊤ : Subgroup G)) := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have : Subsingleton (H1 (G ⧸ (⊤ : Subgroup G)) (FixedPoints.addSubgroup (⊤ : Subgroup G) M)) :=
    subsingleton_H1_of_subsingleton
  have : Subsingleton (H2 (G ⧸ (⊤ : Subgroup G)) (FixedPoints.addSubgroup (⊤ : Subgroup G) M)) :=
    subsingleton_H2_of_subsingleton
  exact (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).res_bijective_of_subsingleton

/-- For `N = ⊤`, every `G/⊤`-invariant class of `H¹(⊤, M)` is a restriction, `PROVED` (from
`explicitResConj1_top_bijective`: the transgression lands in `H²(G/⊤, M^⊤) = 0`). -/
theorem explicitResConj1_top_surjective :
    Function.Surjective (explicitResConj1 G M (⊤ : Subgroup G)) :=
  (explicitResConj1_top_bijective G M).2

/-- **`d_a(c) = 2^{2e} c` for `I = ∅`, genuine, as a direct application of RC10's restated
`FiveTerm.descend_trivial`**, tex 3030–3032.  Kind: `PROVED`, from the remaining hypothesis (H2)
for `N = ⊤` ("`2^e` kills the `G`-fixed elements of `M`", for `E(H_f)[2^a]`), on a profinite group
`G` (for `G_{H_f}`) and a discrete module `M` (for `E[2^a]`).  Conclusion: for an invariant class
`c ∈ H¹(⊤, M)^{G/⊤}` (the third term of the genuine sequence for `N = ⊤`), `d_a(c)` is `2^{2e}`
times the class of `H¹(G, M)` restricting to `c`.  The hypothesis `hres` of `descend_trivial` is
`explicitResConj1_top_bijective`. -/
theorem descend_trivial_top (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : (⊤ : Subgroup G), n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    (c : H1ConjInvariants G M ⊤) :
    (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).descend e
        (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2).killD c =
      ((2 : ℤ) ^ (2 * e)) •
        (AddEquiv.ofBijective (explicitResConj1 G M ⊤) (explicitResConj1_top_bijective G M)).symm
          c :=
  (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).descend_trivial e
    (explicitResConj1_top_bijective G M) _ c

/-- **`d_a(c) = 2^{2e} c` for `I = ∅`, genuine**, tex 3030–3032.  Kind: `PROVED`, from the
remaining hypothesis (H2) for `N = ⊤` ("`2^e` kills the `G`-fixed elements of `M`", for
`E(H_f)[2^a]`), on a profinite group `G` (for `G_{H_f}`) and a discrete module `M` (for `E[2^a]`).
Conclusion: for `c ∈ H¹(G, M)`, the descent (H9) on the genuine five-term sequence for `N = ⊤`,
applied to the restriction of `c`, is `2^{2e} c`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm.descend_trivial` (lane RC10, as restated by
Lane RC27 over a general `FiveTerm A B C D`).  This is now a corollary of it (through
`descend_trivial_top`); it is also the identity `FiveTerm.descend_res` on the genuine sequence.
Dischargers: `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.fiveTermGenuine`,
`.infResInputGenuine`, with `explicitResConj1_top_bijective`. -/
theorem descend_trivial_genuine (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : (⊤ : Subgroup G), n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    (c : H1 G M) :
    (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).descend e
        (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2).killD
        (explicitResConj1 G M ⊤ c) =
      ((2 : ℤ) ^ (2 * e)) • c := by
  rw [descend_trivial_top G M e hH2]
  congr 1
  exact (AddEquiv.ofBijective _ _).symm_apply_eq.mpr rfl

/-- **(H8)–(H9) and (H11) for `I = ∅`, genuine**, tex 3030–3032 and 3293–3295.  Kind: `PROVED`,
from the remaining hypotheses: a profinite group `G` (for `G_{H_f}`), a discrete module `M` (for
`E[2^a]`), (H2) for `N = ⊤` (`2^e` kills `M^G`, for `E(H_f)[2^a]`), and an additive map
`κ : P → H¹(G, M)` (for the Kummer map of `E(H_f)`).  Conclusion: `b_{∅,a} = m₀ C_bad d_a(c_{∅,a})`,
with `c_{∅,a}` the restriction of `κ(C_π x)` to `⊤`, is the class `κ(L x)`,
`L = m₀ C_π C_bad 2^{2e}`: the Kummer class of the `L`-multiplied point.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H11_empty` (lane RC10, as restated by Lane RC27 over a
general `InfResInput A B C D e`).  This is now a direct application of it, with `δa = res ∘ κ`
(so its hypothesis `hκ` holds by definition): a non-vacuity witness for `H11_empty` on the genuine
sequence.  Dischargers: `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.infResInputGenuine`. -/
theorem H11_empty_genuine (e : ℕ)
    (hH2 : ∀ m : M, (∀ n : (⊤ : Subgroup G), n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    {P : Type*} [AddCommGroup P] (κ : P →+ H1 G M) (m0 Cπ Cbad : ℕ) (x : P) :
    ((m0 * Cbad : ℕ) : ℤ) •
        (fiveTermGenuine G M ⊤ (isClosed_top_subgroup G)).descend e
          (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2).killD
          (explicitResConj1 G M ⊤ (κ ((Cπ : ℤ) • x))) =
      κ (Lmult m0 Cπ Cbad e • x) :=
  H11_empty e (infResInputGenuine G M ⊤ (isClosed_top_subgroup G) e hH2) κ
    ((explicitResConj1 G M ⊤).comp κ) (fun _ => rfl) m0 Cπ Cbad x

section Torsion

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- (H2) for `N = ⊤` holds for `V_a = E[2^a]` with `e = a`, `PROVED`: `2^a` kills `E(K^sep)[2^a]`,
hence its `G_K`-fixed part. -/
theorem hH2_torsion_top (a : ℕ) :
    ∀ P : W.TorsionCoeff (2 ^ a),
      (∀ σ : (⊤ : Subgroup (TauCeti.AbsoluteGaloisGroup K)), σ • P = P) →
        ((2 : ℤ) ^ a) • P = 0 := by
  intro P _
  have hP : (2 ^ a : ℕ) • P = 0 := AddSubgroup.torsionBy.nsmul P
  rw [show ((2 : ℤ) ^ a) = ((2 ^ a : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul]
  exact hP

/-- **Non-vacuity of the restated `FiveTerm.descend_trivial` on the genuine Galois sequence**,
tex 3030–3032, `PROVED`: for every Weierstrass curve `E/K` and every `a`, the genuine five-term
sequence of `V_a = E[2^a]` over `G_K` at `N = ⊤` (the case `I = ∅`, `M_∅ = K`), with `e = a`,
meets all hypotheses of `descend_trivial` (restriction bijective: `explicitResConj1_top_bijective`;
`2^e` on the outer terms: `infResInputTorsion` from `hH2_torsion_top`), and the theorem applies. -/
theorem descend_trivial_torsion_top (a : ℕ)
    (c : H1ConjInvariants (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) ⊤) :
    (infResInputTorsion W a ⊤ (isClosed_top_subgroup _) a (hH2_torsion_top W a)).seq.descend a
        (infResInputTorsion W a ⊤ (isClosed_top_subgroup _) a (hH2_torsion_top W a)).killD c =
      ((2 : ℤ) ^ (2 * a)) •
        (AddEquiv.ofBijective
            (explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) ⊤)
            (explicitResConj1_top_bijective _ _)).symm c :=
  descend_trivial_top (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) a
    (hH2_torsion_top W a) c

end Torsion

end ZInQ.Manuscript.RC.GlueSweep.Heeg
