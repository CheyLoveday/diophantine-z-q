import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes

/-!
# HeegnerCohomology, part 9: actual Selmer-cone witnesses (H22)

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 8
"Actual finite Selmer-cone witnesses", tex 3372–3384:

"Represent `P_{I,m}` by a continuous global cocycle `p`.  At each constrained place, membership in
the indicated local condition gives a local cycle `u_v` and a degree-zero cochain `q_v` with
`loc_v p - ι_v u_v = d q_v`.  (H22)  These entries give a cycle in
`Cone(C^•(G_{K,S}, M) ⊕ ⨁ U_v → ⨁ C^•(K_v, M))[-1]`."

`exists_witness` (`PROVED`, continuous cohomology): if the localization of a class `[p]` (pullback
along a continuous homomorphism `φ : D → G`, for `G_{K_v} → G_{K,S}`, and an equivariant
coefficient map `f`) lies in the image of a local condition `H¹(D, U) → H¹(D, M')` induced by a
`D`-equivariant `ι : U → M'`, then there are a continuous cocycle `u` of `D` in `U` and `q ∈ M'`
with `f(p(φ x)) - ι(u(x)) = x q - q` for all `x ∈ D`: (H22) in degree one.  `cone_cycle` records
that `(p, u, q)` is then a degree-one cycle of the mapping cone `Cone(C^•(G) ⊕ C^•(D,U) → C^•(D,M'))[-1]`
(its components satisfy `dp = 0`, `du = 0`, `loc p - ι u - dq = 0`).
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti.ContCohomology

variable {G : Type*} [Monoid G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {D : Type*} [Monoid D] [TopologicalSpace D]
  {M' : Type*} [AddCommGroup M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
  [DistribMulAction D M'] [ContinuousSMul D M']
  {U : Type*} [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [DistribMulAction D U] [ContinuousSMul D U]

/-- **(H22) in degree one**, tex 3373–3378, `PROVED`. -/
theorem exists_witness (φ : D →ₜ* G) (f : M →+ M') (hf : Continuous f)
    (hequiv : ∀ (x : D) (m : M), f (φ x • m) = x • f m)
    (ι : U →+[D] M') (hι : Continuous ι) (p : Z1 G M)
    (hp : explicitMap1 G M D M' φ f hf hequiv (p : H1 G M) ∈
      (explicitCoeff1 D U ι hι).range) :
    ∃ (u : Z1 D U) (q : M'), ∀ x : D, f ((p : G → M) (φ x)) - ι ((u : D → U) x) = x • q - q := by
  obtain ⟨y, hy⟩ := hp
  induction y using QuotientAddGroup.induction_on with
  | H u =>
    rw [explicitCoeff1_mk, explicitMap1_mk] at hy
    obtain ⟨q, hq⟩ := mem_B1_iff.mp (H1pi_eq_iff.mp hy.symm)
    refine ⟨u, q, fun x => ?_⟩
    rw [hq x]
    rfl

omit [ContinuousSMul G M] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul D M']
  [ContinuousSMul D U] in
/-- The witness triple is a cycle of the mapping cone in degree one: `p` and `u` are cocycles and
the degree-one component of the cone differential, `loc p - ι u - d q`, vanishes (tex 3378–3380),
`PROVED`. -/
theorem cone_cycle (φ : D →ₜ* G) (f : M →+ M') (ι : U →+[D] M') (p : Z1 G M) (u : Z1 D U)
    (q : M') (h : ∀ x : D, f ((p : G → M) (φ x)) - ι ((u : D → U) x) = x • q - q) :
    groupCohomology.IsCocycle₁ (p : G → M) ∧ groupCohomology.IsCocycle₁ (u : D → U) ∧
      ∀ x : D, f ((p : G → M) (φ x)) - ι ((u : D → U) x) - (x • q - q) = 0 :=
  ⟨(mem_Z1_iff.mp p.2).2, (mem_Z1_iff.mp u.2).2, fun x => by rw [h x, sub_self]⟩

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
