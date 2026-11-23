import ZInQKernel.Contrib.OneProof.KummerLocalDuality.CochainDuality
import ZInQKernel.Contrib.OneProof.KummerLocalDuality.CoefficientDual
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison

/-!
# The finite trace and the roots-of-unity cup

On the same degree-two cycles as the supplied trace, the class obtained
by projecting to the top coefficient is an additive character of that
trace. Its scalar translates recover every power-basis coordinate. This
proves the generating condition needed to test `Acoef`-linear perfectness.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain
open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (topCoord topCoord_mul_gen_pow)

section Post

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {k k' : Type} [CommRing k] [CommRing k']
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  {N : Type} [AddCommGroup N] [Module k' N] [DistribMulAction G N] [SMulCommClass G k' N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

private theorem post_contD_two (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (c : contCochain k G M 2) :
    kannPost (k' := k') f (contD k G M 2 c) = contD k' G N 2 (kannPost f c) := by
  refine contCochains_ext fun v => ?_
  have hv : v = ![v 0, v 1, v 2] := by
    funext j
    fin_cases j <;> rfl
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  change f (contFun (contD k G M 2 c) ![v 0, v 1, v 2]) =
    contFun (contD k' G N 2 (kannPost f c)) ![v 0, v 1, v 2]
  have heval (u : Fin 2 → G) :
      contFun (kannPost (k' := k') f c) u = f (contFun c u) := rfl
  refine (congrArg f (contFun_d23 (k := k) (G := G) (M := M) c (v 0) (v 1) (v 2))).trans ?_
  refine Eq.trans ?_ (contFun_d23 (k := k') (G := G) (M := N)
    (kannPost (k' := k') f c) (v 0) (v 1) (v 2)).symm
  simp only [map_sub, map_add, hf, heval]

/-- The map on degree-two cycles from a discrete equivariant coefficient map,
allowing the source and target to have different scalar rings. -/
def postCycle2 (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x) :
    LinearMap.ker (contD k G M 2) →+ LinearMap.ker (contD k' G N 2) where
  toFun z := ⟨kannPost f z.1, by
    change contD k' G N 2 (kannPost f z.1) = 0
    rw [← post_contD_two f hf, show contD k G M 2 z.1 = 0 from z.2]
    exact contCochains_ext fun g => map_zero f⟩
  map_zero' := Subtype.ext (contCochains_ext fun g => map_zero f)
  map_add' x y := Subtype.ext (contCochains_ext fun g => map_add f _ _)

/-- Reassemble a primitive when every coordinate of a two-cochain is a boundary. -/
private theorem boundary_of_coordinate_boundaries {ι : Type} [Fintype ι]
    (b : ι → k) (j : N →+ M) (hj : ∀ (g : G) (x : N), j (g • x) = g • j x)
    (τ : ι → M →+ N) (hrec : ∀ x : M, ∑ a, b a • j (τ a x) = x)
    (w : contCochain k G M 2)
    (hk : ∀ a, ∃ e : contCochain k' G N 1, contD k' G N 1 e = kannPost (τ a) w) :
    ∃ e, contD k G M 1 e = w := by
  classical
  choose e he using hk
  refine ⟨∑ a, b a • kannPost (k' := k) j (e a), ?_⟩
  apply Subtype.ext
  funext g
  change cfun (contD k G M 1 (∑ a, b a • kannPost j (e a))) g = cfun w g
  rw [map_sum]
  simp only [map_smul]
  rw [kann_cfun_sum_smul, ← hrec (cfun w g)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← kannPost_contD_one j hj (e a), he a]
  rfl

end Post

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (i : ℕ) [NeZero i] (v : Places K S) (hμ : HasRootsOfUnity K S₀ (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]

/-- The actual finite Tate-twist coefficients restricted to this place. -/
abbrev finiteLocalTateTarget :=
  ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ))

private abbrev finiteLocalTateBase :=
  ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ))

private theorem top_mul_recovers_coordinate (k : Fin (kannPB i).dim)
    (z : finiteLocalTateTarget hS i v hμ) :
    urMTopTate hS i hμ v ((kannPB i).gen ^ ((kannPB i).dim - 1 - k.val) • z) =
      kannTau hS i v hμ k z := by
  let pb := kannPB i
  letI : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow (NeZero.ne i)⟩
  have hdim : pb.dim = i := Polynomial.natDegree_X_pow i
  have hpos : 0 < pb.dim := by
    rw [hdim]
    exact Nat.pos_of_ne_zero (NeZero.ne i)
  have hnil : pb.gen ^ pb.dim = 0 := by
    rw [hdim]
    change (AdjoinRoot.root (Polynomial.X ^ i : Polynomial (ZMod (2 ^ i)))) ^ i = 0
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have htop (a : Acoef i) : urMTop i a = topCoord pb hpos a := by
    unfold topCoord
    rw [Module.Basis.coord_apply]
    change ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow i)) a).coeff (i - 1) =
      ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow i)) a).coeff (pb.dim - 1)
    rw [hdim]
  let a : Acoef i := z
  change urMTop i (pb.gen ^ (pb.dim - 1 - k.val) * a) = pb.basis.repr a k
  rw [htop, mul_comm, topCoord_mul_gen_pow pb hpos hnil]

private abbrev restrictedRootCharacter :
    finiteLocalTateTarget hS i v hμ →+ MuAlg (v.1.adicCompletion K) (2 ^ i) :=
  localRootCharacter hS i v hμ

/-- The degree-two class after applying the same character that gives the
coefficient pairing with roots of unity. -/
def localRootCycleClass :
    LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2) →+
      H2 (Gloc K v.1) (MuAlg (v.1.adicCompletion K) (2 ^ i)) :=
  (kerToH2 (k := ℤ) (G := Gloc K v.1) (M := MuAlg (v.1.adicCompletion K) (2 ^ i))).comp
    (postCycle2 (restrictedRootCharacter hS i v hμ) (localRootCharacter_smul hS i v hμ))

private theorem localRootCycleClass_eq_zero_iff
    (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2)) :
    localRootCycleClass hS i v hμ z = 0 ↔
      kannPost (k := Acoef i) (k' := ℤ) (restrictedRootCharacter hS i v hμ) z.1 ∈
        LinearMap.range (contD ℤ (Gloc K v.1) (MuAlg (v.1.adicCompletion K) (2 ^ i)) 1) :=
  kerToH2_eq_zero_iff (k := ℤ) (G := Gloc K v.1) (M := MuAlg (v.1.adicCompletion K) (2 ^ i))
    (postCycle2 (k := Acoef i) (k' := ℤ) (restrictedRootCharacter hS i v hμ)
      (localRootCharacter_smul hS i v hμ) z)

private theorem localRootCycleClass_boundary
    (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2))
    (hz : ∃ t, contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 1 t = z.1) :
    localRootCycleClass hS i v hμ z = 0 := by
  apply (localRootCycleClass_eq_zero_iff hS i v hμ z).2
  exact kannPost_mem_range_two (k := Acoef i) (k' := ℤ) (G := Gloc K v.1)
    (restrictedRootCharacter hS i v hμ) (localRootCharacter_smul hS i v hμ) hz

private theorem localRootCycleClass_detects
    (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2))
    (hz : ∀ r : Acoef i, localRootCycleClass hS i v hμ (r • z) = 0) :
    ∃ t, contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 1 t = z.1 := by
  refine boundary_of_coordinate_boundaries (k := Acoef i) (k' := ℤ) (G := Gloc K v.1)
    (M := finiteLocalTateTarget hS i v hμ) (N := finiteLocalTateBase hS i v hμ)
    (fun k => (kannPB i).basis k) (kannJ hS i v hμ) (kannJ_smul hS i v hμ)
    (kannTau hS i v hμ) (kannTau_recon hS i v hμ) z.1 ?_
  intro k
  let r : Acoef i := (kannPB i).gen ^ ((kannPB i).dim - 1 - k.val)
  obtain ⟨b, hb⟩ := (localRootCycleClass_eq_zero_iff hS i v hμ (r • z)).1 (hz r)
  let e := (kmilneF hS i v hμ).toAddMonoidHom
  refine ⟨kannPost (k := ℤ) (k' := ℤ) e b, ?_⟩
  refine (kannPost_contD_one (k := ℤ) (k' := ℤ) (G := Gloc K v.1)
    e (kmilneF_smul hS i v hμ) b).symm.trans ?_
  refine (congrArg (fun w : contCochain ℤ (Gloc K v.1) (MuAlg (v.1.adicCompletion K) (2 ^ i)) 2 =>
    kannPost (k' := ℤ) e w) hb).trans ?_
  apply Subtype.ext
  funext g
  change (kmilneF hS i v hμ) ((kmilneF hS i v hμ).symm
    (urMTopTate hS i hμ v (r • cfun z.1 g))) = kannTau hS i v hμ k (cfun z.1 g)
  exact ((kmilneF hS i v hμ).apply_symm_apply _).trans
    (top_mul_recovers_coordinate hS i v hμ k (cfun z.1 g))

/-- Evaluate any normalized finite trace by a generating additive character
to obtain exactly the roots-of-unity class. This concerns the supplied trace
on the original finite local cochains, with its original boundary condition. -/
theorem finiteTraceCharacter
    (tr : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).d 1 2 rfl z) = 0)
    (ht : InducesIsoH2 tr) :
    ∃ χ : Acoef i →+ H2 (Gloc K v.1) (MuAlg (v.1.adicCompletion K) (2 ^ i)),
      (∀ z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2),
        χ (tr z.1) = localRootCycleClass hS i v hμ z) ∧
      ∀ a : Acoef i, (∀ b : Acoef i, χ (b * a) = 0) → a = 0 := by
  refine factorTraceCharacter tr ht (localRootCycleClass hS i v hμ)
    (localRootCycleClass_boundary hS i v hμ) ?_
  intro z hz
  obtain ⟨c, hc⟩ := localRootCycleClass_detects hS i v hμ z hz
  exact (congrArg tr hc).symm.trans (htr c)

end Actual

end ZInQ.Manuscript.RC.KummerMaps
