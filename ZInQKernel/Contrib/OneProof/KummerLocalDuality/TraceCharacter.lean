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
  rw [contFun_d23, contFun_d23]
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
      (AdjoinRoot.powerBasisAux' (Polynomial.monic_X_pow i)).repr a
        ⟨pb.dim - 1, by omega⟩
    rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, hdim]
  change urMTop i (pb.gen ^ (pb.dim - 1 - k.val) * (show Acoef i from z)) = pb.basis.coord k z
  rw [htop, mul_comm, topCoord_mul_gen_pow pb hpos hnil, Module.Basis.coord_apply]

/-- The degree-two class after applying the same character that gives the
coefficient pairing with roots of unity. -/
def localRootCycleClass :
    LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2) →+
      H2 (Gloc K v.1) (MuAlg (v.1.adicCompletion K) (2 ^ i)) :=
  (kerToH2 (k := ℤ) (G := Gloc K v.1) (M := MuAlg (v.1.adicCompletion K) (2 ^ i))).comp
    (postCycle2 (localRootCharacter hS i v hμ) (localRootCharacter_smul hS i v hμ))

private theorem localRootCycleClass_boundary
    (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2))
    (hz : ∃ t, contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 1 t = z.1) :
    localRootCycleClass hS i v hμ z = 0 := by
  obtain ⟨t, ht⟩ := hz
  apply (kerToH2_eq_zero_iff _).2
  refine ⟨kannPost (k' := ℤ) (localRootCharacter hS i v hμ) t, ?_⟩
  change _ = kannPost (localRootCharacter hS i v hμ) z.1
  rw [← kannPost_contD_one _ (localRootCharacter_smul hS i v hμ), ht]

private theorem localRootCycleClass_detects
    (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2))
    (hz : ∀ r : Acoef i, localRootCycleClass hS i v hμ (r • z) = 0) :
    ∃ t, contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 1 t = z.1 := by
  classical
  have hc (k : Fin (kannPB i).dim) : ∃ c : contCochain ℤ (Gloc K v.1) (finiteLocalTateBase hS i v hμ) 1,
      contD ℤ (Gloc K v.1) (finiteLocalTateBase hS i v hμ) 1 c = kannPost (kannTau hS i v hμ k) z.1 := by
    let r := (kannPB i).gen ^ ((kannPB i).dim - 1 - k.val)
    obtain ⟨b, hb⟩ := (kerToH2_eq_zero_iff
      (postCycle2 (k := Acoef i) (k' := ℤ) (localRootCharacter hS i v hμ)
        (localRootCharacter_smul hS i v hμ) (r • z))).1 (hz r)
    change contD ℤ (Gloc K v.1) (MuAlg (v.1.adicCompletion K) (2 ^ i)) 1 b =
      kannPost (localRootCharacter hS i v hμ) (r • z.1) at hb
    refine ⟨kannPost (kmilneF hS i v hμ).toAddMonoidHom b, ?_⟩
    rw [← kannPost_contD_one _ (kmilneF_smul hS i v hμ), hb]
    refine contCochains_ext fun g => ?_
    change kmilneF hS i v hμ (localRootCharacter hS i v hμ (r • contFun z.1 g)) =
      kannTau hS i v hμ k (contFun z.1 g)
    rw [show localRootCharacter hS i v hμ (r • contFun z.1 g) =
        (kmilneF hS i v hμ).symm (urMTopTate hS i hμ v (r • contFun z.1 g)) from rfl,
      AddEquiv.apply_symm_apply]
    exact top_mul_recovers_coordinate hS i v hμ k _
  choose c hc using hc
  refine ⟨∑ k, (kannPB i).basis k • kannPost (k' := Acoef i) (kannJ hS i v hμ) (c k), ?_⟩
  apply Subtype.ext
  funext g
  change cfun (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 1
    (∑ k, (kannPB i).basis k • kannPost (kannJ hS i v hμ) (c k))) g = cfun z.1 g
  rw [map_sum]
  simp only [map_smul]
  rw [kann_cfun_sum_smul, ← kannTau_recon hS i v hμ (cfun z.1 g)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← kannPost_contD_one (kannJ hS i v hμ) (kannJ_smul hS i v hμ) (c k), hc k]
  rfl

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
