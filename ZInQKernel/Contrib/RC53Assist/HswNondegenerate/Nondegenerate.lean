import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeDerivTieK
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitBridge

/-!
# Nondegeneracy of the characteristic-zero switch residue

The local duality adjoint supplies both degree-one radicals, without a
nondegeneracy assumption on a switch. For the split derivative model, local
orthogonality supplies the perfect degree-one pairing and hence exactly the
residue nondegeneracy premise used by the shape theorem.

The split model is the model of `diophantine_zq.tex`, lines 4854–4876 and
5059–5061. Its coefficient-stage limit is taken before the field fibre. It is
not the local cochain complex at a fixed characteristic-zero derivative prime.
The discrete, finite-target consumers in `ShapeDerivTie` and `ShapeDerivTieK`
cannot be instantiated with a nonzero characteristic-zero target.

The comparison proposition below separates the remaining cochain comparison,
trace normalization, and quotient identification. It contains no residue
nondegeneracy premise and makes no assumption about switch coordinates.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HswNondegenerate

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Hsw
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped PowerSeries.WithPiTopology

section CupTrace

variable {k : Type} [Field k] {A B T : GCx k}
  (p : GPair A B T) (tr : T.X 2 →ₗ[k] k)
  (htr : ∀ z, tr (T.d (2 - 1) 2 (by omega) z) = 0)

/-- Kind: proved. The left degree-one radical consists of boundaries, from
local duality; manuscript lines 4885–4896 and 5035–5050. -/
theorem cupTrace_left_radical
    (hqi : QuasiIso (GHom.toCC (adjHom p 2 tr htr)))
    (x : A.X 1) (hx : A.d 1 2 rfl x = 0)
    (hzero : ∀ y : B.X 1, B.d 1 2 rfl y = 0 → tr (p.P 1 1 2 rfl x y) = 0) :
    ∃ a : A.X 0, A.d 0 1 rfl a = x := by
  have hacyc := coneCx_acyclic_of_quasiIso (adjHom p 2 tr htr) hqi
  obtain ⟨ψ, hψ⟩ := exists_dual_factor_of_ker (B.d 1 2 rfl)
    (asDual ((adjHom p 2 tr htr).f 1 1 rfl x)) hzero
  obtain ⟨a, _, ha, _⟩ := coneAdj_solve p tr htr hacyc
    0 1 2 rfl rfl 1 2 3 rfl rfl rfl x (-ψ) hx (by
      intro y
      change tr (p.P 1 1 2 rfl x y) = (-(sgn 0)) • (-ψ) (B.d 1 2 rfl y)
      rw [show sgn 0 = 1 from by simp [sgn], neg_one_smul, LinearMap.neg_apply, neg_neg]
      exact hψ y)
  exact ⟨a, ha⟩

/-- Kind: proved. The right degree-one radical consists of boundaries, from
the same local duality adjoint; manuscript lines 4885–4896 and 5035–5050.
No finite-dimensionality assumption is required. -/
theorem cupTrace_right_radical
    (hqi : QuasiIso (GHom.toCC (adjHom p 2 tr htr)))
    (y : B.X 1) (hy : B.d 1 2 rfl y = 0)
    (hzero : ∀ x : A.X 1, A.d 1 2 rfl x = 0 → tr (p.P 1 1 2 rfl x y) = 0) :
    ∃ b : B.X 0, B.d 0 1 rfl b = y := by
  have hacyc := coneCx_acyclic_of_quasiIso (adjHom p 2 tr htr) hqi
  have hyRange : y ∈ LinearMap.range (B.d 0 1 rfl) := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (LinearMap.range (B.d 0 1 rfl)) y).mp
    intro φ hφ
    have hφd : ∀ b : B.X 0, φ (B.d 0 1 rfl b) = 0 := fun b =>
      (Submodule.mem_dualAnnihilator φ).mp hφ _ (LinearMap.mem_range_self _ b)
    obtain ⟨x, ψ, hx, hψ⟩ := coneAdj_solve p tr htr hacyc
      1 2 3 rfl rfl 0 1 2 rfl rfl rfl (0 : A.X 2) φ (map_zero _) (by
        intro b
        rw [LinearMap.map_zero₂, map_zero, hφd, smul_zero])
    have he := hψ y
    rw [hy, map_zero, smul_zero, sub_zero, hzero x hx] at he
    exact he.symm
  exact hyRange

end CupTrace

section Residue

variable {k : Type} [Field k]
  (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
  (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)

/-- Kind: proved. The residue is minus the traced local product with the
arguments reversed; manuscript lines 2816–2820 and 5035–5041. -/
theorem resForm_eq_neg_localTrace (t u : R.D.U.X 1) :
    resForm R Ustr f Q tr t u =
      -tr (locT Q (Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl t))) := by
  unfold resForm
  rw [lhs_eq]
  erw [LinearMap.map_zero₂, zero_sub, map_neg, map_neg]

/-- Kind: comparison data, not a proved arithmetic input. A retained split
local complex reads relaxed cochains, receives every degree-one test, and
identifies the switch quotient and its traced local product. Manuscript
lines 4385–4388, 4391–4451, 4854–4876, and 5035–5041. -/
structure SplitResidueComparison (B : SplitLocalPairing k) where
  /-- Kind: comparison map. The full local cochains map to the retained
  split local complex in all degrees; manuscript lines 4385–4388 and
  4857–4862. -/
  localMap : GHom R.D.L (splitLocalComplex k)
  /-- Kind: comparison map. The relaxed cochains map to the retained full
  split local complex; manuscript lines 4857–4869. -/
  read : GHom R.D.U (splitLocalComplex k)
  /-- Kind: comparison identity. The reading is induced by the actual
  local-condition map, not by a choice of switch coordinates; manuscript
  lines 4385–4388 and 4857–4876. -/
  read_local : read = ghomComp R.D.ι localMap
  /-- Kind: comparison map. Local degree-one classes map to the actual switch
  quotient cohomology; manuscript lines 4877–4887 and 5062–5070. -/
  quotient : Coords k →ₗ[k] R.Wrel.toCC.homology 1
  /-- Kind: comparison identity. The quotient of each relaxed cocycle is the
  quotient of its local reading; manuscript lines 4877–4887 and 5062–5070. -/
  quotient_read : ∀ (t : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0),
    quotient (read.f 1 1 rfl t) =
      cls1 R.Wrel ⟨R.gR.f 1 1 rfl t, LinearMap.mem_ker.2
        ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl t).symm.trans (by rw [ht, map_zero]))⟩
  /-- Kind: comparison surjectivity. Every split local degree-one vector is
  read from a relaxed cocycle; manuscript lines 4859–4869 and 5059–5061. -/
  tests : ∀ x : Coords k, ∃ (u : R.D.U.X 1) (_hu : R.D.U.d 1 2 rfl u = 0),
    read.f 1 1 rfl u = x
  /-- Kind: trace-normalization identity. The cone trace restricts to the
  retained local cup product, before coordinates; manuscript lines
  2816–2820, 4385–4388, and 5035–5041. -/
  trace_read : ∀ (u t : R.D.U.X 1), R.D.U.d 1 2 rfl u = 0 → R.D.U.d 1 2 rfl t = 0 →
    tr (locT Q (Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl t))) =
      B.b11 (read.f 1 1 rfl u) (read.f 1 1 rfl t)

/-- Kind: proved. The comparison transports a perfect retained local pairing
to exactly the residue nondegeneracy premise of the shape theorem; manuscript
lines 4885–4896 and 5035–5050. No switch nondegeneracy is assumed. -/
theorem hnd_of_splitResidueComparison (B : SplitLocalPairing k)
    (C : SplitResidueComparison R Ustr f Q tr B) (h11 : Function.Bijective B.b11) :
    ∀ t (ht : R.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : R.D.U.d 1 2 rfl u = 0), resForm R Ustr f Q tr t u = 0) →
        gClass R t ht = 0 := by
  intro t ht hortho
  have hperf := LinearMap.IsPerfPair.of_bijective B.b11 h11
  have hread : C.read.f 1 1 rfl t = 0 := by
    apply hperf.bijective_right.1
    have he : B.b11.flip (C.read.f 1 1 rfl t) = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨u, hu, hux⟩ := C.tests x
      have hz := hortho u hu
      rw [resForm_eq_neg_localTrace R Ustr f Q tr, C.trace_read u t hu ht, hux] at hz
      exact neg_eq_zero.mp hz
    exact he.trans (map_zero B.b11.flip).symm
  unfold gClass
  rw [← C.quotient_read t ht, hread]
  change R.eR (C.quotient (0 : Coords k)) = 0
  rw [map_zero, map_zero]

/-- Kind: comparison data, not a local-duality proposition. Two maps of the
actual full local complex read the two coefficient slots of a local
pairing. They preserve the switch quotient, give all local tests modulo
boundaries, and preserve the traced cup product. Manuscript lines
2798–2820, 4385–4388, 4854–4887, and 5035–5041. -/
structure LocalResidueComparison {A B T : GCx k} (p : GPair A B T)
    (tr2 : T.X 2 →ₗ[k] k) where
  /-- Kind: cochain comparison map. The first coefficient slot is read from
  the full local cochains in all degrees; manuscript lines 2798–2805 and
  4385–4388. -/
  test : GHom R.D.L A
  /-- Kind: cochain comparison map. The second, possibly conjugate-dual
  coefficient slot is read from the full local cochains in all degrees;
  manuscript lines 2798–2805 and 4385–4388. -/
  value : GHom R.D.L B
  /-- Kind: quotient comparison map. The second local cohomology maps to
  the actual switch quotient; manuscript lines 4877–4887 and 5062–5070. -/
  quotient : B.toCC.homology 1 →ₗ[k] R.Wrel.toCC.homology 1
  /-- Kind: quotient comparison identity. The quotient class is the image
  of the actual second-slot reading; manuscript lines 4877–4887 and
  5062–5070. -/
  quotient_read : ∀ (t : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0),
    quotient (cls1 B ⟨(ghomComp R.D.ι value).f 1 1 rfl t, LinearMap.mem_ker.2
      (((ghomComp R.D.ι value).comm 1 2 1 2 rfl rfl rfl rfl t).symm.trans
        (by rw [ht, map_zero]))⟩) =
      cls1 R.Wrel ⟨R.gR.f 1 1 rfl t, LinearMap.mem_ker.2
        ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl t).symm.trans (by rw [ht, map_zero]))⟩
  /-- Kind: comparison surjectivity. Every local cocycle is the reading
  of a relaxed cocycle modulo local boundaries; manuscript lines
  4854–4887 and 5059–5061. -/
  tests : ∀ (x : A.X 1), A.d 1 2 rfl x = 0 →
    ∃ (u : R.D.U.X 1) (_hu : R.D.U.d 1 2 rfl u = 0) (a : A.X 0),
      (ghomComp R.D.ι test).f 1 1 rfl u + A.d 0 1 rfl a = x
  /-- Kind: trace-normalization identity. The traced cup product, in its
  actual order, agrees with the local coefficient pairing before
  coordinates; manuscript lines 2816–2820 and 5035–5041. -/
  trace_read : ∀ (u t : R.D.U.X 1), R.D.U.d 1 2 rfl u = 0 → R.D.U.d 1 2 rfl t = 0 →
    tr (locT Q (Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl t))) =
      tr2 (p.P 1 1 2 rfl ((ghomComp R.D.ι test).f 1 1 rfl u)
        ((ghomComp R.D.ι value).f 1 1 rfl t))

/-- Kind: proved. A comparison of actual cochains and traces transports
local duality to exactly the shape theorem's residue nondegeneracy premise;
manuscript lines 2798–2820, 4885–4896, and 5035–5050. The local complex and
its two coefficient slots may be different. -/
theorem hnd_of_localResidueComparison {A B T : GCx k} (p : GPair A B T)
    (tr2 : T.X 2 →ₗ[k] k) (htr2 : ∀ z, tr2 (T.d (2 - 1) 2 (by omega) z) = 0)
    (Cmp : LocalResidueComparison R Ustr f Q tr p tr2)
    (hqi : QuasiIso (GHom.toCC (adjHom p 2 tr2 htr2))) :
    ∀ t (ht : R.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : R.D.U.d 1 2 rfl u = 0), resForm R Ustr f Q tr t u = 0) →
        gClass R t ht = 0 := by
  intro t ht hortho
  let readB := ghomComp R.D.ι Cmp.value
  let y := readB.f 1 1 rfl t
  have hy : B.d 1 2 rfl y = 0 :=
    (readB.comm 1 2 1 2 rfl rfl rfl rfl t).symm.trans (by rw [ht, map_zero])
  have hzero : ∀ x : A.X 1, A.d 1 2 rfl x = 0 → tr2 (p.P 1 1 2 rfl x y) = 0 := by
    intro x hx
    obtain ⟨u, hu, a, hux⟩ := Cmp.tests x hx
    have hu0 : tr2 (p.P 1 1 2 rfl ((ghomComp R.D.ι Cmp.test).f 1 1 rfl u) y) = 0 := by
      have hz := hortho u hu
      rw [resForm_eq_neg_localTrace R Ustr f Q tr, Cmp.trace_read u t hu ht] at hz
      exact neg_eq_zero.mp hz
    have ha0 : tr2 (p.P 1 1 2 rfl (A.d 0 1 rfl a) y) = 0 := by
      have hc := (adjHom p 2 tr2 htr2).comm 0 1 0 1 rfl rfl rfl rfl a
      have he := congrArg (fun φ => asDual φ y) hc
      change tr2 (p.P 1 1 2 rfl (A.d 0 1 rfl a) y) =
        (-(sgn 0)) • tr2 (p.P 0 2 2 rfl a (B.d 1 2 rfl y)) at he
      rw [hy, map_zero, map_zero, smul_zero] at he
      exact he
    rw [← hux, LinearMap.map_add₂, map_add, hu0, ha0, add_zero]
  obtain ⟨b, hb⟩ := cupTrace_right_radical p tr2 htr2 hqi y hy hzero
  have hclass : cls1 B ⟨y, LinearMap.mem_ker.2 hy⟩ = 0 := by
    have he : (⟨y, LinearMap.mem_ker.2 hy⟩ : LinearMap.ker (B.d 1 2 rfl)) =
        ⟨B.d 0 1 rfl b, LinearMap.mem_ker.2 (B.d_d 0 1 2 rfl rfl b)⟩ :=
      Subtype.ext hb.symm
    rw [he, cls1_eq_clsAt]
    exact clsAt_boundary B 0 1 2 rfl rfl b
  unfold gClass
  rw [← Cmp.quotient_read t ht, hclass, map_zero, map_zero]

end Residue

section Split

variable {k : Type} [Field k] {G : GCx k}
  (res : GHom G (splitLocalComplex k)) (BG : GlobalTracePairing G)
  (B : SplitLocalPairing k) (hrec : LimitReciprocity res BG B)

/-- Kind: definition. The degree-one vector of a relaxed cochain in the
split model; manuscript lines 4859–4869. -/
def limitRead (t : (limitRelaxed G res).D.U.X 1) : Coords k :=
  (show ↥(⊤ : Submodule k (Coords k)) from t).1

/-- Kind: proved. In the retained split model the residue is the negative
transposed degree-one pairing; manuscript lines 4859–4869 and 5035–5041. -/
theorem limit_resForm (t u : (limitRelaxed G res).D.U.X 1) :
    resForm (limitRelaxed G res) (conditionComplex (⊥ : Submodule k (Coords k)))
      (strictLimitMap G res) (limitPair res BG B hrec) (limitTrace k) t u =
        -B.b11 (limitRead res u) (limitRead res t) :=
  limitResidue_clean res BG B (limitRead res u) (limitRead res t)

/-- Kind: proved. The quotient class of a relaxed cocycle in the split model
is its local degree-one vector; manuscript lines 4859–4869 and 5062–5064. -/
theorem limit_gClass (t : (limitRelaxed G res).D.U.X 1)
    (ht : (limitRelaxed G res).D.U.d 1 2 rfl t = 0) :
    gClass (limitRelaxed G res) t ht = limitRead res t :=
  h1Equiv_cls1_aux (literalLimitRelaxed G res).Wrel (literalLimitRelaxed G res).hWrel _

/-- Kind: constructed comparison. The retained split model satisfies the
cochain, quotient, test, and trace comparison with its own local pairing;
manuscript lines 4854–4876 and 5035–5041. This construction assumes no
nondegeneracy and is available even for the zero local pairing. -/
def limitComparison :
    SplitResidueComparison (limitRelaxed G res)
      (conditionComplex (⊥ : Submodule k (Coords k))) (strictLimitMap G res)
      (limitPair res BG B hrec) (limitTrace k) B where
  localMap := idGHom (splitLocalComplex k)
  read := (limitRelaxed G res).D.ι
  read_local := by
    apply ghom_ext
    intro n t
    rfl
  quotient := (limitRelaxed G res).eR.symm.toLinearMap
  quotient_read t ht := by
    apply (limitRelaxed G res).eR.injective
    exact ((limitRelaxed G res).eR.apply_symm_apply _).trans (limit_gClass res t ht).symm
  tests x := ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩
  trace_read u t _ _ := by
    change (0 : k) + B.b11 (limitRead res u) (limitRead res t) =
      B.b11 (limitRead res u) (limitRead res t)
    exact zero_add _

/-- Kind: proved. Local orthogonality in the split model forces the
bijectivity of the degree-one pairing, without a coordinate identity;
manuscript lines 4862–4873 and 5035–5050. -/
theorem b11_bijective_of_localDuality
    (hqi : QuasiIso (GHom.toCC (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)))) : Function.Bijective B.b11 := by
  have hinj : Function.Injective B.b11 := by
    apply (injective_iff_map_eq_zero B.b11).mpr
    intro x hx
    let c : (locCx (limitStrictSel res)).X 2 := (0, x)
    have hc : (locCx (limitStrictSel res)).d 2 3 rfl c = 0 :=
      limitLoc_d_zero_fst res 2 3 rfl x
    have hmap : (localDualityMap (limitPair res BG B hrec) (limitTrace k)
        (limitPair_htr res BG B hrec)).f 2 2 rfl c = 0 := by
      apply dualCx_ext
      intro u
      refine (limitLocal_apply res BG B hrec 2 0 x u).trans ?_
      refine (limitCupLP_apply_of_two B rfl _ _).trans ?_
      exact LinearMap.congr_fun hx (limitRead res u)
    have hcone : (coneCx (localDualityMap (limitPair res BG B hrec) (limitTrace k)
        (limitPair_htr res BG B hrec))).d 2 3 rfl (c, 0) = 0 := by
      refine Prod.ext hc ?_
      change (localDualityMap (limitPair res BG B hrec) (limitTrace k)
        (limitPair_htr res BG B hrec)).f 2 2 rfl c -
          (dualCx (limitRelaxed G res).D.U 3).d 1 2 rfl 0 = 0
      erw [hmap, map_zero, sub_self]
    obtain ⟨⟨a, _⟩, ha⟩ := coneCx_acyclic_of_quasiIso
      (localDualityMap (limitPair res BG B hrec) (limitTrace k) (limitPair_htr res BG B hrec))
      hqi 1 2 3 rfl rfl (c, 0) hcone
    have he := congrArg (fun z => (show PUnit × Coords k from z.1).2) ha
    change -(show ↥(⊥ : Submodule k (Coords k)) from a.1).1 - 0 = x at he
    have hz : (show ↥(⊥ : Submodule k (Coords k)) from a.1).1 = 0 :=
      (Submodule.mem_bot k).mp (show ↥(⊥ : Submodule k (Coords k)) from a.1).2
    rw [hz, neg_zero, sub_zero] at he
    exact he.symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := k) (V := Coords k)).symm).mp hinj⟩

/-- Kind: proved. A perfect retained degree-one pairing supplies the exact
residue nondegeneracy premise on the split derivative switch; manuscript
lines 4885–4896 and 5035–5050. -/
theorem limit_hnd_of_b11 (h11 : Function.Bijective B.b11) :
    ∀ t (ht : (limitRelaxed G res).D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (limitRelaxed G res).D.U.d 1 2 rfl u = 0),
        resForm (limitRelaxed G res) (conditionComplex (⊥ : Submodule k (Coords k)))
          (strictLimitMap G res) (limitPair res BG B hrec) (limitTrace k) t u = 0) →
      gClass (limitRelaxed G res) t ht = 0 := by
  intro t ht hortho
  have hperf := LinearMap.IsPerfPair.of_bijective B.b11 h11
  have hx : limitRead res t = 0 := by
    apply hperf.bijective_right.1
    have he : B.b11.flip (limitRead res t) = 0 := by
      apply LinearMap.ext
      intro x
      let u : (limitRelaxed G res).D.U.X 1 := ⟨x, Submodule.mem_top⟩
      have hu : (limitRelaxed G res).D.U.d 1 2 rfl u = 0 := rfl
      have hz := hortho u hu
      rw [limit_resForm res BG B hrec] at hz
      exact neg_eq_zero.mp hz
    exact he.trans (map_zero B.b11.flip).symm
  exact (limit_gClass res t ht).trans hx

/-- Kind: proved. Local orthogonality supplies residue nondegeneracy in the
split derivative model, independently of the global duality and of any
residue coordinate identity; manuscript lines 4862–4873 and 5035–5050. -/
theorem limit_hnd_of_localDuality
    (hqi : QuasiIso (GHom.toCC (localDualityMap (limitPair res BG B hrec) (limitTrace k)
      (limitPair_htr res BG B hrec)))) :
    ∀ t (ht : (limitRelaxed G res).D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (limitRelaxed G res).D.U.d 1 2 rfl u = 0),
        resForm (limitRelaxed G res) (conditionComplex (⊥ : Submodule k (Coords k)))
          (strictLimitMap G res) (limitPair res BG B hrec) (limitTrace k) t u = 0) →
      gClass (limitRelaxed G res) t ht = 0 :=
  limit_hnd_of_b11 res BG B hrec (b11_bijective_of_localDuality res BG B hrec hqi)

end Split

section Fibre

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-- Kind: definition. The genuine continuous local pairing of the two fibre
coefficient modules, valued in the Tate twist; manuscript lines 2798–2805
and 4885–4896. -/
abbrev fibreLocalPairing (q : Places K S) :
    GPair
      (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (VP K S W P α) q)
      (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (VP K S W P α⁻¹) q)
      (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (Tate1P K S P) q) :=
  localPair (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α) q

/-- Kind: proved from the existing local-duality proposition. At an odd
height-one fibre, the right radical of the genuine local cup trace is
exactly the local boundaries; manuscript lines 2798–2820 and 4885–4896.
The trace must induce an isomorphism in degree two. -/
theorem fibreCup_right_radical_VP
    (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S) (q : Places K S)
    (trq : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (Tate1P K S P) q).X 2 →ₗ[ResAt P] ResAt P)
    (htrq : ∀ z, trq ((localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (Tate1P K S P) q).d 1 2 rfl z) = 0)
    (htrace : InducesIsoH2 trq)
    (y : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (VP K S W P α⁻¹) q).X 1)
    (hy : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (VP K S W P α⁻¹) q).d 1 2 rfl y = 0)
    (hzero : ∀ x : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (VP K S W P α) q).X 1,
      (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (VP K S W P α) q).d 1 2 rfl x = 0 →
      trq ((fibreLocalPairing W P α q).P 1 1 2 rfl x y) = 0) :
    ∃ b : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (VP K S W P α⁻¹) q).X 0,
      (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (VP K S W P α⁻¹) q).d 0 1 rfl b = y := by
  have hqi := hL S P hset (VP K S W P α) (VP K S W P α⁻¹) (Tate1P K S P)
    (isLatticeTop_vp' P) (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α)
    (betaT_bijective W P α) (betaT_flip_bijective W P α) q trq htrq htrace
  exact cupTrace_right_radical (fibreLocalPairing W P α q) trq htrq hqi y hy hzero

/-- Kind: proved from the existing local-duality proposition and an explicit
cochain comparison. The genuine fibre local pairing supplies exactly the
shape theorem's residue nondegeneracy premise; manuscript lines 2798–2820,
4885–4896, and 5035–5050. No residue nondegeneracy is assumed. -/
theorem fibre_hnd_of_localComparison_VP
    (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S) (q : Places K S)
    (trq : (localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (Tate1P K S P) q).X 2 →ₗ[ResAt P] ResAt P)
    (htrq : ∀ z, trq ((localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (Tate1P K S P) q).d 1 2 rfl z) = 0)
    (htrace : InducesIsoH2 trq)
    (R : QuasiRelaxedLocalization (ResAt P)) (Ustr : GCx (ResAt P))
    (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[ResAt P] ResAt P)
    (Cmp : LocalResidueComparison R Ustr f Q tr (fibreLocalPairing W P α q) trq) :
    ∀ t (ht : R.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : R.D.U.d 1 2 rfl u = 0), resForm R Ustr f Q tr t u = 0) →
        gClass R t ht = 0 := by
  have hqi := hL S P hset (VP K S W P α) (VP K S W P α⁻¹) (Tate1P K S P)
    (isLatticeTop_vp' P) (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaT W P α) (betaT_smul W P α) (continuous_betaT W P α)
    (betaT_bijective W P α) (betaT_flip_bijective W P α) q trq htrq htrace
  exact hnd_of_localResidueComparison R Ustr f Q tr
    (fibreLocalPairing W P α q) trq htrq Cmp hqi

end Fibre

section Retained

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
  (C : ComplexStages (R := Lambda) ZInQ.Manuscript.RC.Limits.stageIdeal U)
  (D : RetainedLimitPairingStages U C) (P : Ideal Lambda) [P.IsPrime]

/-- Kind: definition. The residue pairing data obtained from the retained
localization and trace-pairing matrices, after the coefficient-stage limit
and field specialization; manuscript lines 4385–4388, 4391–4451, and
4854–4887. -/
abbrev retainedPairing :
    SelPairData
      (restrictData (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).D
        (strictLimitMap (fibreLimitGlobal U hU P C) (D.resLimit hU P)))
      (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).D :=
  limitPair (D.resLimit hU P)
    (globalPairingOfMat ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero hU
      (algebraMap Lambda (ResAt P)) C (D.globK P))
    (localPairingOfMat (D.locK P))
    (limitReciprocity_ofMat ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero hU
      (algebraMap Lambda (ResAt P)) C (D.resK P) (D.resK_comm hU P)
      (D.globK P) (D.locK P) (D.matReciprocity hU P))

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- Kind: proved. The retained local pairing with the genuine conjugation
matrix supplies the exact residue nondegeneracy premise at an odd
height-one fibre; manuscript lines 4385–4388, 4854–4896, and 5035–5050.
Neither global duality nor the degree-two scalar being a unit is needed
for this degree-one assertion. -/
theorem fibreLimit_hnd_of_retained [IsHeightOneOdd P]
    (ε₀ ε₂ ε σ : ResAt P) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)) :
    ∀ t (ht : (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).D.U.d 1 2 rfl u = 0),
        resForm (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P))
          (conditionComplex (⊥ : Submodule (ResAt P) (Coords (ResAt P))))
          (strictLimitMap (fibreLimitGlobal U hU P C) (D.resLimit hU P))
          (retainedPairing U hU C D P) (limitTrace (ResAt P)) t u = 0) →
      gClass (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)) t ht = 0 := by
  have h11 : Function.Bijective (localPairingOfMat (D.locK P)).b11 :=
    switch_b11_bijective (localPairingOfMat (D.locK P)) ε σ (conjMatrix Cn W hW P)
      hε hσ (conjMatrix_mul_self Cn W hW P) (by
        intro x y
        rw [hloc]
        rfl)
  exact limit_hnd_of_b11 (D.resLimit hU P)
    (globalPairingOfMat ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero hU
      (algebraMap Lambda (ResAt P)) C (D.globK P))
    (localPairingOfMat (D.locK P))
    (limitReciprocity_ofMat ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero hU
      (algebraMap Lambda (ResAt P)) C (D.resK P) (D.resK_comm hU P)
      (D.globK P) (D.locK P) (D.matReciprocity hU P)) h11

/-- Kind: proved. A cochain comparison to the retained local pairing
supplies the exact nondegeneracy premise for any switch over the fibre
field; manuscript lines 4385–4388, 4854–4896, and 5035–5050. The comparison
is kept separate from the local pairing's arithmetic provenance. -/
theorem hnd_of_comparison_to_retained [IsHeightOneOdd P]
    (R : QuasiRelaxedLocalization (ResAt P)) (Ustr : GCx (ResAt P))
    (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[ResAt P] ResAt P)
    (Cmp : SplitResidueComparison R Ustr f Q tr (localPairingOfMat (D.locK P)))
    (ε₀ ε₂ ε σ : ResAt P) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)) :
    ∀ t (ht : R.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : R.D.U.d 1 2 rfl u = 0), resForm R Ustr f Q tr t u = 0) →
        gClass R t ht = 0 :=
  hnd_of_splitResidueComparison R Ustr f Q tr (localPairingOfMat (D.locK P)) Cmp
    (switch_b11_bijective (localPairingOfMat (D.locK P)) ε σ (conjMatrix Cn W hW P)
      hε hσ (conjMatrix_mul_self Cn W hW P) (by intro x y; rw [hloc]; rfl))

end Retained

section Scope

/-- Kind: proved. A finite module over a characteristic-zero field is zero;
this explains the residual scope of the finite-target shape consumers.
Manuscript lines 4977–4980 and 5026–5041. -/
theorem finite_charZero_module_subsingleton (k T : Type) [Field k] [CharZero k]
    [AddCommGroup T] [Module k T] [Finite T] : Subsingleton T := by
  have hzero : ∀ t : T, t = 0 := by
    intro t
    by_contra ht
    exact Finite.false (Finite.of_injective (fun a : k => a • t) (smul_left_injective k ht))
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k] [CharZero k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T]

/-- Kind: proved. For a finite target over a characteristic-zero field,
residue nondegeneracy is impossible when the switch has a rank-four
quotient and its strict condition vanishes in degree two. This is the
literal finite-target consumer, not the retained split fibre model;
manuscript lines 4854–4876, 4977–4980, and 5035–5041. -/
theorem genuine_finiteTarget_no_hnd (X : GenuineSwitch K S k M)
    (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (x y : M), β (g • x) (g • y) = g • β x y)
    (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) :
    ¬ (∀ t (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
        resForm X.toQuasi (piCx X.US) (piMap X.φ)
          (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u = 0) →
      gClass X.toQuasi t ht = 0) := by
  have hT : Subsingleton T := finite_charZero_module_subsingleton k T
  let Q := galoisPairData K S k β hβ X.ΔS X.ΔR I
  have hlocal : ∀ y : Q.EL.X 2, y = 0 := by
    intro y
    funext v
    apply contCochains_ext
    intro g
    exact @Subsingleton.elim T hT _ _
  have hres : ∀ t u : X.toQuasi.D.U.X 1,
      resForm X.toQuasi (piCx X.US) (piMap X.φ) Q tr t u = 0 := by
    intro t u
    refine (resForm_eq_neg_localTrace X.toQuasi (piCx X.US) (piMap X.φ) Q tr t u).trans ?_
    refine (congrArg (fun z : Q.EL.X 2 => -tr (locT Q z)) (hlocal _)).trans ?_
    rw [map_zero, map_zero, neg_zero]
  intro hnd
  obtain ⟨t, ht, hclass⟩ := exists_gClass X.toQuasi (piCx X.US) (piMap X.φ)
    X.g_surj X.ex (fun x => funext fun v => hUS2 v (x v))
    ((Pi.single 0 1 : Fin 2 → k), (0 : Fin 2 → k))
  have hc := hclass.symm.trans (hnd t ht (fun u _ => hres t u))
  have h10 : (1 : k) = 0 := congrArg (fun a : Coords k => a.1 0) hc
  exact one_ne_zero h10

end Scope

end ZInQ.Contrib.RC53Assist.HswNondegenerate
