import ZInQKernel.Contrib.OneProof.KummerLocalDuality.TraceCharacter
import ZInQKernel.Contrib.OneProof.KummerLocalDuality.TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Collapse
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements

/-!
# Local Tate perfectness on the actual cup product

The explicit cups of the separable-closure model are compared with the
inhomogeneous cups on the project's local complex. The group change uses
`compGal`, the right coefficient change is induced by the original Weil
form, and the degree-two class is the one associated to the supplied trace.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain
open TauCeti TauCeti.ClassFieldTheory TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

section ClassTransport

variable {R G H M N : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [DistribMulAction H N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul H N]
  (g : H ≃ₜ* G) (e : M ≃+ N) (he : ∀ σ x, e (g σ • x) = σ • e x)

private def movedH0 : H0 G M ≃+ H0 H N :=
  AddEquiv.ofBijective (explicitMap0 G M g.toMulEquiv.toMonoidHom e.toAddMonoidHom he)
    (explicitMap0_bijective G M _ g.surjective e he)

private def movedH1 : H1 G M ≃+ H1 H N :=
  explicitMap1Equiv G M H N g e continuous_of_discreteTopology continuous_of_discreteTopology he

private def movedH2 : H2 G M ≃+ H2 H N :=
  explicitMap2Equiv G M H N g e continuous_of_discreteTopology continuous_of_discreteTopology he

private def movedZ1 (z : LinearMap.ker (contD R G M 1)) : Z1 H N :=
  cocyclesMap1 G M H N g e.toAddMonoidHom continuous_of_discreteTopology he
    ⟨fun σ => contFun z.1 (fun _ => σ), mem_Z1_of_d_eq_zero z.1 z.2⟩

private def movedZ2 (z : LinearMap.ker (contD R G M 2)) : Z2 H N :=
  cocyclesMap2 G M H N g e.toAddMonoidHom continuous_of_discreteTopology he
    ⟨fun p => contFun z.1 ![p.1, p.2], mem_Z2_of_d_eq_zero z.1 z.2⟩

private theorem movedH1_class (z : LinearMap.ker (contD R G M 1)) :
    movedH1 g e he (kerToH1 z) = (movedZ1 g e he z : H1 H N) :=
  explicitMap1_mk G M H N g e.toAddMonoidHom continuous_of_discreteTopology he _

private theorem movedH2_class (z : LinearMap.ker (contD R G M 2)) :
    movedH2 g e he (kerToH2 z) = (movedZ2 g e he z : H2 H N) :=
  explicitMap2_mk G M H N g e.toAddMonoidHom continuous_of_discreteTopology he _

private theorem boundary_of_kerToH0 {z : LinearMap.ker (contD R G M 0)}
    (hz : kerToH0 z = 0) :
    ∃ w : (natCx (contCochains R G M)).X (-1),
      (natCx (contCochains R G M)).d (-1) 0 rfl w = z.1 := by
  obtain ⟨w, hw⟩ := (kerToH0_eq_zero_iff z).1 hz
  have hw' : ((contCochains R G M).d 0 0).hom w = 0 := by
    rw [(contCochains R G M).shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.zero_apply]
  exact ⟨0, (map_zero _).trans (hw.symm.trans hw').symm⟩

end ClassTransport

section CoefficientTransport

variable (F : Type) [Field F] [CharZero F] (m : ℕ)

private theorem compMu_symm_smul (g : AbsoluteGaloisGroup F) (u : MuAlg F m) :
    (compMu F m).symm ((compGal F).symm g • u) = g • (compMu F m).symm u := by
  apply (compMu F m).injective
  have h := compMu_smul F m ((compGal F).symm g) ((compMu F m).symm u)
  rw [ContinuousMulEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
  exact ((compMu F m).apply_symm_apply _).trans h.symm

variable (M : Type) [AddCommGroup M]

private def compInternalHom :
    InternalHom (Field.absoluteGaloisGroup F) M (MuAlg F m) ≃+
      InternalHom (AbsoluteGaloisGroup F) (ResMod (compGalSymmHom F) M) (KummerCoeff F m) where
  toFun q := InternalHom.of _ ((compMu F m).symm.toAddMonoidHom.comp q.toAddMonoidHom)
  invFun q := InternalHom.of _ ((compMu F m).toAddMonoidHom.comp q.toAddMonoidHom)
  left_inv q := InternalHom.ext (AddMonoidHom.ext fun x => (compMu F m).apply_symm_apply _)
  right_inv q := InternalHom.ext (AddMonoidHom.ext fun x => (compMu F m).symm_apply_apply _)
  map_add' q r := InternalHom.ext (AddMonoidHom.ext fun x => map_add (compMu F m).symm _ _)

private theorem compInternalHom_smul [DistribMulAction (Field.absoluteGaloisGroup F) M]
    (g : AbsoluteGaloisGroup F) (q : InternalHom (Field.absoluteGaloisGroup F) M (MuAlg F m)) :
    compInternalHom F m M ((compGal F).symm g • q) = g • compInternalHom F m M q := by
  apply InternalHom.ext
  apply AddMonoidHom.ext
  intro x
  change (compMu F m).symm ((compGal F).symm g • q.toAddMonoidHom (((compGal F).symm g)⁻¹ • x)) =
    g • (compMu F m).symm (q.toAddMonoidHom ((compGal F).symm (g⁻¹) • x))
  rw [map_inv, compMu_symm_smul]

end CoefficientTransport

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ : HasRootsOfUnity K S₀ (2 ^ i))
  (hFull : FullTorsion K S₀ W (2 ^ i)) (v : Places K S)

private abbrev localSeparableCoeff :=
  ResMod (compGalSymmHom (v.1.adicCompletion K)) (kummerLocalCoeff hS i v W α)

private abbrev actualFiniteCup :=
  orthGaloisPair K (actLBeta hS W i α hμ) (actLBeta_smul hS W i α hμ) v

private def tateRight : kummerLocalCoeff hS i v W (charInv α) ≃+
    InternalHom (AbsoluteGaloisGroup (v.1.adicCompletion K)) (localSeparableCoeff hS W i α v)
      (KummerCoeff (v.1.adicCompletion K) (2 ^ i)) :=
  (localCoefficientTateDual hS i v hμ W α hFull).trans
    (compInternalHom (v.1.adicCompletion K) (2 ^ i) (kummerLocalCoeff hS i v W α))

private theorem tateRight_smul (g : AbsoluteGaloisGroup (v.1.adicCompletion K))
    (y : kummerLocalCoeff hS i v W (charInv α)) :
    tateRight hS W i α hμ hFull v ((compGal (v.1.adicCompletion K)).symm g • y) =
      g • tateRight hS W i α hμ hFull v y := by
  let e := compInternalHom (v.1.adicCompletion K) (2 ^ i) (kummerLocalCoeff hS i v W α)
  change e (localCoefficientTateDual hS i v hμ W α hFull
    ((compGal (v.1.adicCompletion K)).symm g • y)) =
      g • e (localCoefficientTateDual hS i v hμ W α hFull y)
  rw [localCoefficientTateDual_smul, compInternalHom_smul]

private theorem tateRight_apply (x : kummerLocalCoeff hS i v W α)
    (y : kummerLocalCoeff hS i v W (charInv α)) :
    (tateRight hS W i α hμ hFull v y).toAddMonoidHom x =
      (compMu (v.1.adicCompletion K) (2 ^ i)).symm (localRootCharacter hS i v hμ (kannBeta hS W i v hμ α x y)) := by
  exact congrArg (compMu (v.1.adicCompletion K) (2 ^ i)).symm
    (localCoefficientTateDual_apply hS i v hμ W α hFull x y)

private theorem cup_zero_two
    (x : contCochain (Acoef i) (Gloc K v.1) (kummerLocalCoeff hS i v W α) 0)
    (y : contCochain (Acoef i) (Gloc K v.1) (kummerLocalCoeff hS i v W (charInv α)) 2)
    (g h : Gloc K v.1) :
    contFun ((actualFiniteCup hS W i α hμ v).P 0 2 2 rfl x y) ![g, h] =
      kannBeta hS W i v hμ α (contFun x Fin.elim0) (contFun y ![g, h]) := by
  change cupFun (kannBeta hS W i v hμ α) 0 2 2 rfl (contFun x) (contFun y) ![g, h] = _
  rw [cupFun_apply, headProd_zero, one_smul]
  refine congrArg₂ (fun a b => kannBeta hS W i v hμ α a b)
    (congrArg (contFun x) (Subsingleton.elim _ _)) (congrArg (contFun y) ?_)
  funext j
  fin_cases j <;> rfl

private theorem cup_one_one
    (x : contCochain (Acoef i) (Gloc K v.1) (kummerLocalCoeff hS i v W α) 1)
    (y : contCochain (Acoef i) (Gloc K v.1) (kummerLocalCoeff hS i v W (charInv α)) 1)
    (g h : Gloc K v.1) :
    contFun ((actualFiniteCup hS W i α hμ v).P 1 1 2 rfl x y) ![g, h] =
      kannBeta hS W i v hμ α (contFun x (fun _ => g)) (g • contFun y (fun _ => h)) :=
  cupFun_one_one_apply (kannBeta hS W i v hμ α) (contFun x) (contFun y) ![g, h]

private theorem cup_two_zero
    (x : contCochain (Acoef i) (Gloc K v.1) (kummerLocalCoeff hS i v W α) 2)
    (y : contCochain (Acoef i) (Gloc K v.1) (kummerLocalCoeff hS i v W (charInv α)) 0)
    (g h : Gloc K v.1) :
    contFun ((actualFiniteCup hS W i α hμ v).P 2 0 2 rfl x y) ![g, h] =
      kannBeta hS W i v hμ α (contFun x ![g, h]) ((g * h) • contFun y Fin.elim0) := by
  change cupFun (kannBeta hS W i v hμ α) 2 0 2 rfl (contFun x) (contFun y) ![g, h] = _
  rw [cupFun_apply, headProd_succ, headProd_succ, headProd_zero, one_mul]
  refine congrArg₂ (fun a b => kannBeta hS W i v hμ α a ((g * h) • b))
    (congrArg (contFun x) ?_) (congrArg (contFun y) (Subsingleton.elim _ _))
  funext j
  fin_cases j <;> rfl

private theorem movedRootClass
    (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2)) :
    movedH2 (compGal (v.1.adicCompletion K)).symm (compMu (v.1.adicCompletion K) (2 ^ i)).symm
      (compMu_symm_smul (v.1.adicCompletion K) (2 ^ i)) (localRootCycleClass hS i v hμ z) =
    (movedZ2 (compGal (v.1.adicCompletion K)).symm (compMu (v.1.adicCompletion K) (2 ^ i)).symm
      (compMu_symm_smul (v.1.adicCompletion K) (2 ^ i))
      (postCycle2 (k := Acoef i) (k' := ℤ) (localRootCharacter hS i v hμ)
        (localRootCharacter_smul hS i v hμ) z) : H2 (AbsoluteGaloisGroup (v.1.adicCompletion K))
          (KummerCoeff (v.1.adicCompletion K) (2 ^ i))) :=
  movedH2_class _ _ _ _

/-- The cohomological trace cups of the actual finite modules are perfect
in the three complementary degree pairs. The statement uses the given
finite trace on the original target cochains. -/
theorem actualFiniteCupPerfect
    (tr : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ)) v).d 1 2 rfl z) = 0)
    (ht : InducesIsoH2 tr) (n : ℤ) (hn₀ : 0 ≤ n) (hn₂ : n ≤ 2) :
    CupPerfectAt (actualFiniteCup hS W i α hμ v) tr n := by
  let F := v.1.adicCompletion K
  let Gsep := AbsoluteGaloisGroup F
  let M := kummerLocalCoeff hS i v W α
  let Msep := localSeparableCoeff hS W i α v
  let roots := KummerCoeff F (2 ^ i)
  let cup := actualFiniteCup hS W i α hμ v
  letI : Finite Msep := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  letI : Finite (NumberField.RingOfIntegers K ⧸ v.1.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.1.ne_bot
  let g := (compGal F).symm
  let eL : M ≃+ Msep := AddEquiv.refl M
  let eN := tateRight hS W i α hμ hFull v
  have hL : ∀ σ x, eL (g σ • x) = σ • eL x := fun _ _ => rfl
  have hN : ∀ σ y, eN (g σ • y) = σ • eN y := tateRight_smul hS W i α hμ hFull v
  let eU := movedH2 g (compMu F (2 ^ i)).symm (compMu_symm_smul F (2 ^ i))
  obtain ⟨χ₀, hχ₀, hgen₀⟩ := finiteTraceCharacter hS i v hμ tr htr ht
  let χ : Acoef i →+ H2 Gsep roots := eU.toAddMonoidHom.comp χ₀
  have hχ (z : LinearMap.ker (contD (Acoef i) (Gloc K v.1) (finiteLocalTateTarget hS i v hμ) 2)) :
      χ (tr z.1) = eU (localRootCycleClass hS i v hμ z) :=
    congrArg eU (hχ₀ z)
  have hgen : ∀ a : Acoef i, (∀ b : Acoef i, χ (b * a) = 0) → a = 0 := by
    intro a ha
    exact hgen₀ a fun b => eU.injective ((ha b).trans (map_zero eU).symm)
  have hm : IsUnit ((2 ^ i : ℕ) : F) := isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hM : ∀ x : Msep, (2 ^ i : ℕ) • x = 0 := two_pow_smul_mcoef W i α
  interval_cases n
  · let l := movedH0 g eL hL
    let r := movedH2 g eN hN
    refine cupPerfectAt_of_class_pairing cup tr 0 χ hgen
      (l.toAddMonoidHom.comp kerToH0) (r.toAddMonoidHom.comp kerToH2)
      (l.surjective.comp kerToH0_surjective) (r.surjective.comp kerToH2_surjective)
      (fun x hx => boundary_of_kerToH0 (l.injective (hx.trans (map_zero l).symm)))
      (fun y hy => (kerToH2_eq_zero_iff y).mp (r.injective (hy.trans (map_zero r).symm)))
      (dualityMap0 Gsep Msep roots) (dualityMap0_kummerCoeff_bijective hm Msep hM) ?_
    intro x y
    change χ (tr (cupCycle cup 0 x y).1) =
      dualityMap0 Gsep Msep roots (l (kerToH0 x)) (movedH2 g eN hN (kerToH2 y))
    rw [hχ, movedRootClass, movedH2_class, dualityMap0_mk]
    apply congrArg (H2pi Gsep roots)
    apply Subtype.ext
    funext p
    obtain ⟨σ, τ⟩ := p
    change (compMu F (2 ^ i)).symm
        (localRootCharacter hS i v hμ (contFun (cup.P 0 2 2 rfl x.1 y.1) ![g σ, g τ])) =
      (eN (contFun y.1 ![g σ, g τ])).toAddMonoidHom (contFun x.1 Fin.elim0)
    rw [cup_zero_two, tateRight_apply]
  · let l := movedH1 g eL hL
    let r := movedH1 g eN hN
    refine cupPerfectAt_of_class_pairing cup tr 1 χ hgen
      (l.toAddMonoidHom.comp kerToH1) (r.toAddMonoidHom.comp kerToH1)
      (l.surjective.comp kerToH1_surjective) (r.surjective.comp kerToH1_surjective)
      (fun x hx => (kerToH1_eq_zero_iff x).mp (l.injective (hx.trans (map_zero l).symm)))
      (fun y hy => (kerToH1_eq_zero_iff y).mp (r.injective (hy.trans (map_zero r).symm)))
      (dualityMap1 Gsep Msep roots) (dualityMap1_kummerCoeff_bijective hm Msep hM) ?_
    intro x y
    change χ (tr (cupCycle cup 1 x y).1) =
      dualityMap1 Gsep Msep roots (movedH1 g eL hL (kerToH1 x)) (movedH1 g eN hN (kerToH1 y))
    rw [hχ, movedRootClass, movedH1_class, movedH1_class, dualityMap1_mk]
    apply congrArg (H2pi Gsep roots)
    apply Subtype.ext
    funext p
    obtain ⟨σ, τ⟩ := p
    change (compMu F (2 ^ i)).symm
        (localRootCharacter hS i v hμ (contFun (cup.P 1 1 2 rfl x.1 y.1) ![g σ, g τ])) =
      (σ • eN (contFun y.1 (fun _ => g τ))).toAddMonoidHom (contFun x.1 (fun _ => g σ))
    rw [cup_one_one, ← hN, tateRight_apply]
  · let l := movedH2 g eL hL
    let r := movedH0 g eN hN
    refine cupPerfectAt_of_class_pairing cup tr 2 χ hgen
      (l.toAddMonoidHom.comp kerToH2) (r.toAddMonoidHom.comp kerToH0)
      (l.surjective.comp kerToH2_surjective) (r.surjective.comp kerToH0_surjective)
      (fun x hx => (kerToH2_eq_zero_iff x).mp (l.injective (hx.trans (map_zero l).symm)))
      (fun y hy => boundary_of_kerToH0 (r.injective (hy.trans (map_zero r).symm)))
      (dualityMap2 Gsep Msep roots) (dualityMap2_kummerCoeff_bijective hm Msep hM) ?_
    intro x y
    change χ (tr (cupCycle cup 2 x y).1) =
      dualityMap2 Gsep Msep roots (movedH2 g eL hL (kerToH2 x)) (r (kerToH0 y))
    rw [hχ, movedRootClass, movedH2_class, dualityMap2_mk]
    apply congrArg (H2pi Gsep roots)
    apply Subtype.ext
    funext p
    obtain ⟨σ, τ⟩ := p
    change (compMu F (2 ^ i)).symm
        (localRootCharacter hS i v hμ (contFun (cup.P 2 0 2 rfl x.1 y.1) ![g σ, g τ])) =
      ((σ * τ) • eN (contFun y.1 Fin.elim0)).toAddMonoidHom (contFun x.1 ![g σ, g τ])
    rw [cup_two_zero, ← hN, tateRight_apply, map_mul]

end Actual

end ZInQ.Manuscript.RC.KummerMaps
