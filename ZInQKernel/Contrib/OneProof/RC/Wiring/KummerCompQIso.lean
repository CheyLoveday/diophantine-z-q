import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompLift

/-!
# Theorem 5.3, Lane RC37: the quasi-isomorphism of the Kummer comparison

Manuscript `diophantine_zq.tex`, tex 4005–4014. For a level datum `D` and a subgroup
`L ⊆ H¹(G', M')` satisfying the named input `KcSelmerSupport D L`, the morphism
`kcPhi : τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(L)` is a quasi-isomorphism (`kcPhi_quasiIso`):

* degrees `< 0` and `≥ 2`: both sides have zero cohomology;
* degree `0`: `ψ` is bijective on `H⁰` (`kcPsi_quasiIsoAt_zero`; the level-`m` points of the
  Tate module and the injectivity and surjectivity of the level maps), no arithmetic input;
* degree `1`: `ψ` is injective on `H¹` (`kc_psi_H1_injective`; the local Kummer saturation
  `localKummer_saturated` and the surjectivity of `ρ`), no arithmetic input; every Selmer class
  is hit (`kc_psi_H1_range`; the input `KcSelmerSupport.loc_of_sel` and the local lifting lemma
  `kcLattice_lift`).

The cone bookkeeping of the compact Kummer complex (part (d) of the comparison) is explicit:
components of cochains in degrees `0, 1, 2` (`kcG1`, `kcU1`, `kcL1`, `kcL2`, `kcMk0`, `kcMk1`)
and the differentials on them (`kc_d1_loc`, `kc_d0_*`).

Kinds: definitions and PROVED (from the named input `KcSelmerSupport`).
-/

noncomputable section

set_option maxHeartbeats 3200000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.Finiteness ZInQ.Contrib.RC53Assist.CalibrationShape
open TauCeti TauCeti.ContCohomology
open scoped TensorProduct

attribute [local instance] levTop continuousSMul_lev

/-! ### Components of the compact Kummer complex in degrees `0, 1, 2` -/

section Components

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- The global component in degree one. Kind: definition. -/
abbrev kcG1 (x : (compactKummerComplex S W hFull).X 1) :
    (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1 :=
  kcGlob hFull 1 x

/-- The global component in degree zero. Kind: definition. -/
abbrev kcG0 (x : (compactKummerComplex S W hFull).X 0) :
    (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0 :=
  kcGlob hFull 0 x

/-- The local-condition component at `v` in degree one. Kind: definition. -/
def kcU1 (x : (compactKummerComplex S W hFull).X 1) (v : Places K S) :
    localTateCochain (S := S) W v.1 1 :=
  ((show selT (tateKummerSelData S W hFull) 1 from x).2.1 v).1

/-- The local-condition component at `v` in degree zero. Kind: definition. -/
def kcU0 (x : (compactKummerComplex S W hFull).X 0) (v : Places K S) :
    localTateCochain (S := S) W v.1 0 :=
  ((show selT (tateKummerSelData S W hFull) 0 from x).2.1 v).1

open scoped Classical in
/-- The local-condition component lies in the integral Kummer lattice. Kind: PROVED. -/
theorem kcU1_mem (x : (compactKummerComplex S W hFull).X 1) (v : Places K S) :
    kcU1 hFull x v ∈ localKummerLattice W hFull v.1 :=
  ((show selT (tateKummerSelData S W hFull) 1 from x).2.1 v).2

/-- The local component at `v` in degree one (a local zero-cochain). Kind: definition. -/
def kcL1 (x : (compactKummerComplex S W hFull).X 1) (v : Places K S) :
    localTateCochain (S := S) W v.1 0 :=
  (show selT (tateKummerSelData S W hFull) 1 from x).2.2 v

/-- The local component at `v` in degree two (a local one-cochain). Kind: definition. -/
def kcL2 (y : (compactKummerComplex S W hFull).X 2) (v : Places K S) :
    localTateCochain (S := S) W v.1 1 :=
  (show selT (tateKummerSelData S W hFull) 2 from y).2.2 v

/-- The restriction of the global component to `G_{K_v}` in degree one. Kind: definition. -/
def kcRes1 (x : (compactKummerComplex S W hFull).X 1) (v : Places K S) :
    localTateCochain (S := S) W v.1 1 :=
  natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 1 (kcG1 hFull x)

/-- The restriction of a global zero-cochain to `G_{K_v}`. Kind: definition. -/
def kcRes0 (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0) (v : Places K S) :
    localTateCochain (S := S) W v.1 0 :=
  natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 0 a

/-- The restriction of a global one-cochain to `G_{K_v}`. Kind: definition. -/
def kcResC1 (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1) (v : Places K S) :
    localTateCochain (S := S) W v.1 1 :=
  natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 1 a

/-- **The local component of the differential from degree one**:
`(dx)_v = res_v(a) − u_v − d λ_v`. Kind: PROVED. -/
theorem kc_d1_loc (x : (compactKummerComplex S W hFull).X 1) (v : Places K S) :
    kcL2 hFull (((compactKummerComplex S W hFull).d 1 2).hom x) v =
      kcRes1 hFull x v - kcU1 hFull x v -
        contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 (kcL1 hFull x v) := by
  have h := GCx.toCC_d_hom (selCx (tateKummerSelData S W hFull)) 1 2 rfl x
  unfold kcL2
  rw [show ((compactKummerComplex S W hFull).d 1 2).hom x =
    selD (tateKummerSelData S W hFull) 1 2 rfl x from h]
  rfl

/-- The global component of the differential from degree one. Kind: PROVED. -/
theorem kc_d1_glob (x : (compactKummerComplex S W hFull).X 1) :
    kcGlob hFull 2 (((compactKummerComplex S W hFull).d 1 2).hom x) =
      ((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 1 2).hom (kcG1 hFull x) :=
  kcGlob_d hFull 1 x

/-- The global component of the differential from degree zero. Kind: PROVED. -/
theorem kc_d0_glob (x : (compactKummerComplex S W hFull).X 0) :
    kcG1 hFull (((compactKummerComplex S W hFull).d 0 1).hom x) =
      ((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 0 1).hom (kcG0 hFull x) :=
  kcGlob_d hFull 0 x

/-- The local-condition component of the differential from degree zero. Kind: PROVED. -/
theorem kc_d0_U (x : (compactKummerComplex S W hFull).X 0) (v : Places K S) :
    kcU1 hFull (((compactKummerComplex S W hFull).d 0 1).hom x) v =
      contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 (kcU0 hFull x v) := by
  have h := GCx.toCC_d_hom (selCx (tateKummerSelData S W hFull)) 0 1 rfl x
  unfold kcU1
  rw [show ((compactKummerComplex S W hFull).d 0 1).hom x =
    selD (tateKummerSelData S W hFull) 0 1 rfl x from h]
  exact cocycleCondition_d₀ _ _ _

/-- The local component of the differential from degree zero: `res_v(a) − u_v`.
Kind: PROVED. -/
theorem kc_d0_L (x : (compactKummerComplex S W hFull).X 0) (v : Places K S) :
    kcL1 hFull (((compactKummerComplex S W hFull).d 0 1).hom x) v =
      kcRes0 (kcG0 hFull x) v - kcU0 hFull x v := by
  have h := GCx.toCC_d_hom (selCx (tateKummerSelData S W hFull)) 0 1 rfl x
  unfold kcL1
  rw [show ((compactKummerComplex S W hFull).d 0 1).hom x =
    selD (tateKummerSelData S W hFull) 0 1 rfl x from h]
  change _ - _ - (0 : localTateCochain (S := S) W v.1 0) = _
  rw [sub_zero]
  rfl

/-- Extensionality in degree one. Kind: PROVED. -/
theorem kcC1_ext {x y : (compactKummerComplex S W hFull).X 1} (hG : kcG1 hFull x = kcG1 hFull y)
    (hU : ∀ v, kcU1 hFull x v = kcU1 hFull y v) (hL : ∀ v, kcL1 hFull x v = kcL1 hFull y v) :
    x = y := by
  change (show selT (tateKummerSelData S W hFull) 1 from x) =
    (show selT (tateKummerSelData S W hFull) 1 from y)
  exact Prod.ext hG (Prod.ext (funext fun v => Subtype.ext (hU v)) (funext hL))

/-- Extensionality in degree zero. Kind: PROVED. -/
theorem kcC0_ext {x y : (compactKummerComplex S W hFull).X 0} (hG : kcG0 hFull x = kcG0 hFull y)
    (hU : ∀ v, kcU0 hFull x v = kcU0 hFull y v) : x = y := by
  change (show selT (tateKummerSelData S W hFull) 0 from x) =
    (show selT (tateKummerSelData S W hFull) 0 from y)
  exact Prod.ext hG (Prod.ext (funext fun v => Subtype.ext (hU v))
    (funext fun v => Subsingleton.elim (α := PUnit) _ _))

open scoped Classical in
/-- **A degree-one element from its components.** Kind: definition. -/
def kcMk1 (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1)
    (u : ∀ v : Places K S, localTateCochain (S := S) W v.1 1)
    (hu : ∀ v, u v ∈ localKummerLattice W hFull v.1)
    (l : ∀ v : Places K S, localTateCochain (S := S) W v.1 0) :
    (compactKummerComplex S W hFull).X 1 :=
  (show selT (tateKummerSelData S W hFull) 1 from (a, fun v => ⟨u v, hu v⟩, l))

/-- **A degree-zero element from its components.** Kind: definition. -/
def kcMk0 (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0)
    (u : ∀ v : Places K S, localTateCochain (S := S) W v.1 0) :
    (compactKummerComplex S W hFull).X 0 :=
  (show selT (tateKummerSelData S W hFull) 0 from
    (a, fun v => ofCondZero _ _ (u v), fun _ => PUnit.unit))

open scoped Classical in
@[simp] theorem kcG1_mk1 (a u hu l) : kcG1 hFull (kcMk1 hFull a u hu l) = a := rfl
open scoped Classical in
@[simp] theorem kcU1_mk1 (a u hu l v) : kcU1 hFull (kcMk1 hFull a u hu l) v = u v := rfl
open scoped Classical in
@[simp] theorem kcL1_mk1 (a u hu l v) : kcL1 hFull (kcMk1 hFull a u hu l) v = l v := rfl
@[simp] theorem kcG0_mk0 (a u) : kcG0 hFull (kcMk0 hFull a u) = a := rfl
@[simp] theorem kcU0_mk0 (a u v) : kcU0 hFull (kcMk0 hFull a u) v = u v := rfl

@[simp] theorem kcG1_add (x y) : kcG1 hFull (x + y) = kcG1 hFull x + kcG1 hFull y := rfl
@[simp] theorem kcG1_sub (x y) : kcG1 hFull (x - y) = kcG1 hFull x - kcG1 hFull y := rfl
@[simp] theorem kcG1_smul (c : ℤ_[2]) (x) : kcG1 hFull (c • x) = c • kcG1 hFull x := rfl
@[simp] theorem kcU1_sub (x y v) : kcU1 hFull (x - y) v = kcU1 hFull x v - kcU1 hFull y v := rfl
@[simp] theorem kcU1_smul (c : ℤ_[2]) (x v) : kcU1 hFull (c • x) v = c • kcU1 hFull x v := rfl
@[simp] theorem kcL1_sub (x y v) : kcL1 hFull (x - y) v = kcL1 hFull x v - kcL1 hFull y v := rfl
@[simp] theorem kcL1_smul (c : ℤ_[2]) (x v) : kcL1 hFull (c • x) v = c • kcL1 hFull x v := rfl
@[simp] theorem kcL2_smul (c : ℤ_[2]) (y v) : kcL2 hFull (c • y) v = c • kcL2 hFull y v := rfl
@[simp] theorem kcL2_sub (x y v) : kcL2 hFull (x - y) v = kcL2 hFull x v - kcL2 hFull y v := rfl
@[simp] theorem kcG0_smul (c : ℤ_[2]) (x) : kcG0 hFull (c • x) = c • kcG0 hFull x := rfl
@[simp] theorem kcU1_add (x y v) : kcU1 hFull (x + y) v = kcU1 hFull x v + kcU1 hFull y v := rfl
@[simp] theorem kcL1_add (x y v) : kcL1 hFull (x + y) v = kcL1 hFull x v + kcL1 hFull y v := rfl

/-- **A degree-two element from its global and local components** (the local-condition component
vanishes in degree two). Kind: definition. -/
def kcMk2 (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 2)
    (l : ∀ v : Places K S, localTateCochain (S := S) W v.1 1) :
    (compactKummerComplex S W hFull).X 2 :=
  (show selT (tateKummerSelData S W hFull) 2 from
    (a, (0 : (tateKummerSelData S W hFull).U.X 2), l))

@[simp] theorem kcL2_mk2 (a l v) : kcL2 hFull (kcMk2 hFull a l) v = l v := rfl

/-- The local conditions vanish in degree two. Kind: PROVED. -/
theorem kc_U_two_subsingleton : Subsingleton ((tateKummerSelData S W hFull).U.X 2) := by
  change Subsingleton (∀ v : Places K S, ↥(⊥ : Submodule ℤ_[2]
    (contCochain ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 2)))
  infer_instance

/-- Extensionality in degree two. Kind: PROVED. -/
theorem kcC2_ext {x y : (compactKummerComplex S W hFull).X 2}
    (hG : kcGlob hFull 2 x = kcGlob hFull 2 y) (hL : ∀ v, kcL2 hFull x v = kcL2 hFull y v) :
    x = y := by
  have := kc_U_two_subsingleton hFull
  change (show selT (tateKummerSelData S W hFull) 2 from x) =
    (show selT (tateKummerSelData S W hFull) 2 from y)
  exact Prod.ext hG (Prod.ext (Subsingleton.elim _ _) (funext hL))

/-- `d ∘ d = 0` from degree zero. Kind: PROVED. -/
theorem kc_dd (b : (compactKummerComplex S W hFull).X 0) :
    ((compactKummerComplex S W hFull).d 1 2).hom (((compactKummerComplex S W hFull).d 0 1).hom b)
      = 0 := by
  have e := congrArg (fun f => f.hom b) ((compactKummerComplex S W hFull).d_comp_d 0 1 2)
  exact e
@[simp] theorem kcU0_smul (c : ℤ_[2]) (x v) : kcU0 hFull (c • x) v = c • kcU0 hFull x v := rfl

end Components

/-! ### The lift `φ` -/

section Main

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M') (L : AddSubgroup (H1 G' M'))

/-- The complex `C_K ⊗ ℚ₂/ℤ₂` of abelian groups. Kind: definition. -/
abbrev kcQz : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  integerCoefficientComplex (coefficientQuotientComplex (compactKummerComplex S W hFull))

/-- The inclusion of the cocycle complex of `L` into the continuous cochains. Kind: definition. -/
abbrev kcIotaD : subgroupCocycleComplex L ⟶ (natCx (contCochains ℤ G' M')).toCC :=
  GHom.toCC (cocycleConditionι (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L))

/-- A degree-one continuous cochain, read in the cochain submodule. Kind: definition. -/
def kcCochain1 (z : (natCx (contCochains ℤ G' M')).toCC.X 1) : contCochain ℤ G' M' 1 := z

/-- A degree-zero continuous cochain, read in the cochain submodule. Kind: definition. -/
def kcCochain0 (z : (natCx (contCochains ℤ G' M')).toCC.X 0) : contCochain ℤ G' M' 0 := z

/-- The level-`m` reduction of the global component in degree one. Kind: definition. -/
abbrev kcRed1 (m : ℕ) (x : (compactKummerComplex S W hFull).X 1) :
    (contCochains ℤ (GKS K S) (Lev K S W m)).X 1 :=
  redCochain (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m 1 (kcG1 hFull x)

/-- `θ_m` in degree one is the inflation of the level-`m` reduction. Kind: PROVED. -/
theorem kcTheta_one (m : ℕ) (x : (compactKummerComplex S W hFull).X 1) :
    kcTheta hFull D m 1 x = ((kcInflate D m).f 1).hom (kcRed1 hFull m x) :=
  rfl

open scoped Classical in
/-- The level-`m` coordinate of a `2^m`-multiple vanishes. Kind: PROVED. -/
theorem kc_ltp_two_pow_smul (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (t : TateS K S W) :
    localTatePoint W v m ((2 : ℤ_[2]) ^ m • t) = 0 := by
  have h := localTatePoint_two_pow W v 0 m t
  rw [zero_add] at h
  rw [h, localTatePoint_zero]

/-- A cycle modulo `2^m` has a level-`m` reduction that is a cocycle. Kind: PROVED. -/
theorem kcRed1_d (m : ℕ) (x : (compactKummerComplex S W hFull).X 1)
    (w : (compactKummerComplex S W hFull).X 2)
    (hw : ((compactKummerComplex S W hFull).d 1 2).hom x = (2 : ℤ_[2]) ^ m • w) :
    ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom (kcRed1 hFull m x) = 0 := by
  have h1 := red_comm (kc_isTwoAdicLimit hFull) (isEquivariantLevels_tate K S W) m 1 2 rfl
    (kcGlob hFull 1 x)
  have h2 := kc_d1_glob hFull x
  rw [hw, kcGlob_smul] at h2
  change (natCx (contCochains ℤ (GKS K S) (Lev K S W m))).d 1 2 rfl
    (red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m 1 (kcGlob hFull 1 x)) = 0
  rw [← h1]
  change red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m 2
    (((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 1 2).hom (kcG1 hFull x)) = 0
  rw [← h2]
  exact red_two_pow_smul (kc_isTwoAdicLimit hFull) m 2 _

open scoped Classical in
/-- **Local triviality of the reduction of a cycle (part (c), first half).** If `dx = 2^m w`,
the level-`m` reduction of the global component of `x` is locally trivial at every place of
`S`: at `v`, `res_v(a) = u_v + dλ_v + 2^m w_v` with `u_v` in the integral Kummer lattice, whose
level-`m` coordinate is a coboundary (`kcLattice_coboundary`). Kind: PROVED. -/
theorem kc_locTriv (m : ℕ) (x : (compactKummerComplex S W hFull).X 1)
    (w : (compactKummerComplex S W hFull).X 2)
    (hw : ((compactKummerComplex S W hFull).d 1 2).hom x = (2 : ℤ_[2]) ^ m • w) :
    KcLocTriv W (kcRed1 hFull m x) := by
  intro v
  obtain ⟨R₁, hR₁⟩ := kcLattice_coboundary W hFull v.1 m (kcU1 hFull x v) (kcU1_mem hFull x v)
  refine ⟨R₁ + localTatePoint W v.1 m (show TateS K S W from
    cfun (M := ResMod (locMap K S v.1) (TateS K S W)) (kcL1 hFull x v) default), fun σ => ?_⟩
  have hL : kcL2 hFull (((compactKummerComplex S W hFull).d 1 2).hom x) v =
      (2 : ℤ_[2]) ^ m • kcL2 hFull w v := by
    rw [hw]
    rfl
  rw [kc_d1_loc] at hL
  have hval := congrArg (fun c : localTateCochain (S := S) W v.1 1 => localTatePoint W v.1 m
    (show TateS K S W from cfun (M := ResMod (locMap K S v.1) (TateS K S W)) c (fun _ => σ))) hL
  have e1 : localTatePoint W v.1 m (show TateS K S W from
        cfun (M := ResMod (locMap K S v.1) (TateS K S W)) (kcRes1 hFull x v) (fun _ => σ)) -
      localTatePoint W v.1 m (show TateS K S W from
        cfun (M := ResMod (locMap K S v.1) (TateS K S W)) (kcU1 hFull x v) (fun _ => σ)) -
      localTatePoint W v.1 m (show TateS K S W from
        cfun (M := ResMod (locMap K S v.1) (TateS K S W))
          (contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0
            (kcL1 hFull x v)) (fun _ => σ)) = 0 := by
    rw [← map_sub, ← map_sub]
    refine hval.trans ?_
    exact kc_ltp_two_pow_smul v.1 m (show TateS K S W from
      cfun (M := ResMod (locMap K S v.1) (TateS K S W)) (kcL2 hFull w v) (fun _ => σ))
  rw [hR₁ σ, localTatePoint_boundary, sub_sub, sub_eq_zero] at e1
  beta_reduce at e1
  change localTatePoint W v.1 m (show TateS K S W from
    cfun (M := ResMod (locMap K S v.1) (TateS K S W)) (kcRes1 hFull x v) (fun _ => σ)) = _
  rw [e1, smul_add]
  abel

/-- **The image under `ψ` of a cycle of `C_K ⊗ ℚ₂/ℤ₂` in degree one is a Selmer cocycle**
(from the input `KcSelmerSupport.sel_of_loc`). Kind: PROVED. -/
theorem kc_psi_mem_disc (hG : KcSelmerSupport D L) (y : (kcQz hFull).X 1)
    (hy : ((kcQz hFull).d 1 2).hom y = 0) :
    kcCochain1 (((kcPsi hFull D).f 1).hom y) ∈ subgroupCocycleSub L ⊔ contB1 ℤ G' M' := by
  obtain ⟨m, x, rfl⟩ := kcFrac_surjective (compactKummerComplex S W hFull) 1 y
  obtain ⟨w, hw⟩ := (kcFrac_d_eq_zero_iff (compactKummerComplex S W hFull) 1 2 m x).1 hy
  have hf := kcRed1_d hFull m x w hw
  have hmem := hG.sel_of_loc m (kcRed1 hFull m x) hf (kc_locTriv hFull m x w hw)
  rw [kcPsi_frac]
  exact kc_mem_disc_of_class L _ _ hmem

/-- The lifting condition for `ι_{≤1} ≫ ψ` through the cocycle complex of `L`. Kind: PROVED. -/
theorem kc_lift_cond (hG : KcSelmerSupport D L) (n : ℤ) (a : ((kcQz hFull).truncLE 1).X n) :
    ∃ b : (subgroupCocycleComplex L).X n, ((kcIotaD L).f n).hom b =
      (((kcQz hFull).ιTruncLE 1 ≫ kcPsi hFull D).f n).hom a := by
  rcases n with n | n
  · rcases n with _ | _ | n
    · exact ⟨ofCondZero _ _ (kcCochain0
        ((((kcQz hFull).ιTruncLE 1 ≫ kcPsi hFull D).f 0).hom a)), rfl⟩
    · have hz : IsZero (((kcQz hFull).truncLE 1).X 2) :=
        CochainComplex.isZero_of_isStrictlyLE _ 1 2 (by norm_num)
      have hd : (((kcQz hFull).truncLE 1).d 1 2).hom a = 0 := by
        have := (ModuleCat.isZero_iff_subsingleton).1 hz
        exact Subsingleton.elim _ _
      have hy : ((kcQz hFull).d 1 2).hom ((((kcQz hFull).ιTruncLE 1).f 1).hom a) = 0 := by
        have e := congrArg (fun g => g.hom a) (((kcQz hFull).ιTruncLE 1).comm 1 2)
        change ((kcQz hFull).d 1 2).hom ((((kcQz hFull).ιTruncLE 1).f 1).hom a) =
          (((kcQz hFull).ιTruncLE 1).f 2).hom ((((kcQz hFull).truncLE 1).d 1 2).hom a) at e
        rw [e, hd, map_zero]
      exact ⟨ofCondOne _ _ ⟨_, kc_psi_mem_disc hFull D L hG _ hy⟩, rfl⟩
    · have hz : IsZero (((kcQz hFull).truncLE 1).X (n + 2 : ℕ)) :=
        CochainComplex.isZero_of_isStrictlyLE _ 1 _ (by omega)
      have ha : a = 0 := by
        have := (ModuleCat.isZero_iff_subsingleton).1 hz
        exact Subsingleton.elim _ _
      refine ⟨0, ?_⟩
      rw [ha, map_zero, map_zero]
  · exact ⟨0, Subsingleton.elim (α := PUnit.{1}) _ _⟩

/-- **The morphism `φ : τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(L)`.** Kind: definition. -/
def kcPhi (hG : KcSelmerSupport D L) : (kcQz hFull).truncLE 1 ⟶ subgroupCocycleComplex L :=
  kcLift ((kcQz hFull).ιTruncLE 1 ≫ kcPsi hFull D) (kcIotaD L) (kc_iotaD_injective L)
    (kc_lift_cond hFull D L hG)

/-- **`φ ≫ ι = ι_{≤1} ≫ ψ`.** Kind: PROVED. -/
theorem kcPhi_comp (hG : KcSelmerSupport D L) :
    kcPhi hFull D L hG ≫ kcIotaD L = (kcQz hFull).ιTruncLE 1 ≫ kcPsi hFull D :=
  kcLift_comp _ _ _ _

end Main

/-! ### Degree zero -/

section DegreeZero

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M')

/-- The constant global zero-cochain with value `t`. Kind: definition. -/
def kcConst0 (t : TateS K S W) : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0 :=
  constCochain (G := GKS K S) (k := ℤ_[2]) t

omit [W.IsElliptic] in
/-- Restriction commutes with the degree-zero differential. Kind: PROVED. -/
theorem kc_res_d0 (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0) (v : Places K S) :
    contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 (kcRes0 a v) =
      kcResC1 (((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 0 1).hom a) v :=
  congrArg (fun g => g.hom a)
    ((resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)).comm 0 1)

omit [W.IsElliptic] in
theorem kcRes0_smul (c : ℤ_[2]) (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0)
    (v : Places K S) : kcRes0 (c • a) v = c • kcRes0 a v :=
  LinearMap.map_smul (natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 0) c a

omit [W.IsElliptic] in
theorem kcResC1_smul (c : ℤ_[2]) (a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1)
    (v : Places K S) : kcResC1 (c • a) v = c • kcResC1 a v :=
  LinearMap.map_smul (natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 1) c a

omit [W.IsElliptic] in
theorem kcResC1_sub (a b : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1)
    (v : Places K S) : kcResC1 (a - b) v = kcResC1 a v - kcResC1 b v :=
  LinearMap.map_sub (natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 1) a b

omit [W.IsElliptic] in
theorem kcRes0_zero (v : Places K S) :
    kcRes0 (0 : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0) v = 0 :=
  LinearMap.map_zero (natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 0)

open scoped Classical in
/-- Integral coboundaries lie in the integral Kummer lattice. Kind: PROVED. -/
theorem kc_boundary_mem_lattice (v : Places K S) (c : localTateCochain (S := S) W v.1 0) :
    contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 c ∈
      localKummerLattice W hFull v.1 :=
  Submodule.mem_sup_right ((mem_contB1_iff _).2 ⟨c, rfl⟩)

open scoped Classical in
/-- **Degree zero, existence.** A `G_{K,S}`-invariant level-`m` point `P` gives a cycle `x₀`
modulo `2^m` (the constant cochain of a lift of `P` to `T₂E`, with its restrictions as local
conditions) with `θ_m(x₀)` the constant cochain `J_m(P)`. Kind: PROVED. -/
theorem kc_deg0_cycle (m : ℕ) (P : Lev K S W m) (hP : ∀ g : GKS K S, g • P = P) :
    ∃ x₀ : (compactKummerComplex S W hFull).X 0,
      (∃ w, ((compactKummerComplex S W hFull).d 0 1).hom x₀ = (2 : ℤ_[2]) ^ m • w) ∧
      ∀ g : Fin 0 → G', cochainFun (k := ℤ) (G := G') (M := M') (j := 0)
        (kcTheta hFull D m (Int.ofNat 0) x₀) g = D.J m P := by
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  obtain ⟨t, ht⟩ := projLev_surjective (K := K) (S := S) (W := W) m P
  let a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 0 :=
    constCochain (G := GKS K S) (k := ℤ_[2]) t
  have hda : red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m (Int.ofNat 1)
      (contD ℤ_[2] (GKS K S) (TateS K S W) 0 a) = 0 := by
    apply cochain_ext
    intro g
    change projLev m (cfun (contD ℤ_[2] (GKS K S) (TateS K S W) 0 a) g) = 0
    rw [cfun_contD_constCochain, map_sub, projLev_smul, ht, hP, sub_self]
  obtain ⟨wG, hwG⟩ : ∃ w : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1,
      contD ℤ_[2] (GKS K S) (TateS K S W) 0 a = (2 : ℤ_[2]) ^ m • w :=
    red_ker (kc_isTwoAdicLimit hFull) m (Int.ofNat 1) _ hda
  have hres : ∀ v : Places K S,
      contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 (kcRes0 a v) =
        (2 : ℤ_[2]) ^ m • kcResC1 wG v := fun v => by
    rw [kc_res_d0, ← kcResC1_smul]
    exact congrArg (fun z => kcResC1 z v) hwG
  have hmem : ∀ v : Places K S, kcResC1 wG v ∈ localKummerLattice W hFull v.1 := by
    intro v
    apply localKummer_saturated W hFull v.1 m
    rw [← hres v]
    exact kc_boundary_mem_lattice hFull v _
  refine ⟨kcMk0 hFull a (fun v => kcRes0 a v),
    ⟨kcMk1 hFull wG (fun v => kcResC1 wG v) hmem (fun _ => 0), ?_⟩, fun g => ?_⟩
  · apply kcC1_ext
    · rw [kc_d0_glob, kcG1_smul, kcG1_mk1, kcG0_mk0]
      exact hwG
    · intro v
      rw [kc_d0_U, kcU1_smul, kcU1_mk1, kcU0_mk0]
      exact hres v
    · intro v
      rw [kc_d0_L, kcL1_smul, kcL1_mk1, kcG0_mk0, kcU0_mk0, sub_self, smul_zero]
  · refine (kcTheta_apply hFull D m 0 _ g).trans ?_
    change D.J m (projLev m t) = D.J m P
    rw [ht]

open scoped Classical in
/-- **`ψ` is a quasi-isomorphism in degree zero** (`H⁰(C_K ⊗ ℚ₂/ℤ₂) ≅ H⁰(G', M')`: invariant
torsion points of `M'` are level points of `E(K_S)` fixed by `G_{K,S}`, and these lift to cycles
modulo `2^m`; a cycle whose image vanishes is divisible by `2^m`). Kind: PROVED. -/
theorem kcPsi_quasiIsoAt_zero : QuasiIsoAt (kcPsi hFull D) 0 := by
  refine ZInQ.Contrib.CloudB3RC53.TameModel.quasiIsoAt_of_elem (kcPsi hFull D) (-1) 0 1
    (by simp) (by simp) ?_ ?_
  · intro y hy
    have h0 : contD ℤ G' M' 0 (kcCochain0 y) = 0 := by
      have e := GCx.toCC_d_hom (natCx (contCochains ℤ G' M')) 0 1 rfl y
      rw [e] at hy
      exact hy
    have hinv := (contD_zero_eq_zero_iff _).1 h0
    obtain ⟨m, P', hP'⟩ := D.J_surj (cfun (kcCochain0 y) default)
    have hinv' : ∀ g : GKS K S, g • P' = P' := by
      intro g
      obtain ⟨g', rfl⟩ := D.ρ_surj g
      have h1 : D.J m (D.ρ g' • P' - P') = 0 := by
        rw [map_sub, D.J_smul, hP', hinv, sub_self]
      exact sub_eq_zero.1 (D.J_inj m _ h1)
    obtain ⟨x₀, ⟨w, hw⟩, hθ⟩ := kc_deg0_cycle hFull D m P' hinv'
    refine ⟨kcFrac _ m x₀,
      (kcFrac_d_eq_zero_iff (compactKummerComplex S W hFull) 0 1 m x₀).2 ⟨w, hw⟩, 0, ?_⟩
    rw [map_zero, add_zero, kcPsi_frac]
    apply cochain_ext (k := ℤ) (G := G') (M := M') (j := 0)
    intro g
    refine (hθ g).trans ?_
    rw [hP']
    change cfun (kcCochain0 y) default = cfun (kcCochain0 y) g
    rw [Subsingleton.elim g default]
  · intro x hx z hz
    obtain ⟨m, x₀, rfl⟩ := kcFrac_surjective (compactKummerComplex S W hFull) 0 x
    obtain ⟨w₁, hw₁⟩ := (kcFrac_d_eq_zero_iff (compactKummerComplex S W hFull) 0 1 m x₀).1 hx
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    refine (kcFrac_eq_zero_iff (compactKummerComplex S W hFull) m x₀).2 ?_
    have hz0 : z = 0 := Subsingleton.elim (α := PUnit.{1}) _ _
    rw [hz0, map_zero, kcPsi_frac] at hz
    have ht : (cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W) (j := 0)
        (kcG0 hFull x₀) default).pt m = 0 := by
      have h1 := congrArg (fun c => cochainFun (k := ℤ) (G := G') (M := M') (j := 0)
        (show (contCochains ℤ G' M').X 0 from c) default) hz
      have h2 : D.J m (projLev m (cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W)
          (j := 0) (kcG0 hFull x₀) default)) = 0 := by
        refine Eq.trans ?_ h1
        refine (Eq.trans ?_ (kcTheta_apply hFull D m 0 x₀ default).symm)
        rw [Subsingleton.elim (D.ρ ∘ (default : Fin 0 → G')) default]
        rfl
      exact congrArg Subtype.val (D.J_inj m _ h2)
    obtain ⟨t', ht'⟩ := (mem_ker_projLev_iff m _).1 ht
    refine ⟨kcMk0 hFull (kcConst0 t') (fun v => kcRes0 (kcConst0 t') v - kcL1 hFull w₁ v), ?_⟩
    have hG0 : kcG0 hFull x₀ = (2 : ℤ_[2]) ^ m • kcConst0 t' := by
      refine (eq_constCochain (kcG0 hFull x₀)).trans ?_
      apply Subtype.ext
      funext u
      exact ht'.symm
    apply kcC0_ext
    · rw [kcG0_smul, kcG0_mk0]
      exact hG0
    · intro v
      have hL := congrArg (fun y => kcL1 hFull y v) hw₁
      simp only [kc_d0_L, kcL1_smul] at hL
      rw [kcU0_smul, kcU0_mk0, smul_sub, ← kcRes0_smul, ← hG0, ← hL]
      abel

end DegreeZero

/-! ### Degree one -/

section DegreeOne

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M') (L : AddSubgroup (H1 G' M'))

open scoped Classical in
/-- **Degree one, local step.** A cycle modulo `2^M` with vanishing global component is a
boundary modulo `2^M`: `u_v + dλ_v ∈ 2^M · C¹(G_{K_v}, T₂E)` with `u_v` in the integral Kummer
lattice, and the lattice is saturated (`localKummer_saturated`). Kind: PROVED. -/
theorem kc_boundary_of_glob_zero (M : ℕ) (x : (compactKummerComplex S W hFull).X 1)
    (w : (compactKummerComplex S W hFull).X 2)
    (hw : ((compactKummerComplex S W hFull).d 1 2).hom x = (2 : ℤ_[2]) ^ M • w)
    (hG : kcG1 hFull x = 0) :
    ∃ (b : (compactKummerComplex S W hFull).X 0) (e : (compactKummerComplex S W hFull).X 1),
      x = ((compactKummerComplex S W hFull).d 0 1).hom b + (2 : ℤ_[2]) ^ M • e := by
  have hloc : ∀ v : Places K S, kcU1 hFull x v +
      contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 (kcL1 hFull x v) =
        (2 : ℤ_[2]) ^ M • (-kcL2 hFull w v) := by
    intro v
    have hL := congrArg (fun y => kcL2 hFull y v) hw
    simp only [kc_d1_loc, kcL2_smul] at hL
    have hres : kcRes1 hFull x v = 0 := by
      change natF (resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v.1)) 1
        (kcG1 hFull x) = 0
      rw [hG]
      exact LinearMap.map_zero _
    rw [hres] at hL
    rw [smul_neg, ← hL]
    abel
  have hmem : ∀ v : Places K S, -kcL2 hFull w v ∈ localKummerLattice W hFull v.1 := by
    intro v
    apply localKummer_saturated W hFull v.1 M
    rw [← hloc v]
    exact Submodule.add_mem _ (kcU1_mem hFull x v) (kc_boundary_mem_lattice hFull v _)
  refine ⟨kcMk0 hFull 0 (fun v => -kcL1 hFull x v),
    kcMk1 hFull 0 (fun v => -kcL2 hFull w v) hmem (fun _ => 0), ?_⟩
  apply kcC1_ext
  · rw [kcG1_add, kc_d0_glob, kcG1_smul, kcG1_mk1, kcG0_mk0, hG, map_zero, smul_zero, add_zero]
  · intro v
    rw [kcU1_add, kc_d0_U, kcU1_smul, kcU1_mk1, kcU0_mk0, ← hloc v, map_neg]
    abel
  · intro v
    rw [kcL1_add, kc_d0_L, kcL1_smul, kcL1_mk1, kcG0_mk0, kcU0_mk0, kcRes0_zero, smul_zero,
      add_zero, zero_sub, neg_neg]

open scoped Classical in
/-- **Degree one, global step.** A cycle modulo `2^M` whose global component reduces modulo `2^M`
to the coboundary `g ↦ g P − P` of a level-`M` point is a boundary modulo `2^M`. Kind: PROVED. -/
theorem kc_boundary_of_red_cob (M : ℕ) (x : (compactKummerComplex S W hFull).X 1)
    (w : (compactKummerComplex S W hFull).X 2)
    (hw : ((compactKummerComplex S W hFull).d 1 2).hom x = (2 : ℤ_[2]) ^ M • w)
    (P : Lev K S W M)
    (hP : ∀ g : GKS K S, projLev M (cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W)
      (j := 1) (kcG1 hFull x) (fun _ => g)) = g • P - P) :
    ∃ (b : (compactKummerComplex S W hFull).X 0) (e : (compactKummerComplex S W hFull).X 1),
      x = ((compactKummerComplex S W hFull).d 0 1).hom b + (2 : ℤ_[2]) ^ M • e := by
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  obtain ⟨t, ht⟩ := projLev_surjective (K := K) (S := S) (W := W) M P
  let b₁ := kcMk0 hFull (kcConst0 t) (fun v => kcRes0 (kcConst0 t) v)
  have hG' : kcG1 hFull (x - ((compactKummerComplex S W hFull).d 0 1).hom b₁) =
      kcG1 hFull x - ((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 0 1).hom (kcConst0 t) := by
    rw [kcG1_sub, kc_d0_glob, kcG0_mk0]
  have hred : red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) M (Int.ofNat 1)
      (kcG1 hFull x - ((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 0 1).hom (kcConst0 t)) =
        0 := by
    apply cochain_ext
    intro g
    change projLev M (cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W) (j := 1)
      (kcG1 hFull x) g - cfun (contD ℤ_[2] (GKS K S) (TateS K S W) 0 (kcConst0 t)) g) = 0
    have e : cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W) (j := 1)
        (kcG1 hFull x) g = cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W) (j := 1)
          (kcG1 hFull x) (fun _ => g 0) :=
      congrArg _ (funext fun i => by rw [Subsingleton.elim i 0])
    rw [map_sub, e, hP, kcConst0, cfun_contD_constCochain, map_sub, projLev_smul, ht, sub_self]
  obtain ⟨wG, hwG⟩ : ∃ w' : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1,
      kcG1 hFull x - ((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 0 1).hom (kcConst0 t) =
        (2 : ℤ_[2]) ^ M • w' :=
    red_ker (kc_isTwoAdicLimit hFull) M (Int.ofNat 1) _ hred
  let e₁ := kcMk1 hFull wG (fun _ => 0) (fun v => Submodule.zero_mem _) (fun _ => 0)
  have hG'' : kcG1 hFull (x - ((compactKummerComplex S W hFull).d 0 1).hom b₁ -
      (2 : ℤ_[2]) ^ M • e₁) = 0 := by
    rw [kcG1_sub, hG', hwG, kcG1_smul, kcG1_mk1, sub_self]
  have hw'' : ((compactKummerComplex S W hFull).d 1 2).hom
      (x - ((compactKummerComplex S W hFull).d 0 1).hom b₁ - (2 : ℤ_[2]) ^ M • e₁) =
        (2 : ℤ_[2]) ^ M • (w - ((compactKummerComplex S W hFull).d 1 2).hom e₁) := by
    rw [map_sub, map_sub, hw, kc_dd, LinearMap.map_smul, smul_sub, sub_zero]
  obtain ⟨b₂, e₂, h₂⟩ := kc_boundary_of_glob_zero hFull M _ _ hw'' hG''
  refine ⟨b₁ + b₂, e₂ + e₁, ?_⟩
  rw [map_add, smul_add]
  have hx : x = (x - ((compactKummerComplex S W hFull).d 0 1).hom b₁ - (2 : ℤ_[2]) ^ M • e₁) +
      ((compactKummerComplex S W hFull).d 0 1).hom b₁ + (2 : ℤ_[2]) ^ M • e₁ := by
    abel
  rw [hx, h₂]
  abel

/-- **`ψ` is injective on `H¹`** (no arithmetic input): if `θ_m(x) = d z`, the value of `z` is a
level point `P` of `E(K_S)` and the global component of `2^{m₁} x` reduces to the coboundary of
`P` (surjectivity of `ρ`, injectivity of the level maps), so `[x/2^m]` is a boundary.
Kind: PROVED. -/
theorem kc_psi_H1_injective :
    Function.Injective (HomologicalComplex.homologyMap (kcPsi hFull D) 1).hom := by
  refine kc_homologyMap_injective (kcPsi hFull D) 0 1 2 (by simp) (by simp) ?_
  intro y hy z hz
  obtain ⟨m, x, rfl⟩ := kcFrac_surjective (compactKummerComplex S W hFull) 1 y
  obtain ⟨w, hw⟩ := (kcFrac_d_eq_zero_iff (compactKummerComplex S W hFull) 1 2 m x).1 hy
  rw [kcPsi_frac] at hz
  have hz' : kcCochain1 (kcTheta hFull D m 1 x) = contD ℤ G' M' 0 (kcCochain0 z) := by
    rw [hz]
    exact GCx.toCC_d_hom (natCx (contCochains ℤ G' M')) 0 1 rfl z
  obtain ⟨m₁, P₁, hP₁⟩ := D.J_surj (cfun (kcCochain0 z) default)
  have hmem : ∀ Q : Lev K S W m₁, (Q : Pt K S W) ∈
      AddSubgroup.torsionBy (Pt K S W) ((2 ^ (m + m₁) : ℕ) : ℤ) := fun Q => by
    rw [mem_lev_iff, pow_add, mul_smul, two_pow_nsmul_lev Q, smul_zero]
  have hmem' : ∀ Q : Lev K S W m, (Q : Pt K S W) ∈
      AddSubgroup.torsionBy (Pt K S W) ((2 ^ (m + m₁) : ℕ) : ℤ) := fun Q => by
    rw [mem_lev_iff, pow_add, mul_comm, mul_smul, two_pow_nsmul_lev Q, smul_zero]
  let P₂ : Lev K S W (m + m₁) := ⟨P₁, hmem P₁⟩
  have hpt : ∀ g : GKS K S, projLev (m + m₁) (cochainFun (k := ℤ_[2]) (G := GKS K S)
      (M := TateS K S W) (j := 1) (kcG1 hFull ((2 : ℤ_[2]) ^ m₁ • x)) (fun _ => g)) =
        g • P₂ - P₂ := by
    intro g
    obtain ⟨g', rfl⟩ := D.ρ_surj g
    have h1 := congrArg (fun c => cfun c (fun _ => g')) hz'
    simp only at h1
    rw [contD_zero_apply] at h1
    let Q : Lev K S W (m + m₁) := ⟨_, hmem' (projLev m (cochainFun (k := ℤ_[2])
      (G := GKS K S) (M := TateS K S W) (j := 1) (kcG1 hFull x) (fun _ => D.ρ g')))⟩
    have hQ : D.J (m + m₁) Q = D.J (m + m₁) (D.ρ g' • P₂ - P₂) := by
      rw [map_sub, D.J_smul, ← D.J_compat m₁ (m + m₁) P₁ P₂ rfl, hP₁]
      refine Eq.trans ?_ h1
      exact (D.J_compat m (m + m₁) _ Q rfl).symm
    have hQ' := sub_eq_zero.1 (D.J_inj (m + m₁) (Q - (D.ρ g' • P₂ - P₂))
      (by rw [map_sub, hQ, sub_self]))
    apply Subtype.ext
    change ((2 : ℤ_[2]) ^ m₁ • cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W)
      (j := 1) (kcG1 hFull x) (fun _ => D.ρ g')).pt (m + m₁) = _
    rw [kc_pt_two_pow_smul]
    exact congrArg Subtype.val hQ'
  have hw' : ((compactKummerComplex S W hFull).d 1 2).hom ((2 : ℤ_[2]) ^ m₁ • x) =
      (2 : ℤ_[2]) ^ (m + m₁) • w := by
    rw [LinearMap.map_smul, hw, smul_smul, ← pow_add, add_comm m₁ m]
  obtain ⟨b, e, hbe⟩ := kc_boundary_of_red_cob hFull (m + m₁) _ w hw' P₂ hpt
  refine ⟨kcFrac _ (m + m₁) b, ?_⟩
  change ((coefficientQuotientComplex (compactKummerComplex S W hFull)).d 0 1).hom
    (kcFrac _ (m + m₁) b) = kcFrac _ m x
  have h0 : kcFrac (compactKummerComplex S W hFull) (m + m₁) ((2 : ℤ_[2]) ^ (m + m₁) • e) = 0 :=
    (kcFrac_eq_zero_iff _ _ _).2 ⟨e, rfl⟩
  rw [kcFrac_d, ← kcFrac_shift _ m m₁ x, hbe, ← kcFrac_add, h0, add_zero]


open scoped Classical in
/-- **Every Selmer class is in the image of `ψ` on `H¹`** (part (c), second half): a class of `L`
is the inflation of a locally trivial level-`m` cocycle `f` (input
`KcSelmerSupport.loc_of_sel`); a continuous lift `a` of `f` to `T₂E`, completed by the local
Kummer lifts `res_v(a) = u_v + dλ_v + 2^m w_v` (`kcLattice_lift`), is a cycle modulo `2^m`
whose image under `ψ` is the inflation of `f`. Kind: PROVED. -/
theorem kc_psi_H1_range (hG : KcSelmerSupport D L) (c : (subgroupCocycleComplex L).homology 1) :
    ∃ c', (HomologicalComplex.homologyMap (kcPsi hFull D) 1).hom c' =
      (HomologicalComplex.homologyMap (kcIotaD L) 1).hom c := by
  refine kc_homologyMap_range (kcPsi hFull D) (kcIotaD L) 0 1 2 (by simp) (by simp) ?_ c
  intro y _
  obtain ⟨m, f, hf, hloc, hcls⟩ := hG.loc_of_sel _ (subgroupAmbientClass_mem L y)
  obtain ⟨a, ha⟩ : ∃ a : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 1,
      redCochain (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m 1 a = f :=
    red_surjective (kc_isTwoAdicLimit hFull) m (Int.ofNat 1) f
  have hda : red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m (Int.ofNat 2)
      (((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 1 2).hom a) = 0 := by
    have h1 := red_comm (kc_isTwoAdicLimit hFull) (isEquivariantLevels_tate K S W) m 1 2 rfl a
    refine h1.trans ?_
    change ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom
      (redCochain (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m 1 a) = 0
    rw [ha]
    exact hf
  obtain ⟨wG, hwG⟩ : ∃ w : (contCochains ℤ_[2] (GKS K S) (TateS K S W)).X 2,
      ((contCochains ℤ_[2] (GKS K S) (TateS K S W)).d 1 2).hom a = (2 : ℤ_[2]) ^ m • w :=
    red_ker (kc_isTwoAdicLimit hFull) m (Int.ofNat 2) _ hda
  have hlift : ∀ v : Places K S, ∃ u ∈ localKummerLattice W hFull v.1,
      ∃ (c : localTateCochain (S := S) W v.1 0) (w : localTateCochain (S := S) W v.1 1),
        kcResC1 a v = u + contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0 c +
          (2 : ℤ_[2]) ^ m • w := by
    intro v
    obtain ⟨R, hR⟩ := hloc v
    refine kcLattice_lift W hFull v.1 m (kcResC1 a v) R (fun σ => ?_)
    rw [← ha] at hR
    exact hR σ
  choose u hu cv wv hcw using hlift
  have hdx : ((compactKummerComplex S W hFull).d 1 2).hom (kcMk1 hFull a u hu cv) =
      (2 : ℤ_[2]) ^ m • kcMk2 hFull wG wv := by
    apply kcC2_ext
    · rw [kc_d1_glob, kcG1_mk1, hwG]
      rfl
    · intro v
      rw [kc_d1_loc, kcL2_smul, kcL2_mk2, kcU1_mk1, kcL1_mk1]
      change kcResC1 a v - u v - _ = _
      rw [hcw v]
      abel
  refine ⟨kcFrac _ m (kcMk1 hFull a u hu cv),
    (kcFrac_d_eq_zero_iff (compactKummerComplex S W hFull) 1 2 m _).2 ⟨_, hdx⟩, ?_⟩
  let yk : LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom :=
    ⟨(subgroupCycle L y : contCochain ℤ G' M' 1),
      LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (subgroupCycle L y).2)⟩
  let xk : LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom := ⟨_, kcInflate_mem_ker D hf⟩
  have hyk : kerToH1 (k := ℤ) yk = subgroupAmbientClass L y := rfl
  have hdiff : kerToH1 (k := ℤ) (xk - yk) = 0 := by
    rw [map_sub, hyk]
    exact sub_eq_zero.2 hcls
  obtain ⟨z₀, hz₀⟩ := (kerToH1_eq_zero_iff _).1 hdiff
  refine ⟨z₀, ?_⟩
  have key : ((kcInflate D m).f 1).hom f =
      (yk : (contCochains ℤ G' M').X 1) + ((contCochains ℤ G' M').d 0 1).hom z₀ := by
    rw [hz₀, Submodule.coe_sub, add_sub_cancel]
  rw [kcPsi_frac, kcTheta_one]
  have e := GCx.toCC_d_hom (natCx (contCochains ℤ G' M')) 0 1 rfl z₀
  rw [e]
  have hr : kcRed1 hFull m (kcMk1 hFull a u hu cv) = f := ha
  rw [hr]
  exact key

end DegreeOne

/-! ### The quasi-isomorphism -/

section Assembly

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M') (L : AddSubgroup (H1 G' M'))

/-- The cocycle inclusion is injective on `H¹`. Kind: PROVED. -/
theorem kc_iotaD_H1_injective :
    Function.Injective (HomologicalComplex.homologyMap (kcIotaD L) 1).hom :=
  (ModuleCat.mono_iff_injective _).1 (cocycleCondition_mono_homologyMap_one _ _)

/-- The cocycle inclusion is a quasi-isomorphism in degree zero. Kind: PROVED. -/
theorem kc_iotaD_quasiIsoAt_zero : QuasiIsoAt (kcIotaD L) 0 :=
  (quasiIsoAt_iff_isIso_homologyMap _ 0).2 (cocycleCondition_isIso_homologyMap_zero _ _)

/-- The compact Kummer complex vanishes in negative degrees. Kind: PROVED. -/
theorem kc_compact_X_subsingleton (k : ℕ) :
    Subsingleton ((compactKummerComplex S W hFull).X (Int.negSucc k)) := by
  change Subsingleton (PUnit.{1} × (∀ _ : Places K S, PUnit.{1}) × (∀ _ : Places K S, PUnit.{1}))
  infer_instance

/-- `C_K ⊗ ℚ₂/ℤ₂` vanishes in negative degrees. Kind: PROVED. -/
theorem kcQz_X_subsingleton (k : ℕ) : Subsingleton ((kcQz hFull).X (Int.negSucc k)) := by
  have := kc_compact_X_subsingleton hFull k
  constructor
  intro y y'
  obtain ⟨m, x, rfl⟩ := kcFrac_surjective (compactKummerComplex S W hFull) _ y
  obtain ⟨m', x', rfl⟩ := kcFrac_surjective (compactKummerComplex S W hFull) _ y'
  rw [Subsingleton.elim x 0, Subsingleton.elim x' 0, kcFrac_zero, kcFrac_zero]

/-- The cocycle complex of `L` vanishes in negative degrees and in degrees `≥ 2`.
Kind: PROVED. -/
theorem kc_disc_X_subsingleton (n : ℤ) (hn : n < 0 ∨ 2 ≤ n) :
    Subsingleton ((cocycleCondition (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).X n) := by
  rcases n with n | n
  · rcases n with _ | _ | n
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · change Subsingleton ↥(⊥ : Submodule ℤ (contCochain ℤ G' M' (n + 2)))
      infer_instance
  · change Subsingleton PUnit.{1}
    infer_instance

/-- **`φ` is a quasi-isomorphism** (from the input `KcSelmerSupport D L`). Kind: PROVED. -/
theorem kcPhi_quasiIso (hG : KcSelmerSupport D L) : QuasiIso (kcPhi hFull D L hG) := by
  rw [quasiIso_iff]
  intro n
  have hzero : ∀ (A B : CochainComplex (ModuleCat.{0} ℤ) ℤ) (g : A ⟶ B),
      IsZero (A.homology n) → IsZero (B.homology n) → QuasiIsoAt g n := by
    intro A B g hA hB
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_of_source_target_iso_zero _ hA.isoZero hB.isoZero
  have hdisc : (n < 0 ∨ 2 ≤ n) → IsZero ((subgroupCocycleComplex L).homology n) := fun hn =>
    (ModuleCat.isZero_iff_subsingleton).2 (homology_subsingleton_of_term _ n
      (kc_disc_X_subsingleton L n hn))
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · apply hzero _ _ _ _ (hdisc (Or.inl hn))
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = Int.negSucc k := ⟨(-n - 1).toNat, by omega⟩
    have hQ : IsZero ((kcQz hFull).homology (Int.negSucc k)) := by
      have := kcQz_X_subsingleton hFull k
      exact ShortComplex.isZero_homology_of_isZero_X₂ _
        ((ModuleCat.isZero_iff_subsingleton).2 this)
    have hι : IsIso (HomologicalComplex.homologyMap ((kcQz hFull).ιTruncLE 1) (Int.negSucc k)) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).1
        (CochainComplex.quasiIsoAt_ιTruncLE _ 1 _ (by omega))
    exact hQ.of_iso (asIso (HomologicalComplex.homologyMap ((kcQz hFull).ιTruncLE 1) _))
  · have := kc_iotaD_quasiIsoAt_zero L
    rw [← quasiIsoAt_iff_comp_right (kcPhi hFull D L hG) (kcIotaD L) 0, kcPhi_comp]
    have : QuasiIsoAt ((kcQz hFull).ιTruncLE 1) 0 :=
      CochainComplex.quasiIsoAt_ιTruncLE _ 1 0 (by norm_num)
    rw [quasiIsoAt_iff_comp_left]
    exact kcPsi_quasiIsoAt_zero hFull D
  · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn'
    · exact kc_quasiIsoAt_of_square _ _ _ _ (kcPhi_comp hFull D L hG) 1
        (kc_psi_H1_injective hFull D) (kc_iotaD_H1_injective L) (kc_psi_H1_range hFull D L hG)
    · apply hzero _ _ _ _ (hdisc (Or.inr hn'))
      exact ShortComplex.isZero_homology_of_isZero_X₂ _
        (CochainComplex.isZero_of_isStrictlyLE ((kcQz hFull).truncLE 1) 1 n (by omega))

end Assembly

end ZInQ.Manuscript.RC
