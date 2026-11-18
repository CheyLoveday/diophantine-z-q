import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeAlternating
import ZInQKernel.Contrib.CloudB3RC53.TameModel.UnramifiedQIso

/-!
# RC53 `hsw` shape: the finite plane is isotropic

The first local-duality input of `hsw_of_localDuality` is that classes in the finite plane `F` are
mutually orthogonal for the residue form. At the switch place the finite side is the unramified
condition (`finite_side_iff`, `finiteSide_BF_iff_ur`). The cup product of two unramified classes
is a coboundary because `Gal(K_q^ur/K_q) ≅ ℤ̂` has cohomological dimension one.

## Results

* `cupFun_infl`, `contCup_infl`: the cup product commutes with inflation along `π : G → H`, with
  compatible module maps, on inhomogeneous and continuous cochains.
* `contCup_eq_d_of_subsingleton`: if `H²_cont(H, T) = 0`, the cup product of two continuous
  `1`-cocycles is a coboundary.
* `infl_cup_coboundary`: the two combined, so `infl a' ∪ infl b' = d c`.
* `resForm_eq_zero_of_cup`: the residue form vanishes at `(t, u)` when `ι u ∪ ι t` is a local
  coboundary.
* `urInfl`, `UrAt`: inflation from `Gal(K_q^ur/K_q)` to `G_{K_q}`, and local `1`-cochains
  unramified at `q` and zero elsewhere. The hypothesis on `ψ` is only that the actions agree,
  which holds for every `ψ` with trivial coefficients (`trivMod_urCompat`).
* `localSumPair_urAt`: the local cup product of two such cochains is a coboundary, using
  `ur_subsingleton_contCohomology_ge_two`.
* `genuine_finIso_of_ur`: the finite plane is isotropic for the genuine residue form, given the
  tie `hUrRep`: every vector of `F` is `eR[g t]` for a relaxed cocycle with `ι t` unramified at
  `q`.
* `genuine_switchCoordinates_char2_ur`: for the genuine switch in characteristic two (polarized
  pairing, e.g. Weil on `𝔽₂²`), with the tie, the only remaining input of `SwitchCoordinates` is
  nondegeneracy of the residue form (local Tate duality).

## The tie

`hUrRep` is supplied at the switch place by the derivative coordinates of the genuine switch
family. There `eRAt` sends a cocycle `z` at `q` (zero elsewhere) to its tame coordinates,
`finite_side_iff` identifies the finite plane with the cocycles vanishing on inertia, and
`finiteSide_BF_iff_ur` writes those cocycles as inflations of unramified cocycles.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open CategoryTheory ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

/-! ### Inflation and the cup product -/

section Infl

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]
  {MH TH MG TG : Type u}
  [AddCommGroup MH] [Module k MH] [DistribMulAction H MH]
  [AddCommGroup TH] [Module k TH] [DistribMulAction H TH]
  [AddCommGroup MG] [Module k MG] [DistribMulAction G MG]
  [AddCommGroup TG] [Module k TG] [DistribMulAction G TG]

omit [DistribMulAction H TH] [DistribMulAction G TG] in
/-- **The cup product commutes with inflation** (`PROVED`), on inhomogeneous cochains: for a
homomorphism `π : G → H`, compatible module maps `fM`, and pairings with
`βG (fM x) (fM y) = fT (βH x y)`, `infl a' ∪ infl b' = infl (a' ∪ b')`. -/
theorem cupFun_infl (π : G →* H) (fM : MH →ₗ[k] MG) (fT : TH →ₗ[k] TG)
    (hfM : ∀ (g : G) (m : MH), fM (π g • m) = g • fM m) (βH : MH →ₗ[k] MH →ₗ[k] TH)
    (βG : MG →ₗ[k] MG →ₗ[k] TG) (hβ : ∀ x y, βG (fM x) (fM y) = fT (βH x y))
    (p q n : ℕ) (h : p + q = n) (a' : (Fin p → H) → MH) (b' : (Fin q → H) → MH) :
    cupFun βG p q n h (fun x => fM (a' (π ∘ x))) (fun x => fM (b' (π ∘ x))) =
      fun x => fT (cupFun βH p q n h a' b' (π ∘ x)) := by
  funext x
  simp only [cupFun]
  rw [← hfM, hβ, map_headProd]
  rfl

end Infl

section InflCont

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  {MH TH MG TG : Type u}
  [AddCommGroup MH] [Module k MH] [DistribMulAction H MH] [SMulCommClass H k MH]
  [TopologicalSpace MH] [ContinuousAdd MH] [ContinuousConstSMul k MH] [ContinuousSMul H MH]
  [AddCommGroup TH] [Module k TH] [DistribMulAction H TH] [SMulCommClass H k TH]
  [TopologicalSpace TH] [ContinuousAdd TH] [ContinuousConstSMul k TH] [ContinuousSMul H TH]
  [AddCommGroup MG] [Module k MG] [DistribMulAction G MG] [SMulCommClass G k MG]
  [TopologicalSpace MG] [ContinuousAdd MG] [ContinuousConstSMul k MG] [ContinuousSMul G MG]
  [AddCommGroup TG] [Module k TG] [DistribMulAction G TG] [SMulCommClass G k TG]
  [TopologicalSpace TG] [ContinuousAdd TG] [ContinuousConstSMul k TG] [ContinuousSMul G TG]
  (π : G →ₜ* H) (fM : MH →ₗ[k] MG) (hfMc : Continuous fM)
  (hfM : ∀ (g : G) (m : MH), fM (π g • m) = g • fM m)
  (fT : TH →ₗ[k] TG) (hfTc : Continuous fT) (hfT : ∀ (g : G) (m : TH), fT (π g • m) = g • fT m)
  (βH : MH →ₗ[k] MH →ₗ[k] TH) (hβHc : Continuous fun x : MH × MH => βH x.1 x.2)
  (βG : MG →ₗ[k] MG →ₗ[k] TG) (hβGc : Continuous fun x : MG × MG => βG x.1 x.2)
  (hβ : ∀ x y, βG (fM x) (fM y) = fT (βH x y))

include hβ in
/-- The cup product commutes with inflation on continuous cochains (`PROVED`). -/
theorem contCup_infl (a' b' : (contCochains k H MH).X 1) :
    contCup βG hβGc 1 1 2 rfl (((contCochainsMap π fM hfMc hfM).f 1).hom a')
        (((contCochainsMap π fM hfMc hfM).f 1).hom b') =
      ((contCochainsMap π fT hfTc hfT).f 2).hom (contCup βH hβHc 1 1 2 rfl a' b') := by
  apply Subtype.ext
  funext x
  exact congrFun (cupFun_infl (π : G →* H) fM fT hfM βH βG hβ 1 1 2 rfl (cFun a') (cFun b')) x

omit [IsTopologicalGroup G] in
/-- **Cohomological dimension one kills cup products** (`PROVED`): if `H²_cont(H, T_H) = 0`, the
cup product of two continuous `1`-cocycles of `H` is a coboundary. -/
theorem contCup_eq_d_of_subsingleton (hβH : ∀ (g : H) (a b : MH), βH (g • a) (g • b) = g • βH a b)
    (hcd : Subsingleton (contCohomology k H TH 2)) (a' b' : (contCochains k H MH).X 1)
    (ha : ((contCochains k H MH).d 1 2).hom a' = 0)
    (hb : ((contCochains k H MH).d 1 2).hom b' = 0) :
    ∃ c' : (contCochains k H TH).X 1,
      contCup βH hβHc 1 1 2 rfl a' b' = ((contCochains k H TH).d 1 2).hom c' := by
  have hy : ((contCochains k H TH).d 2 3).hom (contCup βH hβHc 1 1 2 rfl a' b') = 0 := by
    have hl := (contNatPair βH hβH hβHc).leib 1 1 2 rfl a' b'
    change ((contCochains k H TH).d 2 (2 + 1)).hom (contCup βH hβHc 1 1 2 rfl a' b') =
      contCup βH hβHc (1 + 1) 1 (2 + 1) _ (((contCochains k H MH).d 1 (1 + 1)).hom a') b' +
        ((-1 : ℤ) ^ 1) • contCup βH hβHc 1 (1 + 1) (2 + 1) _ a'
          (((contCochains k H MH).d 1 (1 + 1)).hom b') at hl
    rw [hl]
    change contCup βH hβHc (1 + 1) 1 (2 + 1) _ (((contCochains k H MH).d 1 2).hom a') b' +
        ((-1 : ℤ) ^ 1) • contCup βH hβHc 1 (1 + 1) (2 + 1) _ a'
          (((contCochains k H MH).d 1 2).hom b') = 0
    rw [ha, hb, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]
  have hex : (contCochains k H TH).ExactAt 2 :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _)
  rw [HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨z, hz⟩ := hex _ hy
  exact ⟨z, hz.symm⟩

include hβ hβHc hfTc hfT in
/-- **Inflated cocycles from a group of cohomological dimension one have coboundary cup product**
(`PROVED`): if `H²_cont(H, T_H) = 0`, then `infl a' ∪ infl b' = d c` on `G`. -/
theorem infl_cup_coboundary (hβH : ∀ (g : H) (a b : MH), βH (g • a) (g • b) = g • βH a b)
    (hcd : Subsingleton (contCohomology k H TH 2)) (a' b' : (contCochains k H MH).X 1)
    (ha : ((contCochains k H MH).d 1 2).hom a' = 0)
    (hb : ((contCochains k H MH).d 1 2).hom b' = 0) :
    ∃ c : (contCochains k G TG).X 1,
      contCup βG hβGc 1 1 2 rfl (((contCochainsMap π fM hfMc hfM).f 1).hom a')
          (((contCochainsMap π fM hfMc hfM).f 1).hom b') =
        ((contCochains k G TG).d 1 2).hom c := by
  obtain ⟨c', hc'⟩ := contCup_eq_d_of_subsingleton βH hβHc hβH hcd a' b' ha hb
  refine ⟨((contCochainsMap π fT hfTc hfT).f 1).hom c', ?_⟩
  rw [contCup_infl π fM hfMc hfM fT hfTc hfT βH hβHc βG hβGc hβ, hc']
  exact (congrArg (fun φ => ModuleCat.Hom.hom φ c') ((contCochainsMap π fT hfTc hfT).comm 1 2)).symm

end InflCont

/-! ### The residue form vanishes on coboundary cup products -/

/-- The residue form vanishes at `(t, u)` when `ι u ∪ ι t` is a local coboundary (`PROVED`). -/
theorem resForm_eq_zero_of_cup {k : Type} [Field k] (R : QuasiRelaxedLocalization k)
    (Ustr : GCx k) (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (t u : R.D.U.X 1) (C : Q.EL.X 1)
    (hC : Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl t) = Q.EL.d 1 2 rfl C) :
    resForm R Ustr f Q tr t u = 0 := by
  have l := lhs_eq R.D Ustr f Q tr t u 0
  unfold resForm
  rw [l]
  have h0 : Q.hU 2 1 2 rfl (0 : Ustr.X 2) t = 0 := LinearMap.map_zero₂ _ _
  rw [h0, zero_sub, hC, ← map_neg]
  exact tr_locT_d Q tr htr (-C)

/-! ### Unramified classes at the switch place -/

section Genuine

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k]

/-- The identity between two restricted copies of a module. -/
def resModId {G H H' : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [Group H'] [TopologicalSpace H'] (φ : H →ₜ* G) (φ' : H' →ₜ* G) (N : Type) [AddCommGroup N]
    [Module k N] : ResMod φ N →ₗ[k] ResMod φ' N where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (N : Type) [AddCommGroup N] [Module k N] [DistribMulAction (GKS K S) N]
  [SMulCommClass (GKS K S) k N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul (GKS K S) N]

/-- **Inflation from `Gal(K_q^ur/K_q)`** to `G_{K_q}`, for a homomorphism
`ψ : Gal(K_q^ur/K_q) → G_{K,S}` through which the action of `G_{K_q}` on `N` factors:
`ψ (urRes g) • m = loc_q g • m` (for instance any `ψ` when the action is trivial). -/
abbrev urInfl (q : Places K S) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : N), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m) :
    contCochains k (GUr K q.1) (ResMod ψ N) ⟶
      contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) N) :=
  contCochainsMap (urRes K q.1) (resModId ψ (locMap K S q.1) N) continuous_of_discreteTopology
    (fun g m => hψ g m)

variable {N}

/-- **An unramified class at the switch place `q`**: a local `1`-cochain on `⊕_v C¹(G_v, N)`
supported at `q`, where it is the inflation of a continuous `1`-cocycle of `Gal(K_q^ur/K_q)`. -/
def UrAt (q : Places K S) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : N), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (x : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
      N).X 1) : Prop :=
  (∃ a' : (contCochains k (GUr K q.1) (ResMod ψ N)).X 1,
    ((contCochains k (GUr K q.1) (ResMod ψ N)).d 1 2).hom a' = 0 ∧
      x q = ((urInfl N q ψ hψ).f 1).hom a') ∧ ∀ v, v ≠ q → x v = 0

variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T]

/-- **The local cup product of two unramified classes at `q` is a coboundary** (`PROVED`), by
inflation from `Gal(K_q^ur/K_q) ≅ ℤ̂`, which has cohomological dimension one
(`ur_subsingleton_contCohomology_ge_two`). -/
theorem localSumPair_urAt (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b) (q : Places K S)
    (ψ : GUr K q.1 →ₜ* GKS K S) (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hψT : ∀ g (m : T), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (x y : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
      M).X 1) (hx : UrAt q ψ hψ x) (hy : UrAt q ψ hψ y) :
    ∃ C, (localSumPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
        hβ (continuous_pairing β)).P 1 1 2 rfl x y =
      (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
        T).d 1 2 rfl C := by
  classical
  obtain ⟨⟨a', ha', hxq⟩, hx0⟩ := hx
  obtain ⟨⟨b', hb', hyq⟩, hy0⟩ := hy
  have hcd : Subsingleton (contCohomology k (GUr K q.1) (ResMod ψ T) 2) := by
    let _ : TopologicalSpace k := ⊥
    have : DiscreteTopology k := ⟨rfl⟩
    have := ZInQ.Contrib.CloudB3RC53.ContBridge.continuousSMul_of_discrete k (ResMod ψ T)
    have : Finite (ResMod ψ T) := inferInstanceAs (Finite T)
    exact ZInQ.Contrib.CloudB3RC53.TameModel.ur_subsingleton_contCohomology_ge_two K q.1 k
      (ResMod ψ T) 2 le_rfl
  obtain ⟨c, hc⟩ := infl_cup_coboundary (k := k) (G := Gloc K q.1) (H := GUr K q.1)
    (MH := ResMod ψ M) (TH := ResMod ψ T) (MG := ResMod (locMap K S q.1) M)
    (TG := ResMod (locMap K S q.1) T) (urRes K q.1) (resModId ψ (locMap K S q.1) M)
    continuous_of_discreteTopology (fun g m => hψ g m)
    (resModId ψ (locMap K S q.1) T) continuous_of_discreteTopology (fun g m => hψT g m)
    (resPairing k (GKS K S) β ψ) (resPairing_continuous k (GKS K S) β (continuous_pairing β) ψ)
    (resPairing k (GKS K S) β (locMap K S q.1))
    (resPairing_continuous k (GKS K S) β (continuous_pairing β) (locMap K S q.1))
    (fun _ _ => rfl) (fun h a b => hβ (ψ h) a b) hcd a' b' ha' hb'
  refine ⟨Pi.single q c, ?_⟩
  funext v
  by_cases hv : v = q
  · subst hv
    change (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
        hβ (continuous_pairing β) v).P 1 1 2 rfl (x v) (y v) =
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).d 1 2
        rfl (Pi.single (M := fun v => (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).X 1) v c v)
    rw [hxq, hyq]
    exact hc.trans (congrArg ((contCochains k (Gloc K v.1) (ResMod (locMap K S v.1) T)).d 1 2).hom
      (Pi.single_eq_same (M := fun v => (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).X 1) v c).symm)
  · change (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
        hβ (continuous_pairing β) v).P 1 1 2 rfl (x v) (y v) =
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).d 1 2
        rfl (Pi.single (M := fun v => (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).X 1) q c v)
    rw [hx0 v hv, map_zero, LinearMap.zero_apply]
    exact ((congrArg ((contCochains k (Gloc K v.1) (ResMod (locMap K S v.1) T)).d 1 2).hom
      (Pi.single_eq_of_ne (M := fun v => (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).X 1) hv c)).trans (map_zero _)).symm

/-- **The finite plane is isotropic for the genuine residue form** (`PROVED` from the tie).
Suppose every vector of the finite plane is the class of a relaxed cocycle that is unramified at
the switch place `q` and zero elsewhere (`UrAt`; for the tame switch this is `finite_side_iff`
together with `finiteSide_BF_iff_ur`). Then the residue form vanishes on pairs of classes in the
finite plane. -/
theorem genuine_finIso_of_ur (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) (q : Places K S) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hψT : ∀ g (m : T), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hUrRep : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧ UrAt q ψ hψ (X.toQuasi.D.ι.f 1 1 rfl t)) :
    ∀ t u (ht : X.toQuasi.D.U.d 1 2 rfl t = 0) (hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
      gClass X.toQuasi t ht ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      gClass X.toQuasi u hu ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u =
        0 := by
  intro t u ht hu htF huF
  obtain ⟨P, hP⟩ := exists_residuePairing X.toQuasi (piCx X.US) (piMap X.φ) _ tr X.hfg X.φ_inj
    X.g_surj X.ex htr (genuine_strictOrth X β hβ c hc I tr htr hUS2)
  obtain ⟨t', ht', et, hurt⟩ := hUrRep _ htF
  obtain ⟨u', hu', eu, huru⟩ := hUrRep _ huF
  rw [← residuePairing_gClass X.toQuasi (piCx X.US) (piMap X.φ) _ tr hP t u ht hu, ← et, ← eu,
    residuePairing_gClass X.toQuasi (piCx X.US) (piMap X.φ) _ tr hP t' u' ht' hu']
  obtain ⟨C, hC⟩ := localSumPair_urAt β hβ q ψ hψ hψT _ _ huru hurt
  exact resForm_eq_zero_of_cup X.toQuasi (piCx X.US) (piMap X.φ) _ tr htr t' u' C hC

/-- **`SwitchCoordinates` for the genuine switch in characteristic two from local Tate duality
alone** (`PROVED` from the inputs). Take a polarized equivariant pairing (e.g. the Weil pairing on
trivial `𝔽₂²`), any isotropy data, strict condition complexes vanishing in degree two, and finite
`T`. Assume the tie of the finite plane to the unramified classes at the switch place (`UrAt`
representatives). Then only nondegeneracy of the residue form (local Tate duality) remains. -/
theorem genuine_switchCoordinates_char2_ur (h2 : (2 : k) = 0) (X : GenuineSwitch K S k M)
    (β γ : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hγ : ∀ (g : GKS K S) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1) (q : Places K S)
    (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hψT : ∀ g (m : T), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hUrRep : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧ UrAt q ψ hψ (X.toQuasi.D.ι.f 1 1 rfl t))
    (hnd : ∀ t (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
        resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u =
          0) → gClass X.toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr ε (-(-1)) J :=
  genuine_switchCoordinates_char2 h2 X β γ hβ hγ hpol I tr htr hUS2 hε hJ2
    (genuine_finIso_of_ur X β hβ (-1) (fun x y => by rw [hpol, hpol, neg_one_smul, neg_sub]) I
      tr htr hUS2 q ψ hψ hψT hUrRep) hnd

end Genuine

/-! ### Non-vacuity -/

section NonVacuity

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
  [Field k]

/-- **The action compatibility of `urInfl` holds for every `ψ` with trivial coefficients**
(`PROVED`), e.g. `𝔽₂²` and `μ₂ = 𝔽₂` at an odd place. -/
theorem trivMod_urCompat (V : Type) [AddCommGroup V] (q : Places K S)
    (ψ : GUr K q.1 →ₜ* GKS K S) (g : Gloc K q.1) (m : TrivMod (GKS K S) V) :
    ψ (urRes K q.1 g) • m = locMap K S q.1 g • m := rfl

/-- The zero cochain is unramified at `q` (`PROVED`). -/
theorem urAt_zero {N : Type} [AddCommGroup N] [Module k N] [DistribMulAction (GKS K S) N]
    [SMulCommClass (GKS K S) k N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (GKS K S) N] (q : Places K S) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : N), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m) :
    UrAt q ψ hψ (0 : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) N).X 1) :=
  ⟨⟨0, map_zero _, (map_zero _).symm⟩, fun _ _ => rfl⟩

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.Hsw
