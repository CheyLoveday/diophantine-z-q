import ZInQKernel.Contrib.CloudB3RC53.Hsw.Shape

/-!
# RC53 `hsw` shape: the residue form is alternating in characteristic two

In characteristic two `hsw_of_localDuality` needs the residue form to vanish on the diagonal of
`S`. The cup-one identity with sign `c = −1` gives no information there. This file proves the
diagonal vanishing for the genuine data whenever the pairing is polarized, `β x y = γ x y − γ y x`
with `γ` equivariant. Then `a ∪_β a = a ∪_γ a + a ∪_{γᵗ} a = −d(a ∪₁^γ a)` for a cocycle `a`.

* `dFun_cupOneFun_flip`: the cup-one formula for an arbitrary equivariant pairing,
  `d(a ∪₁ b) = −a ∪_β b − b ∪_{βᵗ} a + X(da, b)` for a cocycle `b`.
* `cupFun_self_eq_neg_dFun`, `contCup_self`, `localSumPair_self`: `a ∪ a` is a coboundary, on
  inhomogeneous cochains, on continuous cochains, and on `⊕_v`.
* `resForm_self_of_sq`, `genuine_resForm_self`: the genuine residue form is alternating.
* `genuine_switchCoordinates_char2`: `SwitchCoordinates` for the genuine switch in characteristic
  two (`σ = 1`). The only remaining inputs are local duality: `F` isotropic and the residue form
  nondegenerate.
* `weil_polarized`: the Weil pairing on `𝔽₂²` (trivial action) is polarized, by
  `γ(x, y) = x₀ y₁`.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

section Fun

variable {k G : Type u} [CommRing k] [Group G]
  {M T : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [AddCommGroup T] [Module k T] [DistribMulAction G T]

/-- **The cup-one formula for an arbitrary equivariant pairing** (`PROVED`): for a `1`-cocycle
`b`, `d(a ∪₁ b) = −a ∪_β b − b ∪_{βᵗ} a + X(da, b)`, where `βᵗ = β.flip`. -/
theorem dFun_cupOneFun_flip (γ : M →ₗ[k] M →ₗ[k] T)
    (hγ : ∀ (g : G) (x y : M), γ (g • x) (g • y) = g • γ x y) (a b : (Fin 1 → G) → M)
    (hb : dFun k 1 b = 0) :
    dFun k 1 (cupOneFun γ a b) = -cupFun γ 1 1 2 rfl a b - cupFun γ.flip 1 1 2 rfl b a +
      x2Fun γ (dFun k 1 a) b := by
  funext g
  have hbg : g 0 • b (fun _ => g 1) - b (fun _ => g 0 * g 1) + b (fun _ => g 0) = 0 := by
    have := congrFun hb g
    rw [dFun_one] at this
    exact this
  have hB : b (fun _ => g 0 * g 1) = g 0 • b (fun _ => g 1) + b (fun _ => g 0) := by
    rw [sub_add_eq_add_sub, sub_eq_zero] at hbg
    exact hbg.symm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, dFun_one, cupFun_one_one_apply, x2Fun,
    cupOneFun, LinearMap.flip_apply]
  rw [hB, ← hγ]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

/-- **`a ∪ a` is a coboundary for a polarized pairing in characteristic two** (`PROVED`): if
`β x y = γ x y − γ y x` with `γ` equivariant and `2 = 0` in `k`, then for a `1`-cocycle `a`,
`a ∪_β a = −d(a ∪₁^γ a)`. -/
theorem cupFun_self_eq_neg_dFun (h2 : (2 : k) = 0) (β γ : M →ₗ[k] M →ₗ[k] T)
    (hγ : ∀ (g : G) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (a : (Fin 1 → G) → M) (ha : dFun k 1 a = 0) :
    cupFun β 1 1 2 rfl a a = -dFun k 1 (cupOneFun γ a a) := by
  rw [dFun_cupOneFun_flip γ hγ a a ha, ha]
  funext g
  have h2T : ∀ z : T, z + z = 0 := fun z => by
    rw [← two_smul k z, h2, zero_smul]
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, cupFun_one_one_apply, x2Fun,
    LinearMap.flip_apply, hpol, Pi.zero_apply, map_zero, LinearMap.zero_apply, add_zero, neg_sub]
  have := h2T ((γ (g 0 • a fun _ => g 1)) (a fun _ => g 0))
  rw [sub_eq_iff_eq_add]
  rw [← sub_eq_zero]
  have e : ∀ X Y : T, X - (Y - -X + Y) = -(Y + Y) := fun X Y => by abel
  rw [e]
  rw [this, neg_zero]

end Fun

/-! ### Continuous cochains and the local sum -/

section Cont

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M T : Type u}
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul G T]

/-- `a ∪ a = −d(a ∪₁^γ a)` on continuous `1`-cocycles (`PROVED`), for a polarized pairing in
characteristic two. -/
theorem contCup_self (h2 : (2 : k) = 0) (β γ : M →ₗ[k] M →ₗ[k] T)
    (hβc : Continuous fun x : M × M => β x.1 x.2) (hγc : Continuous fun x : M × M => γ x.1 x.2)
    (hγ : ∀ (g : G) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (a : (contCochains k G M).X 1)
    (ha : ((contCochains k G M).d 1 2).hom a = 0) :
    contCup β hβc 1 1 2 rfl a a = -((contCochains k G T).d 1 2).hom (contCupOne γ hγc a a) := by
  have ha' : dFun k 1 (cFun a) = 0 := by
    have h := congrArg (fun z : (contCochains k G M).X (1 + 1) =>
      asFun k G M (((contSubCx k G M).el z : contCochain k G M (1 + 1)) :
        (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1))) ha
    simp only at h
    rw [contCochains_d_coe] at h
    exact h
  apply Subtype.ext
  change cupFun β 1 1 2 rfl (cFun a) (cFun a) =
    -((((contSubCx k G T).el (((contCochains k G T).d 1 (1 + 1)).hom
      (contCupOne γ hγc a a))) : contCochain k G T (1 + 1)) :
        (groupCohomology.inhomogeneousCochains (rep k G T)).X (1 + 1))
  rw [contCochains_d_coe]
  exact cupFun_self_eq_neg_dFun h2 β γ hγ hpol (cFun a) ha'

end Cont

section Local

variable {k : Type} [Field k] (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {M T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]

omit [IsTopologicalGroup GS] in
/-- **The genuine local cup square of a cocycle is a coboundary** for a polarized pairing in
characteristic two (`PROVED`). -/
theorem localSumPair_self (h2 : (2 : k) = 0) (β γ : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GS) (a b : M), β (g • a) (g • b) = g • β a b)
    (hβc : Continuous fun x : M × M => β x.1 x.2) (hγc : Continuous fun x : M × M => γ x.1 x.2)
    (hγ : ∀ (g : GS) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (a : (localSumCx k GS Gv loc M).X 1)
    (ha : (localSumCx k GS Gv loc M).d 1 2 rfl a = 0) :
    (localSumPair k GS Gv loc β hβ hβc).P 1 1 2 rfl a a =
      -(localSumCx k GS Gv loc T).d 1 2 rfl (sumCupOne GS Gv loc γ hγc a a) := by
  funext v
  exact contCup_self h2 (resPairing k GS β (loc v)) (resPairing k GS γ (loc v))
    (resPairing_continuous k GS β hβc (loc v)) (resPairing_continuous k GS γ hγc (loc v))
    (fun h x y => hγ (loc v h) x y) hpol (a v) (congrFun ha v)

end Local

/-! ### The genuine switch in characteristic two -/

/-- The residue form vanishes on the diagonal at `t` when `ι t ∪ ι t` is a local coboundary
(`PROVED`). -/
theorem resForm_self_of_sq {k : Type} [Field k] (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (t : R.D.U.X 1) (C : Q.EL.X 1)
    (hC : Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl t) (R.D.ι.f 1 1 rfl t) = -Q.EL.d 1 2 rfl C) :
    resForm R Ustr f Q tr t t = 0 := by
  have l := lhs_eq R.D Ustr f Q tr t t 0
  unfold resForm
  rw [l]
  have h0 : Q.hU 2 1 2 rfl (0 : Ustr.X 2) t = 0 := LinearMap.map_zero₂ _ _
  rw [h0, zero_sub, hC, neg_neg]
  exact tr_locT_d Q tr htr C

section Genuine

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **The genuine residue form is alternating in characteristic two** (`PROVED`) for a polarized
pairing `β x y = γ x y − γ y x` with `γ` equivariant. For example, the Weil pairing on trivial
`𝔽₂²` coefficients, with `γ(x, y) = x₀ y₁`. -/
theorem genuine_resForm_self (h2 : (2 : k) = 0) (X : GenuineSwitch K S k M)
    (β γ : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hγ : ∀ (g : GKS K S) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0) :
    resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t t =
      0 := by
  have hdt : X.toQuasi.D.L.d 1 2 rfl (X.toQuasi.D.ι.f 1 1 rfl t) = 0 := by
    rw [← X.toQuasi.D.ι.comm 1 2 1 2 rfl rfl rfl rfl, ht, map_zero]
  exact resForm_self_of_sq X.toQuasi (piCx X.US) (piMap X.φ) _ tr htr t _
    (localSumPair_self (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) h2 β γ hβ (continuous_pairing β) (continuous_pairing γ) hγ hpol
      (X.toQuasi.D.ι.f 1 1 rfl t) hdt)

/-- **`SwitchCoordinates` for the genuine switch in characteristic two** (`PROVED` from the
inputs). Take a polarized equivariant pairing `β = γ − γᵗ` (so `c = −1` and `σ = 1`), any
isotropy data, and strict condition complexes vanishing in degree two. The only shape inputs left
are local duality: the finite plane is isotropic (unramified classes) and the residue form is
nondegenerate (local Tate duality). -/
theorem genuine_switchCoordinates_char2 (h2 : (2 : k) = 0) (X : GenuineSwitch K S k M)
    (β γ : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hγ : ∀ (g : GKS K S) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (hFiso : ∀ t u (ht : X.toQuasi.D.U.d 1 2 rfl t = 0) (hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
      gClass X.toQuasi t ht ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      gClass X.toQuasi u hu ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u = 0)
    (hnd : ∀ t (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
        resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u =
          0) → gClass X.toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr ε (-(-1)) J :=
  genuine_switchCoordinates_of_localDuality X β hβ (-1)
    (fun x y => by rw [hpol, hpol, neg_one_smul, neg_sub]) I tr htr hUS2 hε hJ2 hFiso hnd
    (Or.inr ⟨rfl, fun t ht _ => genuine_resForm_self h2 X β γ hβ hγ hpol I tr htr t ht⟩)

end Genuine

/-! ### Non-vacuity -/

/-- **The Weil pairing is polarized** (`PROVED`): `e₂(x, y) = γ(x, y) − γ(y, x)` with
`γ(x, y) = x₀ y₁`. This is equivariant for the trivial action on `𝔽₂²` coefficients. -/
theorem weil_polarized {k : Type} [Field k] (x y : Fin 2 → k) :
    weil x y = (LinearMap.mul k k).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1) x y -
      (LinearMap.mul k k).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1) y x := by
  simp [weil_apply]
  ring

end ZInQ.Contrib.CloudB3RC53.Hsw
