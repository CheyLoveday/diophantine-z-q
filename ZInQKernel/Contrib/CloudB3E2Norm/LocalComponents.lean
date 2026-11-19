import ZInQKernel.Contrib.CloudB3E2Norm.GlobalCochain

/-!
# The local components `hU`, `hL` of the norm identity, and the full `hzR`

Manuscript `diophantine_zq.tex`, tex 4157–4170 ("The actual norm identity is `z_R = e_q i(z_P)`,
with its retained boundary"), with the Selmer complex `C = Cone(G ⊕ U → L)[−1]`
(`C^n = G^n ⊕ U^n ⊕ L^{n−1}`, `d(a, u, x) = (da, du, res a − ι u − dx)`). The consumer is lane
RC32's `hzR_of_components` (`RC/Wiring/CommonCoordinate11Genuine.lean`), which needs the global
component `hG` (`GlobalCochain.lean`), the local-condition component
`hU : zR.2.1 = e • f(u_P) + d b_U` and the homotopy component
`hL : zR.2.2 = e • x_P + (res b_G − ι b_U − d b_L)`.

**Strict lifts.** A global cochain `a` whose localization lies exactly in the local condition,
`res a = ι u`, has the Selmer lift `(a, u, 0)` with zero homotopy component (`strictLift`). For the
Kummer classes this is the situation at the old places (the local Kummer condition contains the
localizations of the global Kummer cochains, tex 3262–3270: "the old Kummer conditions … survive
(H20)"; the condition `U¹ = kummerZ ⊔ B¹` contains every cochain cohomologous to a Kummer cocycle)
and at the new place `w` of the relaxed complex, where the condition is the full one (`U_w = L_w`,
`ι_w = id`).

* **`hU_hL_of_strictLifts`** (PROVED, any Selmer data): if `z_R = (a_R, u_R, 0)` and
  `z_P = (a_P, u_P, 0)` are strict lifts (`ι u_R = res a_R`, `ι (f u_P) = res a_P`), `ι` is
  injective in degree one, `a_R = e a_P + d b_G` (`hG`) and `b_U` lifts `res b_G` through `ι` in
  degree zero, then `hU` and `hL` hold with `b_L = 0`; hence (`hzR_of_strictLifts`) the full
  `hzR`: `z_R = e • i(z_P) + d (b_G, b_U, 0)`.
* `addPlace_ι_injective`, `addPlace_ι_surjective` (PROVED): for the relaxed data
  `relaxedAt D res_w` (old conditions and the full condition at `w`), injectivity in degree one and
  degree-zero liftability reduce to the old conditions.
* **`hzR_genuine_of_strictLifts`** (PROVED): at lane RC32's genuine relaxed Selmer data, the full
  `hzR` for strict lifts of the genuine transferred Kummer cochains (`hG` from
  `hG_genuine_of_transfer`).
* Non-vacuity: `nonVacuity_strictLifts`, `nonVacuity_injective`.

**What remains**: (1) that the actual classes are strict lifts of the transferred Kummer cochains:
`res_v a_T ∈ ι_v(U_v¹)` at the old places (the survival of the old Kummer conditions under the
coefficient push, tex 3262–3270) with `u_T` the corresponding local cochains; (2) injectivity of
the old local conditions in degree one (the Kummer conditions are subcomplexes:
`kummerConditionι_injective`) and their degree-zero liftability (`U⁰ = C⁰`); (3) the global
inputs listed in `GlobalCochain.lean`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex

section Generic

variable {S : Type} [CommRing S] (D : SelData S) {U' : GCx S} (f : GHom U' D.U)

/-- **The strict Selmer lift** `(a, u, 0)` of a degree-one global cochain `a` with local
component `u` (zero homotopy component). Kind: definition. -/
def strictLift (a : D.G.X 1) (u : D.U.X 1) : (selCx D).X 1 :=
  ((a, u, 0) : selT D 1)

/-- The strict lift in the primitive Selmer complex (condition `U'`, through `f`). -/
def strictLiftP (a : D.G.X 1) (u : U'.X 1) : (selCx (selRestrict D f)).X 1 :=
  ((a, u, 0) : selT (selRestrict D f) 1)

/-- **`hU` and `hL` for strict lifts** (PROVED). -/
theorem hU_hL_of_strictLifts (aR aP : D.G.X 1) (uR : D.U.X 1) (uP : U'.X 1) (e : S)
    (bG : D.G.X 0) (bU : D.U.X 0)
    (hι : Function.Injective (D.ι.f 1 1 rfl))
    (hR : D.ι.f 1 1 rfl uR = D.res.f 1 1 rfl aR)
    (hP : D.ι.f 1 1 rfl (f.f 1 1 rfl uP) = D.res.f 1 1 rfl aP)
    (hG : aR = e • aP + D.G.d 0 1 rfl bG)
    (hbU : D.ι.f 0 0 rfl bU = D.res.f 0 0 rfl bG) :
    (strictLift D aR uR).2.1 =
        e • f.f 1 1 rfl (primU D f 1 (strictLiftP D f aP uP)) + D.U.d 0 1 rfl bU ∧
      (strictLift D aR uR).2.2 = e • primL D f 1 (strictLiftP D f aP uP) +
        (D.res.f 0 (1 - 1) (by omega) bG - D.ι.f 0 (1 - 1) (by omega) bU -
          D.L.d (0 - 1) (1 - 1) (by omega) 0) := by
  refine ⟨?_, ?_⟩
  · change uR = e • f.f 1 1 rfl uP + D.U.d 0 1 rfl bU
    apply hι
    rw [map_add, map_smul, hR, hP, hG, map_add, map_smul]
    congr 1
    rw [D.res.comm 0 1 0 1 rfl rfl rfl rfl bG, ← hbU, ← D.ι.comm 0 1 0 1 rfl rfl rfl rfl bU]
  · change (0 : D.L.X (1 - 1)) = e • (0 : D.L.X (1 - 1)) +
      (D.res.f 0 (1 - 1) (by omega) bG - D.ι.f 0 (1 - 1) (by omega) bU -
        D.L.d (0 - 1) (1 - 1) (by omega) 0)
    rw [smul_zero, zero_add, map_zero, sub_zero]
    exact (sub_eq_zero.mpr hbU.symm).symm

/-- **The full norm identity `hzR` for strict lifts** (PROVED): `z_R = e • i(z_P) + d b` with
`b = (b_G, b_U, 0)`. -/
theorem hzR_of_strictLifts (aR aP : D.G.X 1) (uR : D.U.X 1) (uP : U'.X 1) (e : S)
    (bG : D.G.X 0) (bU : D.U.X 0)
    (hι : Function.Injective (D.ι.f 1 1 rfl))
    (hR : D.ι.f 1 1 rfl uR = D.res.f 1 1 rfl aR)
    (hP : D.ι.f 1 1 rfl (f.f 1 1 rfl uP) = D.res.f 1 1 rfl aP)
    (hG : aR = e • aP + D.G.d 0 1 rfl bG)
    (hbU : D.ι.f 0 0 rfl bU = D.res.f 0 0 rfl bG) :
    strictLift D aR uR = e • (changeMap D f).f 1 1 rfl (strictLiftP D f aP uP) +
      (selCx D).d 0 1 rfl ((bG, bU, 0) : selT D 0) := by
  obtain ⟨hU, hL⟩ := hU_hL_of_strictLifts D f aR aP uR uP e bG bU hι hR hP hG hbU
  exact hzR_of_components D f (strictLift D aR uR) (strictLiftP D f aP uP) e bG bU 0 hG hU hL

end Generic

section AddPlace

variable {S : Type} [CommRing S] (D : SelData S) {Lq : GCx S} (resq : GHom D.G Lq)

/-- **Injectivity of the relaxed local conditions in degree one** (PROVED): it reduces to the
old conditions (the condition at the new place is the identity). -/
theorem addPlace_ι_injective (hι : Function.Injective (D.ι.f 1 1 rfl)) :
    Function.Injective ((relaxedAt D resq).ι.f 1 1 rfl) := by
  rintro ⟨u, y⟩ ⟨u', y'⟩ h
  have h' : ((D.ι.f 1 1 rfl u, y) : D.L.X 1 × Lq.X 1) = (D.ι.f 1 1 rfl u', y') := h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hu, rfl⟩ := h'
  rw [hι hu]

/-- **Degree-zero liftability for the relaxed local conditions** (PROVED): it reduces to the old
conditions. -/
theorem addPlace_ι_surjective (hs : ∀ y : D.L.X 0, ∃ x : D.U.X 0, D.ι.f 0 0 rfl x = y)
    (y : (relaxedAt D resq).L.X 0) :
    ∃ x : (relaxedAt D resq).U.X 0, (relaxedAt D resq).ι.f 0 0 rfl x = y := by
  obtain ⟨y₁, y₂⟩ := y
  obtain ⟨x₁, hx₁⟩ := hs y₁
  exact ⟨((x₁, y₂) : D.U.X 0 × Lq.X 0), Prod.ext hx₁ rfl⟩

end AddPlace

/-! ### At the genuine relaxed Selmer data -/

section GenuineTriangle

open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {D : Type} [AddCommGroup D] [Module k D] (ρ : GKS K S →* Module.End k D)
  (HP HR : Subgroup (GKS K S)) [HP.Normal] [HR.Normal] [Fintype (GKS K S ⧸ HP)]
  [Fintype (GKS K S ⧸ HR)]
  (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
  (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
  (θP : GKS K S ⧸ HP →* kˣ) (θR : GKS K S ⧸ HR →* kˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

set_option linter.unusedSectionVars false

include hrP hrR hU ht in
/-- **The full norm identity `hzR` at lane RC32's genuine relaxed Selmer data** (PROVED; tex
4157–4170 at a finite coefficient stage): for strict lifts `z_R = (a_R, u_R, 0)`,
`z_P = (a_P, u_P, 0)` of genuine global cochains `a_R`, `a_P` carried by `ι` to the transferred
Kummer cocycles (`hzR`, `hzP`), with the old local conditions injective in degree one and
liftable in degree zero, `z_R = e_q • i(z_P) + d b` for some `b`. -/
theorem hzR_genuine_of_strictLifts
    (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) M) (w : Places K S) {U' : GCx k}
    (f : GHom U' (genuineRelaxed K S₀ S k M Δ w).U)
    (aR aP : (globalCx k (GKS K S) M).X 1)
    (uR : (genuineRelaxed K S₀ S k M Δ w).U.X 1) (uP : U'.X 1)
    (hιold : Function.Injective ((genuineOld K S₀ S k M Δ).ι.f 1 1 rfl))
    (hsold : ∀ y : (genuineOld K S₀ S k M Δ).L.X 0,
      ∃ x : (genuineOld K S₀ S k M Δ).U.X 0, (genuineOld K S₀ S k M Δ).ι.f 0 0 rfl x = y)
    (hRloc : (genuineRelaxed K S₀ S k M Δ w).ι.f 1 1 rfl uR =
      (genuineRelaxed K S₀ S k M Δ w).res.f 1 1 rfl aR)
    (hPloc : (genuineRelaxed K S₀ S k M Δ w).ι.f 1 1 rfl (f.f 1 1 rfl uP) =
      (genuineRelaxed K S₀ S k M Δ w).res.f 1 1 rfl aP)
    (hle : HR ≤ HP)
    (hθ : ∀ x : GKS K S, ((θR (x : GKS K S ⧸ HR) : kˣ) : k) = θP (x : GKS K S ⧸ HP))
    (kk a : ℤ) (σ : GKS K S) {yR yP QR QP : D}
    (hQR : kk • QR = yR) (hQP : kk • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : GKS K S) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP)
    (ι : M →ₗ[k] D) (hι : Function.Injective ι)
    (hιeq : ∀ (g : GKS K S) (m : M), ι (g • m) = R HR ρ θR g (ι m))
    (htors : ∀ x : D, kk • x = 0 → ∃ m : M, ι m = x)
    (hzR : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aR g) = T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g)
    (hzP : ∀ g : Fin 1 → GKS K S,
      ι (gval (A := k) (M := M) aP g) = T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g) :
    ∃ b : (selCx (genuineRelaxed K S₀ S k M Δ w)).X 0,
      strictLift (genuineRelaxed K S₀ S k M Δ w) aR uR =
        eq_ HP θP a σ • (changeMap (genuineRelaxed K S₀ S k M Δ w) f).f 1 1 rfl
          (strictLiftP (genuineRelaxed K S₀ S k M Δ w) f aP uP) +
        (selCx (genuineRelaxed K S₀ S k M Δ w)).d 0 1 rfl b := by
  obtain ⟨bG, hG⟩ := hG_of_transfer ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ kk a σ hQR hQP
    hfixR hfixP hnorm ι hι hιeq htors aR aP hzR hzP
  obtain ⟨bU, hbU⟩ := addPlace_ι_surjective (genuineOld K S₀ S k M Δ) (genuineRes K S k M w)
    hsold ((genuineRelaxed K S₀ S k M Δ w).res.f 0 0 rfl bG)
  exact ⟨_, hzR_of_strictLifts (genuineRelaxed K S₀ S k M Δ w) f aR aP uR uP _ bG bU
    (addPlace_ι_injective (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) hιold) hRloc hPloc
    hG hbU⟩

end GenuineTriangle

/-! ### Non-vacuity -/

/-- **Non-vacuity of the equational hypotheses of `hU_hL_of_strictLifts`**: for any Selmer data,
the zero cochains with `b_G = b_U = 0` (injectivity: `nonVacuity_injective`). -/
theorem nonVacuity_strictLifts {S : Type} [CommRing S] (D : SelData S) {U' : GCx S}
    (f : GHom U' D.U) (e : S) :
    D.ι.f 1 1 rfl 0 = D.res.f 1 1 rfl 0 ∧ D.ι.f 1 1 rfl (f.f 1 1 rfl 0) = D.res.f 1 1 rfl 0 ∧
      (0 : D.G.X 1) = e • (0 : D.G.X 1) + D.G.d 0 1 rfl 0 ∧
      D.ι.f 0 0 rfl 0 = D.res.f 0 0 rfl 0 := by
  simp

/-- **Non-vacuity of the injectivity hypothesis**: the Selmer data with the full condition
`L --id--> L` (the condition at the new place of the relaxed data) have injective local
condition in degree one. -/
theorem nonVacuity_injective {S : Type} [CommRing S] (G L : GCx S) (res : GHom G L) :
    Function.Injective ((⟨G, L, L, res, idGHom L⟩ : SelData S).ι.f 1 1 rfl) :=
  fun _ _ h => h

end ZInQ.Contrib.CloudB3E2.NormCochain
