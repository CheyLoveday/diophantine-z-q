import ZInQKernel.Contrib.RC53Assist.Calibration.KummerIntegral
import ZInQKernel.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge

/-!
# The degree-zero disk order of the calibration, proved for the actual rational torsion

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141); its proof
(tex 4007–4010): for the compact Kummer complex `C_K` of the central twist `E^{(h)}/K`,
`H¹(C_K)_tors = E^{(h)}(K)[2^∞]` (also tex 5284–5291: `H⁰(C_K) = 0` and the degree-zero Kummer
identifications). At finite level `i` this is the statement that `H⁰` of the genuine finite
central Kummer Selmer complex is `(E^{(h)}(K)[2^i])^i`. This file proves it, and with it the field
`arith0` of `DiskArith` for the actual order of the rational `2`-primary torsion.

* `card_selH0`: for any Selmer cone whose local conditions contain all local `0`-cochains and are
  injective in degree one (zero in degree `−1`), `|H⁰(C_f)| = |M^{G_S}|` (Nekovář 6.1.3).
* `card_selH_zero`: the actual Kummer conditions of the finite central Selmer data satisfy these
  hypotheses (`U⁰ = C⁰`, `U¹ = Kummer cocycles + B¹`), so `|H⁰| = |M_i^{G_{K,S}}|`.
* `coordEquiv`, `card_rightInvariants`: `(ℤ/n)^ι ⊗_ℤ T ≅ T^ι` naturally, so the invariants of
  `(ℤ/n)^ι ⊗ T` are `(T^Γ)^ι`.
* `finiteCentralTensorEquiv_galois`, `card_central_invariants`: the twist identification
  `A_i ⊗ E^{(h)}(K_S)[2^i] ≅ M_i = (E[2^i] ⊗ A_i)(χ_h)` is Galois equivariant, and since `A_i` is
  free of rank `i` over `ℤ/2^i`, `|M_i^{G}| = |E^{(h)}(K_S)[2^i]^{G}|^i`.
* `card_lev_invariants`: Galois descent, `E^{(h)}(K_S)[2^i]^{G_{K,S}} = E^{(h)}(K)[2^i]`.
* `card_primaryComponent_two`, `torsionBy_eq_primaryComponent`: a finite `2`-primary component
  has order `2^a`, and equals the `2^i`-torsion for `i ≥ a`.
* `MordellWeilNumberFieldPrint` (PRINT, Silverman, AEC, 2nd ed., Theorem VIII.6.7), and
  `finite_central_torsion`: the rational `2`-primary torsion of the central twist is finite.
* **`arith0_central`**: for all large `i`, `|H⁰| = 2^{i v₂ t}`, `t` the order of the rational
  `2`-primary torsion of `E^{(h)}/K` (the field `arith0` of `DiskArith`, for `tA = t`).

* `arith0_of_mordellWeil`: the same from `MordellWeilNumberFieldPrint` alone.

Kinds: definitions, PROVED; the one PRINT is `MordellWeilNumberFieldPrint` (only through
`finite_central_torsion` and `arith0_of_mordellWeil`); `arith0_central` itself assumes
finiteness of the rational `2`-primary torsion as an instance argument.
-/


noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open scoped TensorProduct

section RawH0

variable {R : Type} [CommRing R]

/-- Cohomology in degree `n` is cycles modulo boundaries, with the displayed differentials.
Kind: definition. -/
def rawHomologyEquiv (C : GCx R) (i n j : ℤ) (hi : i + 1 = n) (hj : n + 1 = j) :
    C.toCC.homology n ≃ₗ[R]
      ZInQ.Contrib.RC53Assist.InnerLimitArith.subquot (LinearMap.range (C.d i n hi))
        (LinearMap.ker (C.d n j hj)) := by
  let e := ZInQ.Contrib.RC53Assist.Finiteness.gcxHomologyEquiv C i n j hi hj
  rw [ZInQ.Contrib.RC53Assist.Finiteness.sc'_f_hom C i n j hi,
    ZInQ.Contrib.RC53Assist.Finiteness.sc'_g_hom C i n j hj] at e
  exact e

/-- With a zero term in degree `−1`, the order of `H⁰` is the order of the `0`-cocycles.
Kind: PROVED. -/
theorem card_homology_zero (C : GCx R) (h : Subsingleton (C.X (-1))) :
    Nat.card (C.toCC.homology 0) = Nat.card (LinearMap.ker (C.d 0 1 rfl)) := by
  rw [Nat.card_congr (rawHomologyEquiv C (-1) 0 1 (by norm_num) rfl).toEquiv]
  have hB : (LinearMap.range (C.d (-1) 0 (by norm_num))).comap
      (LinearMap.ker (C.d 0 1 rfl)).subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hy0 : y = 0 := Subsingleton.elim _ _
    rw [hy0, map_zero] at hy
    exact (Submodule.mem_bot R).2 (Subtype.ext hy.symm)
  exact Nat.card_congr (Submodule.quotEquivOfEqBot _ hB).toEquiv

end RawH0

section SelmerH0

variable {k : Type} [CommRing k] {GS : Type} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- The `0`-cocycles of a Selmer cone, projected to the global `0`-cochains. Kind: definition. -/
def selZ0ToGlobal (Δ : LocalConditions k GS Gv loc M) :
    LinearMap.ker ((selCx (selData k GS Gv loc M Δ)).d 0 1 rfl) →ₗ[k]
      LinearMap.ker ((globalCx k GS M).d 0 1 rfl) where
  toFun c := ⟨c.1.1, by
    have hc : (selCx (selData k GS Gv loc M Δ)).d 0 1 rfl c.1 = 0 := c.2
    exact LinearMap.mem_ker.2 (congrArg Prod.fst hc)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The `0`-cocycles of the Selmer cone are the global `0`-cocycles** when every local
condition is all of the local `0`-cochains and injective in degree one (Nekovář 6.1.3: the cone
has `H⁰(C_f) = H⁰(G_S, M)` for such conditions). Kind: PROVED. -/
theorem selZ0ToGlobal_bijective (Δ : LocalConditions k GS Gv loc M)
    (h0 : ∀ v, Function.Bijective ((Δ.i v).f 0 0 rfl))
    (h1 : ∀ v, Function.Injective ((Δ.i v).f 1 1 rfl)) :
    Function.Bijective (selZ0ToGlobal Δ) := by
  have hL : Subsingleton ((selData k GS Gv loc M Δ).L.X (0 - 1)) := by
    change Subsingleton (∀ v : ι, PUnit.{1})
    infer_instance
  constructor
  · intro c c' h
    obtain ⟨⟨a, u, x⟩, hc⟩ := c
    obtain ⟨⟨a', u', x'⟩, hc'⟩ := c'
    have ha : a = a' := congrArg Subtype.val h
    subst ha
    have hx : x = x' := Subsingleton.elim _ _
    subst hx
    have hc0 : (selCx (selData k GS Gv loc M Δ)).d 0 1 rfl (a, u, x) = 0 := hc
    have hc0' : (selCx (selData k GS Gv loc M Δ)).d 0 1 rfl (a, u', x) = 0 := hc'
    have h3 := congrArg (fun z : selT (selData k GS Gv loc M Δ) 1 => z.2.2) hc0
    have h3' := congrArg (fun z : selT (selData k GS Gv loc M Δ) 1 => z.2.2) hc0'
    have hu : u = u' := by
      funext v
      apply (h0 v).1
      have e1 := congrFun h3 v
      have e2 := congrFun h3' v
      change (resS k GS Gv loc M).f 0 0 rfl a v - (Δ.i v).f 0 0 rfl (u v) -
        (localSumCx k GS Gv loc M).d (-1) 0 (by norm_num) x v = 0 at e1
      change (resS k GS Gv loc M).f 0 0 rfl a v - (Δ.i v).f 0 0 rfl (u' v) -
        (localSumCx k GS Gv loc M).d (-1) 0 (by norm_num) x v = 0 at e2
      have := e1.trans e2.symm
      rw [sub_left_inj, sub_right_inj] at this
      exact this
    subst hu
    rfl
  · rintro ⟨a, ha⟩
    have ha' : (globalCx k GS M).d 0 1 rfl a = 0 := LinearMap.mem_ker.1 ha
    let u : (piCx Δ.U).X 0 := fun v =>
      Function.surjInv (h0 v).2 ((resS k GS Gv loc M).f 0 0 rfl a v)
    have hu (v : ι) : (Δ.i v).f 0 0 rfl (u v) = (resS k GS Gv loc M).f 0 0 rfl a v :=
      Function.surjInv_eq (h0 v).2 _
    let x : (localSumCx k GS Gv loc M).X (0 - 1) := 0
    let c : (selCx (selData k GS Gv loc M Δ)).X 0 := (a, u, x)
    have hc : (selCx (selData k GS Gv loc M Δ)).d 0 1 rfl c = 0 := by
      refine Prod.ext ha' (Prod.ext ?_ ?_)
      · funext v
        apply h1 v
        have e1 := (Δ.i v).comm 0 1 0 1 rfl rfl rfl rfl (u v)
        have e2 := (resS k GS Gv loc M).comm 0 1 0 1 rfl rfl rfl rfl a
        change (Δ.i v).f 1 1 rfl ((Δ.U v).d 0 1 rfl (u v)) = (Δ.i v).f 1 1 rfl 0
        rw [e1, hu v, map_zero]
        have e3 := congrFun e2 v
        change (resS k GS Gv loc M).f 1 1 rfl ((globalCx k GS M).d 0 1 rfl a) v =
          (localCx k GS Gv loc M v).d 0 1 rfl ((resS k GS Gv loc M).f 0 0 rfl a v) at e3
        rw [← e3, ha', map_zero]
        rfl
      · funext v
        change (resS k GS Gv loc M).f 0 0 rfl a v - (Δ.i v).f 0 0 rfl (u v) -
          (localSumCx k GS Gv loc M).d (-1) 0 (by norm_num) x v = 0
        rw [hu v, sub_self, zero_sub, neg_eq_zero]
        have : x = 0 := rfl
        rw [this, map_zero]
        rfl
    exact ⟨⟨c, LinearMap.mem_ker.2 hc⟩, rfl⟩

/-- The global `0`-cocycles are the invariants. Kind: definition. -/
def globalZ0Equiv :
    LinearMap.ker ((globalCx k GS M).d 0 1 rfl) ≃ₗ[k] invariantsSub k GS M where
  toFun c := ⟨cfun (c.1 : contCochain k GS M 0) default,
    (contD_zero_eq_zero_iff _).1 (LinearMap.mem_ker.1 c.2)⟩
  invFun m := ⟨constCochain m.1, LinearMap.mem_ker.2
    ((contD_zero_eq_zero_iff (constCochain (k := k) (G := GS) m.1)).2 (fun g => m.2 g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := by
    apply Subtype.ext
    exact (eq_constCochain (c.1 : contCochain k GS M 0)).symm
  right_inv m := rfl

/-- **`H⁰` of a Selmer cone is `H⁰(G_S, M)`** for local conditions that are all of the local
`0`-cochains and injective in degree one, with zero terms in degree `−1`. Kind: PROVED. -/
theorem card_selH0 (Δ : LocalConditions k GS Gv loc M)
    (hneg : ∀ v, Subsingleton ((Δ.U v).X (-1)))
    (h0 : ∀ v, Function.Bijective ((Δ.i v).f 0 0 rfl))
    (h1 : ∀ v, Function.Injective ((Δ.i v).f 1 1 rfl)) :
    Nat.card ((selCx (selData k GS Gv loc M Δ)).toCC.homology 0) =
      Nat.card (invariantsSub k GS M) := by
  have hX : Subsingleton ((selCx (selData k GS Gv loc M Δ)).X (-1)) := by
    have hG : Subsingleton ((globalCx k GS M).X (-1)) := by
      change Subsingleton PUnit.{1}
      infer_instance
    have hU : Subsingleton ((piCx Δ.U).X (-1)) := by
      change Subsingleton (∀ v, (Δ.U v).X (-1))
      exact @Pi.instSubsingleton _ _ hneg
    have hL : Subsingleton ((localSumCx k GS Gv loc M).X (-1 - 1)) := by
      change Subsingleton (∀ v : ι, PUnit.{1})
      infer_instance
    change Subsingleton ((globalCx k GS M).X (-1) × (piCx Δ.U).X (-1) ×
      (localSumCx k GS Gv loc M).X (-1 - 1))
    infer_instance
  rw [card_homology_zero _ hX,
    Nat.card_congr (Equiv.ofBijective _ (selZ0ToGlobal_bijective Δ h0 h1)),
    Nat.card_congr (globalZ0Equiv (k := k) (GS := GS) (M := M)).toEquiv]

end SelmerH0


section Coordinates

variable {n : ℕ} [NeZero n] {ι : Type} [Fintype ι] [DecidableEq ι]
  {T : Type} [AddCommGroup T] [Module (ZMod n) T]

/-- A `ZMod n`-scalar acts through its representative in `ℕ`. Kind: PROVED. -/
theorem zmod_smul_eq_val {X : Type} [AddCommGroup X] [Module (ZMod n) X] (z : ZMod n) (x : X) :
    z • x = z.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact Nat.cast_smul_eq_nsmul (ZMod n) z.val x

/-- The coordinate pairing `(f, t) ↦ (f_j • t)_j`. Kind: definition. -/
def coordBilin : (ι → ZMod n) →ₗ[ℤ] T →ₗ[ℤ] (ι → T) :=
  LinearMap.mk₂ ℤ (fun f t j => f j • t)
    (fun f f' t => by funext j; exact add_smul _ _ _)
    (fun c f t => by
      funext j
      change (c • f j) • t = c • (f j • t)
      exact smul_assoc c (f j) t)
    (fun f t t' => by funext j; exact smul_add _ _ _)
    (fun c f t => by funext j; exact smul_comm _ _ _)

/-- **Coordinates of `(ℤ/n)^ι ⊗_ℤ T`** for a `ℤ/n`-module `T`: `(ℤ/n)^ι ⊗ T ≅ T^ι`.
Kind: definition. -/
def coordEquiv : (ι → ZMod n) ⊗[ℤ] T ≃+ (ι → T) where
  toFun := TensorProduct.lift (coordBilin (n := n) (ι := ι) (T := T))
  invFun g := ∑ j, (Pi.single j 1 : ι → ZMod n) ⊗ₜ g j
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul f t =>
      rw [TensorProduct.lift.tmul]
      change ∑ j, (Pi.single j 1 : ι → ZMod n) ⊗ₜ (f j • t) = f ⊗ₜ t
      have hf : f = ∑ j, f j • (Pi.single j 1 : ι → ZMod n) := by
        funext m
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hf]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zmod_smul_eq_val, zmod_smul_eq_val, ← natCast_zsmul, ← natCast_zsmul,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      rw [map_add]
      simp only [Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) hx hy
  right_inv g := by
    funext m
    rw [map_sum]
    simp only [TensorProduct.lift.tmul]
    change (∑ j, (fun j' => (Pi.single j 1 : ι → ZMod n) j' • g j)) m = g m
    simp [Finset.sum_apply, Pi.single_apply]
  map_add' := map_add _

/-- The coordinates of a pure tensor. Kind: PROVED. -/
theorem coordEquiv_tmul (f : ι → ZMod n) (t : T) (j : ι) :
    coordEquiv (f ⊗ₜ t) j = f j • t := rfl

/-- The coordinates are natural for additive maps of `T`. Kind: PROVED. -/
theorem coordEquiv_lTensor (φ : T →+ T) (x : (ι → ZMod n) ⊗[ℤ] T) (j : ι) :
    coordEquiv (LinearMap.lTensor (ι → ZMod n) φ.toIntLinearMap x) j = φ (coordEquiv x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul f t =>
    rw [LinearMap.lTensor_tmul, coordEquiv_tmul, coordEquiv_tmul, zmod_smul_eq_val,
      zmod_smul_eq_val]
    exact (map_nsmul φ _ t).symm
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply]
    exact (map_add φ _ _).symm

end Coordinates

section InvariantCount

variable {n : ℕ} [NeZero n] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Γ : Type} [Group Γ] {T : Type} [AddCommGroup T] [DistribMulAction Γ T]

/-- `σ` acting on the right factor of `(ℤ/n)^ι ⊗ T`. Kind: definition. -/
abbrev rightAct (σ : Γ) : (ι → ZMod n) ⊗[ℤ] T →ₗ[ℤ] (ι → ZMod n) ⊗[ℤ] T :=
  LinearMap.lTensor (ι → ZMod n) (DistribSMul.toAddMonoidHom T σ).toIntLinearMap

/-- **Invariants of `(ℤ/n)^ι ⊗ T`, with `Γ` acting on `T`, are `(T^Γ)^ι`.** Kind: PROVED. -/
theorem card_rightInvariants [Module (ZMod n) T] :
    Nat.card {x : (ι → ZMod n) ⊗[ℤ] T // ∀ σ : Γ, rightAct σ x = x} =
      Nat.card {t : T // ∀ σ : Γ, σ • t = t} ^ Fintype.card ι := by
  let e : {x : (ι → ZMod n) ⊗[ℤ] T // ∀ σ : Γ, rightAct σ x = x} ≃
      (ι → {t : T // ∀ σ : Γ, σ • t = t}) :=
    { toFun := fun x j => ⟨coordEquiv x.1 j, fun σ => by
        have h : coordEquiv (LinearMap.lTensor (ι → ZMod n)
            (DistribSMul.toAddMonoidHom T σ).toIntLinearMap x.1) j = coordEquiv x.1 j :=
          congrArg (fun y => coordEquiv y j) (x.2 σ)
        rw [coordEquiv_lTensor] at h
        exact h⟩
      invFun := fun f => ⟨coordEquiv.symm (fun j => (f j).1), fun σ => by
        apply coordEquiv.injective
        funext j
        change coordEquiv (LinearMap.lTensor (ι → ZMod n)
            (DistribSMul.toAddMonoidHom T σ).toIntLinearMap
              (coordEquiv.symm (fun j => (f j).1))) j = _
        rw [coordEquiv_lTensor, AddEquiv.apply_symm_apply]
        exact (f j).2 σ⟩
      left_inv := fun x => Subtype.ext (coordEquiv.symm_apply_apply x.1)
      right_inv := fun f => by
        funext j
        apply Subtype.ext
        change coordEquiv (coordEquiv.symm (fun j => (f j).1)) j = (f j).1
        rw [AddEquiv.apply_symm_apply] }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ]

end InvariantCount

section CentralInvariants

open Polynomial
open ZInQ.Contrib.RC53Assist.CalibrationShape

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The Galois action on the right factor of `A_i ⊗ E^{(h)}(K_S)[2^i]`. Kind: definition. -/
abbrev tensorAct (G : GenuineKummerData K E₀ hZ) (i : ℕ) (σ : GKS K G.S) :
    Acoef i ⊗[ℤ] Lev K G.S (centralCurve G) i →ₗ[ℤ] Acoef i ⊗[ℤ] Lev K G.S (centralCurve G) i :=
  LinearMap.lTensor (Acoef i)
    (DistribSMul.toAddMonoidHom (Lev K G.S (centralCurve G) i) σ).toIntLinearMap

/-- The finite central module read in the coefficient module over `G_{K,S}` (the identity).
Kind: definition. -/
def toMcoef (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    finiteCentralModule G i →ₗ[Acoef i] Mcoef K G.S G.W i (centralChar i G.s G.hs G.hs0) :=
  LinearMap.id

/-- The identity reading is injective. Kind: PROVED. -/
theorem toMcoef_injective (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Function.Injective (toMcoef G i) := fun _ _ h => h

/-- Inflation along the identity of the support does not change the action. Kind: PROVED. -/
theorem toMcoef_smul (G : GenuineKummerData K E₀ hZ) (i : ℕ) (σ : GKS K G.S)
    (x : finiteCentralModule G i) : toMcoef G i (σ • x) = σ • toMcoef G i x := by
  change inflMap K (subset_refl G.S) σ • toMcoef G i x = σ • toMcoef G i x
  rw [inflMap_self]

/-- The twist identification `A_i ⊗ E^{(h)}[2^i] ≅ M_i` is Galois equivariant.
Kind: PROVED. -/
theorem finiteCentralTensorEquiv_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K G.S) (x : Acoef i ⊗[ℤ] Lev K G.S (centralCurve G) i) :
    finiteCentralTensorEquiv G i (tensorAct G i σ x) = σ • finiteCentralTensorEquiv G i x := by
  induction x using TensorProduct.inductionOn with
  | tmul a P =>
    let φ := globalTwistTorsEquiv G.W G.s G.hs G.hs0 i
    let o := oneTmul (Acoef i) (centralChar i G.s G.hs G.hs0) (TorsS K G.S G.W ((2 ^ i : ℕ) : ℤ))
    have e1 : ∀ Q : Lev K G.S (centralCurve G) i,
        toMcoef G i (finiteCentralTensorEquiv G i (a ⊗ₜ[ℤ] Q)) = a • o (φ Q) := by
      intro Q
      change a ⊗ₜ[ℤ] φ Q = a • ((1 : Acoef i) ⊗ₜ[ℤ] φ Q)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    apply toMcoef_injective
    change toMcoef G i (finiteCentralTensorEquiv G i (a ⊗ₜ[ℤ] (σ • P))) = _
    rw [toMcoef_smul, e1, e1, smul_comm σ a]
    congr 1
    change o (φ (σ • P)) = σ • o (φ P)
    rw [globalTwistTorsEquiv_galois, map_zsmul]
    exact (smul_oneTmul (Acoef i) (centralChar i G.s G.hs G.hs0) _ σ _
      (quadChar G.s G.hs G.hs0 σ) (centralChar_apply G i σ)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

/-- **The Galois invariants of the finite central coefficient module** `M_i = (E[2^i] ⊗ A_i)(χ_h)`
are `(E^{(h)}(K_S)[2^i]^{G_{K,S}})^i`. Kind: PROVED. -/
theorem card_central_invariants (G : GenuineKummerData K E₀ hZ) (i : ℕ) (hi : i ≠ 0) :
    Nat.card (invariantsSub (Acoef i) (GKS K G.S) (finiteCentralModule G i)) =
      Nat.card {P : Lev K G.S (centralCurve G) i // ∀ σ : GKS K G.S, σ • P = P} ^ i := by
  classical
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := ZMod (2 ^ i)) i)
  have hdim : pb.dim = i := by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow]
  let eA : Acoef i ≃ₗ[ℤ] (Fin pb.dim → ZMod (2 ^ i)) :=
    pb.basis.equivFun.toAddEquiv.toIntLinearEquiv
  let _ : Module (ZMod (2 ^ i)) (Lev K G.S (centralCurve G) i) :=
    AddCommGroup.zmodModule (fun P => two_pow_nsmul_lev' P)
  let L := Lev K G.S (centralCurve G) i
  let eT : Acoef i ⊗[ℤ] L ≃ₗ[ℤ] (Fin pb.dim → ZMod (2 ^ i)) ⊗[ℤ] L :=
    TensorProduct.congr eA (LinearEquiv.refl ℤ L)
  have heT : ∀ (σ : GKS K G.S) (x : Acoef i ⊗[ℤ] L),
      eT (tensorAct G i σ x) = rightAct (n := 2 ^ i) σ (eT x) := by
    intro σ x
    induction x using TensorProduct.inductionOn with
    | tmul a P => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  let e1 : invariantsSub (Acoef i) (GKS K G.S) (finiteCentralModule G i) ≃
      {x : Acoef i ⊗[ℤ] L // ∀ σ : GKS K G.S, tensorAct G i σ x = x} :=
    { toFun := fun m => ⟨(finiteCentralTensorEquiv G i).symm m.1, fun σ => by
        apply (finiteCentralTensorEquiv G i).injective
        rw [finiteCentralTensorEquiv_galois, LinearEquiv.apply_symm_apply]
        exact m.2 σ⟩
      invFun := fun x => ⟨finiteCentralTensorEquiv G i x.1, fun σ => by
        rw [← finiteCentralTensorEquiv_galois, x.2 σ]⟩
      left_inv := fun m => Subtype.ext (LinearEquiv.apply_symm_apply _ m.1)
      right_inv := fun x => Subtype.ext (LinearEquiv.symm_apply_apply _ x.1) }
  let e2 : {x : Acoef i ⊗[ℤ] L // ∀ σ : GKS K G.S, tensorAct G i σ x = x} ≃
      {y : (Fin pb.dim → ZMod (2 ^ i)) ⊗[ℤ] L //
        ∀ σ : GKS K G.S, rightAct (n := 2 ^ i) σ y = y} :=
    { toFun := fun x => ⟨eT x.1, fun σ => by rw [← heT, x.2 σ]⟩
      invFun := fun y => ⟨eT.symm y.1, fun σ => by
        apply eT.injective
        rw [heT, LinearEquiv.apply_symm_apply]
        exact y.2 σ⟩
      left_inv := fun x => Subtype.ext (LinearEquiv.symm_apply_apply _ x.1)
      right_inv := fun y => Subtype.ext (LinearEquiv.apply_symm_apply _ y.1) }
  rw [Nat.card_congr e1, Nat.card_congr e2, card_rightInvariants, Fintype.card_fin, hdim]

end CentralInvariants

section RationalTorsion

open ZInQ.Contrib.RC53Assist.CalibrationShape
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

omit [NumberField K] in
/-- A rational point is fixed by `G_{K,S}`. Kind: PROVED. -/
theorem basePointS_fixed (W : WeierstrassCurve K) (Q : W.toAffine.Point) (σ : GKS K S) :
    Affine.Point.map (galS K S σ).toAlgHom (basePointS (S := S) W Q) = basePointS W Q := by
  change Affine.Point.map (galS K S σ).toAlgHom
      (Affine.Point.map (W' := W.toAffine) (Algebra.ofId K (KS K S))
        (Affine.Point.equivBaseChangeSelf W.toAffine Q)) =
    Affine.Point.map (W' := W.toAffine) (Algebra.ofId K (KS K S))
      (Affine.Point.equivBaseChangeSelf W.toAffine Q)
  have hσ : (galS K S σ).toAlgHom.comp (Algebra.ofId K (KS K S)) = Algebra.ofId K (KS K S) :=
    AlgHom.ext fun x => AlgHom.commutes _ x
  rw [Affine.Point.map_map, hσ]

/-- **Galois descent for the level-`i` torsion**: the `G_{K,S}`-invariants of `W(K_S)[2^i]` are
the rational `2^i`-torsion `W(K)[2^i]`. Kind: PROVED. -/
theorem card_lev_invariants (W : WeierstrassCurve K) (i : ℕ) :
    Nat.card {P : Lev K S W i // ∀ σ : GKS K S, σ • P = P} =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point ((2 ^ i : ℕ) : ℤ)) := by
  symm
  refine Nat.card_eq_of_bijective (fun Q => ⟨⟨basePointS (S := S) W Q.1, ?_⟩, ?_⟩) ⟨?_, ?_⟩
  · rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.1 Q.2, map_zero]
  · intro σ
    exact Subtype.ext (basePointS_fixed W Q.1 σ)
  · intro Q Q' h
    exact Subtype.ext (basePointS_injective W (congrArg (fun P => P.1.1) h))
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hQ⟩ := exists_basePointS_of_fixed W P.1 (fun σ => congrArg Subtype.val (hP σ))
    have hQt : Q ∈ AddSubgroup.torsionBy W.toAffine.Point ((2 ^ i : ℕ) : ℤ) := by
      rw [AddSubgroup.torsionBy.nsmul_iff]
      apply basePointS_injective (S := S) W
      rw [map_nsmul, hQ, map_zero]
      exact AddSubgroup.torsionBy.nsmul_iff.1 P.2
    exact ⟨⟨Q, hQt⟩, Subtype.ext (Subtype.ext hQ)⟩

end RationalTorsion

section PrimaryComponent

variable {A : Type} [AddCommGroup A]

/-- A finite `2`-primary component has order a power of two. Kind: PROVED. -/
theorem card_primaryComponent_two [Finite (AddCommGroup.primaryComponent A 2)] :
    Nat.card (AddCommGroup.primaryComponent A 2) =
      2 ^ padicValNat 2 (Nat.card (AddCommGroup.primaryComponent A 2)) := by
  set N := Nat.card (AddCommGroup.primaryComponent A 2) with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  have huniq : ∀ {d : ℕ}, d.Prime → d ∣ N → d = 2 := by
    intro d hd hdN
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' d hdN
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 g.2
    have hk' : (2 ^ k) • g = 0 := Subtype.ext hk
    have hdvd : d ∣ 2 ^ k := hg ▸ addOrderOf_dvd_of_nsmul_eq_zero hk'
    exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).1 (hd.dvd_of_dvd_pow hdvd)
  have h := Nat.eq_prime_pow_of_unique_prime_dvd hN0 huniq
  conv_lhs => rw [h]
  congr 1
  conv_rhs => rw [h]
  rw [padicValNat.prime_pow]

/-- **The rational `2^i`-torsion is the whole `2`-primary component for large `i`.**
Kind: PROVED. -/
theorem torsionBy_eq_primaryComponent [Finite (AddCommGroup.primaryComponent A 2)] (i : ℕ)
    (hi : padicValNat 2 (Nat.card (AddCommGroup.primaryComponent A 2)) ≤ i) :
    AddSubgroup.torsionBy A ((2 ^ i : ℕ) : ℤ) = AddCommGroup.primaryComponent A 2 := by
  ext x
  rw [AddSubgroup.torsionBy.nsmul_iff]
  constructor
  · intro hx
    exact AddCommGroup.mem_primaryComponent.2 ⟨i, hx⟩
  · intro hx
    have h1 : (Nat.card (AddCommGroup.primaryComponent A 2)) •
        (⟨x, hx⟩ : AddCommGroup.primaryComponent A 2) = 0 := card_nsmul_eq_zero'
    rw [card_primaryComponent_two] at h1
    have h2 : (2 ^ padicValNat 2 (Nat.card (AddCommGroup.primaryComponent A 2))) • x = 0 :=
      congrArg Subtype.val h1
    obtain ⟨c, hc⟩ := pow_dvd_pow 2 hi
    rw [hc, mul_nsmul, h2, nsmul_zero]

end PrimaryComponent

section DiteConditions

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M] {v : Places K S}
  {p : Prop} {d : Decidable p} {c₁ : p → CondAt K S k M v} {c₂ : ¬ p → CondAt K S k M v}

/-- A chosen local condition inherits its degree `−1` term. Kind: PROVED. -/
theorem condAt_neg_dite (hp : p) (h : Subsingleton ((c₁ hp).U.X (-1))) :
    Subsingleton ((@dite _ p d c₁ c₂).U.X (-1)) := by
  rw [dite_eq_left_of_eq_true (eq_true hp)]
  exact h

/-- A chosen local condition inherits degree-zero bijectivity. Kind: PROVED. -/
theorem condAt_zero_dite (hp : p) (h : Function.Bijective ((c₁ hp).i.f 0 0 rfl)) :
    Function.Bijective ((@dite _ p d c₁ c₂).i.f 0 0 rfl) := by
  rw [dite_eq_left_of_eq_true (eq_true hp)]
  exact h

/-- A chosen local condition inherits degree-one injectivity. Kind: PROVED. -/
theorem condAt_one_dite (hp : p) (h : Function.Injective ((c₁ hp).i.f 1 1 rfl)) :
    Function.Injective ((@dite _ p d c₁ c₂).i.f 1 1 rfl) := by
  rw [dite_eq_left_of_eq_true (eq_true hp)]
  exact h

end DiteConditions

section Arith0

open ZInQ.Contrib.RC53Assist.CalibrationShape

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- A cocycle condition is all of the `0`-cochains. Kind: PROVED. -/
theorem cocycleConditionι_zero_bijective {k : Type} [CommRing k] {G : Type} [Group G]
    [TopologicalSpace G] [ContinuousMul G] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction G M] [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul k M] [ContinuousSMul G M] (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) :
    Function.Bijective ((cocycleConditionι Z hZ).f 0 0 rfl) :=
  ⟨cocycleConditionι_injective Z hZ 0, fun y => ⟨ofCondZero Z hZ y, rfl⟩⟩

/-- **`H⁰` of the genuine finite central Kummer Selmer complex is the invariants of `M_i`.**
Kind: PROVED. -/
theorem card_selH_zero (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Nat.card (G.selH i 0) =
      Nat.card (invariantsSub (Acoef i) (GKS K G.S) (finiteCentralModule G i)) := by
  unfold GenuineKummerData.selH centralKummerSelData kummerSelData actualSelData galoisSelData
  refine card_selH0 _ (fun v => ?_) (fun v => ?_) (fun v => ?_)
  · refine condAt_neg_dite v.2 (condAt_neg_dite v.2 ?_)
    change Subsingleton PUnit
    infer_instance
  · exact condAt_zero_dite v.2 (condAt_zero_dite v.2 (cocycleConditionι_zero_bijective _ _))
  · exact condAt_one_dite v.2 (condAt_one_dite v.2 (cocycleConditionι_injective _ _ 1))

end Arith0

section MordellWeil

/-- **PRINT** (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Theorem VIII.6.7, the
Mordell–Weil theorem, page 239; used, without citation, at tex 295, 3905, 3976): "Let `K` be a
number field, and let `E/K` be
an elliptic curve. Then the group `E(K)` is finitely generated." Kind: definition (PRINT input;
no inhabitant is supplied). -/
def MordellWeilNumberFieldPrint : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K] (W : WeierstrassCurve K),
    W.IsElliptic → AddGroup.FG W.toAffine.Point

/-- The `2`-primary component of a finitely generated abelian group is finite. Kind: PROVED. -/
theorem finite_primaryComponent_of_fg {A : Type} [AddCommGroup A] [h : AddGroup.FG A] :
    Finite (AddCommGroup.primaryComponent A 2) := by
  have : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr h
  have : Module.Finite ℤ (AddCommGroup.primaryComponent A 2) :=
    Module.Finite.of_injective (AddCommGroup.primaryComponent A 2).subtype.toIntLinearMap
      Subtype.val_injective
  have : AddGroup.FG (AddCommGroup.primaryComponent A 2) := Module.Finite.iff_addGroup_fg.mp this
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun g => ?_
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 g.2
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 ^ k, pow_pos two_pos k, Subtype.ext hk⟩

/-- **Finiteness of the rational `2`-primary torsion of the central twist, from Mordell–Weil.**
Kind: PROVED (from the PRINT). -/
theorem finite_central_torsion (hMW : MordellWeilNumberFieldPrint) {K : Type} [Field K]
    [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
    (G : GenuineKummerData K E₀ hZ) :
    Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2) :=
  have := hMW K (centralCurve G) inferInstance
  finite_primaryComponent_of_fg

/-- Non-vacuity of the finiteness bridge: the `2`-primary component of the finitely generated
group `ℤ/4` is finite. Kind: PROVED (non-vacuity). -/
example : Finite (AddCommGroup.primaryComponent (ZMod 4) 2) := finite_primaryComponent_of_fg

end MordellWeil

section Arith0Final

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- **The field `arith0` of `DiskArith`, PROVED for the actual torsion** (tex 4005–4010:
`H¹(C_K)_tors = E^{(h)}(K)[2^∞]`, read at finite level as `H⁰(M_i) = (E^{(h)}(K)[2^i])^i`):
for the genuine finite central Kummer Selmer complexes of `G`, if the rational `2`-primary torsion
of the central twist `E^{(h)}/K` is finite, of order `t`, then `|H⁰| = 2^{i v₂ t}` for all large
`i`. Kind: PROVED. -/
theorem arith0_central (G : GenuineKummerData K E₀ hZ)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)] :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 0) =
      2 ^ (padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
        (centralCurve G).toAffine.Point 2)) * i) := by
  refine ⟨padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
    (centralCurve G).toAffine.Point 2)) + 1, fun i hi => ?_⟩
  have hi0 : i ≠ 0 := by omega
  rw [card_selH_zero, card_central_invariants G i hi0, card_lev_invariants,
    torsionBy_eq_primaryComponent _ (by omega)]
  conv_lhs => rw [card_primaryComponent_two]
  rw [← pow_mul]

/-- **`arith0` from the Mordell–Weil theorem alone**: for the genuine finite central Kummer
Selmer complexes of `G`, `|H⁰| = 2^{i v₂ t}` for all large `i`, `t` the order of the (finite)
rational `2`-primary torsion of the central twist. Kind: PROVED (from the PRINT). -/
theorem arith0_of_mordellWeil (hMW : MordellWeilNumberFieldPrint)
    (G : GenuineKummerData K E₀ hZ) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 0) =
      2 ^ (padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
        (centralCurve G).toAffine.Point 2)) * i) :=
  have := finite_central_torsion hMW G
  arith0_central G

end Arith0Final

end ZInQ.Contrib.RC53Assist.DiskOrders
