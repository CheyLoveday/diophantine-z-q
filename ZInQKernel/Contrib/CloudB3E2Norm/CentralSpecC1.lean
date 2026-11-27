import ZInQKernel.Contrib.CloudB3E2Norm.CentralSpec

/-!
# The coefficients at the center: a concrete comparison

Manuscript `diophantine_zq.tex`, tex 2781–2791, 3904, 3911–3933.

**Supersedes the read-out form of `CentralStageComparison`.** In `CentralStageComparison`
(`CentralSpec.lean`) the read-out `Φ` is typed on `E(K_{S₁})`-valued cochains. No concrete
faithful target exists for that form: a target must be a module over the residue ring
`R0 = ℤ/2^i` at the center, and `E[2^i]` can lie in `2^i·E(K_{S₁})` (whenever `E[2^{2i}]` is
rational over `K_{S₁}`), so any additive read-out of `E(K_{S₁})`-valued cochains into an
`ℤ/2^i`-module kills the nonzero `2^i`-torsion-valued cochains and `hΦinj` fails. The
replacement **`CentralStageComparison₂`** types `Φ` on `E[2^i]`-valued cochains (the values of the
augmented classes, which lie in `E[2^i]` over `K_{S₀}`), with `hpush` through `augTors = ε ⊗ id`.

* `augTors`, `torsInclS_augTors` (PROVED): the augmentation `ℤ[Δ] ⊗ E[2^i] → E[2^i]`, and
  `incl ∘ augTors = aug ∘ ι`.
* **`CentralStageComparison₂`** (definition; GLUE): as `CentralStageComparison`, with `Φ` on
  `E[2^i]`-valued cochains and `hred` stated for any `E[2^i]`-valued form of the twisted Kummer
  cocycle; **`central45_global₂`** (PROVED): (4.5) at a stage, global component, as
  `central45_global`.
* **(C1) concrete, ambient pointwise form** (PROVED): `evalT0 : A_i → ℤ/2^i` (`t ↦ 0`); the
  target `E[2^i]` (a `ℤ/2^i`-module) with the `χ_h`-twisted action; `Z1C`, the ambient group of
  all `E[2^i]`-valued `1`-cochains (it contains the continuous cochains of the central stage
  complex; `specGC_continuous`: the specialization lands in them), `Z0 = E[2^i]`, `dZ`; `specG`,
  `specG0` (`evalT0 ⊗ id`), `hd`, `hsmul`; `Φ = id` with `hΦinj`; `hpush` — under the named
  hypothesis `Ψ ≡ 1 mod t` (`evalT0 ∘ ψ = 1`, true for `ψ = (1 + t)^{ξ}`). The comparison is the
  pointwise one into this ambient target, not a map of complexes onto the central stage complex.
* **`centralStageComparison₂_of_C2`** (definition): the comparison built from the concrete (C1)
  data and the (C2) data alone (`twistPt`, `red`, `hred`, `twistPt_injective`), which stay named.

Kinds: definitions, GLUE and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] groupRingTop ptSAction

set_option linter.unusedSectionVars false

/-! ### The augmentation on the Shapiro-level module -/

section AugTors

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) (i : ℕ)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- **`augTors = ε ⊗ id : ℤ[Δ] ⊗ E[2^i] → E[2^i]`**. Kind: definition. -/
def augTors : shapMod hS W i s hs hs0 π →+ TorsT S₀ W i :=
  ((TensorProduct.lid ℤ (TorsT S₀ W i)).toLinearMap ∘ₗ
    TensorProduct.map (augε Δ).toIntAlgHom.toLinearMap LinearMap.id).toAddMonoidHom

theorem augTors_tmul (u : MonoidAlgebra ℤ Δ) (t : TorsT S₀ W i) :
    augTors hS W i s hs hs0 π ((u ⊗ₜ t : MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i) :
      shapMod hS W i s hs hs0 π) = augε Δ u • t := by
  change TensorProduct.lid ℤ (TorsT S₀ W i) (TensorProduct.map (augε Δ).toIntAlgHom.toLinearMap
    LinearMap.id (u ⊗ₜ t)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

/-- **`incl ∘ augTors = aug ∘ ι`** (PROVED). -/
theorem torsInclS_augTors (m : shapMod hS W i s hs hs0 π) :
    torsInclS h01 W i (augTors hS W i s hs hs0 π m) =
      augAmb h1 W (ambIotaS hS h01 h1 W i s hs hs0 π m) := by
  have key : ∀ y : MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i,
      torsInclS h01 W i (augTors hS W i s hs hs0 π (show shapMod hS W i s hs hs0 π from y)) =
        augAmb h1 W
          (ambIotaS hS h01 h1 W i s hs hs0 π (show shapMod hS W i s hs hs0 π from y)) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul u t =>
      rw [augTors_tmul]
      change torsInclS h01 W i (augε Δ u • t) = augAmb h1 W
        (((u ⊗ₜ torsInclS h01 W i t : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₁ W)) : ambU h1 W Δ)
      rw [augAmb_tmul, map_zsmul]
    | add y z hy hz =>
      show torsInclS h01 W i (augTors hS W i s hs hs0 π
          ((show shapMod hS W i s hs hs0 π from y) + (show shapMod hS W i s hs hs0 π from z))) =
        augAmb h1 W (ambIotaS hS h01 h1 W i s hs hs0 π
          ((show shapMod hS W i s hs hs0 π from y) + (show shapMod hS W i s hs hs0 π from z)))
      rw [map_add, map_add, map_add, map_add]
      exact congrArg₂ (· + ·) hy hz
  exact key m

end AugTors

/-! ### The comparison, read out on `E[2^i]`-valued cochains -/

section Comparison

open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Manuscript.RC.CalPoint (IsGlobalDivTower globalKummerCochain)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve)

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : GenuineKummerData K E₀ hZ)

attribute [local instance] mcoefModuleK

/-- **The comparison of the presentation at a stage with the compact central complex, read-out on
`E[2^i]`-valued cochains** (tex 3911–3975; replaces `CentralStageComparison`, whose read-out on
`E(K_{S₁})`-valued cochains admits no faithful `ℤ/2^i`-module target, see the file header):

* (C1) the coefficients at the center (tex 2781–2791, 3924–3933): the specialization
  `sp : A_s → R0` (`t ↦ 0`, so `sp(Ψ) = 1`, `hspψ`), a common degree-one target `Z1` (an
  `R0`-module) with degree-zero term `Z0` and differential `dZ`, the specialization of the
  presentation's global cochains `specG`/`specG0` (`sp`-semilinear, commuting with `d`), the
  read-out `Φ` of `χ_h`-twisted torsion cochains of `E(K_{S₁})`, and the identity of the
  specialization of a pushed Shapiro cochain with the read-out of its augmentation (`hpush`; the
  push `ℤ[Δ] → A_s` followed by `t ↦ 0` is the augmentation); the twist identification
  `twistPt : E^{(h)}(K_{S_C}) → E(K_{S₁})` (tex 3904: `E^{(h)}[2^s] ≅ E[2^s](χ_h)`);
* (C2) the support comparison (tex 3911–3915): the reduction `red` of the central global
  `2`-adic cochains of `G_{K,S_C}` to `Z1` (reduction mod `2^s` followed by inflation to
  `G_{K,S}`), with the reduction of a global Kummer cochain the read-out of the `χ_h`-twisted
  Kummer cocycle of the twisted division point (`hred`);
* faithfulness: `Φ` is injective and `twistPt` is injective
  (the genuine read-out and twist identification are), so the target is not degenerate.

The local conditions (C3: the central Kummer conditions map into the presentation's conditions,
tex 3913–3915) are needed only for the lift of (4.5) to the Selmer cones and are not part of this
global-component comparison; they remain a separately named input.

Kind: definition (GLUE; the comparison of complexes is not in the tree). -/
structure CentralStageComparison₂ where
  /-- the residue ring at the center -/
  R0 : Type
  [ringR0 : CommRing R0]
  /-- (C1) the specialization `t ↦ 0` -/
  sp : k →+* R0
  /-- (C1) `Ψ = 1` at the center -/
  hspψ : ∀ d : Δ, sp ((eK k i).symm (ψ d : Acoef i)) = 1
  /-- the degree-one cochains of the central stage complex -/
  Z1 : Type
  [acgZ1 : AddCommGroup Z1]
  [modZ1 : Module R0 Z1]
  /-- its degree-zero cochains -/
  Z0 : Type
  [acgZ0 : AddCommGroup Z0]
  /-- its differential -/
  dZ : Z0 →+ Z1
  /-- (C1) the specialization of the presentation's global cochains, degree one -/
  specG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1 →+ Z1
  /-- (C1) degree zero -/
  specG0 : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0 →+ Z0
  /-- it commutes with the differential -/
  hd : ∀ x, specG ((globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl x) =
    dZ (specG0 x)
  /-- it is `sp`-semilinear -/
  hsmul : ∀ (c : k) x, specG (c • x) = sp c • specG x
  /-- (C1) the read-out of `χ_h`-twisted `E[2^i]`-valued cochains -/
  Φ : ((Fin 1 → GKS K S) → TorsT S₀ W i) →+ Z1
  /-- (C1) the specialization of a pushed Shapiro cochain is the read-out of its augmentation -/
  hpush : ∀ c : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1,
    specG (gPushK hS W i s hs hs0 π ψ k 1 c) =
      Φ (fun g => augTors hS W i s hs hs0 π
        (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) c g))
  /-- (C1) the twist identification of the central points with `E(K_{S₁})` -/
  twistPt : ((centralCurve G).baseChange (KS K G.S)).toAffine.Point →+ PtS K S₁ W
  /-- (C2) the reduction of the central global cochains -/
  red : contCochain ℤ_[2] (GKS K G.S)
    (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (centralCurve G)) 1 →+ Z1
  /-- (C2) the reduction of a global Kummer cochain is the read-out of any `E[2^i]`-valued form
  of the `χ_h`-twisted Kummer cocycle of the twisted division point -/
  hred : ∀ {P : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) P Rt) (f : (Fin 1 → GKS K S) → TorsT S₀ W i),
    (∀ g, torsInclS h01 W i (f g) = ((quadChar s hs hs0 (inflMap K hS (g 0)) : ℤˣ) : ℤ) •
        (inflMap K h1 (g 0) • twistPt (Rt i)) - twistPt (Rt i)) →
    red (globalKummerCochain hR) = Φ f
  /-- faithfulness: `Φ` is injective on `2^i`-torsion-valued cochains -/
  hΦinj : ∀ f : (Fin 1 → GKS K S) → TorsT S₀ W i, Φ f = 0 → f = 0
  /-- faithfulness: the twist identification is injective -/
  twistPt_injective : Function.Injective twistPt

attribute [instance] CentralStageComparison₂.ringR0 CentralStageComparison₂.acgZ1
  CentralStageComparison₂.modZ1 CentralStageComparison₂.acgZ0

/-- **The comparison's target is not degenerate** (PROVED): if `E[2^i]` over `K_{S₀}` is
nonzero, the degree-one target `Z1` is nontrivial. -/
theorem CentralStageComparison₂.nontrivial_Z1₂
    (C : CentralStageComparison₂ hS h01 h1 W i s hs hs0 π ψ k G)
    {t : TorsT S₀ W i} (ht : t ≠ 0) : Nontrivial C.Z1 := by
  refine ⟨⟨C.Φ (fun _ => t), 0, fun h0 => ht ?_⟩⟩
  exact congrFun (C.hΦinj (fun _ => t) h0) (fun _ => 1)

variable {hS h01 h1 W i s hs hs0 π ψ k G}

/-- **(4.5) at a stage, global component** (PROVED from the named comparison; tex 3911–3915):
for the actual points `A_T`, `A_R` of a switch at the moving prime with the global identity
`g_R = pointFactor a z z⁻¹ · g_T + d b_G` (`gx_step_heegner_at`, `z = α(σ)`), and a global tower
`R` of a central point `P` whose twisted `2^i`-division point is the augmented weighted sum of
`A_T` (`htower`; for the text `P = P^{rc}`, the descent of the `χ_h`-weighted trace,
`aug_wsumQ`), the specialization of the class of `A_R` is
`specG g_R = (sp a − 2χ_h(σ)) · red(κ(P)) + dZ(…)`: the retained boundary `z̄ = i(m · P)` with
`m = a_r − 2χ_h(r)`. The fixed multiplier `L` of (H11) is not carried by these classes (it
multiplies both sides of the text's (4.5)). -/
theorem central45_global₂ (hFull : FullTorsion K S₀ W (2 ^ i)) {P : Set (HeightOneSpectrum (𝓞 K))}
    {ι : Type} {place : ι × Bool → Places K S}
    (C : CentralStageComparison₂ hS h01 h1 W i s hs hs0 π ψ k G) {Tp Tq : Finset ι}
    (AT : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
    (AR : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tq)
    (a : k) (σ : GKS K S₀)
    (bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0)
    (hG : gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
      pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π ψ σ : Acoef i))
          ((eK k i).symm (((alphaStage i s hs hs0 π ψ σ)⁻¹ : (Acoef i)ˣ) : Acoef i)) •
        gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
      (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG)
    {Pc : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) Pc Rt)
    (htower : C.twistPt (Rt i) = augAmb h1 W AT.wsumQ) :
    C.specG (gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR) =
      (C.sp a - 2 * (((quadChar s hs hs0 σ : ℤˣ) : ℤ) : C.R0)) •
          C.red (globalKummerCochain hR) + C.dZ (C.specG0 bG) := by
  rw [hG, map_add, C.hsmul, C.hd, sp_pointFactor_center i s hs hs0 π ψ k C.sp C.hspψ a σ]
  congr 2
  rw [gx, C.hpush]
  refine (C.hred hR _ fun g => ?_).symm
  rw [torsInclS_augTors hS h01 h1, aug_shapClass AT g, htower]

end Comparison

/-! ### (C1) concrete: the specialization at the center and the target -/

section Concrete

/-- **The specialization `t ↦ 0`, `A_i → ℤ/2^i`** (tex 2781–2791). Kind: definition. -/
def evalT0 (i : ℕ) [NeZero i] : Acoef i →+* ZMod (2 ^ i) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [Polynomial.eval_mul, NeZero.ne i])

theorem evalT0_mk (i : ℕ) [NeZero i] (a : Polynomial (ZMod (2 ^ i))) :
    evalT0 i (Ideal.Quotient.mk _ a) = Polynomial.eval 0 a := rfl

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (i : ℕ) [NeZero i]

/-- `E[2^i]` is killed by `2^i`. Kind: PROVED. -/
theorem torsT_two_pow (t : TorsT S₀ W i) : (2 ^ i : ℕ) • t = 0 := by
  have h := (Submodule.mem_torsionBy_iff _ _).mp t.2
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul]
  exact_mod_cast h

/-- **`E[2^i]` as a `ℤ/2^i`-module**. Kind: definition. -/
abbrev torsZMod : Module (ZMod (2 ^ i)) (TorsT S₀ W i) :=
  AddCommGroup.zmodModule (torsT_two_pow W i)

attribute [local instance] torsZMod

/-- **`evalT0 ⊗ id : A_i ⊗ E[2^i] → E[2^i]`**, `a ⊗ t ↦ a(0) t`. Kind: definition. -/
def mapZ : Acoef i ⊗[ℤ] TorsT S₀ W i →+ TorsT S₀ W i :=
  (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : Acoef i) (t : TorsT S₀ W i) => evalT0 i a • t)
    (fun a b t => by rw [map_add, add_smul])
    (fun n a t => by
      rw [map_zsmul, zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul])
    (fun a t u => smul_add _ _ _)
    (fun n a t => by rw [smul_comm]))).toAddMonoidHom

theorem mapZ_tmul (a : Acoef i) (t : TorsT S₀ W i) :
    mapZ W i (a ⊗ₜ t) = evalT0 i a • t := by
  simp [mapZ]

theorem mapZ_smul (c : Acoef i) (x : Acoef i ⊗[ℤ] TorsT S₀ W i) :
    mapZ W i (c • x) = evalT0 i c • mapZ W i x := by
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, mapZ_tmul, mapZ_tmul, map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end Concrete

/-! ### (C1) concrete: the comparison maps -/

section ConcreteMaps

open ZInQ.Manuscript.RC.CalPoint (IsGlobalDivTower globalKummerCochain)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve)

attribute [local instance] torsZMod mcoefModuleK

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]

/-- **The specialization of the stage ring at the center**, `k ≃ A_i → ℤ/2^i`. Kind: definition. -/
def spC : k →+* ZMod (2 ^ i) := (evalT0 i).comp (eK k i).toRingHom

/-- `z • t = z.val • t` on `E[2^i]`. Kind: PROVED. -/
theorem zmod_smul_eq (z : ZMod (2 ^ i)) (t : TorsT S₀ W i) : z • t = z.val • t := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact Nat.cast_smul_eq_nsmul _ _ _

/-- **The `χ_h`-twisted action on `E[2^i]`** of `g ∈ G_{K,S}`. Kind: definition. -/
def actZ (g : GKS K S) (t : TorsT S₀ W i) : TorsT S₀ W i :=
  ((quadChar s hs hs0 (inflMap K hS g) : ℤˣ) : ℤ) • (inflMap K hS g • t)

/-- **The degree-one target**: plain `1`-cochains with values in `E[2^i]`. Kind: definition. -/
abbrev Z1C : Type := (Fin 1 → GKS K S) → TorsT S₀ W i

/-- **The target's differential** `t ↦ (g ↦ χ_h(g) g t − t)`. Kind: definition. -/
def dZC : TorsT S₀ W i →+ Z1C W i (S := S) (S₀ := S₀) where
  toFun t g := actZ hS W i s hs hs0 (g 0) t - t
  map_zero' := by funext g; simp [actZ]
  map_add' a b := by funext g; simp only [actZ, smul_add, Pi.add_apply]; abel

/-- The value of a degree-zero cochain. Kind: definition. -/
def gval0 {A : Type} [CommRing A] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
    (z : (globalCx A G M).X 0) : M :=
  asFun A G M ((contSubCx A G M).el z : contCochain A G M 0) Fin.elim0

/-- A degree-zero cochain is the constant cochain of its value. Kind: PROVED. -/
theorem const0_gval0 {A : Type} [CommRing A] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulCommClass G A M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
    (z : (globalCx A G M).X 0) : z = const0 (gval0 z) := by
  apply Subtype.ext
  funext x
  change asFun A G M ((contSubCx A G M).el z : contCochain A G M 0) x =
    asFun A G M ((contSubCx A G M).el z : contCochain A G M 0) Fin.elim0
  congr 1
  funext j
  exact j.elim0

variable {ψ} in
/-- **`evalT0 ∘ α = χ_h`** under `Ψ ≡ 1 mod t` (PROVED). -/
theorem evalT0_alphaStage (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1) (g : GKS K S₀) :
    evalT0 i (alphaStage i s hs hs0 π ψ g : Acoef i) =
      (((quadChar s hs hs0 g : ℤˣ) : ℤ) : ZMod (2 ^ i)) := by
  have hz : alphaStage i s hs hs0 π ψ g =
      intUnitsTo (Acoef i) (quadChar s hs hs0 g) * ψ (π g) := by
    simp [alphaStage, charMul_apply]
  rw [hz, Units.val_mul, map_mul, hψ1, mul_one]
  rcases Int.units_eq_one_or (quadChar s hs hs0 g) with h | h <;> rw [h] <;> simp [intUnitsTo]

variable {ψ} in
/-- **`evalT0 ⊗ id` intertwines the action on `M_i` with the `χ_h`-twisted action** under
`Ψ ≡ 1 mod t` (PROVED). -/
theorem mapZ_act (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1) (g : GKS K S)
    (m : MinS hS W i (alphaStage i s hs hs0 π ψ)) :
    mapZ W i (show Acoef i ⊗[ℤ] TorsT S₀ W i from g • m) =
      actZ hS W i s hs hs0 g (mapZ W i (show Acoef i ⊗[ℤ] TorsT S₀ W i from m)) := by
  have key : ∀ y : Acoef i ⊗[ℤ] TorsT S₀ W i,
      mapZ W i (show Acoef i ⊗[ℤ] TorsT S₀ W i from
        (g • (show MinS hS W i (alphaStage i s hs hs0 π ψ) from y))) =
        actZ hS W i s hs hs0 g (mapZ W i y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a t =>
      have e := CoefMod.smul_tmul (Acoef i) (alphaStage i s hs hs0 π ψ)
        (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) (inflMap K hS g) a t
      change mapZ W i (show Acoef i ⊗[ℤ] TorsT S₀ W i from
        (inflMap K hS g • CoefMod.equiv _ _ _ (a ⊗ₜ t) :
          Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))) = _
      rw [e]
      change mapZ W i
        ((((alphaStage i s hs hs0 π ψ (inflMap K hS g) : (Acoef i)ˣ) : Acoef i) * a) ⊗ₜ
          (inflMap K hS g • t)) = _
      rw [mapZ_tmul, mapZ_tmul, map_mul, evalT0_alphaStage i s hs hs0 π hψ1, mul_smul,
        Int.cast_smul_eq_zsmul, actZ, zmod_smul_eq, zmod_smul_eq,
        smul_comm (inflMap K hS g) ((evalT0 i a).val) t]
    | add y z hy hz =>
      show mapZ W i (show Acoef i ⊗[ℤ] TorsT S₀ W i from
          (g • ((show MinS hS W i (alphaStage i s hs hs0 π ψ) from y) +
            (show MinS hS W i (alphaStage i s hs hs0 π ψ) from z)))) =
        actZ hS W i s hs hs0 g (mapZ W i (y + z))
      rw [smul_add]
      change mapZ W i ((show Acoef i ⊗[ℤ] TorsT S₀ W i from
          (g • (show MinS hS W i (alphaStage i s hs hs0 π ψ) from y))) +
          (show Acoef i ⊗[ℤ] TorsT S₀ W i from
          (g • (show MinS hS W i (alphaStage i s hs hs0 π ψ) from z)))) = _
      rw [map_add, map_add, hy, hz, actZ, actZ, actZ, smul_add, smul_add]
  exact key m

/-- An element of `M_i` read as a tensor. Kind: definition. -/
def asTens (m : MinS hS W i (alphaStage i s hs hs0 π ψ)) : Acoef i ⊗[ℤ] TorsT S₀ W i := m

/-- **The specialization of the presentation's global `1`-cochains**, `evalT0 ⊗ id`.
Kind: definition. -/
def specGC : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1 →+
    Z1C W i (S := S) (S₀ := S₀) where
  toFun x g := mapZ W i (asTens hS W i s hs hs0 π ψ (gval x g))
  map_zero' := by funext g; exact map_zero _
  map_add' x y := by funext g; exact map_add _ _ _

/-- **The specialization lands in the continuous cochains** (PROVED): `specGC x` is continuous for
the discrete topology on `E[2^i]`. The target `Z1C` of the concrete comparison is the ambient group
of all `E[2^i]`-valued `1`-cochains, which contains the continuous ones (the read-out `Φ` of the
comparison is defined on all cochains). -/
theorem specGC_continuous
    (x : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1) :
    @Continuous _ _ _ (⊥ : TopologicalSpace (TorsT S₀ W i)) (specGC hS W i s hs hs0 π ψ k x) := by
  let _ : TopologicalSpace (TorsT S₀ W i) := ⊥
  exact (continuous_of_discreteTopology (f := fun m : MinS hS W i (alphaStage i s hs hs0 π ψ) =>
    mapZ W i (asTens hS W i s hs hs0 π ψ m))).comp
      ((contSubCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).el x).2

/-- **Degree zero**. Kind: definition. -/
def specG0C : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0 →+
    TorsT S₀ W i where
  toFun x := mapZ W i (asTens hS W i s hs hs0 π ψ (gval0 x))
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

variable {ψ} in
/-- **The specialization commutes with the differential** (PROVED, under `Ψ ≡ 1 mod t`). -/
theorem specGC_d (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1)
    (x : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0) :
    specGC hS W i s hs hs0 π ψ k
        ((globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl x) =
      dZC hS W i s hs hs0 (specG0C hS W i s hs hs0 π ψ k x) := by
  funext g
  conv_lhs => rw [const0_gval0 x]
  change mapZ W i (asTens hS W i s hs hs0 π ψ (gval
    ((globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl
      (const0 (gval0 x))) g)) = _
  rw [gval_d_const0]
  change mapZ W i ((show Acoef i ⊗[ℤ] TorsT S₀ W i from g 0 • gval0 x) -
    (asTens hS W i s hs hs0 π ψ (gval0 x))) = _
  rw [map_sub, mapZ_act hS W i s hs hs0 π hψ1]
  rfl

/-- **The specialization is `sp`-semilinear** (PROVED). -/
theorem specGC_smul (c : k)
    (x : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1) :
    specGC hS W i s hs hs0 π ψ k (c • x) = spC i k c • specGC hS W i s hs hs0 π ψ k x := by
  funext g
  change mapZ W i (eK k i c • asTens hS W i s hs hs0 π ψ (gval x g)) = _
  rw [mapZ_smul]
  rfl

variable {ψ} in
/-- **`evalT0 ∘ φ = ε`** on `ℤ[Δ]` under `Ψ ≡ 1 mod t` (PROVED). -/
theorem evalT0_h20 (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1) :
    (evalT0 i).comp (ZInQ.Contrib.CloudB3E2.NormCochain.h20RingHom ψ) =
      (Int.castRingHom (ZMod (2 ^ i))).comp (augε Δ) := by
  apply MonoidAlgebra.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, ZInQ.Contrib.CloudB3E2.NormCochain.h20RingHom, augε,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, map_one, eq_intCast]
    simp
  · intro d
    simp only [RingHom.comp_apply, ZInQ.Contrib.CloudB3E2.NormCochain.h20RingHom, augε,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_comp,
      Function.comp_apply, Units.coeHom_apply, one_smul, MonoidHom.one_apply, hψ1]
    exact (map_one _).symm

variable {ψ} in
/-- **`hpush`** (PROVED, under `Ψ ≡ 1 mod t`): the specialization of a pushed Shapiro cochain is
its augmentation. -/
theorem specGC_push (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1)
    (c : (globalCx (MonoidAlgebra ℤ Δ) (GKS K S) (shapMod hS W i s hs hs0 π)).X 1) :
    specGC hS W i s hs hs0 π ψ k (gPushK hS W i s hs hs0 π ψ k 1 c) =
      fun g => augTors hS W i s hs hs0 π
        (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) c g) := by
  funext g
  change mapZ W i (TensorProduct.map
    (ZInQ.Contrib.CloudB3E2.NormCochain.h20RingHom ψ).toAddMonoidHom.toIntLinearMap LinearMap.id
    (gval (A := MonoidAlgebra ℤ Δ) (M := shapMod hS W i s hs hs0 π) c g :
      MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i)) = _
  have key : ∀ y : MonoidAlgebra ℤ Δ ⊗[ℤ] TorsT S₀ W i,
      mapZ W i (TensorProduct.map
        (ZInQ.Contrib.CloudB3E2.NormCochain.h20RingHom ψ).toAddMonoidHom.toIntLinearMap
          LinearMap.id y) =
        augTors hS W i s hs hs0 π (show shapMod hS W i s hs hs0 π from y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul u t =>
      rw [TensorProduct.map_tmul, mapZ_tmul, augTors_tmul]
      change evalT0 i (ZInQ.Contrib.CloudB3E2.NormCochain.h20RingHom ψ u) • t = _
      rw [← RingHom.comp_apply, evalT0_h20 i hψ1, RingHom.comp_apply, eq_intCast,
        Int.cast_smul_eq_zsmul]
    | add y z hy hz =>
      rw [map_add, map_add, hy, hz]
      exact (map_add (augTors hS W i s hs hs0 π) (show shapMod hS W i s hs hs0 π from y)
        (show shapMod hS W i s hs hs0 π from z)).symm
  exact key _

variable {ψ} in
/-- **The comparison from the concrete (C1) data and the (C2) data alone** (tex 3911–3933), in
ambient pointwise form: the center `R0 = ℤ/2^i`, `sp = evalT0 ∘ e`, the target `E[2^i]` with the
`χ_h`-twisted action, the ambient group of its `1`-cochains (containing the continuous ones),
`specG = evalT0 ⊗ id`, `Φ = id` — all PROVED under `Ψ ≡ 1 mod t` (`hψ1`); the
named inputs are the (C2) data: the twist identification `twistPt` (injective), the reduction
`red` of the central `2`-adic cochains, and its value `hred` on the global Kummer cochains.
Kind: definition. -/
def centralStageComparison₂_of_C2 {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
    (G : GenuineKummerData K E₀ hZ) (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1)
    (twistPt : ((centralCurve G).baseChange (KS K G.S)).toAffine.Point →+ PtS K S₁ W)
    (htw : Function.Injective twistPt)
    (red : contCochain ℤ_[2] (GKS K G.S)
      (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (centralCurve G)) 1 →+ Z1C W i (S := S) (S₀ := S₀))
    (hred : ∀ {P : (centralCurve G).toAffine.Point}
      {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
      (hR : IsGlobalDivTower (centralCurve G) P Rt) (f : (Fin 1 → GKS K S) → TorsT S₀ W i),
      (∀ g, torsInclS h01 W i (f g) = ((quadChar s hs hs0 (inflMap K hS (g 0)) : ℤˣ) : ℤ) •
          (inflMap K h1 (g 0) • twistPt (Rt i)) - twistPt (Rt i)) →
      red (globalKummerCochain hR) = f) :
    CentralStageComparison₂ hS h01 h1 W i s hs hs0 π ψ k G where
  R0 := ZMod (2 ^ i)
  sp := spC i k
  hspψ d := by
    change evalT0 i (eK k i ((eK k i).symm (ψ d : Acoef i))) = 1
    rw [RingEquiv.apply_symm_apply, hψ1]
  Z1 := Z1C W i (S := S) (S₀ := S₀)
  Z0 := TorsT S₀ W i
  dZ := dZC hS W i s hs hs0
  specG := specGC hS W i s hs hs0 π ψ k
  specG0 := specG0C hS W i s hs hs0 π ψ k
  hd := specGC_d hS W i s hs hs0 π k hψ1
  hsmul := specGC_smul hS W i s hs hs0 π ψ k
  Φ := AddMonoidHom.id _
  hpush := specGC_push hS W i s hs hs0 π k hψ1
  twistPt := twistPt
  red := red
  hred := hred
  hΦinj _ h := h
  twistPt_injective := htw

end ConcreteMaps

/-! ### (4.5) at a stage on the concrete target -/

section Concrete45

open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Manuscript.RC.CalPoint (IsGlobalDivTower globalKummerCochain)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve)

attribute [local instance] torsZMod mcoefModuleK

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S₀ ⊆ S} {h01 : S₀ ⊆ S₁} {h1 : S₁ ⊆ S} {W : WeierstrassCurve K} [W.IsElliptic] {i : ℕ}
  [NeZero i] {s : KS K S₀} {h : K} {hs : s ^ 2 = algebraMap K (KS K S₀) h} {hs0 : s ≠ 0}
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] {π : GKS K S₀ →* Δ} {ψ : Δ →* (Acoef i)ˣ}
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  {k : Type} [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]

/-- **(4.5) at a stage on the concrete target, pointwise** (PROVED from the (C2) data): with the
concrete (C1) comparison, `evalT0 ⊗ id` of the class of `A_R` is
`(a(0) − 2χ_h(σ)) · red(κ(P)) + d(evalT0 ⊗ id (b_G))` as `E[2^i]`-valued `1`-cochains. -/
theorem central45_C2 (hFull : FullTorsion K S₀ W (2 ^ i)) {P : Set (HeightOneSpectrum (𝓞 K))}
    {ι : Type} {place : ι × Bool → Places K S} {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
    (G : GenuineKummerData K E₀ hZ) (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1)
    (twistPt : ((centralCurve G).baseChange (KS K G.S)).toAffine.Point →+ PtS K S₁ W)
    (htw : Function.Injective twistPt)
    (red : contCochain ℤ_[2] (GKS K G.S)
      (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (centralCurve G)) 1 →+ Z1C W i (S := S) (S₀ := S₀))
    (hred : ∀ {P : (centralCurve G).toAffine.Point}
      {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
      (hR : IsGlobalDivTower (centralCurve G) P Rt) (f : (Fin 1 → GKS K S) → TorsT S₀ W i),
      (∀ g, torsInclS h01 W i (f g) = ((quadChar s hs hs0 (inflMap K hS (g 0)) : ℤˣ) : ℤ) •
          (inflMap K h1 (g 0) • twistPt (Rt i)) - twistPt (Rt i)) →
      red (globalKummerCochain hR) = f)
    {Tp Tq : Finset ι}
    (AT : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
    (AR : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tq)
    (a : k) (σ : GKS K S₀)
    (bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0)
    (hG : gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
      pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π ψ σ : Acoef i))
          ((eK k i).symm (((alphaStage i s hs hs0 π ψ σ)⁻¹ : (Acoef i)ˣ) : Acoef i)) •
        gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
      (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG)
    {Pc : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) Pc Rt)
    (htower : twistPt (Rt i) = augAmb h1 W AT.wsumQ) :
    specGC hS W i s hs hs0 π ψ k (gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR) =
      (spC i k a - 2 * (((quadChar s hs hs0 σ : ℤˣ) : ℤ) : ZMod (2 ^ i))) •
          red (globalKummerCochain hR) +
        dZC hS W i s hs hs0 (specG0C hS W i s hs hs0 π ψ k bG) :=
  central45_global₂ hFull (centralStageComparison₂_of_C2 hS h01 h1 W i s hs hs0 π k G hψ1
    twistPt htw red hred) AT AR a σ bG hG hR htower

end Concrete45

end ZInQ.Contrib.CloudB3E2.NormCochain
