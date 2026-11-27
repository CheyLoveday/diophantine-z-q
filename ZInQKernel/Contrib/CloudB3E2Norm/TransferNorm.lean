import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Transfer
import ZInQKernel.Contrib.OneProof.RC.Central.EulerFactors

/-!
# The norm identity at cochain level over `G_K`, through the twisted transfer

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4170): "The
actual norm identity is `z_R = e_q i(z_P)`, with its retained boundary", with `e_q = a_q − z − z⁻¹`
and `z` the scalar Frobenius value; the classes `z_T` are the images of the Kummer classes of the
points `y_T` under the integral Shapiro-plus-coefficient map, the twisted transfer `𝒯_θ` of tex
3219–3250 (`HeegnerCohomology/Transfer.lean`, `TwistedTransfer.T`).

This file is the `G_K`-level companion of `CochainNorm.lean`, at a finite coefficient stage, in
degree one, with the boundary explicit. Setting:

* `G` a group (for the text `G_K`) acting `A`-linearly on an `A`-module `M` through `ρ` (for the text
  the finite coefficient module, e.g. `A_i ⊗ E(ℚ̄)` at a finite stage);
* `HP`, `HR` normal subgroups of finite index (`G_{H_P}`, `G_{H_R}`, the ring class fields of
  supports `P` and `R = P ∪ {q}`), sections `rP`, `rR`, characters `θP`, `θR` of the quotients,
  compatible (`hθ`: `θR` is inflated from `θP` on `G`);
* points `y_P` (fixed by `HP`) and `y_R`, division points `k Q_P = y_P`, `k Q_R = y_R`, and a
  Frobenius lift `σ ∈ G`, with scalar Frobenius value `z = θP(σ)` (`frobValue`).

The actual classes are `z_T = 𝒯_θ(κ(Q_T))`, the twisted transfer of the Kummer cocycle
`h ↦ ρ(h) Q_T − Q_T` (`kummerCochain`).

* `wsum_smul_frob` (PROVED): for `y` fixed by `HP`, `∑_δ R(r_δ) ρ(σ) y = z⁻¹ ∑_δ R(r_δ) y`: the
  Frobenius acts on the weighted sum (the degree-zero transfer) by the scalar `z⁻¹`.
* **`transfer_kummer_norm`** (PROVED): if the twisted weighted sum of `y_R` over `G/HR` is the
  twisted weighted sum over `G/HP` of `Tr y_R` (`hW`, the inflation-compatibility of the twisted
  norm along the support change) and (4.1) holds, `Tr y_R = a y_P − σ y_P − σ⁻¹ y_P`, then for every
  `g ∈ G`,
  `z_R(g) = e_q · z_P(g) + (R(g) b − b)`, with `e_q = pointFactor a z z⁻¹` and the retained boundary
  `b = ∑_δ R(rR_δ) Q_R − e_q ∑_δ R(rP_δ) Q_P` explicit and `k`-torsion (`k • b = 0`).
  This is the shape of lane RC32's `hzR` on global cochains.
* `pairClass_bijective`, **`wsum_inflation`** (PROVED): for `HR ≤ HP`, `U` the image of `HR` in
  `HP` with a transversal `t` (lifts of `Gal(H_R/H_P)`), `θR` inflated from `θP` and `y` fixed by
  `HR`, the twisted weighted sum of `y` over `G/HR` is the twisted weighted sum over `G/HP` of the
  transversal norm `∑_τ ρ(t_τ) y`; this is `hW`, with `Tr y_R = ∑_τ ρ(t_τ) y_R`.
* **`transfer_kummer_norm_of_transversal`** (PROVED): the identity from (4.1) in its transversal
  form `∑_τ ρ(t_τ) y_R = a y_P − σ y_P − σ⁻¹ y_P` directly, together with `k • z_R(g) = 0` and
  `k • z_P(g) = 0` (`R_wsum`, `zsmul_transfer_kummer`): all cochains in the identity take values in
  `M[k]`, so it is an identity of `M[k]`-valued cochains through the injective coercion.
* Non-vacuity: `nonVacuity_transfer`, `nonVacuity_transversal`.

**Hypotheses to be supplied by the consumer.** `hθ` (the coefficient character at support `R` is
inflated from the one at support `P`, i.e. trivial on `Gal(H_R/H_P)`): without it the trace over
`Gal(H_R/H_P)` is twisted and (4.1) does not apply; whether the manuscript's coefficient push uses
such compatible characters across supports is to be checked against tex 3219–3250.

**What remains** for `hzR` in the genuine complexes: (1) the local components of the classes in the
Selmer cones (the local Kummer cocycles lie in the Kummer condition) and the identification of `i`
with the identity on global cochains plus the inclusion of local conditions; (2) the identification
of `M[k]` (here a subgroup of the ambient `M`) with the finite coefficient module of the genuine
complexes, and continuity of the cochains (the genuine complexes are continuous cochains; the
identities here are pointwise); (3) the inner limit to `Λ` and the identification of the actual
classes with those of the Heegner points.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Central (pointFactor)

variable {G : Type*} [Group G] {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M)

/-- **The Kummer cocycle of a division point** `Q` on a subgroup `H`, as an inhomogeneous
`1`-cochain: `h ↦ ρ(h) Q − Q`. Kind: definition. -/
def kummerCochain (H : Subgroup G) (Q : M) : (Fin 1 → H) → M := fun x => ρ (x 0 : G) Q - Q

/-- **The weighted sum** `∑_δ R(r_δ) x` over `G/H` (the degree-zero twisted transfer).
Kind: definition. -/
def wsum (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)] (r : G ⧸ H → G) (θ : G ⧸ H →* Aˣ)
    (x : M) : M :=
  ∑ δ : G ⧸ H, R H ρ θ (r δ) x

/-- **The scalar Frobenius value** `z = θ(σ)`. Kind: definition. -/
def frobValue (H : Subgroup G) [H.Normal] (θ : G ⧸ H →* Aˣ) (σ : G) : A := θ (σ : G ⧸ H)

/-- Its inverse `z⁻¹ = θ(σ)⁻¹`. Kind: definition. -/
def frobValueInv (H : Subgroup G) [H.Normal] (θ : G ⧸ H →* Aˣ) (σ : G) : A :=
  ((θ (σ : G ⧸ H))⁻¹ : Aˣ)

section Frob

variable (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)] (r : G ⧸ H → G)
  (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (θ : G ⧸ H →* Aˣ)

include hr in
/-- **The Frobenius acts on the weighted sum by `z⁻¹`** (PROVED): for `y` fixed by `H`,
`∑_δ R(r_δ) ρ(σ) y = θ(σ)⁻¹ ∑_δ R(r_δ) y`. -/
theorem wsum_smul_frob (σ : G) {y : M} (hy : ∀ h ∈ H, ρ h y = y) :
    wsum ρ H r θ (ρ σ y) = frobValueInv H θ σ • wsum ρ H r θ y := by
  simp only [wsum, R, hr, LinearMap.smul_apply, Finset.smul_sum]
  -- move `σ` into the section: `r_δ σ = r_{δσ} h` with `h ∈ H`
  have key : ∀ δ : G ⧸ H, ρ (r δ) (ρ σ y) = ρ (r (δ * (σ : G ⧸ H))) y := by
    intro δ
    have hmem : (r (δ * (σ : G ⧸ H)))⁻¹ * (r δ * σ) ∈ H := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_mul, hr, hr]
    rw [← Module.End.mul_apply, ← map_mul, ← mul_inv_cancel_left (r (δ * (σ : G ⧸ H))) (r δ * σ),
      map_mul, Module.End.mul_apply, hy _ hmem]
  simp_rw [key]
  -- reindex `δ ↦ δ σ`
  rw [Fintype.sum_equiv (Equiv.mulRight (σ : G ⧸ H)) (fun δ => ((θ δ : Aˣ) : A) •
      ρ (r (δ * (σ : G ⧸ H))) y) (fun δ => ((θ (δ * (σ : G ⧸ H)⁻¹) : Aˣ) : A) • ρ (r δ) y)
      (fun δ => by simp)]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [map_mul, map_inv, Units.val_mul, mul_comm, mul_smul, frobValueInv]

include hr in
/-- **The weighted sum of an `H`-fixed element is fixed by the twisted action** (PROVED):
`R(g) ∑_δ R(r_δ) y = ∑_δ R(r_δ) y`. -/
theorem R_wsum (g : G) {y : M} (hy : ∀ h ∈ H, ρ h y = y) :
    R H ρ θ g (wsum ρ H r θ y) = wsum ρ H r θ y := by
  simp only [wsum, map_sum]
  have key : ∀ δ : G ⧸ H, R H ρ θ g (R H ρ θ (r δ) y) = R H ρ θ (r ((g : G ⧸ H) * δ)) y := by
    intro δ
    rw [← Module.End.mul_apply, ← R_r_mul_hc H r hr ρ θ g δ, Module.End.mul_apply,
      hy _ (hc_mem H r hr g δ)]
  simp_rw [key]
  exact Fintype.sum_equiv (Equiv.mulLeft (g : G ⧸ H)) _ _ (fun _ => rfl)

include hr in
/-- **The transferred Kummer cocycle takes values in `M[k]`** (PROVED): for `k Q = y` with `y`
fixed by `H`, `k • 𝒯_θ(κ(Q))(g) = 0` for every `g`. -/
theorem zsmul_transfer_kummer (k : ℤ) {Q y : M} (hQ : k • Q = y) (hy : ∀ h ∈ H, ρ h y = y)
    (g : Fin 1 → G) : k • T H r hr ρ θ 1 (kummerCochain ρ H Q) g = 0 := by
  obtain ⟨hk, hT⟩ := kummer_weighted_sum H r hr ρ θ k y Q hQ
  have e : kummerCochain ρ H Q = fun x => ρ (x 0 : G) Q - Q := rfl
  rw [e, hT g, smul_sub, ← map_zsmul, hk]
  exact sub_eq_zero.mpr (R_wsum ρ H r hr θ (g 0) hy)

end Frob

section Norm

variable (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (θP : G ⧸ HP →* Aˣ) (θR : G ⧸ HR →* Aˣ)

/-- **The point factor** `e_q = a − z − z⁻¹` with `z = θP(σ)`. Kind: definition. -/
def eq_ (a : ℤ) (σ : G) : A := pointFactor (a : A) (frobValue HP θP σ) (frobValueInv HP θP σ)

/-- **The retained boundary** `b = ∑_δ R(rR_δ) Q_R − e_q ∑_δ R(rP_δ) Q_P`. Kind: definition. -/
def retainedBoundaryT (a : ℤ) (σ : G) (QR QP : M) : M :=
  wsum ρ HR rR θR QR - eq_ HP θP a σ • wsum ρ HP rP θP QP

include hrP hrR in
/-- **The actual norm identity at cochain level over `G`, with its retained boundary** (PROVED;
tex 4157–4170 at a finite coefficient stage). With `z_T = 𝒯_θ(κ(Q_T))` the twisted transfers of the
Kummer cocycles, the compatibility `hθ` of the characters, the inflation-compatibility `hW` of the
twisted norm and the point relation (4.1) `Tr y_R = a y_P − σ y_P − σ⁻¹ y_P`:
`z_R(g) = e_q z_P(g) + (R(g) b − b)` for every `g`, and `k • b = 0` (an identity of `M`-valued
cochains; with `y_R` fixed by `HR` the values of `z_R`, `z_P` lie in `M[k]`, see
`transfer_kummer_norm_of_transversal`). -/
theorem transfer_kummer_norm
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : Aˣ) : A) = θP (x : G ⧸ HP))
    (k a : ℤ) (σ : G) {yR yP QR QP TrR : M}
    (hQR : k • QR = yR) (hQP : k • QP = yP) (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hW : wsum ρ HR rR θR yR = wsum ρ HP rP θP TrR)
    (hnorm : TrR = a • yP - ρ σ yP - ρ σ⁻¹ yP) :
    (∀ g : Fin 1 → G, T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g =
        eq_ HP θP a σ • T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g +
          (R HR ρ θR (g 0) (retainedBoundaryT ρ HP HR rP rR θP θR a σ QR QP) -
            retainedBoundaryT ρ HP HR rP rR θP θR a σ QR QP)) ∧
      k • retainedBoundaryT ρ HP HR rP rR θP θR a σ QR QP = 0 := by
  have hRR : ∀ x : G, R HR ρ θR x = R HP ρ θP x := fun x => by simp only [R, hθ]
  obtain ⟨hkR, hTR⟩ := kummer_weighted_sum HR rR hrR ρ θR k yR QR hQR
  obtain ⟨hkP, hTP⟩ := kummer_weighted_sum HP rP hrP ρ θP k yP QP hQP
  refine ⟨fun g => ?_, ?_⟩
  · have e1 : kummerCochain ρ HR QR = fun x => ρ (x 0 : G) QR - QR := rfl
    have e2 : kummerCochain ρ HP QP = fun x => ρ (x 0 : G) QP - QP := rfl
    rw [e1, e2, hTR g, hTP g, retainedBoundaryT, map_sub, map_smul, hRR (g 0), wsum, wsum]
    simp only [smul_sub]
    abel
  · have hsig := wsum_smul_frob ρ HP rP hrP θP σ hfixP
    have hsigi := wsum_smul_frob ρ HP rP hrP θP σ⁻¹ hfixP
    have hinv : frobValueInv HP θP σ⁻¹ = frobValue HP θP σ := by
      simp [frobValueInv, frobValue]
    rw [hinv] at hsigi
    have hP' : k • wsum ρ HP rP θP QP = wsum ρ HP rP θP yP := hkP
    have hR' : k • wsum ρ HR rR θR QR = wsum ρ HR rR θR yR := hkR
    have hlin : ∀ x y : M, wsum ρ HP rP θP (x - y) = wsum ρ HP rP θP x - wsum ρ HP rP θP y :=
      fun x y => by simp only [wsum, map_sub, Finset.sum_sub_distrib]
    have hzs : ∀ x : M, wsum ρ HP rP θP (a • x) = a • wsum ρ HP rP θP x :=
      fun x => by simp only [wsum, map_zsmul, Finset.smul_sum]
    rw [retainedBoundaryT, smul_sub, hR', smul_comm k, hP', hW, hnorm, hlin, hlin, hzs, hsig,
      hsigi, eq_, pointFactor, sub_smul, sub_smul, Int.cast_smul_eq_zsmul]
    abel

end Norm

section Inflation

set_option linter.unusedSectionVars false

variable (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (θP : G ⧸ HP →* Aˣ) (θR : G ⧸ HR →* Aˣ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : G) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

/-- The enumeration `(δ, τ) ↦ [r_δ t_τ]` of `G/HR` by `G/HP × HP/HR`. Kind: definition. -/
def pairClass (p : (G ⧸ HP) × (HP ⧸ U)) : G ⧸ HR := ((rP p.1 * (t p.2 : G) : G) : G ⧸ HR)

include hrP hU ht in
/-- **The enumeration is a bijection** (PROVED), for `HR ≤ HP` with `U` the image of `HR` in `HP`. -/
theorem pairClass_bijective (hle : HR ≤ HP) : Function.Bijective (pairClass HP HR rP U t) := by
  constructor
  · rintro ⟨δ₁, τ₁⟩ ⟨δ₂, τ₂⟩ h
    simp only [pairClass] at h
    have h' := QuotientGroup.eq.mp h
    have hP : (rP δ₁ * (t τ₁ : G))⁻¹ * (rP δ₂ * (t τ₂ : G)) ∈ HP := hle h'
    have hδ : δ₁ = δ₂ := by
      rw [← hrP δ₁, ← hrP δ₂, QuotientGroup.eq]
      have h1 : (rP δ₁)⁻¹ * rP δ₂ = (t τ₁ : G) * ((rP δ₁ * (t τ₁ : G))⁻¹ * (rP δ₂ * (t τ₂ : G))) *
          (t τ₂ : G)⁻¹ := by group
      rw [h1]
      exact HP.mul_mem (HP.mul_mem (t τ₁).2 hP) (HP.inv_mem (t τ₂).2)
    subst hδ
    have hτ : τ₁ = τ₂ := by
      rw [← ht τ₁, ← ht τ₂, QuotientGroup.eq, hU]
      have h2 : (((t τ₁)⁻¹ * t τ₂ : HP) : G) =
          (rP δ₁ * (t τ₁ : G))⁻¹ * (rP δ₁ * (t τ₂ : G)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [h2]; exact h'
    rw [hτ]
  · intro δ
    induction δ using QuotientGroup.induction_on with
    | H g =>
      set δP : G ⧸ HP := (g : G ⧸ HP)
      have hmem : (rP δP)⁻¹ * g ∈ HP := by
        rw [← QuotientGroup.eq, hrP]
      set τ : HP ⧸ U := ((⟨_, hmem⟩ : HP) : HP ⧸ U)
      refine ⟨(δP, τ), ?_⟩
      simp only [pairClass]
      rw [QuotientGroup.eq]
      have h3 := QuotientGroup.eq.mp (ht τ)
      rw [hU] at h3
      have h4 : (rP δP * (t τ : G))⁻¹ * g = ((t τ)⁻¹ * ⟨_, hmem⟩ : HP) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [h4]; exact h3

include hrP hrR hU ht in
/-- **Inflation of the twisted norm along the support change** (PROVED): for `HR ≤ HP`, `θR`
inflated from `θP` and `y` fixed by `HR`, the twisted weighted sum of `y` over `G/HR` is the
twisted weighted sum over `G/HP` of the transversal norm `∑_τ ρ(t_τ) y` (the hypothesis `hW` of
`transfer_kummer_norm`, with `Tr y = ∑_τ ρ(t_τ) y`). -/
theorem wsum_inflation (hle : HR ≤ HP)
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : Aˣ) : A) = θP (x : G ⧸ HP))
    {y : M} (hy : ∀ h ∈ HR, ρ h y = y) :
    wsum ρ HR rR θR y = wsum ρ HP rP θP (∑ τ : HP ⧸ U, ρ (t τ : G) y) := by
  -- the summand at a class `[x]` only depends on `x`
  have hval : ∀ x : G, R HR ρ θR (rR (x : G ⧸ HR)) y = ((θP (x : G ⧸ HP) : Aˣ) : A) • ρ x y := by
    intro x
    have hm : x⁻¹ * rR (x : G ⧸ HR) ∈ HR := by rw [← QuotientGroup.eq, hrR]
    rw [R, hrR, hθ, LinearMap.smul_apply, ← mul_inv_cancel_left x (rR (x : G ⧸ HR)), map_mul,
      Module.End.mul_apply, hy _ hm]
  rw [wsum, ← (Equiv.ofBijective _ (pairClass_bijective HP HR rP hrP U hU t ht hle)).sum_comp,
    Fintype.sum_prod_type, wsum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  simp only [Equiv.ofBijective_apply, pairClass, hval]
  rw [R, hrP, LinearMap.smul_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc : ((rP δ * (t τ : G) : G) : G ⧸ HP) = δ := by
    rw [QuotientGroup.mk_mul, hrP, (QuotientGroup.eq_one_iff _).mpr (t τ).2, mul_one]
  rw [hc, map_mul, Module.End.mul_apply]

include hrP hrR hU ht in
/-- **The actual norm identity over `G` from the transversal relation (4.1)** (PROVED; tex
4157–4170 at a finite coefficient stage): for `HR ≤ HP`, `U` the image of `HR` in `HP` with
transversal `t` (lifts of `Gal(H_R/H_P)`), `θR` inflated from `θP`, `y_R` fixed by `HR`, `y_P` fixed
by `HP`, and (4.1) in the form `∑_τ ρ(t_τ) y_R = a y_P − σ y_P − σ⁻¹ y_P`:
`z_R(g) = e_q z_P(g) + (R(g) b − b)` for every `g ∈ G`, with `z_T = 𝒯_θ(κ(Q_T))`, `e_q = a − z − z⁻¹`,
`z = θP(σ)`, and the retained boundary `b` explicit and `k`-torsion; and `z_R`, `z_P` take values in
`M[k]` (so the identity is one of `M[k]`-valued cochains through the injective coercion). -/
theorem transfer_kummer_norm_of_transversal (hle : HR ≤ HP)
    (hθ : ∀ x : G, ((θR (x : G ⧸ HR) : Aˣ) : A) = θP (x : G ⧸ HP))
    (k a : ℤ) (σ : G) {yR yP QR QP : M}
    (hQR : k • QR = yR) (hQP : k • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : G) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP) :
    (∀ g : Fin 1 → G, T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g =
        eq_ HP θP a σ • T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g +
          (R HR ρ θR (g 0) (retainedBoundaryT ρ HP HR rP rR θP θR a σ QR QP) -
            retainedBoundaryT ρ HP HR rP rR θP θR a σ QR QP)) ∧
      k • retainedBoundaryT ρ HP HR rP rR θP θR a σ QR QP = 0 ∧
      (∀ g : Fin 1 → G, k • T HR rR hrR ρ θR 1 (kummerCochain ρ HR QR) g = 0) ∧
      (∀ g : Fin 1 → G, k • T HP rP hrP ρ θP 1 (kummerCochain ρ HP QP) g = 0) := by
  obtain ⟨h1, h2⟩ := transfer_kummer_norm ρ HP HR rP hrP rR hrR θP θR hθ k a σ hQR hQP hfixP
    (wsum_inflation ρ HP HR rP hrP rR hrR θP θR U hU t ht hle hθ hfixR) hnorm
  exact ⟨h1, h2, zsmul_transfer_kummer ρ HR rR hrR θR k hQR hfixR,
    zsmul_transfer_kummer ρ HP rP hrP θP k hQP hfixP⟩

end Inflation

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `transfer_kummer_norm`**: `G = HP = HR` the trivial group
acting trivially on `M = A = ℤ`, trivial characters and sections, `k = 2`, `a = 3`,
`y_P = y_R = 2`, `Q_P = Q_R = 1`, `Tr y_R = 2 = 3·2 − 2 − 2`. -/
theorem nonVacuity_transfer :
    ∃ (ρ : Unit →* Module.End ℤ ℤ) (HP HR : Subgroup Unit) (_ : HP.Normal) (_ : HR.Normal)
      (_ : Fintype (Unit ⧸ HP)) (_ : Fintype (Unit ⧸ HR)) (rP : Unit ⧸ HP → Unit)
      (rR : Unit ⧸ HR → Unit) (θP : Unit ⧸ HP →* ℤˣ) (θR : Unit ⧸ HR →* ℤˣ)
      (yR yP QR QP TrR : ℤ),
      (∀ δ, ((rP δ : Unit) : Unit ⧸ HP) = δ) ∧ (∀ δ, ((rR δ : Unit) : Unit ⧸ HR) = δ) ∧
      (∀ x : Unit, ((θR (x : Unit ⧸ HR) : ℤˣ) : ℤ) = θP (x : Unit ⧸ HP)) ∧
      (2 : ℤ) • QR = yR ∧ (2 : ℤ) • QP = yP ∧ (∀ h ∈ HP, ρ h yP = yP) ∧
      wsum ρ HR rR θR yR = wsum ρ HP rP θP TrR ∧
      TrR = (3 : ℤ) • yP - ρ () yP - ρ ()⁻¹ yP := by
  refine ⟨1, ⊤, ⊤, inferInstance, inferInstance, Fintype.ofFinite _, Fintype.ofFinite _, fun _ => (),
    fun _ => (), 1, 1, 2, 2, 1, 1, 2, fun δ => Subsingleton.elim _ _,
    fun δ => Subsingleton.elim _ _, fun _ => rfl, by norm_num, by norm_num, fun _ _ => rfl, rfl,
    by norm_num⟩

/-- **Non-vacuity of the hypotheses of `transfer_kummer_norm_of_transversal`** (all of them,
instances, sections and transversal included): the trivial group acting trivially on `ℤ`,
`HP = HR = ⊤`, `U = ⊤`, trivial characters, sections and transversal, `k = 2`, `a = 3`,
`y_P = y_R = 2`, `Q_P = Q_R = 1` (so `∑_τ t_τ y_R = 2 = 3·2 − 2 − 2`). -/
theorem nonVacuity_transversal :
    ∃ (ρ : Unit →* Module.End ℤ ℤ) (HP HR : Subgroup Unit) (_ : HP.Normal) (_ : HR.Normal)
      (_ : Fintype (Unit ⧸ HP)) (_ : Fintype (Unit ⧸ HR)) (rP : Unit ⧸ HP → Unit)
      (rR : Unit ⧸ HR → Unit) (θP : Unit ⧸ HP →* ℤˣ) (θR : Unit ⧸ HR →* ℤˣ) (U : Subgroup HP)
      (_ : Fintype (HP ⧸ U)) (t : HP ⧸ U → HP) (yR yP QR QP : ℤ),
      (∀ δ, ((rP δ : Unit) : Unit ⧸ HP) = δ) ∧ (∀ δ, ((rR δ : Unit) : Unit ⧸ HR) = δ) ∧
      (∀ h : HP, h ∈ U ↔ (h : Unit) ∈ HR) ∧
      (∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ) ∧ HR ≤ HP ∧
      (∀ x : Unit, ((θR (x : Unit ⧸ HR) : ℤˣ) : ℤ) = θP (x : Unit ⧸ HP)) ∧
      (2 : ℤ) • QR = yR ∧ (2 : ℤ) • QP = yP ∧ (∀ h ∈ HR, ρ h yR = yR) ∧
      (∀ h ∈ HP, ρ h yP = yP) ∧
      ∑ τ : HP ⧸ U, ρ (t τ : Unit) yR = (3 : ℤ) • yP - ρ () yP - ρ ()⁻¹ yP := by
  have hq : ∀ τ : (⊤ : Subgroup Unit) ⧸ (⊤ : Subgroup (⊤ : Subgroup Unit)), τ = 1 := fun τ => by
    induction τ using QuotientGroup.induction_on with
    | H x => exact QuotientGroup.eq.mpr (Subgroup.mem_top _)
  let _ : Fintype ((⊤ : Subgroup Unit) ⧸ (⊤ : Subgroup (⊤ : Subgroup Unit))) :=
    ⟨{1}, fun τ => by simp [hq τ]⟩
  refine ⟨1, ⊤, ⊤, inferInstance, inferInstance, Fintype.ofFinite _, Fintype.ofFinite _,
    fun _ => (), fun _ => (), 1, 1, ⊤, inferInstance, fun _ => 1, 2, 2, 1, 1,
    fun δ => Subsingleton.elim _ _, fun δ => Subsingleton.elim _ _, fun h => by simp,
    fun τ => (hq τ).symm ▸ rfl, le_rfl, fun _ => rfl, by norm_num, by norm_num, fun _ _ => rfl,
    fun _ _ => rfl, ?_⟩
  have hcard : (Finset.univ : Finset ((⊤ : Subgroup Unit) ⧸ (⊤ : Subgroup (⊤ : Subgroup Unit)))) =
      {1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun τ _ => hq τ⟩
  rw [hcard, Finset.sum_singleton]
  norm_num

end ZInQ.Contrib.CloudB3E2.NormCochain
