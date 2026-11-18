import ZInQKernel.Contrib.OneProof.RC.CoefModules.Dual
import ZInQKernel.Contrib.OneProof.RC.CoefModules.ConjStable
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Lane RC28 (coefficient modules), part 10: `τ^*M_i ≃ M_i^*(1)` through the Weil pairing

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-conjugate-duality`, tex 2761–2808:

> Fix an actual complex conjugation `τ ∈ G_ℚ`, so that `τ² = 1`. … Conjugation acts on this
> ring-class group by inversion. Consequently `Ψ_i(τgτ⁻¹) = Ψ_i(g)⁻¹` … Then
> `ε^τ = ε = ε^{-1}` and `α_i^τ = α_i^{-1}`. Here `τ^*M_i` denotes pullback of the Galois action;
> it does not act on `R_i`. The Weil pairing gives the following `R_i`-linear perfect pairing:
> `M_i ⊗_{R_i} τ^*M_i → R_i(1)`, `(v,w) ↦ e_2(v, ρ_T(τ)w)`. Indeed `ρ_T(τ)² = 1`, the two scalar
> characters multiply to one, and `e_2` transforms by the cyclotomic character. Thus
> `τ^*M_i ≃ M_i^*(1)`. … In this convention `t` and every element of the group-ring basis are
> fixed.

All objects are genuine: the actual complex conjugation `τ` of `K̄` and the induced continuous
automorphism `c = conjGKS` of `G_{K,S}` (file `ConjStable.lean`, for `S` stable under
`τ|_K`), `ρ_T(τ)` acting on `E(K_S)[N]` through the coordinates (`conjTors`).

* `ActualConj K S`: an actual complex conjugation (`ι ∘ τ = conj ∘ ι` for an embedding
  `ι : K̄ → ℂ`), involutive, restricting to `κ` on `K`, with `S` `κ`-stable; `ActualConj.exists`
  (for imaginary quadratic `K`, PROVED in `ConjStable.lean`); `C.conj : G_{K,S} →ₜ* G_{K,S}`.
* `PullMod c M`: **`τ^*M`**, the pullback of the action along `c`; a discrete `G_{K,S}`-module.
* `conjTors`: **`ρ_T(τ)` on `E(K_S)[N]`**, `(x, y) ↦ (τx, τy)` for `W` defined over the fixed
  field of `κ` (`W.map κ = W`, e.g. `E_K` for `E/ℚ`); `conjTors_smul`: `ρ_T(τ)(σP) = c(σ)ρ_T(τ)P`;
  `conjTors_conjTors`: `ρ_T(τ)² = 1`.
* `conjToInv`: `w ↦ (id ⊗ ρ_T(τ))w`, **`τ^*M(α) ≃ M(α⁻¹)`** as discrete `G_{K,S}`-modules when
  `α ∘ c = α⁻¹` (`α_i^τ = α_i^{-1}`); it is `A`-linear (fixes `t` and the group-ring basis).
* **`conjDualEquiv`**: **`τ^*M_i ≃ M_i^*(1) = Hom_{A}(M_i, A(1))`**, an `A`-linear
  `G_{K,S}`-equivariant bijection (`conjDualEquiv_smul`), given by
  `w ↦ (v ↦ e(v, ρ_T(τ)w))` (`conjDualEquiv_apply`) — exactly the formula of tex 2765–2766.
* **`conjPairing`**: the perfect pairing `M_i × τ^*M_i → A(1)`, `(v, w) ↦ e(v, ρ_T(τ)w)`, in lane
  RC26's shape (`conjPairing_smul` = `hβ`; `conjPairing_bijective`, `conjPairing_flip_bijective`).
* `conjPerfectCoefficientPairing`: the same pairing in the other group's
  `PerfectCoefficientPairing` shape (values in `A` through `A(1) ≃ A` as `A`-modules).
* `quadChar_conj`, `alphaChar_conj`: `χ_h^τ = χ_h` (for rational `h`) and `α_i^τ = α_i^{-1}` from
  `ξ_i^τ = ξ_i^{-1}`.

Kinds: definitions and PROVED (perfectness from `FullTorsion`, GLUE).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside GaloisGroupS)
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open scoped WeierstrassCurve

/-! ### The pullback `τ^*M` -/

section Pull

variable {G : Type} [Group G] [TopologicalSpace G] (c : G →ₜ* G) (M : Type)

/-- **`τ^*M`**: `M` with the action pulled back along `c` (`σ ⋆ m = c(σ) • m`). -/
@[nolint unusedArguments]
def PullMod (_c : G →ₜ* G) (M : Type) : Type := M

variable [AddCommGroup M] [DistribMulAction G M] {A : Type} [CommRing A] [Module A M]
  [SMulCommClass G A M]

instance : AddCommGroup (PullMod c M) := inferInstanceAs (AddCommGroup M)

instance : Module A (PullMod c M) := inferInstanceAs (Module A M)

instance : DistribMulAction G (PullMod c M) where
  smul σ m := show M from c σ • (show M from m)
  one_smul m := by
    change c 1 • (show M from m) = m
    rw [map_one, one_smul]
  mul_smul σ τ m := by
    change c (σ * τ) • (show M from m) = c σ • (c τ • (show M from m))
    rw [map_mul, mul_smul]
  smul_zero σ := by
    change c σ • (0 : M) = 0
    exact smul_zero _
  smul_add σ m m' := by
    change c σ • ((show M from m) + (show M from m')) = c σ • (show M from m) + c σ • (show M from m')
    exact smul_add _ _ _

theorem PullMod.smul_def (σ : G) (m : PullMod c M) :
    (show M from σ • m) = c σ • (show M from m) := rfl

instance : SMulCommClass G A (PullMod c M) where
  smul_comm σ a m := smul_comm (c σ) a (show M from m)

instance [TopologicalSpace M] : TopologicalSpace (PullMod c M) :=
  inferInstanceAs (TopologicalSpace M)

instance [TopologicalSpace M] [DiscreteTopology M] : DiscreteTopology (PullMod c M) :=
  inferInstanceAs (DiscreteTopology M)

instance [TopologicalSpace M] [ContinuousAdd M] : ContinuousAdd (PullMod c M) :=
  inferInstanceAs (ContinuousAdd M)

/-- `τ^*M` is a discrete `G`-module (`c` is continuous). Kind: PROVED. -/
instance [TopologicalSpace M] [ContinuousSMul G M] : ContinuousSMul G (PullMod c M) :=
  ⟨(continuous_smul (M := G) (X := M)).comp (c.continuous.prodMap continuous_id)⟩

instance [Finite M] : Finite (PullMod c M) := inferInstanceAs (Finite M)

end Pull

/-! ### An actual complex conjugation acting on `G_{K,S}` -/

/-- **An actual complex conjugation** of `K̄` (for an embedding `ι : K̄ → ℂ`,
`ι ∘ τ = conj ∘ ι`), involutive, restricting to the automorphism `κ` of `K`, for a set `S` of
primes stable under `κ` (tex 2778: "Fix an actual complex conjugation `τ ∈ G_ℚ`, so that
`τ² = 1`"). -/
structure ActualConj (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) where
  /-- The embedding `K̄ → ℂ`. -/
  ι : AlgebraicClosure K →+* ℂ
  /-- The conjugation. -/
  τ : AlgebraicClosure K ≃+* AlgebraicClosure K
  /-- Its restriction to `K`. -/
  κ : K ≃+* K
  hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x)
  hι : ∀ x, ι (τ x) = starRingEnd ℂ (ι x)
  hinv : ∀ x, τ (τ x) = x
  hS : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Non-vacuity**: for an imaginary quadratic `K` and a set `S` stable under every automorphism
of `K` (e.g. the places above a set of rational primes, `isStable_comap_int`), an actual complex
conjugation exists, and it restricts to the nontrivial automorphism of `K`. Kind: PROVED. -/
theorem ActualConj.exists (h2 : Module.finrank ℚ K = 2) [IsTotallyComplex K]
    (hS : ∀ κ : K ≃+* K, ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S)) :
    ∃ C : ActualConj K S, C.κ ≠ RingEquiv.refl K := by
  obtain ⟨ι, τ, κ, hτ, hι, hinv, hκ, -, -⟩ := exists_conjGKS_of_imagQuad K h2 S hS
  exact ⟨⟨ι, τ, κ, hτ, hι, hinv, hS κ⟩, hκ⟩

namespace ActualConj

variable (C : ActualConj K S)

/-- `τ` restricted to `K_S` (`ConjStable.lean`'s `tauS`). -/
def tau : KS K S ≃+* KS K S := tauS K C.κ C.τ C.hτ S C.hS

theorem coe_tau (x : KS K S) : ((C.tau x : KS K S) : AlgebraicClosure K) = C.τ x :=
  tauS_apply K C.κ C.τ C.hτ S C.hS x

theorem tau_algebraMap (a : K) : C.tau (algebraMap K (KS K S) a) = algebraMap K (KS K S) (C.κ a) :=
  tauS_algebraMap K C.κ C.τ C.hτ S C.hS a

theorem tau_tau (x : KS K S) : C.tau (C.tau x) = x :=
  Subtype.ext (by rw [coe_tau, coe_tau, C.hinv])

/-- **The conjugation `c(σ) = τστ⁻¹` of `G_{K,S}`**, a continuous automorphism. -/
def conj : GKS K S →ₜ* GKS K S :=
  ⟨(conjGKS K C.κ C.τ C.hτ S C.hS).toMonoidHom, continuous_conjGKS K C.κ C.τ C.hτ S C.hS⟩

theorem conj_apply (σ : GKS K S) : C.conj σ = conjGKS K C.κ C.τ C.hτ S C.hS σ := rfl

theorem conj_conj (σ : GKS K S) : C.conj (C.conj σ) = σ :=
  conjGKS_conjGKS K C.κ C.τ C.hτ S C.hS C.hinv σ

/-- `c(σ)(τ x) = τ(σ x)`. Kind: PROVED. -/
theorem galS_conj_tau (σ : GKS K S) (x : KS K S) :
    galS K S (C.conj σ) (C.tau x) = C.tau (galS K S σ x) := by
  change C.tau (galS K S σ (C.tau.symm (C.tau x))) = C.tau (galS K S σ x)
  rw [RingEquiv.symm_apply_apply]

end ActualConj

/-! ### `ρ_T(τ)` on `E(K_S)[N]` -/

section ConjTors

variable (C : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W)

include hW in
/-- `W_{K_S}` is fixed by `τ` (its coefficients lie in the fixed field of `κ`). -/
theorem baseChange_map_tau :
    (W.baseChange (KS K S)).map (C.tau : KS K S →+* KS K S) = W.baseChange (KS K S) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  have : (C.tau : KS K S →+* KS K S).comp (algebraMap K (KS K S)) =
      (algebraMap K (KS K S)).comp (C.κ : K →+* K) :=
    RingHom.ext fun a => C.tau_algebraMap a
  rw [this, ← WeierstrassCurve.map_map, hW]

/-- **`ρ_T(τ)` on the points of `E` over `K_S`**: `(x, y) ↦ (τx, τy)` (Tau Ceti's point map
along a ring homomorphism, transported along `W.map τ = W`). -/
def conjPt : (W.baseChange (KS K S)).toAffine.Point →+ (W.baseChange (KS K S)).toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve (KS K S) => V.toAffine.Point)
      (baseChange_map_tau C W hW)).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Affine.Point.mapAlong (C.tau : KS K S →+* KS K S)
      (C.tau : KS K S →+* KS K S).injective) (Affine.Point.mapAlong_add _ _))

theorem conjPt_zero : conjPt C W hW 0 = 0 := map_zero _

include hW in
/-- The image of a nonsingular point under `τ` is nonsingular. -/
theorem conjNonsing {x y : KS K S} (h : (W.baseChange (KS K S)).toAffine.Nonsingular x y) :
    (W.baseChange (KS K S)).toAffine.Nonsingular (C.tau x) (C.tau y) :=
  (baseChange_map_tau C W hW) ▸
    (Affine.map_nonsingular (W.baseChange (KS K S)).toAffine C.tau.injective x y).mpr h

theorem conjPt_some {x y : KS K S} (h : (W.baseChange (KS K S)).toAffine.Nonsingular x y) :
    conjPt C W hW (.some x y h) = .some (C.tau x) (C.tau y) (conjNonsing C W hW h) := by
  change (AddEquiv.cast (M := fun V : WeierstrassCurve (KS K S) => V.toAffine.Point)
      (baseChange_map_tau C W hW)) (Affine.Point.mapAlong (C.tau : KS K S →+* KS K S)
        (C.tau : KS K S →+* KS K S).injective (.some x y h)) = _
  rw [Affine.Point.mapAlong_some, AddEquiv.cast_apply,
    Affine.Point.cast_some (baseChange_map_tau C W hW)]
  rfl

variable (N : ℤ)

/-- **`ρ_T(τ)` on `E(K_S)[N]`**. -/
def conjTors : TorsS K S W N →+ TorsS K S W N where
  toFun P := ⟨conjPt C W hW P.1, by
    have hP : N • P.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp P.2
    change conjPt C W hW P.1 ∈ Submodule.torsionBy ℤ _ N
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

theorem coe_conjTors (P : TorsS K S W N) :
    ((conjTors C W hW N P : TorsS K S W N) : (W.baseChange (KS K S)).toAffine.Point) =
      conjPt C W hW (P : (W.baseChange (KS K S)).toAffine.Point) := rfl

/-- **`ρ_T(τ)(σ P) = c(σ) ρ_T(τ) P`** (`ρ_T(τστ⁻¹) ρ_T(τ) = ρ_T(τ) ρ_T(σ)`). Kind: PROVED. -/
theorem conjTors_smul (σ : GKS K S) (P : TorsS K S W N) :
    conjTors C W hW N (σ • P) = C.conj σ • conjTors C W hW N P := by
  apply Subtype.ext
  rw [coe_conjTors, coe_smul_torsS, coe_smul_torsS, coe_conjTors]
  obtain ⟨P, hP⟩ := P
  change conjPt C W hW (Affine.Point.map (galS K S σ).toAlgHom P) =
    Affine.Point.map (galS K S (C.conj σ)).toAlgHom (conjPt C W hW P)
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, conjPt_zero, map_zero]
  · rw [conjPt_some, Affine.Point.map_some, Affine.Point.map_some, conjPt_some,
      Affine.Point.some.injEq]
    exact ⟨(C.galS_conj_tau σ x).symm, (C.galS_conj_tau σ y).symm⟩

/-- **`ρ_T(τ)² = 1`**. Kind: PROVED. -/
theorem conjTors_conjTors (P : TorsS K S W N) : conjTors C W hW N (conjTors C W hW N P) = P := by
  apply Subtype.ext
  rw [coe_conjTors, coe_conjTors]
  obtain ⟨P, hP⟩ := P
  change conjPt C W hW (conjPt C W hW P) = P
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, conjPt_zero, conjPt_zero]
  · rw [conjPt_some, conjPt_some, Affine.Point.some.injEq]
    exact ⟨C.tau_tau x, C.tau_tau y⟩

end ConjTors

/-! ### `τ^*M(α) ≃ M(α⁻¹)` and `τ^*M_i ≃ M_i^*(1)` -/

section ConjDual

variable (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hW : W.map (C.κ : K →+* K) = W) {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (A : Type) [CommRing A] [Algebra (ZMod N) A] (α : GKS K S →* Aˣ)

/-- `id ⊗ ρ_T(τ)` on `A ⊗ E(K_S)[N]`. -/
def conjBC : A ⊗[ℤ] TorsS K S W N →ₗ[A] A ⊗[ℤ] TorsS K S W N :=
  LinearMap.baseChange A (conjTors C W hW N).toIntLinearMap

theorem conjBC_tmul (a : A) (P : TorsS K S W N) :
    conjBC C W hW A (a ⊗ₜ P) = a ⊗ₜ conjTors C W hW N P := rfl

theorem conjBC_conjBC (x : A ⊗[ℤ] TorsS K S W N) : conjBC C W hW A (conjBC C W hW A x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a P => rw [conjBC_tmul, conjBC_tmul, conjTors_conjTors]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem conjBC_baseChangeAct (σ : GKS K S) (x : A ⊗[ℤ] TorsS K S W N) :
    conjBC C W hW A (baseChangeAct A _ (C.conj σ) x) = baseChangeAct A _ σ (conjBC C W hW A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a P =>
    rw [baseChangeAct_tmul, conjBC_tmul, conjBC_tmul, baseChangeAct_tmul, conjTors_smul, C.conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **`τ^*M(α) → M(α⁻¹)`, `w ↦ (id ⊗ ρ_T(τ)) w`** (`A`-linear: it fixes `t` and the group-ring
basis, tex 2766–2767). -/
def conjToInv :
    PullMod C.conj (CoefMod A α (TorsS K S W N)) →ₗ[A] CoefMod A (charInv α) (TorsS K S W N) :=
  conjBC C W hW A

/-- **`τ^*M(α) ≃ M(α⁻¹)` is `G_{K,S}`-equivariant when `α_i^τ = α_i^{-1}`** (tex 2795: "the two
scalar characters multiply to one"). Kind: PROVED. -/
theorem conjToInv_smul (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (σ : GKS K S)
    (w : PullMod C.conj (CoefMod A α (TorsS K S W N))) :
    conjToInv C W hW A α (σ • w) = σ • conjToInv C W hW A α w := by
  change conjBC C W hW A (((α (C.conj σ) : Aˣ) : A) •
      baseChangeAct A _ (C.conj σ) (show A ⊗[ℤ] TorsS K S W N from w)) =
    (((charInv α) σ : Aˣ) : A) • baseChangeAct A _ σ (conjBC C W hW A w)
  rw [map_smul, conjBC_baseChangeAct, hα σ, charInv_apply]

/-- `ρ_T(τ)² = 1`: `τ^*M(α) → M(α⁻¹)` is bijective. Kind: PROVED. -/
theorem conjToInv_bijective : Function.Bijective (conjToInv (N := N) C W hW A α) :=
  Function.bijective_iff_has_inverse.mpr ⟨conjBC C W hW A, conjBC_conjBC C W hW A,
    conjBC_conjBC C W hW A⟩

/-- **`τ^*M_i ≃ M_i^*(1) = Hom_A(M_i, A(1))`** (tex 2765, 2805), `A`-linear. -/
def conjDualEquiv (hFull : FullTorsion K S W N) :
    PullMod C.conj (CoefMod A α (TorsS K S W N)) ≃ₗ[A] DualM W hμ A α :=
  (LinearEquiv.ofBijective (conjToInv C W hW A α) (conjToInv_bijective C W hW A α)).trans
    (weilDualEquiv W hμ A α hFull)

/-- **The formula of tex 2765–2766**: `τ^*M_i → M_i^*(1)`, `w ↦ (v ↦ e(v, ρ_T(τ)w))`.
Kind: PROVED (definitional). -/
theorem conjDualEquiv_apply (hFull : FullTorsion K S W N)
    (w : PullMod C.conj (CoefMod A α (TorsS K S W N))) (v : CoefMod A α (TorsS K S W N)) :
    (show CoefMod A α (TorsS K S W N) →ₗ[A] Tate1 A hμ from conjDualEquiv C W hW hμ A α hFull w) v =
      weilPairingM W hμ A α v (conjToInv C W hW A α w) := rfl

/-- **`τ^*M_i ≃ M_i^*(1)` is an isomorphism of discrete `G_{K,S}`-modules** (equivariant).
Kind: PROVED. -/
theorem conjDualEquiv_smul (hFull : FullTorsion K S W N) (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)
    (σ : GKS K S) (w : PullMod C.conj (CoefMod A α (TorsS K S W N))) :
    conjDualEquiv C W hW hμ A α hFull (σ • w) = σ • conjDualEquiv C W hW hμ A α hFull w := by
  change weilDualEquiv W hμ A α hFull (conjToInv C W hW A α (σ • w)) = _
  rw [conjToInv_smul C W hW A α hα]
  exact weilDualEquiv_smul W hμ A α hFull σ _

/-- **The perfect pairing `M_i ⊗ τ^*M_i → A(1)`, `(v, w) ↦ e(v, ρ_T(τ)w)`** (tex 2798–2802), in
lane RC26's shape. -/
def conjPairing :
    CoefMod A α (TorsS K S W N) →ₗ[A] PullMod C.conj (CoefMod A α (TorsS K S W N)) →ₗ[A]
      Tate1 A hμ :=
  (weilPairingM W hμ A α).compl₂ (conjToInv C W hW A α)

theorem conjPairing_apply (v : CoefMod A α (TorsS K S W N))
    (w : PullMod C.conj (CoefMod A α (TorsS K S W N))) :
    conjPairing C W hW hμ A α v w = weilPairingM W hμ A α v (conjToInv C W hW A α w) := rfl

/-- **Equivariance** of the conjugate pairing (lane RC26's `hβ`). Kind: PROVED. -/
theorem conjPairing_smul (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (σ : GKS K S)
    (v : CoefMod A α (TorsS K S W N)) (w : PullMod C.conj (CoefMod A α (TorsS K S W N))) :
    conjPairing C W hW hμ A α (σ • v) (σ • w) = σ • conjPairing C W hW hμ A α v w := by
  rw [conjPairing_apply, conjToInv_smul C W hW A α hα, weilPairingM_smul]
  rfl

/-- **Perfectness** of the conjugate pairing (lane RC26's `hb`, `hb'`), under `FullTorsion`.
Kind: PROVED. -/
theorem conjPairing_bijective (hFull : FullTorsion K S W N) :
    Function.Bijective (conjPairing C W hW hμ A α) := by
  have h : ⇑(conjPairing C W hW hμ A α) =
      ⇑((LinearEquiv.ofBijective (conjToInv C W hW A α)
          (conjToInv_bijective C W hW A α)).symm.arrowCongr
          (LinearEquiv.refl A (Tate1 A hμ))) ∘ ⇑(weilPairingM W hμ A α) := by
    funext v
    refine LinearMap.ext fun w => ?_
    rfl
  rw [h]
  exact (LinearEquiv.bijective _).comp (weilPairingM_bijective W hμ A α hFull)

theorem conjPairing_flip_bijective (hFull : FullTorsion K S W N) :
    Function.Bijective (conjPairing C W hW hμ A α).flip := by
  have h : ⇑(conjPairing C W hW hμ A α).flip =
      ⇑(weilPairingM W hμ A α).flip ∘ ⇑(conjToInv C W hW A α) := by
    funext w
    rfl
  rw [h]
  exact (weilPairingM_flip_bijective W hμ A α hFull).comp (conjToInv_bijective C W hW A α)

/-- **The conjugate Weil pairing in the other group's `PerfectCoefficientPairing` shape**:
`M_i × τ^*M_i → A`, `(v, w) ↦ e(v, ρ_T(τ)w)` read in `A` through `A(1) ≃ A` (as `A`-modules), with
both adjoints bijective under `FullTorsion`. Kind: definition, perfectness PROVED. -/
def conjPerfectCoefficientPairing (hFull : FullTorsion K S W N) :
    ZInQ.Contrib.CloudB3RC53.SelmerDuality.PerfectCoefficientPairing A where
  M := ModuleCat.of A (CoefMod A α (TorsS K S W N))
  M' := ModuleCat.of A (PullMod C.conj (CoefMod A α (TorsS K S W N)))
  pair := (conjPairing C W hW hμ A α).compr₂ (CharMod.equiv A (cycA A hμ)).toLinearMap
  perfect_left := by
    have h : ⇑((conjPairing C W hW hμ A α).compr₂ (CharMod.equiv A (cycA A hμ)).toLinearMap) =
        ⇑((LinearEquiv.refl A (PullMod C.conj (CoefMod A α (TorsS K S W N)))).arrowCongr
          (CharMod.equiv A (cycA A hμ))) ∘ ⇑(conjPairing C W hW hμ A α) := by
      funext v
      exact LinearMap.ext fun w => rfl
    rw [h]
    exact (LinearEquiv.bijective _).comp (conjPairing_bijective C W hW hμ A α hFull)
  perfect_right := by
    have h : ⇑((conjPairing C W hW hμ A α).compr₂ (CharMod.equiv A (cycA A hμ)).toLinearMap).flip =
        ⇑((LinearEquiv.refl A (CoefMod A α (TorsS K S W N))).arrowCongr
          (CharMod.equiv A (cycA A hμ))) ∘ ⇑(conjPairing C W hW hμ A α).flip := by
      funext w
      exact LinearMap.ext fun v => rfl
    rw [h]
    exact (LinearEquiv.bijective _).comp (conjPairing_flip_bijective C W hW hμ A α hFull)

end ConjDual

/-! ### `χ_h^τ = χ_h` and `α_i^τ = α_i^{-1}` -/

section Chars

variable (C : ActualConj K S)

/-- **The quadratic character of a `κ`-fixed `h` is `τ`-invariant**: `χ_h(τστ⁻¹) = χ_h(σ)`
(tex 2792–2795: a rational quadratic character restricted to `G_K`). Kind: PROVED. -/
theorem quadChar_conj (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (hκh : C.κ h = h) (σ : GKS K S) : quadChar s hs hs0 (C.conj σ) = quadChar s hs hs0 σ := by
  -- `τ s = ±s`
  have hts : (C.tau s) ^ 2 = s ^ 2 := by
    rw [← map_pow, hs, C.tau_algebraMap, hκh]
  have hne := neg_ne_self_of_ne_zero s hs0
  have key : galS K S (C.conj σ) s = s ↔ galS K S σ s = s := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hts with h1 | h1
    · -- `τ s = s`
      have := C.galS_conj_tau σ s
      rw [h1] at this
      rw [this]
      constructor
      · intro h2
        have := congrArg C.tau h2
        rwa [C.tau_tau, h1] at this
      · intro h2; rw [h2, h1]
    · -- `τ s = -s`
      have := C.galS_conj_tau σ s
      rw [h1, map_neg] at this
      have hs' : galS K S (C.conj σ) s = -C.tau (galS K S σ s) := neg_eq_iff_eq_neg.mp this
      rw [hs']
      constructor
      · intro h2
        have h3 : C.tau (galS K S σ s) = -s := neg_eq_iff_eq_neg.mp h2
        have := congrArg C.tau h3
        rwa [C.tau_tau, map_neg, h1, neg_neg] at this
      · intro h2; rw [h2, h1, neg_neg]
  have hiff : ∀ σ' : GKS K S, quadChar s hs hs0 σ' = 1 ↔ galS K S σ' s = s := by
    intro σ'
    rw [quadChar_spec s hs hs0 σ']
    constructor
    · intro h1
      rw [h1, Units.val_one, one_smul]
    · intro h1
      rcases Int.units_eq_one_or (quadChar s hs hs0 σ') with h3 | h3
      · exact h3
      · rw [h3, Units.val_neg, Units.val_one, neg_smul, one_smul] at h1
        exact absurd h1 hne
  have hne1 : (-1 : ℤˣ) ≠ 1 := fun h1 => absurd (congrArg Units.val h1) (by norm_num)
  rcases Int.units_eq_one_or (quadChar s hs hs0 (C.conj σ)) with h1 | h1 <;>
    rcases Int.units_eq_one_or (quadChar s hs hs0 σ) with h2 | h2
  · rw [h1, h2]
  · exact absurd ((hiff σ).mpr (key.mp ((hiff _).mp h1))) (by rw [h2]; exact hne1)
  · exact absurd ((hiff _).mpr (key.mpr ((hiff σ).mp h2))) (by rw [h1]; exact hne1)
  · rw [h1, h2]

/-- **`α_i^τ = α_i^{-1}`** (tex 2786–2795) for `α_i = χ_h Ψ_i` with `h` fixed by `κ` and
`ξ_i(τστ⁻¹) = ξ_i(σ)^{-1}` ("conjugation acts on this ring-class group by inversion"). Kind:
PROVED. -/
theorem alphaChar_conj (i : ℕ) (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h)
    (hs0 : s ≠ 0) (hκh : C.κ h = h) (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i))))
    (hξ : ∀ σ, ξ (C.conj σ) = (ξ σ)⁻¹) (σ : GKS K S) :
    alphaChar i (quadChar s hs hs0) ξ (C.conj σ) = (alphaChar i (quadChar s hs hs0) ξ σ)⁻¹ := by
  have hq : (quadChar s hs hs0 σ)⁻¹ = quadChar s hs hs0 σ := by
    rcases Int.units_eq_one_or (quadChar s hs hs0 σ) with h1 | h1 <;> rw [h1] <;> rfl
  rw [alphaChar, charMul_apply, charMul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    quadChar_conj C s hs hs0 hκh,
    show movingCharS i ξ (C.conj σ) = (movingCharS i ξ σ)⁻¹ from
      movingCharS_conj i ξ C.conj.toMonoidHom hξ σ]
  have ha : (intUnitsTo (Acoef i) (quadChar s hs hs0 σ))⁻¹ =
      intUnitsTo (Acoef i) (quadChar s hs hs0 σ) := by
    rw [← map_inv, hq]
  calc intUnitsTo (Acoef i) (quadChar s hs hs0 σ) * (movingCharS i ξ σ)⁻¹
      = (intUnitsTo (Acoef i) (quadChar s hs hs0 σ))⁻¹ * (movingCharS i ξ σ)⁻¹ := by rw [ha]
    _ = (intUnitsTo (Acoef i) (quadChar s hs hs0 σ) * movingCharS i ξ σ)⁻¹ := by
      rw [mul_inv_rev]
      exact mul_comm (G := (Acoef i)ˣ) (intUnitsTo (Acoef i) (quadChar s hs hs0 σ))⁻¹
        (movingCharS i ξ σ)⁻¹

end Chars

end ZInQ.Manuscript.RC.CoefModules
