import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Collapse

/-!
# Lane RC28 (coefficient modules), part 13: the Kummer condition at the actual modules

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-local-kummer` (tex 3413–3468), with the
coefficient extension at tex 3430–3438 ("derived coefficient extension defines the scalar `A_i`
condition") and (4.3) at tex 3455–3463.

* `kummerAt`: **the Kummer condition from `B(K_v)`** at one place `v ∈ S`, for an elliptic curve
  `B` over `K_v` (the twist `E^{(h)}` in the text) and a `G_{K_v}`-equivariant coefficient map
  `ι : B(K̄_v)[m] → M` (`M` with `G_{K_v}` acting through the localization): the condition
  `kummerConditionIn` of `Kummer.lean` (`U⁰ = C⁰`, `U¹ = (span of the extended Kummer cocycles) +
  B¹`, `Uⁿ = 0`; `H⁰ = B(K_v)[m]` and `H¹ = B(K_v)/mB(K_v)` for identity coefficients),
  in this lane's per-place format `CondAt`; `kummerAt_isInjective`.
* `kummerActualConditions`: **the actual local conditions of (4.3)** at `M_i`: the Kummer
  condition at the places of the coefficient support `S₀` (the places above `2N`, the moving prime
  and the twist), the unramified condition at `S − S₀`; `isGaloisSelData_kummerActual`: genuine
  Galois Selmer data in the leaf's sense.

GLUE input (not built here): the coefficient maps `ι_v : E^{(h)}(K̄_v)[2^i] → M_i` — the twist
identification `E^{(h)}[2^i] ≅ E[2^i](χ_h)` over `K̄_v`, the comparison of `E(K̄_v)[2^i]` with
`E(K_S)[2^i]` along an embedding `K_S → K̄_v` (a choice of decomposition group), and `t ↦ 1 ⊗ t`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Wiring (IsGaloisSelData)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

section At

variable {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

/-- **The Kummer condition from `B(K_v)` at a place `v ∈ S`** (tex 3413–3438), with coefficients
extended along a `G_{K_v}`-equivariant map `ι : B(K̄_v)[m] → M`. -/
def kummerAt (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t) :
    CondAt K S k M v :=
  ⟨kummerConditionIn k ι hι, kummerConditionInι k ι hι⟩

/-- The Kummer condition is a subcomplex of the local cochains. Kind: PROVED. -/
theorem kummerAt_isInjective (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t) :
    (kummerAt (k := k) v B m ι hι).IsInjective :=
  fun n => kummerConditionInι_injective k ι hι n

end At

section Actual

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
  (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i α))
  (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i)),
    ι v (σ • t) = σ • ι v t)

/-- **The actual Kummer-type Selmer data (4.3) at `M_i`**: the Kummer condition from `B_v(K_v)`
(`B_v = E^{(h)}` over `K_v`) at the places of the coefficient support `S₀`, the unramified
condition at the new places `S − S₀` (tex 3455–3463, 3483–3498). -/
def kummerActualSelData : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (Acoef i) :=
  actualSelData hS W i α (fun v _ => kummerAt v (B v) (2 ^ i) (ι v) (hι v))

/-- **The actual Kummer-type Selmer data are genuine Galois Selmer data** (`IsGaloisSelData`, the
leaf's predicate) for finite `S`. Kind: PROVED. -/
theorem isGaloisSelData_kummerActual (hSfin : S.Finite) :
    IsGaloisSelData (kummerActualSelData hS W i α B ι hι) :=
  isGaloisSelData_actual hS hSfin W i α _ fun v _ => kummerAt_isInjective v (B v) (2 ^ i) (ι v) (hι v)

end Actual

end ZInQ.Manuscript.RC.CoefModules
