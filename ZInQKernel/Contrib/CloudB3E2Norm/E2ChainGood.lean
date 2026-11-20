import ZInQKernel.Contrib.CloudB3E2Norm.E2ChainActual

/-!
# Good reduction of the actual curve outside the stage support

Manuscript `diophantine_zq.tex`, tex 2729–2741, 2836–2838.

The actual curve `E_ℓ : y² = x³ + 2ℓx² − 3ℓ²x` is the base change of the integral equation
`W₀ = [0, 2ℓ, 0, −3ℓ², 0]` over `ℤ`, with discriminant `Δ(W₀) = 2⁸·3²·ℓ⁶` (`intCurve_Δ`). So it
has good reduction at every place not above `6ℓ` (`hasGoodReductionAt_of_not_mem`, from the tree's
`hasGoodReductionAt_baseChange`).

* **`hgood_of_support`** (PROVED): the input `hgood` of `e2ChainInputsS_of_actual` — good
  reduction outside the stage support — from the places above `2` being in the support (derived
  from `E[2^∞]` rational over `K_{S₀}`) and the named hypothesis `h3ℓ`: the places above `3ℓ` lie
  in the stage support. The text states that the support contains the primes above `N`
  (tex 2729–2741); `h3ℓ` replaces `N` by the explicit `3ℓ` (the primes of `Δ(W₀)` other than
  `2`): a formalization requirement (the tree decides neither `3 ∣ N(E_ℓ)` nor the primes of `ℓ`
  dividing `N`).
* **`e2ChainInputsS_of_actual'`** (definition): the chain inputs with `h3ℓ` in place of `hgood`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.ChainActual

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.PrintsArith (Qbar CCLThm2_15Applied)
open ZInQ.Contrib.CloudB3E2.NormCochain (CSTParam FullAnchor)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Manuscript.RC.CoefModules (acoefTop acoefTop_discrete)
open ZInQ.Contrib.CloudB3E2.NormCochain (stageIsoA)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)

/-- **The integral equation of the actual curve**, `[0, 2ℓ, 0, −3ℓ², 0]` over `ℤ`.
Kind: definition. -/
def intCurve (ℓ : ℕ) : WeierstrassCurve ℤ := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

/-- `Δ = 2⁸·3²·ℓ⁶` (PROVED). -/
theorem intCurve_Δ (ℓ : ℕ) : (intCurve ℓ).Δ = 2 ^ 8 * 3 ^ 2 * (ℓ : ℤ) ^ 6 := by
  simp only [intCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The actual curve is the base change of the integral equation (PROVED). -/
theorem ecurve_eq (ℓ : ℕ) : Ecurve ℓ = (intCurve ℓ).baseChange ℚ := by
  ext <;> simp [intCurve, Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]

variable {K : Type} [Field K] [NumberField K]

/-- `E_ℓ / K` is the base change of the integral equation (PROVED). -/
theorem ecurve_baseChange_eq (ℓ : ℕ) :
    (Ecurve ℓ).baseChange K = (intCurve ℓ).baseChange K := by
  rw [ecurve_eq, WeierstrassCurve.baseChange, WeierstrassCurve.baseChange,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- **Good reduction at every place not above `6ℓ`** (PROVED). -/
theorem hasGoodReductionAt_of_not_mem (ℓ : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (h2 : (2 : 𝓞 K) ∉ v.asIdeal) (h3ℓ : ((3 * ℓ : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange K) v := by
  rw [ecurve_baseChange_eq]
  apply ZInQ.Manuscript.RC.DivisionPoints.hasGoodReductionAt_baseChange
  rw [intCurve_Δ]
  intro hmem
  rw [Nat.cast_mul, Nat.cast_ofNat] at h3ℓ
  have h3 : (3 : 𝓞 K) ∉ v.asIdeal := fun h => h3ℓ (v.asIdeal.mul_mem_right _ h)
  have hl : (ℓ : 𝓞 K) ∉ v.asIdeal := fun h => h3ℓ (v.asIdeal.mul_mem_left _ h)
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_ofNat, map_ofNat, map_natCast] at hmem
  rcases v.isPrime.mem_or_mem hmem with h | h
  · rcases v.isPrime.mem_or_mem h with h' | h'
    · exact h2 (v.isPrime.mem_of_pow_mem _ h')
    · exact h3 (v.isPrime.mem_of_pow_mem _ h')
  · exact hl (v.isPrime.mem_of_pow_mem _ h)

/-! ### The input `hgood` of the chain -/

section Chain

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}

attribute [local instance] acoefTop acoefTop_discrete stageIsoA

/-- **`hgood` from the stage support** (PROVED): good reduction of `E_ℓ` outside the stage
support, from the places above `2` (in the support, as `E[2^∞]` is rational over `K_{S₀}`) and
`h3ℓ`: the places above `3ℓ` lie in the stage support.

About `h3ℓ`: the text's support contains the primes above `N` (tex 2729–2741), and `2` is
covered by full `2`-power torsion. At the primes `p ∤ 6` of `ℓ` the equation reduces to the cusp
`y² = x³`, so they are expected to divide `N`; at `3` it is open. Neither is decided by the tree
(its `newformLevel` is the least level of a cusp form with the coefficients of `L(E, s)`; no
conductor computation is formalized), so `h3ℓ` is a formalization requirement, the text's
inclusion read at the explicit primes of `Δ(W₀)`. -/
theorem hgood_of_support (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ)
    (h3ℓ : ∀ v : HeightOneSpectrum (𝓞 C.K), ((3 * ℓ : ℕ) : 𝓞 C.K) ∈ v.asIdeal →
      v ∈ P.S₀ (t + 1)) :
    ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ P.S₀ (t + 1) →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v := by
  intro v hv
  have := P.full (t + 1)
  have h2 : ∀ w : HeightOneSpectrum (𝓞 C.K), (2 : 𝓞 C.K) ∈ w.asIdeal → w ∈ P.S₀ (t + 1) :=
    ZInQ.Contrib.CloudB3RC53.Finiteness.h2_of_hasFullTwoTorsion_proof ((Ecurve ℓ).baseChange C.K)
  exact hasGoodReductionAt_of_not_mem ℓ v (fun h => hv (h2 v h)) (fun h => hv (h3ℓ v h))

/-- **The actual chain inputs with `h3ℓ` in place of `hgood`** (tex 2729–2741): as
`e2ChainInputsS_of_actual`, with good reduction outside the stage support derived
(`hgood_of_support`). Kind: definition. -/
def e2ChainInputsS_of_actual' (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ)
    (cp : CSTParam (Ecurve ℓ)) (emb : Qbar →ₐ[ℚ] ℂ) (κ : Qbar ≃ₐ[ℚ] AlgebraicClosure C.K)
    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
    (St : RCSteps D) (hodd : ¬ D.OddEmptyUnit) (hAdm : Fam.Admissible D.S D.kfin)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    (hrk : ¬ ((G.r (t + 1) : ℕ) : ℤ) ∣ D.kfin)
    (hQS0 : ∀ q ∈ Fam.Q, Fam.lam q x = 1 → ∀ v : HeightOneSpectrum (𝓞 C.K),
      ((q : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ (t + 1))
    (hpidx : ∀ p : P.ι, ∃ j < P.ps.length, P.pidx j = p) (hQ3 : ∀ q ∈ unusedAt Fam x, q ≠ 3)
    (h3ℓ : ∀ v : HeightOneSpectrum (𝓞 C.K), ((3 * ℓ : ℕ) : 𝓞 C.K) ∈ v.asIdeal →
      v ∈ P.S₀ (t + 1)) :
    E2ChainInputsS P t :=
  e2ChainInputsS_of_actual P t cp emb κ print St hodd hAdm hS2N hrk hQS0 hpidx hQ3
    (hgood_of_support P t h3ℓ)

end Chain

end ZInQ.Contrib.CloudB3E2.ChainActual
