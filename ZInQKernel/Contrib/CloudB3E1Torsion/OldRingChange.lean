import ZInQKernel.Contrib.CloudB3E1Torsion.KummerRingChange
import ZInQKernel.Contrib.RC53Assist.ResidualBounds.StageBounds
import ZInQKernel.Contrib.CloudB3E2Norm.RingChangeResidual

/-!
# The standard old conditions along a ring isomorphism

Manuscript `diophantine_zq.tex`, tex 3413–3438, 4385–4414.

This continues `KummerRingChange.lean` (piece (3) of `GenCxResidualIso`).

* `kummerAtCond'` (definition): the Kummer conditions over `k` and over `k'` for two coefficient
  maps that agree pointwise.
* **`standardOldAtCond`** (definition, PROVED fields): the standard old condition `standardOldAt`
  (zero, full or Kummer, by label) over `k` against the same over `k'`.
* **`actualForm_residual`** (PROVED): for the actual-conditions Selmer complex (given old
  conditions, unramified at the new places) over local rings `k ≃ k'`, residual finiteness and
  ranks agree, from old-place `CondSEquiv`s (`actualForm_ringChange` with lane E2's
  `residualFinite_iff_of_ringEquiv`, `residualFinrank_eq_of_ringEquiv`).
* **`standardOld_residual`** (PROVED): the same for the standard old conditions, with no further
  input.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.ResidualBounds (standardOldAt)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt)
open IsLocalRing

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace k'] [DiscreteTopology k']
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [Module k' M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [SMulCommClass (GKS K S₀) k' M₀] [TopologicalSpace M₀]
  [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  (hV : ∀ (r : k) (m : M₀), r • m = e r • m)

/-- **The Kummer conditions for two pointwise equal coefficient maps.** Kind: definition. -/
def kummerAtCond' (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι₁ ι₂ : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) (InflMod hS M₀))
    (hι₁ : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι₁ (σ • t) = σ • ι₁ t)
    (hι₂ : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι₂ (σ • t) = σ • ι₂ t)
    (h : ∀ t, ι₁ t = ι₂ t) :
    CondSEquiv hS e M₀ hV v (kummerAt (k := k) v B m ι₁ hι₁) (kummerAt (k := k') v B m ι₂ hι₂) := by
  obtain rfl : ι₁ = ι₂ := AddMonoidHom.ext h
  exact kummerAtCond hS e M₀ hV v B m ι₁ hι₁

/-- **The standard old condition over `k` against the same over `k'`** (same label, curve,
level and coefficient map). Kind: definition (PROVED fields). -/
def standardOldAtCond (v : Places K S) [DecidableEq (v.1.adicCompletion K)] (label : ℕ)
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) (InflMod hS M₀))
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t) :
    CondSEquiv hS e M₀ hV v (standardOldAt K S k (InflMod hS M₀) v label B m ι hι)
      (standardOldAt K S k' (InflMod hS M₀) v label B m ι hι) := by
  unfold standardOldAt
  split_ifs
  · exact zeroAtCond hS e M₀ hV v
  · exact fullAtCond hS e M₀ hV v
  · exact kummerAtCond hS e M₀ hV v B m ι hι

variable {hS e M₀ hV}

/-- **Residual cohomology of the actual-conditions Selmer complex along a ring isomorphism**
(tex 4385–4414): with old-place condition isomorphisms, the residual cohomology of
`selCx (galoisSelData … (ofCondAt (urOutside c)))` over the local ring `k` is finite iff that over
`k'` is, with the same rank. Kind: PROVED. -/
theorem actualForm_residual [IsLocalRing k] [IsLocalRing k']
    {c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k (InflMod hS M₀) v}
    {c' : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k' (InflMod hS M₀) v}
    (EU : ∀ v h, CondSEquiv hS e M₀ hV v (c v h) (c' v h)) (n : ℤ) :
    (Module.Finite (ResidueField k) (residualCohomologyAt (selCx (galoisSelData K S k
        (InflMod hS M₀) (ofCondAt K S k (InflMod hS M₀) (urOutside hS k M₀ c)))) n) ↔
      Module.Finite (ResidueField k') (residualCohomologyAt (selCx (galoisSelData K S k'
        (InflMod hS M₀) (ofCondAt K S k' (InflMod hS M₀) (urOutside hS k' M₀ c')))) n)) ∧
    Module.finrank (ResidueField k) (residualCohomologyAt (selCx (galoisSelData K S k
        (InflMod hS M₀) (ofCondAt K S k (InflMod hS M₀) (urOutside hS k M₀ c)))) n) =
      Module.finrank (ResidueField k') (residualCohomologyAt (selCx (galoisSelData K S k'
        (InflMod hS M₀) (ofCondAt K S k' (InflMod hS M₀) (urOutside hS k' M₀ c')))) n) := by
  obtain ⟨fR, hfR, hdR⟩ := actualForm_ringChange EU
  exact ⟨ZInQ.Contrib.CloudB3E2.St0Shape.residualFinite_iff_of_ringEquiv e fR hfR hdR n,
    ZInQ.Contrib.CloudB3E2.St0Shape.residualFinrank_eq_of_ringEquiv e fR hfR hdR n⟩

/-- **The standard old Selmer complexes over `k` and over `k'`**: the same residual finiteness
and ranks, for the same labels, curves, level and coefficient maps at the old places.
Kind: PROVED. -/
theorem standardOld_residual (e : k ≃+* k') (hV : ∀ (r : k) (m : M₀), r • m = e r • m)
    [IsLocalRing k] [IsLocalRing k']
    [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)] (label : Places K S → ℕ)
    (B : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (m : ℕ) [NeZero m]
    (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) m →+
      ResMod (locMap K S v.1) (InflMod hS M₀))
    (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι v (σ • t) = σ • ι v t) (n : ℤ) :
    (Module.Finite (ResidueField k) (residualCohomologyAt (selCx (galoisSelData K S k
        (InflMod hS M₀) (ofCondAt K S k (InflMod hS M₀) (urOutside hS k M₀
          (fun v _ => standardOldAt K S k (InflMod hS M₀) v (label v) (B v) m (ι v) (hι v)))))) n) ↔
      Module.Finite (ResidueField k') (residualCohomologyAt (selCx (galoisSelData K S k'
        (InflMod hS M₀) (ofCondAt K S k' (InflMod hS M₀) (urOutside hS k' M₀
          (fun v _ => standardOldAt K S k' (InflMod hS M₀) v (label v) (B v) m (ι v)
            (hι v)))))) n)) ∧
    Module.finrank (ResidueField k) (residualCohomologyAt (selCx (galoisSelData K S k
        (InflMod hS M₀) (ofCondAt K S k (InflMod hS M₀) (urOutside hS k M₀
          (fun v _ => standardOldAt K S k (InflMod hS M₀) v (label v) (B v) m (ι v) (hι v)))))) n) =
      Module.finrank (ResidueField k') (residualCohomologyAt (selCx (galoisSelData K S k'
        (InflMod hS M₀) (ofCondAt K S k' (InflMod hS M₀) (urOutside hS k' M₀
          (fun v _ => standardOldAt K S k' (InflMod hS M₀) v (label v) (B v) m (ι v)
            (hι v)))))) n) :=
  actualForm_residual (fun v _ => standardOldAtCond hS e M₀ hV v (label v) (B v) m (ι v) (hι v)) n

end ZInQ.Contrib.CloudB3E1Torsion
