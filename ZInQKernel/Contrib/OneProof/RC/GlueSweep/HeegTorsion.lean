import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegInfRes
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegAdjusted

/-!
# Lane RC22 (glue sweep), share Heeg: the Galois instances for an elliptic curve

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner`, tex 2992–3032,
3064–3081 and 3122–3190.

The general bridges `H7_H11_genuine` and `H19_assembled_adjusted` (files `HeegInfRes`,
`HeegAdjusted`) specialized to the Kummer sequence `0 → E[2^a] → E → E → 0` of an elliptic curve
`E/K` over the absolute Galois group `G_K` (Tau Ceti's `kummerShortExact`, `2^a` invertible in `K`),
as the `CloudB3RC53` layer does for its interfaces (`kummerSequenceTorsion`,
`infResInputTorsion`).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- The second map of Tau Ceti's Kummer sequence `0 → E[2^a] → E → E → 0` is multiplication by
`2^a` (integer form), `PROVED` (as in `kummerSequenceTorsion` of the `CloudB3RC53` layer). -/
theorem kummerShortExact_proj (a : ℕ) (h2 : IsUnit ((2 ^ a : ℕ) : K)) (b : W.PointCoeff) :
    (W.kummerShortExact (2 ^ a) h2).proj b = ((2 : ℤ) ^ a) • b := by
  show (2 ^ a : ℕ) • b = _
  rw [← natCast_zsmul]; push_cast; rfl

/-- **(H7) and (H8)–(H11) for an elliptic curve over genuine Galois cohomology**, tex 2992–3032
and 3064–3081.  Kind: `PROVED`, from the remaining hypotheses: an elliptic curve `E/K` (for
`K = H_f`), `2^a` invertible in `K`, a closed normal subgroup `N` of `G_K` (for `G_{M_I}`), (H2) as
"`2^e` kills the `N`-fixed points of `E[2^a]`", RC10's `DerivativeInput` over `G_K ⧸ N` acting on
`E(K^sep)^N` (for `E(M_I)`), and (H12) at every prime of `I`.  With `x = D_I y_{f n_I}`:
`c_{I,a} = δ_a(C_π x)` is a `G_K/N`-invariant class of `H¹(N, E[2^a])`, and
`b_{I,a} = m₀ C_bad d_a(c_{I,a}) ∈ H¹(G_K, E[2^a])` restricts to `δ_a(L x)`,
`L = m₀ C_π C_bad 2^{2e}`.

Consumers: `ZInQ.Manuscript.RC.HeegnerAlgebra.H7_assembled`, `.H11_assembled` (lane RC10).
Dischargers: `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.kummerSequenceGenuine`,
`.infResInputGenuine` (through `H7_H11_genuine`) with Tau Ceti's `kummerShortExact`. -/
theorem H7_H11_torsion (a e : ℕ) (h2 : IsUnit ((2 ^ a : ℕ) : K))
    (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal]
    (hN : IsClosed (N : Set (TauCeti.AbsoluteGaloisGroup K)))
    (hH2 : ∀ P : W.TorsionCoeff (2 ^ a), (∀ σ : N, σ • P = P) → ((2 : ℤ) ^ e) • P = 0)
    {ι 𝒜 : Type*} [DecidableEq ι] [CommRing 𝒜] [Module 𝒜 (H0 N W.PointCoeff)]
    (I : Finset ι) (Din : DerivativeInput ι 𝒜 (TauCeti.AbsoluteGaloisGroup K ⧸ N)
      (H0 N W.PointCoeff) I)
    (hH12 : ∀ i ∈ I, (2 : ℤ) ^ (a + 1) ∣ Din.aℓ i ∧ (2 : ℤ) ^ (a + 1) ∣ Din.ℓnum i + 1)
    (m0 Cπ Cbad : ℕ) :
    ∃ c : H1ConjInvariants (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N,
      (c : H1 N (W.TorsionCoeff (2 ^ a))) =
        ((W.kummerShortExact (2 ^ a) h2).restrict N).explicitDelta0
          ((Cπ : ℤ) • ((∏ j ∈ I, Din.D j) • Din.y I)) ∧
      (explicitResConj1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N
          (((m0 * Cbad : ℕ) : ℤ) •
            (fiveTermGenuine (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N hN).descend
              e (infResInputGenuine (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N hN
                e hH2).killD c) :
          H1 N (W.TorsionCoeff (2 ^ a))) =
        ((W.kummerShortExact (2 ^ a) h2).restrict N).explicitDelta0
          (Lmult m0 Cπ Cbad e • ((∏ j ∈ I, Din.D j) • Din.y I)) :=
  H7_H11_genuine (TauCeti.AbsoluteGaloisGroup K) N hN a e (W.kummerShortExact (2 ^ a) h2)
    (kummerShortExact_proj W a h2) hH2 I Din hH12 m0 Cπ Cbad

/-- **(H16)–(H19) for an elliptic curve, adjusted representative discharged**, tex 3122–3190.
Kind: `PROVED`, from the remaining hypotheses: an elliptic curve `E/K` (for `K = H_f`), `2^a`
invertible in `K`, a normal subgroup `N` of `G_K` (for `G_{H_{f n_I ℓ}}`), a class
`v ∈ H¹(G_K, E[2^a])` (for `b_{I∪ℓ,a}`) whose restriction to `N` is the Kummer class of the
`N`-invariant point `x' = L D_ℓ Y`, and the fields of RC10's `DerivativePrimeInput` other than
`cocycle`, `tors`, `kummer_upper` (see `H19_assembled_adjusted`).  Conclusion: some cocycle `b₀`
represents `v` and, with `b = S.incl ∘ b₀` (values in `E[2^a] ⊆ E(K^sep)`), the singular coordinate
of `b` at the derivative place is `J` applied to `f_old = (F² - 1) Q̄` at precision `2^m`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.H19_assembled` (lane RC10).  Discharger:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.exists_adjusted_rep` (through
`H19_assembled_adjusted`). -/
theorem H19_assembled_adjusted_torsion (a : ℕ) (h2 : IsUnit ((2 ^ a : ℕ) : K))
    (N : Subgroup (TauCeti.AbsoluteGaloisGroup K)) [N.Normal]
    (v : H1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a))) (x' : H0 N W.PointCoeff)
    (hv : explicitRes1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)) N v =
      ((W.kummerShortExact (2 ^ a) h2).restrict N).explicitDelta0 x')
    {Vb : Type*} [AddCommGroup Vb] (σ : TauCeti.AbsoluteGaloisGroup K) (ℓ e m : ℕ)
    (L aℓ u' v' : ℤ) (X Y Z Q : W.PointCoeff)
    (hx' : (x' : W.PointCoeff) = L • Dact σ ℓ Y)
    (hZ : ((2 : ℤ) ^ a) • Z = L • Dact σ ℓ Y) (hQ : ((2 : ℤ) ^ a) • Q = L • X)
    (hY : σ ^ (ℓ + 1) • Y = Y) (hTr : Tract σ ℓ Y = aℓ • X)
    (hXfix : ∀ h ∈ N, h • X = X) (hYfix : ∀ h ∈ N, h • Y = Y)
    (hH2 : ∀ P : W.PointCoeff, (∀ h ∈ N, h • P = P) → (∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) →
      ((2 : ℤ) ^ e) • P = 0)
    (hu' : (ℓ : ℤ) + 1 = 2 ^ a * u') (hv' : aℓ = 2 ^ a * v')
    (red : W.PointCoeff →+ Vb) (F J : Vb →+ Vb) (hinert : red (σ • Z) = red Z)
    (hYX : red Y = F (red X)) (hXF : F (F (red X)) = red X)
    (hchar : ∀ w : Vb, F (F w) - aℓ • F w + (ℓ : ℤ) • w = 0)
    (hJ : ∀ w : Vb, ((2 : ℤ) ^ a) • w = 0 → F w - aℓ • w = J w) (hm : e ≤ a - m) :
    ∃ b₀ : Z1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a)),
      (b₀ : H1 (TauCeti.AbsoluteGaloisGroup K) (W.TorsionCoeff (2 ^ a))) = v ∧
      ((2 : ℤ) ^ (a - m)) •
          red ((W.kummerShortExact (2 ^ a) h2).incl
            ((b₀ : TauCeti.AbsoluteGaloisGroup K → W.TorsionCoeff (2 ^ a)) σ)) =
        J (((2 : ℤ) ^ (a - m)) • (F (F (red Q)) - red Q)) :=
  H19_assembled_adjusted a (W.kummerShortExact (2 ^ a) h2) (kummerShortExact_proj W a h2) N v x'
    hv σ ℓ e m L aℓ u' v' X Y Z Q hx' hZ hQ hY hTr hXfix hYfix hH2 hu' hv' red F J hinert hYX hXF
    hchar hJ hm

end ZInQ.Manuscript.RC.GlueSweep.Heeg
