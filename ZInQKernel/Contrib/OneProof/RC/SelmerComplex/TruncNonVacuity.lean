import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncReverse
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.H0Condition

/-!
# Lane RC26 (round 4): non-vacuity of the `τ≥2` restatement

Manuscript `diophantine_zq.tex`, tex 3471–3481 (unramified conditions), tex 4479–4480 (the residual
module `W = 𝔽₂²`), tex 5068–5072 (conditions in degrees `0` and `0, 1`); Nekovář, *Selmer
complexes* (Astérisque 310), 6.1–6.3.

* `h0UnramifiedTruncIsotropy`: for any coefficient pairing, the zero homotopies are `τ≥2` isotropy
  data for the `H⁰` conditions (degree `0`) against the unramified conditions (degrees `0, 1`) —
  the shape of the text's derivative conditions, where the local product lands in degrees `≤ 1`;
  an untruncated null-homotopy would have to kill the degree-one cup products `ι u ∪ ι' v` (the
  other group's `exUntruncated_fails` for the model);
* `h0UnramifiedPairDataT`: the corresponding genuine Selmer pairing data over `τ≥2`;
* `exSwitchTruncIsotropy`: truncated isotropy data with the reverse field for the round-2 genuine
  switch example (strict conditions zero, so `StrictSymm` is automatic).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts


variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

section Generic

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {R : Type} [CommRing R] [TopologicalSpace R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  (X : ∀ w : Places K S, TopRep.{0} R (GUr K w.1))
  [∀ w, ContinuousSMul (GUr K w.1) (X w).V] [∀ w, DiscreteTopology (X w).V] [∀ w, Finite (X w).V]
  (f : ∀ w, (X w).V →ₗ[R] M')
  (hf : ∀ w (g : Gloc K w.1) (x : (X w).V), f w (resUr K w.1 g • x) = locMap K S w.1 g • f w x)

/-- **Non-vacuity of `τ≥2` isotropy data for a pair of nonzero conditions**: the zero homotopies
for the `H⁰` conditions on `M` (degree `0`) against the unramified conditions on `M'`
(degrees `0, 1`), for any coefficient pairing (Nekovář 6.2–6.3; tex 5068–5072). PROVED. -/
def h0UnramifiedTruncIsotropy :
    GaloisTruncIsotropyData K S R β hβ (galoisH0Conditions K S R M)
      (allUnramifiedLocalConditions K S X f hf) :=
  TruncIsotropyData.ofLowDegree (h0_unramified_degrees K S M X f hf)

/-- **Genuine Selmer pairing data over `τ≥2`** for the `H⁰` conditions against the unramified
conditions. -/
abbrev h0UnramifiedPairDataT :
    SelPairData (galoisSelData K S R M (galoisH0Conditions K S R M))
      (galoisSelData K S R M' (allUnramifiedLocalConditions K S X f hf)) :=
  galoisPairDataT K S R β hβ _ _ (h0UnramifiedTruncIsotropy K S β hβ X f hf)

end Generic

section Switch

variable (q : HeightOneSpectrum (𝓞 K)) (k : Type) [Field k]

/-- **Non-vacuity of `SwitchTruncIsotropy`** for the round-2 genuine switch example (zero strict
conditions, zero pairing on the trivial module): the reverse field comes from
`SwitchTruncIsotropy.ofStrictDegreeZero` (PROVED, no GLUE). -/
def exSwitchTruncIsotropy :
    SwitchTruncIsotropy (exGenuineSwitch K q (k := k))
      (0 : TrivMod (GKS K {q}) PUnit →ₗ[k] TrivMod (GKS K {q}) PUnit →ₗ[k] TrivMod (GKS K {q}) PUnit)
      (fun _ _ _ => rfl) :=
  SwitchTruncIsotropy.ofStrictDegreeZero _ _ _
    (TruncIsotropyData.ofLowDegree fun _ _ _ _ => Or.inl ⟨fun _ _ => rfl⟩) 1
    (fun _ _ => rfl) (fun _ => ⟨fun _ _ => rfl⟩)

end Switch

end ZInQ.Manuscript.RC.SelmerComplex
