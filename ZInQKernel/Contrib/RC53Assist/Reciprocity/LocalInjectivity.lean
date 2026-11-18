import ZInQKernel.Contrib.RC53Assist.Reciprocity.LocalCompatibility
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CompKummer

/-!
# Reciprocity without the local injectivity input

The local input of `reciprocityAt_from_sumFormula`, injectivity of
`H²(K_q, μ₂) → Br K_q`, is the theorem `ZInQ.Manuscript.RC.KummerMaps.compKummerToBr_injective`
(`ZInQKernel/Contrib/OneProof/RC/KummerMaps/CompKummer.lean`, Hilbert 90), since `2` is a unit in
the completion `K_q`, a field of characteristic zero. This holds at every finite place, including
the places above `2`.
-/

namespace ZInQ.Contrib.RC53Assist.Reciprocity

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex TauCeti.ContCohomology
  TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  (D : SquareRootCoefficients K S M)

/-- PROVED. The Kummer-Brauer map `H²(K_q, μ₂) → Br K_q` is injective at every finite place `q`
(Hilbert 90 through `compKummerToBr_injective`; `2` is a unit in the characteristic-zero
field `K_q`). -/
theorem kummerToBr_two_injective (q : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.adicCompletion K) 2) :=
  ZInQ.Manuscript.RC.KummerMaps.compKummerToBr_injective _ 2
    (isUnit_iff_ne_zero.mpr (by norm_num))

/-- PROVED. `reciprocityAt_from_sumFormula` with its local injectivity input
discharged by `kummerToBr_two_injective`: for a totally complex number field and a global map
with its defining construction property, the reciprocity statement holds at every place of `S`. -/
theorem reciprocityAt_from_canonical (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hcanonical : GlobalBrauerConstructionCanonical K S D toBrauer)
    (q : Places K S) :
    let T := TrivMod (GKS K S) (ZMod 2)
    let E := globalCx (ZMod 2) (GKS K S) T
    let A := localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    let R := resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    ∀ e : E.X 2, E.d 2 3 rfl e = 0 →
      (∀ v : Places K S, v ≠ q → ∃ y : (A v).X 1, (A v).d 1 2 rfl y = R.f 2 2 rfl e v) →
      ∃ y : (A q).X 1, (A q).d 1 2 rfl y = R.f 2 2 rfl e q :=
  reciprocityAt_from_sumFormula K S D hK toBrauer hcanonical q (kummerToBr_two_injective K q.1)

end ZInQ.Contrib.RC53Assist.Reciprocity
