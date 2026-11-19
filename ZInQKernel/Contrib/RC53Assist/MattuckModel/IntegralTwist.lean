import ZInQKernel.Contrib.CloudB3RC53.OldKummer.Mattuck
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Two

/-!
# The integral model of an actual old Kummer twist

The hypothesis `hC` in `OldKummer/Mattuck.lean`, lines 89–94, is the
literal equality of the generic fibre of a local integral Weierstrass equation
with the actual local twist. It is not a quasi-isomorphism of complexes.

For an integral equation with `a₁ = a₃ = 0` and an integral twisting parameter
`h`, the equation `[0, h a₂, 0, h² a₄, h³ a₆]` is integral at every finite
place, including places above two. Its generic fibre is exactly the actual
local twist used by `actualKummerAt`. Thus its identification is proved from
the coefficients, rather than assumed as an arbitrary equality of models.

The resulting cardinality theorem uses the genuine residual Kummer condition
and retains both degree-zero torsion and the degree-one point quotient.
This concerns the residual level `i = 1`. It is not a comparison of an arbitrary
finite free presentation with the completed point module in all levels.

Locators: `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, lines 3413–3438;
the old Kummer row, lines 4544–4573; `OldKummer/Mattuck.lean`, lines 89–113;
`RC/KummerMaps/Iota.lean`, lines 71–92 and 313–325.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.MattuckModel

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Contrib.CloudB3RC53.OldKummer ZInQ.Contrib.CloudB3RC53.Mattuck
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

section IntegralEquation

variable {R : Type} [CommRing R]

/-- Definition: the denominator-free twist of an equation with `a₁ = a₃ = 0`;
Lemma `ex:arith-local-kummer`, lines 3413–3416. -/
def integralTwist (W : WeierstrassCurve R) (h : R) : WeierstrassCurve R :=
  ⟨0, h * W.a₂, 0, h ^ 2 * W.a₄, h ^ 3 * W.a₆⟩

/-- Proved: the integral twist commutes with every coefficient homomorphism;
Lemma `ex:arith-local-kummer`, lines 3413–3416. -/
theorem integralTwist_map {T : Type} [CommRing T] (W : WeierstrassCurve R)
    (h : R) (f : R →+* T) :
    (integralTwist W h).map f = integralTwist (W.map f) (f h) := by
  ext <;> simp [integralTwist, WeierstrassCurve.map]

/-- Proved: over a characteristic-zero field, the denominator-free equation
is exactly the actual quadratic twist, not merely an isomorphic curve;
`RC/TwistDictionary/Model.lean`, lines 110–113. -/
theorem integralTwist_generic_fibre {F : Type} [Field F] [CharZero F]
    [Algebra R F] (W : WeierstrassCurve R) (h : R)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    (integralTwist W h).baseChange F =
      twistK (W.baseChange F) (algebraMap R F h) := by
  ext <;> simp [integralTwist, twistK, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, h₁, h₃] <;> ring

/-- Proved: generic fibres compose along a scalar tower;
`OldKummer/Mattuck.lean`, line 93. -/
theorem baseChange_tower {T F : Type} [CommRing T] [CommRing F]
    [Algebra R T] [Algebra T F] [Algebra R F] [IsScalarTower R T F]
    (W : WeierstrassCurve R) :
    (W.baseChange T).baseChange F = W.baseChange F := by
  change (W.map (algebraMap R T)).map (algebraMap T F) = W.map (algebraMap R F)
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R T F]

end IntegralEquation

section LocalModel

variable {K : Type} [Field K] [NumberField K]

/-- Definition: the actual integral twist equation over the completed integers
at `v`; `OldKummer/Mattuck.lean`, lines 89–94. -/
def localIntegralTwist (W : WeierstrassCurve (𝓞 K)) (h : 𝓞 K)
    (v : HeightOneSpectrum (𝓞 K)) : WeierstrassCurve (v.adicCompletionIntegers K) :=
  (integralTwist W h).baseChange (v.adicCompletionIntegers K)

/-- Proved: the inclusions of global and completed integers form the required
scalar tower; `OldKummer/Mattuck.lean`, line 93. -/
theorem local_integer_tower (v : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Proved: this is the exact `hC` required by the old Kummer count, constructed
from integral coefficients. No model-identification hypothesis occurs;
`OldKummer/Mattuck.lean`, line 93, and Lemma `ex:arith-local-kummer`,
lines 3413–3438. -/
theorem hC_localIntegralTwist (W : WeierstrassCurve (𝓞 K)) (h : 𝓞 K)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (v : HeightOneSpectrum (𝓞 K)) :
    (localIntegralTwist W h v).baseChange (v.adicCompletion K) =
      localTwist (W.baseChange K) (algebraMap (𝓞 K) K h) v := by
  have := local_integer_tower v
  rw [localIntegralTwist, baseChange_tower,
    integralTwist_generic_fibre W h h₁ h₃]
  unfold localTwist
  rw [baseChange_tower, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]

/-- Proved: the constructed generic fibre is elliptic when the original curve
is elliptic and the twisting parameter is nonzero;
`RC/KummerMaps/Iota.lean`, lines 83–92. -/
theorem localIntegralTwist_isElliptic (W : WeierstrassCurve (𝓞 K))
    [((W.baseChange K)).IsElliptic] (h : 𝓞 K) (hh : h ≠ 0)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (v : HeightOneSpectrum (𝓞 K)) :
    ((localIntegralTwist W h v).baseChange (v.adicCompletion K)).IsElliptic := by
  rw [hC_localIntegralTwist W h h₁ h₃ v]
  have hK : algebraMap (𝓞 K) K h ≠ 0 := by
    intro he
    apply hh
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) K)
      (he.trans (map_zero (algebraMap (𝓞 K) K)).symm)
  exact isElliptic_localTwist (W.baseChange K) hK v

end LocalModel

section ActualCount

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve (𝓞 K)) [(W.baseChange K).IsElliptic] (h : 𝓞 K)
  (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (s : KS K S)
  (hs : s ^ 2 = algebraMap K (KS K S) (algebraMap (𝓞 K) K h)) (hs0 : s ≠ 0)
  (α : GKS K S →* (Acoef 1)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S (W.baseChange K) (2 ^ 1))

include h₁ h₃

open scoped Classical in
/-- Proved: the genuine residual Kummer condition has the dimension counted
by the constructed integral model. The original `hC` is discharged by the
coefficient identity, not supplied as a hypothesis;
`OldKummer/Mattuck.lean`, lines 89–113. -/
theorem oldKummer_count_integralTwist (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1)
    [Finite (ModN (localTwist (W.baseChange K) (algebraMap (𝓞 K) K h)
      v.1).toAffine.Point 2)] :
    Nat.card ((actualKummerAt (W.baseChange K) 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt (W.baseChange K) 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
      2 ^ ZInQ.Contrib.CloudB3RC53.GenuineInst.genCondDim2 K S v.1 .oldKummer
        (kummerResidualDim v.1 (localIntegralTwist W h v.1)) := by
  have hC := hC_localIntegralTwist W h h₁ h₃ v.1
  have : ((localIntegralTwist W h v.1).baseChange (v.1.adicCompletion K)).IsElliptic := by
    rw [hC]
    exact isElliptic_localTwist (W.baseChange K) (ne_zero_of_sqrt s hs hs0) v.1
  have : Finite (ModN ((localIntegralTwist W h v.1).baseChange
      (v.1.adicCompletion K)).toAffine.Point 2) := by
    rw [hC]
    infer_instance
  exact genCondDim2_oldKummer_actual (W.baseChange K) s hs hs0 α hFull v hα
    (localIntegralTwist W h v.1) hC

open scoped Classical in
/-- Proved: at an odd place the genuine old Kummer count is `2⁴`; neither
finiteness of the point quotient nor `hC` is assumed;
`OldKummer/Mattuck.lean`, lines 120–135, and manuscript lines 4551–4556. -/
theorem oldKummer_count_integralTwist_odd (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1)
    (h2 : (2 : 𝓞 K) ∉ v.1.asIdeal)
    (h4 : Nat.card (Submodule.torsionBy ℤ
      (localTwist (W.baseChange K) (algebraMap (𝓞 K) K h) v.1).toAffine.Point 2) = 4) :
    Nat.card ((actualKummerAt (W.baseChange K) 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt (W.baseChange K) 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
      2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer 0 := by
  have hC := hC_localIntegralTwist W h h₁ h₃ v.1
  have : ((localIntegralTwist W h v.1).baseChange (v.1.adicCompletion K)).IsElliptic := by
    rw [hC]
    exact isElliptic_localTwist (W.baseChange K) (ne_zero_of_sqrt s hs hs0) v.1
  have h4C : Nat.card (Submodule.torsionBy ℤ
      ((localIntegralTwist W h v.1).baseChange (v.1.adicCompletion K)).toAffine.Point 2) = 4 := by
    rw [hC]
    exact h4
  exact genCondDim2_oldKummer_actual_odd (W.baseChange K) s hs hs0 α hFull v hα h2
    (localIntegralTwist W h v.1) hC h4C

open scoped Classical in
/-- Proved: at a place above two the genuine old Kummer count is
`2^(4 + [K_v : ℚ₂])`, with the same constructed model. This retains the
rational two-torsion and does not assume finiteness of the point quotient;
manuscript lines 4551–4556 and `Mattuck/Two.lean`, lines 118–152. -/
theorem oldKummer_count_integralTwist_two (v : Places K S)
    [v.1.asIdeal.LiesOver (ZInQ.Contrib.CloudB3RC53.RankCounts.vP
      (⟨2, Nat.prime_two⟩ : Nat.Primes)).asIdeal]
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1)
    (h4 : Nat.card (Submodule.torsionBy ℤ
      (localTwist (W.baseChange K) (algebraMap (𝓞 K) K h) v.1).toAffine.Point 2) = 4) :
    letI := ZInQ.Contrib.CloudB3RC53.RankCounts.qpAlg K
      (⟨2, Nat.prime_two⟩ : Nat.Primes) v.1
    Nat.card ((actualKummerAt (W.baseChange K) 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt (W.baseChange K) 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
      2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer
        (Module.finrank ℚ_[2] (v.1.adicCompletion K)) := by
  let := ZInQ.Contrib.CloudB3RC53.RankCounts.qpAlg K
    (⟨2, Nat.prime_two⟩ : Nat.Primes) v.1
  have hC := hC_localIntegralTwist W h h₁ h₃ v.1
  have : ((localIntegralTwist W h v.1).baseChange (v.1.adicCompletion K)).IsElliptic := by
    rw [hC]
    exact isElliptic_localTwist (W.baseChange K) (ne_zero_of_sqrt s hs hs0) v.1
  have h4C : Nat.card (Submodule.torsionBy ℤ
      ((localIntegralTwist W h v.1).baseChange (v.1.adicCompletion K)).toAffine.Point 2) = 4 := by
    rw [hC]
    exact h4
  have := finiteIndex_latticeU K v.1 (localIntegralTwist W h v.1)
  have hcard := card_modN_two_of_lattice (latticeU K v.1 (localIntegralTwist W h v.1))
    (latticeU_noTwoTorsion K v.1 (localIntegralTwist W h v.1))
    (card_modN_latticeU K v.1 (localIntegralTwist W h v.1))
  have : Finite (ModN ((localIntegralTwist W h v.1).baseChange
      (v.1.adicCompletion K)).toAffine.Point 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard, h4C]; positivity)
  rw [genCondDim2_oldKummer_actual (W.baseChange K) s hs hs0 α hFull v hα
    (localIntegralTwist W h v.1) hC]
  exact congrArg (2 ^ ·) (kummerResidualDim_two K v.1 (localIntegralTwist W h v.1) h4C)

end ActualCount

section ManuscriptCurve

variable {K : Type} [Field K] [NumberField K]

/-- Definition: the integral equation `y² = x(x-ℓ)(x+3ℓ)` over the global
integers; manuscript line 1763 and `Hypotheses/PoleManuscript.lean`, line 56. -/
def integralEcurve (ℓ : ℕ) : WeierstrassCurve (𝓞 K) :=
  ⟨0, 2 * (ℓ : 𝓞 K), 0, -3 * (ℓ : 𝓞 K) ^ 2, 0⟩

/-- Proved: the integral equation is the manuscript's actual elliptic-curve
equation after base change; manuscript line 1763. -/
theorem integralEcurve_baseChange (ℓ : ℕ) :
    (integralEcurve (K := K) ℓ).baseChange K =
      (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).baseChange K := by
  ext <;> simp [integralEcurve, ZInQ.Contrib.CloudB3RC53.Ecurve,
    ZInQ.Manuscript.curve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

/-- Proved: for every integer twisting parameter and every finite place, the
constructed integral equation supplies the exact `hC` for the manuscript curve.
There is no old-model comparison assumption; `OldKummer/Mattuck.lean`, line 93,
and manuscript lines 1763 and 3413–3438. -/
theorem hC_Ecurve_integer (ℓ : ℕ) (h : ℤ) (v : HeightOneSpectrum (𝓞 K)) :
    (localIntegralTwist (integralEcurve (K := K) ℓ) (h : 𝓞 K) v).baseChange
        (v.adicCompletion K) =
      localTwist ((ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).baseChange K) (h : K) v := by
  simpa only [integralEcurve_baseChange, map_intCast] using
    hC_localIntegralTwist (integralEcurve (K := K) ℓ) (h : 𝓞 K) rfl rfl v

end ManuscriptCurve

end ZInQ.Contrib.RC53Assist.MattuckModel
