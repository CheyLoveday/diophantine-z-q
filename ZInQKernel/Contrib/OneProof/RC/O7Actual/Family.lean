import ZInQKernel.Contrib.OneProof.RC.Adelic.Level
import ZInQKernel.Contrib.OneProof.RC.Adelic.Ideal
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Assembly

/-! The family uses the explicit level order at every stage. -/
noncomputable section

open scoped NumberField

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler O12StageVal Visibility Visibility.ThetaStage NumberField

/-- The actual theta stage, with PMLocal and PM.Geometry supplied by their
respective constructions. The order is fixed to the explicit level order. -/
structure StageAt (O : Type) [CommRing O] (N M : ℕ) (hN : 0 < N) (m : ℤ) where
  ell : ℕ
  [prime : Fact ell.Prime]
  mod_four : ell % 4 = 3
  K : Type
  [field : Field K]
  [alg : Algebra (ZMod ell) K]
  [dec : DecidableEq K]
  [closed : IsSepClosed K]
  Ebar : WeierstrassCurve (ZMod ell)
  [elliptic : Ebar.IsElliptic]
  ap : ℕ → ℤ
  G : PM.Geometry K (Adelic.levelOrder ell mod_four N hN) N Ebar ap
  d : PM.Evaluation K Ebar M
  L : ℕ
  weights : PMLocal O (Adelic.levelOrder ell mod_four N hN) M N ell
  m_eq : (weights.m : ℤ) = m
  u : ClassSet (Adelic.levelOrder ell mod_four N hN) → ℤ
  hu : PM.IsLift G d L u

attribute [instance] StageAt.prime StageAt.field StageAt.alg StageAt.dec StageAt.closed
  StageAt.elliptic

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- The full visibility stage here is definitionally `pmLift.geom`. -/
abbrev StageAt.visibility (s : StageAt O N M hN m) :
    ThetaStage O (-1) (-(s.ell : ℚ)) := actualVisibility s.G s.d s.L s.weights s.u s.hu

/-- Tex 9123–9135: the class order in the support calculation is the
rational intersection of the actual conjugate level orders. -/
theorem classOrder_mem_adelic {a b : ℚ} {R : Order a b} (ha : a < 0) (hb : b < 0)
    (z : ClassSet R) (x : B a b) :
    x ∈ (classOrder ha hb z).ring ↔ ∀ p : Adelic.Prime,
      (↑((Adelic.classRepresentative z).val p)⁻¹ : Bp p.val a b) *
          toLocal p.val x * ((Adelic.classRepresentative z).val p : Bp p.val a b) ∈
        R.completion p.val := by
  change x ∈ (Eichler.representative z).val.leftRing ↔ _
  rw [← Adelic.fromAdelic_classRepresentative z, Adelic.mem_leftRing_iff]

/-- The exact local membership needed on nonzero support and the arithmetic
of the actual quadratic field of this datum. -/
structure IntegralSupport (s : StageAt O N M hN m) (D : ℤ) where
  Fq : Type
  [field : Field Fq]
  [numberField : NumberField Fq]
  basis : QuadraticBasis Fq (D * -(s.weights.m : ℤ))
  disc_neg : D * -(s.weights.m : ℤ) < 0
  disc_mod_eight : (D * -(s.weights.m : ℤ)) % 8 = 1
  half : ∀ z (x : s.visibility.supp z (((s.weights.m : ℤ) * D : ℤ) : ℚ)),
    HalfIntegral (classOrder s.weights.ha s.weights.hb z) x

/-- The Picard group of the maximal order, using the class-group quotient
of its fractional ideals. -/
abbrev IntegralSupport.classGroup {s : StageAt O N M hN m} {D : ℤ}
    (I : IntegralSupport s D) :=
  letI := I.field
  letI := I.numberField
  ClassGroup (𝓞 I.Fq)

instance {s : StageAt O N M hN m} {D : ℤ} (I : IntegralSupport s D) :
    Fintype I.classGroup := by
  let := I.field
  let := I.numberField
  exact NumberField.RingOfIntegers.instFintypeClassGroup I.Fq

/-- Tex 9308–9311: the filter and local half-integrality give stabilizers
of order two on the full nonzero support of the actual stage. -/
theorem IntegralSupport.stabilizer {s : StageAt O N M hN m} {D : ℤ}
    (I : IntegralSupport s D) (z : s.visibility.X)
    (x : s.visibility.supp z (((s.weights.m : ℤ) * D : ℤ) : ℚ)) :
    Nat.card (stageStabilizer s.visibility z x) = 2 := by
  let := I.field
  let := I.numberField
  let k := (D * -(s.weights.m : ℤ) - 1) / 4
  have h8 := I.disc_mod_eight
  have hk : D * -(s.weights.m : ℤ) = 4 * k + 1 := by dsimp [k]; omega
  exact actual_stabilizer s.G s.d s.L s.weights s.u s.hu I.basis (by ring) hk
    I.disc_neg h8 z x
    ((halfIntegral_iff_optimal _ I.basis rfl x.prop.1 x.prop.2.1).mp (I.half z x))

/-- Datumwise objects used to build the comparison, with the reference
reduction and the integral support supplied separately. The
weight and normalizer data concern individual embedding orbits. -/
structure DatumAt (s : StageAt O N M hN m) (D lam : ℤ) where
  support : IntegralSupport s D
  orbits : OrbitFibers s.visibility (((s.weights.m : ℤ) * D : ℤ) : ℚ)
    N.primeFactors.card support.classGroup
  weights : TorusWeights _ orbits
  moves : Normalizers s.G s.d s.L s.weights s.u s.hu orbits
  reference : Orientations N.primeFactors.card
  reduce : (2 : O) ^ M ∣
    ∑ c, weights.character c * (s.u (zc orbits.param (reference, c)) : O) - (lam : O)

/-- The integer representative obtained from the raw (O.7) congruence. -/
theorem DatumAt.representative {s : StageAt O N M hN m} {D lam : ℤ} (I : DatumAt s D lam) :
    (2 : O) ^ M ∣ I.weights.phase I.reference *
        (((Odd.c0 : ℤ) * 2 ^ N.primeFactors.card * lam : ℤ) : O) -
      thetaCoeff s.visibility (((s.weights.m : ℤ) * D : ℤ) : ℚ) :=
  actual_representative s.weights s.hu I.orbits I.weights I.moves I.reference I.reduce I.support.stabilizer

/-- Actual `ComparisonInputs` for any prescribed integer reading of the
phase-removed (O.4) coefficient (tex 2081–2084, 9101–9390). -/
def DatumAt.inputs {s : StageAt O N M hN m} {D lam : ℤ} (I : DatumAt s D lam)
    (contract : ∀ n : ℤ, (2 : O) ^ M ∣ (n : O) → (2 : ℤ) ^ M ∣ n) (aθ : ℤ)
    (ha : (2 : O) ^ M ∣ I.weights.phase I.reference * (aθ : O) -
      thetaCoeff s.visibility (((s.weights.m : ℤ) * D : ℤ) : ℚ)) :
    ComparisonInputs s.visibility M m D N.primeFactors.card lam aθ := by
  exact cast (congrArg (fun m' : ℤ =>
    ComparisonInputs s.visibility M m' D N.primeFactors.card lam aθ) s.m_eq)
    (comparisonInputs s.weights s.hu I.orbits I.weights I.moves I.reference I.reduce
      I.support.stabilizer contract aθ ha)

/-- Family form of the actual comparison. The premise concerning the
integer coefficient identifies it with the phase-removed raw theta sum,
independently of the right-hand side of (O.7). -/
theorem thetaComparison_actual (Mθ : ℕ → ℕ) (S : ∀ θ, StageAt O N (Mθ θ) hN m)
    (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (I : ∀ θ D, admissible θ D → DatumAt (S θ) D (lam θ D))
    (contract : ∀ θ (n : ℤ), (2 : O) ^ Mθ θ ∣ (n : O) → (2 : ℤ) ^ Mθ θ ∣ n)
    (ha : ∀ θ D (hD : admissible θ D),
      (2 : O) ^ Mθ θ ∣ (I θ D hD).weights.phase (I θ D hD).reference * (aθ θ D : O) -
        thetaCoeff (S θ).visibility ((((S θ).weights.m : ℤ) * D : ℤ) : ℚ)) :
    Odd.ThetaComparison Mθ aθ lam admissible N.primeFactors.card :=
  thetaComparison_of_inputs (fun θ => (S θ).visibility) Mθ aθ lam admissible
    N.primeFactors.card m (fun θ D hD => (I θ D hD).inputs (contract θ) _ (ha θ D hD))

end ZInQ.Manuscript.RC.O7Actual
