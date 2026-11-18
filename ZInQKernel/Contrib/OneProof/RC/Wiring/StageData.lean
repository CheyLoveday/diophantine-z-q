import ZInQKernel.Contrib.OneProof.RC.Wiring.OddModels
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Realization
import ZInQKernel.Contrib.OneProof.RC.Stages.PreparedStages
import ZInQKernel.Contrib.OneProof.RC.Stages.Witness

/-!
**Theorem 5.3, Lane RC0 round 6: the stage data from the Appendix F stage construction.**

Before this file, lane RC0's leaves asked for two things about the stages: `PreDataSpec W`, a
requirement on the freely chosen interface data, and, inside the odd instance, (O.2) at the fixed
witness (`OddInstance.hO2 : WitnessValuation …`, ELLIOT + PRINT). Both are now reduced to the stage
construction of `RC/Stages` (Appendix F, tex 8225–8405; App G 10190–10191):

* `StageSupport W` (definitions): the fixed support consists of primes and contains `S₀` and the
  primes of `h_*` (tex 1974–1975, 2460–2461, 8250–8254), and the prepared filter is the positive
  unit-squareclass filter containing one over that support (`positivePrepared`, tex 2404–2410,
  2460–2461, 8222, 8246–8248). `StageSupport.preparedSpec` (PROVED) gives the old leaf
  `PreparedSpec` (the square class at `2` forces `≡ 1 (mod 8)`).
* `StagesFrom W q` (definitions): the stage fields of `W` are the construction at a stage sequence
  `q`: the hyperfilter, `M_θ = c_w + 1 + θ` and the prepared filter cut by the Legendre test of the
  `θ`-th prime (tex 2489–2493, 2531–2536, 8399–8405, App G 10190–10191). With `StageSupport` it
  gives `PreDataSpec W` and the advancing precision (`preDataSpec_of_stagesFrom`, PROVED from the
  construction's `preDataSpec_preparedStages`).
* `OddStagedInstance W`: the odd models (`OddModels`) together with the fixed witness `D_w`, its
  selected genus datum, the outputs of the detector construction (a Galois-fixed point `Q` on
  `A = E^{(D_w)}`, a division tower, the auxiliary field, `σ`, the row `b` with
  `b c_Q(σ²) = 2^{a+1}`, an actual detecting sequence `q`), the stage link `StagesFrom W q`, and the
  open input `WitnessSpecialization` (tex 8392–8398). (O.2) at the witness is PROVED from it
  (`OddStagedInstance.witnessValuation`, by the construction's `witnessValuation_withStages`), so
  `OddInstance` is PROVED (`OddStagedInstance.toOddInstance`).

Order of choices (tex 2460–2467, 8246–8260). `RCLeaves.data ℓ h` is chosen after the genus
partner `h_*`; the support enlargement by the primes of `h_*`, the witness `D_w`, the multiplier,
the detector and the stage sequence are all made after `h_*`, so they may depend on it, and the
stage fields of `data ℓ h` are the construction at that sequence. The odd models are chosen after
the data, and `OddStagedInstance` asks that its `D_w` and its stage maps be the ones of that same
construction (the stage maps are tied to the sequence through `WitnessSpecialization`).

Remaining input. `WitnessSpecialization` (tex 8392–8398; ELLIOT + GLUE: Elliot's good-reduction
step "Good reduction identifies the reduction of the global division cocycle with this exact map",
whose GLUE is reduction of points at the chosen Chebotarev place, Frobenius equivariance of
reduction on the division point and the prime-to-`p` torsion, and reduction of the split twist
identification; owner: the Appendix F stage construction, `RC/Stages/Witness.lean`). As there, the
point `Q` is a parameter: the text's `Q` is the rational point corresponding to `L P_{D_w}` (tex
2462–2466, 8295–8306), which the Lean statement does not force.

Caveat for a discharge. The one field `ev` (the stage maps) is read at every admissible parameter,
by `lamOf` in the comparison argument `hcore`, and at the witness by `WitnessSpecialization`. A
stage map defined only at the selected datum of `D_w` and zero elsewhere meets the second but not
the first at the other parameters, so it cannot discharge both.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open scoped WeierstrassCurve
open TauCeti ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC.PrintsArith
  ZInQ.Manuscript.RC.Stages ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd Filter Topology

/-! The fixed support and the prepared filter. -/

/-- **The fixed support and the prepared filter** (definitions; owner RC0):
* `support_prime`, `support_base`: the support consists of primes and contains
  `S₀ ℓ = {2, 3} ∪ primes(ℓ)` (tex 1974–1975);
* `support_hstar`: it contains the primes of `h_*`, adjoined before the witness is chosen (tex
  2405–2408, 2460–2461, App F 8250–8254);
* `prepared_eq`: the prepared filter is the positive unit-squareclass filter containing one over
  the support (`positivePrepared`: positive, squarefree, prime to the support, a square at every
  prime of the support; tex 2404–2410, 2460–2461, App F 8222, 8246–8248, 8255–8256). -/
structure StageSupport {ℓ : ℕ} (W : WData ℓ) : Prop where
  support_prime : ∀ p ∈ W.S, p.Prime
  support_base : S0 ℓ ⊆ W.S
  support_hstar : W.hstar.natAbs.primeFactors ⊆ W.S
  prepared_eq : W.prepared = positivePrepared W.S

/-- **The old leaf `PreparedSpec` from the support** (PROVED): a prepared parameter is positive,
squarefree and prime to the support, and the square class at `2 ∈ S₀` gives `≡ 1 (mod 8)`. -/
theorem StageSupport.preparedSpec {ℓ : ℕ} {W : WData ℓ} (hS : StageSupport W) :
    PreparedSpec W := by
  intro d hd
  rw [hS.prepared_eq] at hd
  obtain ⟨hpos, hsf, hd⟩ := hd
  have h2 : 2 ∈ W.S := hS.support_base (by simp [S0])
  obtain ⟨h2d, hsq⟩ := hd 2 h2
  have h2d' : ¬ (2 : ℤ) ∣ d := by exact_mod_cast h2d
  have hodd : Odd d := Int.odd_iff.mpr (by omega)
  have h8 := Nonvanishing.modEq_eight_of_isSquareAt_two hodd odd_one (by simpa using hsq)
  have h8' : d % 8 = 1 % 8 := h8
  exact ⟨hpos, hsf, by omega, fun p hp => (hd p hp).1⟩

/-! The stage fields from a stage sequence. -/

/-- **The stage fields of `W` are the construction at the stage sequence `q`** (definitions; tex
2489–2493, 2531–2536, App F 8399–8405, App G 10190–10191; owner RC0): the hyperfilter on the stages,
the precision `M_θ = c_w + 1 + θ`, and the stage support cut from the prepared filter by the
Legendre test of the `θ`-th prime of `q` (the construction's `withStages`). -/
structure StagesFrom {ℓ : ℕ} (W : WData ℓ) {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ}
    (q : StageSequence At cw B) : Prop where
  stages_eq : W.stages = hyperfilter ℕ
  Mθ_eq : W.Mθ = fun i => cw + 1 + i
  admissible_eq : W.admissible = fun i D => W.prepared D ∧ stageTest q i D

section Link

variable {ℓ : ℕ} {W : WData ℓ} {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ}
  {q : StageSequence At cw B}

/-- **The data are the construction's `withStages`** (PROVED). -/
theorem StagesFrom.withStages_eq (h : StagesFrom W q) : withStages W q W.prepared = W := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold withStages
  rw [← h1, ← h2, ← h3]

/-- **The data are the construction's `withPreparedStages` at their own support and `h_*`**
(PROVED). -/
theorem StagesFrom.withPreparedStages_eq (hS : StageSupport W) (h : StagesFrom W q) :
    withPreparedStages W W.S W.hstar q = W := by
  show withStages W q (positivePrepared W.S) = W
  rw [← hS.prepared_eq]
  exact h.withStages_eq

/-- **The data specification and the advancing precision from the construction** (PROVED: the
construction's `preDataSpec_preparedStages`). -/
theorem preDataSpec_of_stagesFrom (hS : StageSupport W) (h : StagesFrom W q) :
    PreDataSpec W ∧ Tendsto W.Mθ (W.stages : Filter ℕ) atTop := by
  have hW := h.withPreparedStages_eq hS
  obtain ⟨h1, h2⟩ := preDataSpec_preparedStages W W.S W.hstar q hS.support_prime hS.support_base
  rw [hW] at h1 h2
  exact ⟨h1, h2⟩

end Link

/-! The odd models with the constructed stages. -/

/-- **The odd side's genuine models with the stage data of the Appendix F construction** (tex
2460–2536, 8225–8405). Fields beyond `OddModels` (kinds and owners):
* `eE`, `eA`: `E_ℓ` and `A = E^{(D_w)}` are elliptic (definitions, instance arguments; PROVED-able
  for `ℓ > 0`, `D_w ≠ 0`; owner RC0);
* `Dw`, `hDw`, `dat`, `hdat`: the fixed witness, in the prepared filter, and its selected
  conductor-one genus datum (definitions; tex 2460–2462, 8249–8256; the selection exists at a
  prepared simple zero by `GenusOddInstance.hselG`);
* `Q`, `hQ`, `d`, `F₀`, `σ`, `a`, `b`, `hvalue`, `B`, `q`: the outputs of the detector
  construction, a Galois-fixed point of `A`, a compatible division tower, the auxiliary field, the
  detecting element `σ = hτ`, the fixed row `b` with `b c_Q(σ²) = 2^{a+1}` (`c_w = a + 1`), a
  finite exclusion and an actual detecting sequence at precisions `a + 2 + θ` (ELLIOT, Proposition
  `ex:app-detector`, tex 2468–2493, 8295–8405, PROVED by the construction's
  `exists_detector_stages` from a nontorsion rational point of `A`, PRINT Serre, GLUE no CM and a
  definitional auxiliary field, see `RC/Wiring/StageDataNonVacuity.lean`; owner: the Appendix F
  stage construction);
* `hstages`: the stage fields of `W` are the construction at `q` (definitions, `StagesFrom`);
* `hred`: the specialization identity at the witness, `WitnessSpecialization` (ELLIOT + GLUE;
  tex 8392–8398; owner: the Appendix F stage construction, `RC/Stages/Witness.lean`; the open
  input). -/
structure OddStagedInstance {ℓ : ℕ} (W : WData ℓ) : Type 1 extends OddModels W where
  /-- `E_ℓ` is elliptic -/
  [eE : (Ecurve ℓ).IsElliptic]
  /-- the fixed witness `D_w` -/
  Dw : ℤ
  /-- it is prepared -/
  hDw : W.prepared Dw
  /-- its selected conductor-one genus datum -/
  dat : HeegnerDatum (Ecurve ℓ) f Lat κ (Dw * W.hstar) 1 W.hstar
  /-- it is the selected one -/
  hdat : selG Dw = some dat
  /-- `A = E^{(D_w)}` is elliptic -/
  [eA : (qtwist (Ecurve ℓ) Dw).IsElliptic]
  /-- the witness point of `A`, over `ℚ̄` -/
  Q : GeomPoint (qtwist (Ecurve ℓ) Dw)
  /-- it is Galois fixed -/
  hQ : ∀ g : GalQ,
    WeierstrassCurve.Affine.Point.map (W' := qtwist (Ecurve ℓ) Dw) g.toAlgHom Q = Q
  /-- a compatible tower of divisions of `Q` -/
  d : DivisionTower (qtwist (Ecurve ℓ) Dw) Q
  /-- the auxiliary field -/
  F₀ : IntermediateField ℚ Qbar
  /-- the detecting element -/
  σ : GalQ
  /-- the exponent, `c_w = a + 1` -/
  a : ℕ
  /-- the fixed integral row -/
  b : TateMod (qtwist (Ecurve ℓ) Dw) 2 →ₗ[ℤ_[2]] ℤ_[2]
  /-- its value at the square of the detecting element -/
  hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1)
  /-- the finite prime exclusion -/
  B : Finset ℕ
  /-- the actual detecting sequence -/
  q : StageSequence (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ σ Dw W.hstar) (a + 1) B
  /-- the stage fields of the data are the construction at `q` -/
  hstages : StagesFrom W q
  /-- the specialization identity at the witness -/
  hred : WitnessSpecialization (L := L) dat ev d hQ (fun i => (selectedFrobenius q i).val)
    (finiteRow b)

namespace OddStagedInstance

variable {ℓ : ℕ} {W : WData ℓ}

/-- **(O.2) at the fixed witness, read on `λ`** (PROVED: the construction's
`witnessValuation_withStages`, transported along `StagesFrom.withStages_eq`; tex 2490–2493,
2534–2536, 8392–8398): on every stage `D_w` is admissible and `v₂ λ_θ(D_w) = a + 1`. -/
theorem witnessValuation (I : OddStagedInstance W) :
    Visibility.WitnessValuation W (Visibility.lamOf W.Mθ I.L I.selG I.ev) I.Dw (I.a + 1) := by
  have := I.eE
  have := I.eA
  have key : ∀ (V : WData ℓ), withStages W I.q W.prepared = V →
      ∀ ev : Visibility.StageKummer (Ecurve ℓ) I.f I.Lat I.κ W.hstar V.Mθ,
      WitnessSpecialization (L := I.L) I.dat ev I.d I.hQ
        (fun i => (selectedFrobenius I.q i).val) (finiteRow I.b) →
      Visibility.WitnessValuation V (Visibility.lamOf V.Mθ I.L I.selG ev) I.Dw (I.a + 1) := by
    intro V hV
    subst hV
    intro ev hred
    exact witnessValuation_withStages W I.d I.hQ I.q I.hDw I.selG I.dat I.hdat ev I.b I.hvalue hred
  exact key W I.hstages.withStages_eq I.ev I.hred

/-- **The odd instance** (PROVED): the models, the witness `D_w`, `c_w = a + 1` and (O.2) from
`witnessValuation`. -/
def toOddInstance (I : OddStagedInstance W) : OddInstance W where
  toOddModels := I.toOddModels
  Dw := I.Dw
  cw := I.a + 1
  hO2 := I.witnessValuation

/-- **The data specification and the advancing precision** (PROVED from the support and the stage
link, `preDataSpec_of_stagesFrom`). -/
theorem preDataSpec (I : OddStagedInstance W) (hS : StageSupport W) :
    PreDataSpec W ∧ Tendsto W.Mθ (W.stages : Filter ℕ) atTop :=
  preDataSpec_of_stagesFrom hS I.hstages

end OddStagedInstance

end ZInQ.Manuscript.RC.Wiring
