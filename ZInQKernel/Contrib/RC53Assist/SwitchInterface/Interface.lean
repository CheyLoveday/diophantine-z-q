import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.InnerLimitWiring

/-!
# Switching with cohomological side identifications

The nonquadratic descent uses the two side-to-stage cohomology equivalences
and the coordinate step to the specified next configuration. Equality of
Selmer data is not used: the two equalities are discarded by
`GaloisSwitchData.toHeightOneSwitchData` before the dimension and coordinate
arguments. The structures below retain every family model and starting
identification, but impose no equality of local-condition inclusions.

The side-to-family cohomology equivalences are constructed, rather than
assumed, by composing the side-to-stage equivalences with the inverse family
models. A singular successor can consequently be the finite side of the next
switch up to cohomology, without identifying the two local-condition images.

Sources: tex L4391–4451, L4976–5003, L5027–5086, L5137–5195.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.SwitchInterface

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane singPlane)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped Matrix

section Models

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- Kind: family-model structure. The fixed configuration family, its
starting class, functional and coordinate, and primitivity are unchanged;
tex L4976–5003, L5072–5195. -/
structure NonquadSwitchFrame (Φ : SwitchFamily k A) (ι : A →+* F)
    (ρ : A →+* k) (u : F) where
  /-- Kind: data. Integral two-term stages; tex L4976–4996. -/
  stage : Φ.Config → TwoTermStage ι
  /-- Kind: cochain-model input. Every stage models its prescribed family
  fibre; tex L4976–4996. -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC
    (twoTermFiberComplex ρ (stage c))
  /-- Kind: class identification. The actual cycle is retained;
  tex L4976–5003. -/
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i)
  /-- Kind: functional identification. The actual paired functional is
  retained; tex L4976–5003. -/
  hw0 : ∀ y, Φ.lamAct y = (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ
    (((model Φ.actual).hom.f 2).hom y : Fin _ → k)
  /-- Kind: coordinate identification. The starting coordinate is the
  specified coordinate; tex L4976–5003. -/
  hu0 : (stage Φ.actual).u = u
  /-- Kind: specialization hypothesis. This branch is nonquadratic;
  tex L5005–5008. -/
  hnq : ¬ Φ.quadratic ρ
  /-- Kind: primitive-class input. Reachable stages have nonzero reduced
  cycles; tex L4986–4992, L5154–5157. -/
  primitive : ∀ c, Reach Φ.next Φ.actual c → ∃ i, ρ ((stage c).z i) ≠ 0

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- Kind: proved theorem. The stage dimensions remain the cohomology
ranks of the prescribed family, so they cannot be chosen independently;
tex L4976–4996. -/
theorem NonquadSwitchFrame.fiberDim_eq (X : NonquadSwitchFrame Φ ι ρ u)
    (c : Φ.Config) :
    (X.stage c).fiberDim ρ = Module.finrank k ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 k A F ι ρ (X.stage c) (Φ.fibre c) ⟨X.model c⟩

/-- Kind: constructed cohomology equivalence. The finite side is identified
with the old family fibre through their common stage; no equality of Selmer
data is required; tex L4391–4451, L5040–5054. -/
def NonquadSwitchFrame.finiteH1Equiv (X : NonquadSwitchFrame Φ ι ρ u)
    {c c' : Φ.Config} (N : QuasiNonquadStep ρ (X.stage c) (X.stage c')) :
    (selCx N.SF.Dside).toCC.homology 1 ≃ₗ[k]
      (selCx (Φ.fibre c)).toCC.homology 1 :=
  N.φ.trans (h1EquivOfHomotopyEquiv ρ (X.stage c) (Φ.fibre c) (X.model c)).symm

/-- Kind: constructed cohomology equivalence. The singular side is
identified with the specified successor fibre through its stage;
tex L4391–4451, L5040–5054. -/
def NonquadSwitchFrame.singularH1Equiv (X : NonquadSwitchFrame Φ ι ρ u)
    {c c' : Φ.Config} (N : QuasiNonquadStep ρ (X.stage c) (X.stage c')) :
    (selCx N.SS.Dside).toCC.homology 1 ≃ₗ[k]
      (selCx (Φ.fibre c')).toCC.homology 1 :=
  N.φ'.trans (h1EquivOfHomotopyEquiv ρ (X.stage c') (Φ.fibre c') (X.model c')).symm

/-- Kind: constructed cohomology equivalence. Consecutive switches share
the successor cohomology, not their local-condition inclusion images;
tex L4997–5003, L5027–5086. -/
def NonquadSwitchFrame.successorH1Equiv (X : NonquadSwitchFrame Φ ι ρ u)
    {a b c : Φ.Config} (N : QuasiNonquadStep ρ (X.stage a) (X.stage b))
    (M : QuasiNonquadStep ρ (X.stage b) (X.stage c)) :
    (selCx N.SS.Dside).toCC.homology 1 ≃ₗ[k] (selCx M.SF.Dside).toCC.homology 1 :=
  N.φ'.trans M.φ.symm

/-- Kind: model-level switching-input structure. The side-to-stage
cohomology equivalences already belong to each nonquadratic step. The next
configuration and its coordinate step remain prescribed; the redundant
literal side equalities are omitted; tex L4976–5195. -/
structure NonquadSwitchInputsIso (Φ : SwitchFamily k A) (ι : A →+* F)
    (ρ : A →+* k) (u : F) extends NonquadSwitchFrame Φ ι ρ u where
  /-- Kind: per-switch input. A coordinate step and a cohomological switch
  to the specified successor, with duality and detection inside the step;
  tex L4997–5003, L5027–5086. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      Nonempty (QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)))

/-- Kind: constructed downstream data. The original dimension proof is
reused on each switch, and reachable configurations are retained as the
stages of the original descent consumer; tex L4997–5003, L5137–5195. -/
def NonquadSwitchInputsIso.toHeightOneSwitchData (X : NonquadSwitchInputsIso Φ ι ρ u) :
    HeightOneSwitchData ι ρ where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := X.stage s.1
  quadratic := Φ.quadratic ρ
  sp s := (X.stage s.1).fiberDim ρ
  sm _ := 0
  sign_sum _ _ := add_zero _
  primitive s := X.primitive s.1 s.2
  switch_mixed s _ h1 := by
    obtain ⟨p, hcs, ⟨N⟩⟩ := X.step s.1 s.2 h1
    exact ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hcs,
      fun q => absurd q X.hnq, fun _ => ⟨N.toNonquadDims⟩⟩
  switch_single _ q := absurd q X.hnq

/-- Kind: proved sufficiency theorem. The unchanged descent theorem yields
the same regularity conclusion from cohomological switches;
tex L4976–5195. -/
theorem regular_of_nonquadSwitchInputsIso [IsLocalRing A]
    (hι : Function.Injective ι) (hρ : ∀ x ∈ maximalIdeal A, ρ x = 0)
    (X : NonquadSwitchInputsIso Φ ι ρ u) : ∃ a, ι a = u := by
  obtain ⟨a, ha⟩ := regular_of_switchData hι hρ X.toHeightOneSwitchData
    ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans X.hu0⟩

end Models

section InnerLimit

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]

/-- Kind: weakened inner-limit input structure. Every retained arithmetic
step still has its original duality, residue identities, detection and
side-to-stage cohomology equivalences. Literal equality with the family
Selmer data is replaced by the cohomological identifications constructed
from these equivalences and the unchanged family models;
tex L4391–4451, L4976–5195, L5027–5086. -/
structure InnerLimitSwitchInputsIso
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F)
    extends NonquadSwitchFrame Φ ι (resAt P) u where
  /-- Kind: retained-step input. The original step data and coordinate step
  are indexed by the prescribed successor, without equalities of Selmer
  data; tex L4391–4451, L4997–5003, L5027–5086. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      Nonempty (InnerLimitStepData P (stage c) (stage (Φ.next c p)))

variable {P} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
  {ι : Localization.AtPrime P →+* F} {u : F}

/-- Kind: constructed model-level inputs. The original retained-step
producer supplies the cohomological switch at each specified successor;
tex L4391–4451, L5027–5086. -/
def InnerLimitSwitchInputsIso.toModel (X : InnerLimitSwitchInputsIso P Φ ι u) :
    NonquadSwitchInputsIso Φ ι (resAt P) u where
  toNonquadSwitchFrame := X.toNonquadSwitchFrame
  step c hc h1 := by
    obtain ⟨p, hcs, ⟨Y⟩⟩ := X.step c hc h1
    exact ⟨p, hcs, ⟨Y.toStep⟩⟩

/-- Kind: constructed downstream data. The original dimension and descent
consumers are reused without changing their statements or proofs;
tex L4997–5003, L5137–5195. -/
def InnerLimitSwitchInputsIso.toHeightOneSwitchData
    (X : InnerLimitSwitchInputsIso P Φ ι u) : HeightOneSwitchData ι (resAt P) :=
  X.toModel.toHeightOneSwitchData

/-- Kind: proved sufficiency theorem. The weakened inner-limit interface
has exactly the original regularity conclusion; tex L4976–5195. -/
theorem regular_of_innerLimitSwitchInputsIso (hι : Function.Injective ι)
    (X : InnerLimitSwitchInputsIso P Φ ι u) : ∃ a, ι a = u :=
  regular_of_nonquadSwitchInputsIso hι
    (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).mpr hx) X.toModel

/-- Kind: constructed compatibility map. The original literal inputs give
the weakened inputs by forgetting only the two side equalities;
tex L4391–4451, L4976–5195. -/
def ofLiteral (X : InnerLimitSwitchInputs P Φ ι u) :
    InnerLimitSwitchInputsIso P Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  primitive := X.primitive
  step c hc h1 := by
    obtain ⟨p, hcs, Y, _, _⟩ := X.step c hc h1
    exact ⟨p, hcs, ⟨Y⟩⟩

end InnerLimit

end ZInQ.Contrib.RC53Assist.SwitchInterface
