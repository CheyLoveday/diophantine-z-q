import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPinGenuine
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35ILP

/-!
**Theorem 5.3, Lane RC0: the (3.5) leaf with the regularity predicate over the family's genuine
moving character**

Proposition `ex:limits-uniform-lower-bound` (tex 4909–4972, with the height-one regularity of
tex 4976–5200) at the ring instances `(h, k')` of Proposition `ex:sec7-genus-lower` (tex
2418–2446). The regularity conjunct of `Eq35InputsGenuineABoundedR W` asks for
`RegularityInputsHPK (uprim h k')`. This file restates it with the per-instance form of the
height-one leaf over the family's moving character given by genuine ring-class data:
`RegularityInputsILG ℓ h k' (uprim h k')`, that is `u = 0`, or the field `K` (quadratic, with
`√k' ∈ K`), places, the actual conjugation, the curve `E_ℓ ⊗ K` with full two-torsion and a
genuine moving character over the primes of `h`, chosen once, then the address's moving family
over that character and a retained limit of it, chosen before the primes, with the pinned clause
`PinnedLimitAt` at every height-one prime `𝔭 ≠ (2)` (tex 4976–5200).

* `Eq35InputsGenuineABoundedRG W`: `Eq35InputsGenuineABoundedR W` with the regularity conjunct
  `RegularityInputsILG ℓ h k' (uprim h k')`, under the same quantifiers, all other conjuncts
  verbatim.
* What the consumers use. The regularity conjunct is read only through `uprim h k' ∈ Λ[1/2]`
  (tex 5190–5194; `eq35RegularHyp_iff_mem_lambdaHalf`), which the new predicate gives through
  `RegularityInputsILG.toMdl` and `RegularityInputsMdl.mem_lambdaHalf`; (5.5) does not use it.

PROVED: `Eq35InputsGenuineABoundedRG.toRL` (to the minimal form `Eq35InputsGenuineABoundedRL`);
`eq35Target_of_inputsARG` ((3.5) for each `A`, tex 2442–2446, 5200–5201, through
`eq35Target_of_inputsARL`); `eq55_of_inputsARG` ((5.5), tex 4958–4967); the degenerate
satisfiability `eq35InputsGenuineABoundedRG_of_not_prepared`.

Scope. As for `Eq35InputsGenuineABoundedR`: `uprim` is an existential witness, the outer data,
the configuration families and the address families are existential, and their identification
with the actual arithmetic instance is OPEN.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter
open ZInQ.Manuscript.RC.Determinant (OO)
open ZInQ.Contrib.RC53Assist.OuterRealization (RetainedOuterModels RetainedOuterSwitchData
  IsGenuineTwoTermModel eq55_of_retained)

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) with the regularity predicate over the family's genuine moving
character** (Proposition `ex:limits-uniform-lower-bound`, tex 4909–4972, at the ring instances
`(h, k')` of Proposition `ex:sec7-genus-lower`, tex 2418–2446): `Eq35InputsGenuineABoundedR W`
with its regularity conjunct `RegularityInputsHPK (uprim h k')` replaced by
`RegularityInputsILG ℓ h k' (uprim h k')`: `u = 0`, or the instance's field data and a genuine
moving character over the primes of `h`, the address's moving family over it and a retained limit
of that family, and the pinned clause at every height-one prime `𝔭 ≠ (2)` (tex 4976–5200).
The quantifiers are those of `Eq35InputsGenuineABoundedR`, and all other conjuncts are verbatim:
`u_prim`, `C₀` before `A`, (4.6) at the companion pairs, and for every `A` the retained outer
family with sizes at most the cap of (5.1), genuine two-term models, the coordinate clause and
the switch input (tex 4927–4972). Kind: definition. -/
def Eq35InputsGenuineABoundedRG : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsILG ℓ h k' (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, T.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineTwoTermModel (T.model i l).M) ∧
      (∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst

/-- **The genuine-character form gives the minimal form** (tex 4909–4972, 4976–5200,
5190–5194): the regularity conjunct weakens to `RegularityInputsMdl`
(`RegularityInputsILG.toMdl`) and then to `Λ[1/2]` (`RegularityInputsMdl.mem_lambdaHalf`); the
other conjuncts are unchanged. Kind: PROVED. -/
theorem Eq35InputsGenuineABoundedRG.toRL (hin : Eq35InputsGenuineABoundedRG W) :
    Eq35InputsGenuineABoundedRL W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, fun h k' hp hr hro => (hreg h k' hp hr hro).toMdl.mem_lambdaHalf, h46,
    hout⟩

/-- **(3.5) for each fixed `A` from the genuine-character form** (tex 2442–2446, 5200–5201),
through the minimal form (`Eq35InputsGenuineABoundedRG.toRL`, `eq35Target_of_inputsARL`).
Kind: PROVED. -/
theorem eq35Target_of_inputsARG (hin : Eq35InputsGenuineABoundedRG W) : Eq35Target W :=
  eq35Target_of_inputsARL W (Eq35InputsGenuineABoundedRG.toRL W hin)

/-- **(5.5) for the coordinates `u_prim`, directly from the genuine-character form** (tex
4927–4972, 4958–4967): for each `A`, `v_𝒪 (ι_𝒪 u_prim) ≥ −C(E, A)` at every companion
pair with `ω(k') ≤ A`, from the retained model family and the switch input on these model data
(`eq55_of_retained`), as `eq55_of_inputsARP`; the regularity conjunct is not used.
Kind: PROVED. -/
theorem eq55_of_inputsARG (hin : Eq35InputsGenuineABoundedRG W) :
    ∃ uprim : ℤ → ℤ → FractionRing Lambda, ∀ A : ℕ, ∃ C : ℕ,
      ∀ i : CompanionPair W A, (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨uprim, -, -, -, hout⟩ := hin
  refine ⟨uprim, fun A => ?_⟩
  obtain ⟨Pl, T, -, -, hcoord, hsw⟩ := hout A
  exact eq55_of_retained uprim T hcoord hsw

/-- **`Eq35InputsGenuineABoundedRG W` is satisfiable** in the degenerate case (no ring instances;
tex 2418–2446): the regularity conjunct is vacuous, and the other conjuncts are those of the
degenerate witness `eq35InputsGenuineABoundedR_of_not_prepared`. Kind: PROVED. -/
theorem eq35InputsGenuineABoundedRG_of_not_prepared (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineABoundedRG W := by
  obtain ⟨uprim, C₀, -, h46, hout⟩ := eq35InputsGenuineABoundedR_of_not_prepared W hW
  exact ⟨uprim, C₀, fun h _ hp => absurd hp (hW h), h46, hout⟩

end ZInQ.Manuscript.RC.Wiring
