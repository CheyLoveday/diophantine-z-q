import ZInQKernel.Contrib.OneProof.RC.Visibility.Inputs
import ZInQKernel.Contrib.OneProof.RC.Wiring.OddMinimum

/-!
# Lane RC23: the fixed visible witness from (O.2) and (O.7) (App F, tex 9391–9403; (3.7), tex 2460–2536)

"In particular, write `c_θ = 9 + ω(N)`, the valuation of the fixed integer `c₀ 2^{ω(N)}`. At the fixed
witness `D_w`, (O.2) and (O.7) imply `v₂ a_M(D_w) = c_θ + c_w` whenever `M > c_θ + c_w`. The phase is a
unit and the congruence error has strictly larger valuation, so this is an equality, not merely a lower
bound. Discarding the finitely many earlier stages is sufficient." (tex 9391–9400)

The wiring's leaf `WitnessLeaf W` (`RC/Wiring/OddMinimum.lean`: one admissible `D_w` whose coefficient
has one fixed valuation `c < M_θ` on a set of stages in the ultrafilter) is PROVED here from:
* (O.7) for `λ` (`Odd.ThetaComparison`, the same input as in `visibilityInputs_of_genuine`);
* (O.2) at the witness, read on `λ` (`WitnessValuation`: on a set of stages in the ultrafilter, `D_w` is
  admissible and `v₂ λ_θ(D_w) = c_w` exactly; ELLIOT + PRINT, `ex:app-detector`, tex 8225–8405: the
  cocycle value at `σ²` has `b`-value `2^{a+1}`, the specialization identifies it with `λ_M(\bar Q)`,
  tex 8392–8398, 8457–8460, and `(D_w/ℓ₀) = 1` keeps `D_w` in every stage's support, tex 2534–2536);
* the advancing stages (`M_θ → ∞` along the ultrafilter; the skeleton's `stages_advance`).
The arithmetic is lane RC12's `witness_vZ` (PROVED).

What the text asserts about `λ_M(\bar Q)` (lane RC27): (O.2)/(3.7), `v₂ λ_{M_θ}(\bar Q) = c_w < M_θ` at
every stage of the detecting sequence, `c_w = a + 1` fixed (tex 8236–8239, 8396–8398, 2486–2493),
proved from the detector data and the specialization identity `λ_M(\bar Q) = b c_Q(σ²) mod 2^M`
(tex 8343–8360, 8457–8460). Batch 3's `FixedWitness` supplies only the nontorsion of the genus point and
of a rational point `Q` on `E^{(D_w)}`, the input of the detector's Kummer argument; it says nothing
about `λ_M(\bar Q)`. So `WitnessValuation` stays an input, now also derived (PROVED) from finer faithful
inputs:
* `WitnessO2At` — (O.2) as printed, on the residue of `λ` in `ℤ/2^{M_θ}` (with `c_w < M_θ`);
  `witnessValuation_of_O2`;
* `WitnessDetectorAt` — the detector data (`Odd.WitnessDetector`: cocycle, `h`, `τ`, `b`, `t₀`, `a`;
  ELLIOT + PRINT + GLUE, tex 8308–8360) and, on a set of stages in the ultrafilter, the specialization
  identity for `λ` (GLUE: finite Chebotarev and good reduction, tex 8362–8398, 8457–8460);
  `witnessValuation_of_detector`, `witnessLeaf_of_detector`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Visibility

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring Filter Topology

/-- **(O.2) at the fixed witness, read on `λ`** (ELLIOT + PRINT; tex 8225–8405, 2490–2493, 2534–2536):
on a set of stages in the ultrafilter, `D_w` is admissible and `λ_θ(D_w)` has 2-adic valuation exactly
`c_w`. -/
def WitnessValuation {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (Dw : ℤ) (cw : ℕ) : Prop :=
  ∀ᶠ θ in (W.stages : Filter ℕ), W.admissible θ Dw ∧ (2 : ℤ) ^ cw ∣ lam θ Dw ∧
    ¬ (2 : ℤ) ^ (cw + 1) ∣ lam θ Dw

/-- **(O.2) at the fixed witness, as printed** (ELLIOT + PRINT; tex 8236–8239, 8396–8398, (3.7) at
2486–2493): on a set of stages in the ultrafilter, `D_w` is admissible, `c_w < M_θ`, and the residue of
`λ_θ(D_w)` in `ℤ/2^{M_θ}` (the stage value `λ_{M_θ}(\bar Q)`) has `2`-adic valuation exactly `c_w`. -/
def WitnessO2At {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (Dw : ℤ) (cw : ℕ) : Prop :=
  ∀ᶠ θ in (W.stages : Filter ℕ), W.admissible θ Dw ∧ cw < W.Mθ θ ∧
    (2 : ZMod (2 ^ W.Mθ θ)) ^ cw ∣ ((lam θ Dw : ℤ) : ZMod (2 ^ W.Mθ θ)) ∧
    ¬ (2 : ZMod (2 ^ W.Mθ θ)) ^ (cw + 1) ∣ ((lam θ Dw : ℤ) : ZMod (2 ^ W.Mθ θ))

/-- **PROVED.** (O.2) as printed gives `WitnessValuation` (lane RC12's `exact_order_of_residue`). -/
theorem witnessValuation_of_O2 {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) {Dw : ℤ} {cw : ℕ}
    (hO2 : WitnessO2At W lam Dw cw) : WitnessValuation W lam Dw cw := by
  filter_upwards [hO2] with θ hθ
  obtain ⟨hadm, hcw, h1, h2⟩ := hθ
  exact ⟨hadm, Odd.exact_order_of_residue hcw h1 h2 rfl⟩

/-- **(O.2) at the fixed witness in its detector form** (ELLIOT + PRINT + GLUE; tex 8308–8398,
8457–8460; §7, tex 2469–2493, 2534–2536). The detector data `X` of the Kummer cocycle of
`Q = L P_{D_w}` (`Odd.WitnessDetector`: fixed before the precision varies) and, on a set of stages in
the ultrafilter, `D_w` admissible and the specialization identity: the residue of `λ_θ(D_w)` in
`ℤ/2^{M_θ}` (the stage value `λ_{M_θ}(\bar Q)`) is the reduction modulo `2^{M_θ}` of the row value
`b c_Q(σ²)`. -/
def WitnessDetectorAt {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (Dw : ℤ) {Gp T : Type*} [Group Gp]
    [AddCommGroup T] (X : Odd.WitnessDetector Gp T) : Prop :=
  ∀ᶠ θ in (W.stages : Filter ℕ), W.admissible θ Dw ∧
    ((lam θ Dw : ℤ) : ZMod (2 ^ W.Mθ θ)) = PadicInt.toZModPow (W.Mθ θ) (X.b (X.c (X.σ * X.σ)))

/-- **PROVED (tex 8457–8460, 8396–8398).** The detector form of (O.2) with the advancing stages gives
`WitnessValuation` with `c_w = a + 1` (lane RC12's `WitnessDetector.lambda_eq_two_pow` and
`exact_order_of_eq_two_pow`). -/
theorem witnessValuation_of_detector {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) {Dw : ℤ}
    {Gp T : Type*} [Group Gp] [AddCommGroup T] (X : Odd.WitnessDetector Gp T)
    (hX : WitnessDetectorAt W lam Dw X) (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    WitnessValuation W lam Dw X.cw := by
  have hM : ∀ᶠ θ in (W.stages : Filter ℕ), X.cw < W.Mθ θ :=
    hadv.eventually (eventually_gt_atTop _)
  filter_upwards [hX, hM] with θ hθ hMθ
  exact ⟨hθ.1, Odd.exact_order_of_eq_two_pow hMθ (X.lambda_eq_two_pow hθ.2)⟩

/-- **PROVED (tex 9391–9400): the fixed visible witness** (`WitnessLeaf`, with `c = 9 + ω(N) + c_w`)
from (O.7), (O.2) at the witness and the advancing stages. -/
theorem witnessLeaf_of_O7 {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (ω : ℕ)
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ lam W.admissible ω) {Dw : ℤ} {cw : ℕ}
    (hO2 : WitnessValuation W lam Dw cw) (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    WitnessLeaf W := by
  refine ⟨Dw, ((9 + ω + cw : ℕ) : ℤ), ?_⟩
  have hM : ∀ᶠ θ in (W.stages : Filter ℕ), 9 + ω + cw < W.Mθ θ :=
    hadv.eventually (eventually_gt_atTop _)
  filter_upwards [hO2, hM] with θ hθ hMθ
  obtain ⟨hadm, h1, h2⟩ := hθ
  obtain ⟨ζ, hζ, hcong⟩ := hO7 θ Dw hadm
  refine ⟨hadm, ?_, ?_⟩
  · rw [← odd_vZ_eq]
    exact Odd.witness_vZ ω (W.Mθ θ) cw hζ h1 h2 hcong hMθ
  · have : ((9 + ω + cw : ℕ) : ℤ) < ((W.Mθ θ : ℕ) : ℤ) := by exact_mod_cast hMθ
    exact_mod_cast this

/-- **PROVED: the fixed visible witness over the genuine genus points** — `witnessLeaf_of_O7` with
`λ = lamOf` (the stage maps applied to `L` times the genus points of the selected data). -/
theorem witnessLeaf_of_genuine {ℓ : ℕ} (W : WData ℓ)
    {E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (ZInQ.Contrib.CloudB3RC53.CST.newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ} {L : ℕ}
    (selG : (h : ℤ) → Option (ZInQ.Contrib.CloudB3RC53.GenusOdd.HeegnerDatum E f Lat κ
      (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar W.Mθ) (ω : ℕ)
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ (lamOf W.Mθ L selG ev) W.admissible ω) {Dw : ℤ} {cw : ℕ}
    (hO2 : WitnessValuation W (lamOf W.Mθ L selG ev) Dw cw)
    (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    WitnessLeaf W :=
  witnessLeaf_of_O7 W _ ω hO7 hO2 hadv

/-- **PROVED (tex 9391–9400, 8457–8460): the fixed visible witness from the detector form of (O.2)**
(`WitnessLeaf W`, with `c = 9 + ω(N) + c_w`, `c_w = a + 1`). -/
theorem witnessLeaf_of_detector {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (ω : ℕ)
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ lam W.admissible ω) {Dw : ℤ} {Gp T : Type*} [Group Gp]
    [AddCommGroup T] (X : Odd.WitnessDetector Gp T) (hX : WitnessDetectorAt W lam Dw X)
    (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) : WitnessLeaf W :=
  witnessLeaf_of_O7 W lam ω hO7 (witnessValuation_of_detector W lam X hX hadv) hadv

/-- **PROVED (non-vacuity of `WitnessDetectorAt`).** For any data in which `D_w` lies in every stage
support (e.g. lane RC0's toy data `toyW`, with `D = 1`), the detector form of (O.2) holds with the
detector data `Odd.witnessDetector_example` (`c_w = 1`) and `λ = 2`. -/
theorem witnessDetectorAt_example {ℓ : ℕ} (W : WData ℓ) {Dw : ℤ}
    (hadm : ∀ θ, W.admissible θ Dw) :
    WitnessDetectorAt W (fun _ _ => 2) Dw Odd.witnessDetector_example := by
  refine Filter.Eventually.of_forall fun θ => ⟨hadm θ, ?_⟩
  rw [Odd.witnessDetector_example.row_sq]
  simp only [Odd.WitnessDetector.cw, Odd.witnessDetector_example, zero_add, pow_one, Int.cast_ofNat]
  exact (map_ofNat (PadicInt.toZModPow (W.Mθ θ)) 2).symm

/-- **PROVED (non-vacuity of `WitnessO2At`).** For any data in which `D_w` lies in every stage support
and every precision is at least `2` (e.g. lane RC0's toy data `toyW`, `M_θ = θ + 3`), (O.2) as printed
holds with `λ = 2`, `c_w = 1`. -/
theorem witnessO2At_example {ℓ : ℕ} (W : WData ℓ) {Dw : ℤ} (hadm : ∀ θ, W.admissible θ Dw)
    (hM : ∀ θ, 2 ≤ W.Mθ θ) : WitnessO2At W (fun _ _ => 2) Dw 1 := by
  refine Filter.Eventually.of_forall fun θ => ⟨hadm θ, by have := hM θ; omega, ?_⟩
  have h := Odd.residue_exact_order_two_pow (M := W.Mθ θ) (cw := 1) (by have := hM θ; omega)
  simpa using h

end ZInQ.Manuscript.RC.Visibility
