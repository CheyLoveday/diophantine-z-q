import ZInQKernel.Contrib.OneProof.RC.Skeleton.Skeleton
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Companion
import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.RCTarget

/-!
# Theorem 5.3, Lane RC0 round 2: data and targets of the wiring

The deduction of the blueprint node `BranchPackageNode` (`RC/Skeleton`) consumes Elliot's steps as
the fields of `RCSteps D` for interface data `D : RCData ℓ`. In round 2 the steps are discharged,
where a lane has done so, from that lane's (smaller) hypotheses, and the remaining hypotheses are
collected in one structure (`Leaves.lean`). This file fixes the shared vocabulary:

* `S0 ℓ = {2, 3} ∪ {p ∣ ℓ}` — the base support at which the genus partner is chosen;
* `IsGenusPartner ℓ h` — the conclusion of lane RC13's `genusPartner` at `S0 ℓ` (tex 2404–2408:
  `h_*` negative odd fundamental, square at the fixed primes, `L(E^{(h_*)}, 1) ≠ 0`);
* `WData ℓ` — the interface data `RCData ℓ` together with the predicate `Partitionable` of the
  even source (lane RC2, used by lane RC13's rough companion);
* `WData.IsRoughCompanion h k'` — `k'` is a rough companion of `h` in the form produced by lane
  RC13's `roughCompanion` (tex 2320–2401: a negative fundamental discriminant `k' ≡ 1 (mod 8)`,
  square and prime at the fixed support and at the primes of `h`, avoiding the primes of `h_*`,
  `hk'` partitionable, `L(E^{(hk')}, 1) ≠ 0`);
* `sFun ℓ h = s(h)` (tex 1828–1830) as an integer;
* the targets: each field of `RCSteps` as a `Prop` about the data (`…Target`), and the inputs of
  batch 3's `FinalFamilyField` in their exact form ((F.3), (3.4) at all companions and at the final
  `k`, (3.5), the prepared-filter GLUE, the attained odd minimum and the address input).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## The genus partner -/

/-- The base support `S₀ = {2, 3} ∪ {p : p ∣ ℓ}` (tex 1790–1793: the primes of `2N` for `E_ℓ`). -/
def S0 (ℓ : ℕ) : Finset ℕ := insert 2 (insert 3 ℓ.primeFactors)

/-- **`h` is a genus partner** in the form of lane RC13's `genusPartner` at `S₀` (with no extra
avoidance set), tex 2404–2408: `h_* < 0`, `h_* ≡ 1 (mod 8)`, fundamental, a square and prime to `p`
at every `p ∈ S₀`, `ω(h_*) ≤ 5`, `L(E^{(h_*)}, 1) ≠ 0`. (Then `|h_*| ≥ 7 > 4` and `h_*` is in the
squareclasses at `2N` of the prepared positive filter containing one, as the text requires.) -/
def IsGenusPartner (ℓ : ℕ) (h : ℤ) : Prop :=
  h < 0 ∧ h % 8 = 1 ∧ Nonvanishing.IsFundamentalDiscriminant h ∧
    (∀ p ∈ S0 ℓ, Nonvanishing.IsSquareAt p (h : ℚ) ∧ ¬ (p : ℤ) ∣ h) ∧
    Nonvanishing.omega h ≤ 5 ∧ Nonvanishing.CentralNonzero (curve ((h * ℓ : ℤ) : ℚ))

/-! ## Data -/

/-- **The interface data of round 2**: `RCData ℓ` and the predicate `Partitionable` of the
even source (Definition `ex:sec7-seed-partition`, tex 2144–2177; lane RC2), which lane RC13's
rough companion takes as a parameter. -/
structure WData (ℓ : ℕ) extends RCData ℓ where
  /-- `Partitionable d`: the even source at `d` is partitionable (tex 2144–2177) -/
  Partitionable : ℤ → Prop

/-- `s(h)` (tex 1828–1830) as an integer. -/
def sFun (ℓ : ℕ) (h : ℤ) : ℤ := (shaLength (Etw ℓ h) : ℤ)

namespace WData

variable {ℓ : ℕ} (W : WData ℓ)

/-- **`k'` is a rough companion of `h`** (Proposition `ex:sec7-rough-companion`, tex 2320–2401,
App G 10055–10150), in the form produced by lane RC13's `roughCompanion` at the fixed support
`S` and the avoidance set of the primes of `h_*` (tex 2407–2410). -/
def IsRoughCompanion (h k' : ℤ) : Prop :=
  k' < 0 ∧ k' % 8 = 1 ∧ Nonvanishing.IsFundamentalDiscriminant k' ∧
    (∀ p ∈ W.S ∪ h.natAbs.primeFactors, Nonvanishing.IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
    (∀ p ∈ W.hstar.natAbs.primeFactors, ¬ (p : ℤ) ∣ k') ∧ W.Partitionable (h * k') ∧
    Nonvanishing.CentralNonzero (Etw ℓ (h * k'))

end WData

/-! ## The targets: the fields of `RCSteps` -/

section Targets

variable {ℓ : ℕ} (D : RCData ℓ)

/-- `RCSteps.lstar_ne_zero_iff` (tex 1825–1830). -/
def LstarTarget : Prop := ∀ h : ℤ, h ≠ 0 → (D.Lstar h ≠ 0 ↔ AnalyticRank (Etw ℓ h) 0)

/-- `RCSteps.genus_partner` (tex 2404–2408). -/
def GenusPartnerTarget : Prop := D.hstar < 0 ∧ D.Lstar D.hstar ≠ 0

/-- `RCSteps.visibility` ((O.8), tex 9407–9445). -/
def VisibilityTarget : Prop :=
  ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
    AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet

/-- `RCSteps.companion` (tex 2595–2603). -/
def CompanionTarget : Prop :=
  ¬ D.OddEmptyUnit → D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin ≠ -1 ∧
    D.kfin ≠ -3 ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ D.kfin → p ∈ D.S) ∧ D.kfin % 4 = 1 ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p D.kfin) ∧
    IsCoprime D.kfin D.hstar ∧ AnalyticRank (Etw ℓ D.kfin) 0

/-- `RCSteps.gz_comparison` ((3.4) at the final `k`, tex 2436–2440, 2692–2693). -/
def GzFinalTarget : Prop :=
  ∃ Cper : ℤ, ∀ h : ℤ, D.prepared h → AnalyticRank (Etw ℓ h) 1 →
    D.Lstar (h * D.kfin) ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ D.S ∧ jacobiSym D.kfin q = 1) →
    ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * D.jrc h D.kfin - 2 * D.jgen h =
      padicValRat 2 (D.Lstar (h * D.kfin)) - padicValRat 2 (D.Lstar D.hstar) + Cper + ε

/-- `RCSteps.final_family` ((3.9), tex 2674–2712, App G 10792–10858). -/
def FinalFamilyTarget : Prop :=
  ¬ D.OddEmptyUnit → ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
    ∃ F : Family, F.b = b ∧ D.FinalFamilyAt Co Ce F

/-- `RCSteps.calibration` ((4.6), tex 3987–4141). -/
def CalibrationTarget : Prop :=
  ∃ Ccal : ℤ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 →
      ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ Ccal ∧
        v2 (central (D.uPrim F x)) =
          ((2 * D.jrc (F.h x) D.kfin - 4 * omega (F.h x) - shaLength (Etw ℓ (F.h x)) -
            shaLength (Etw ℓ (F.h x * D.kfin)) - ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) +
              err : ℤ) : WithTop ℤ)

/-- `RCSteps.common_coordinate` ((4.7), tex 4142–4328). -/
def CommonCoordinateTarget : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde F x = ε * D.uPrim F x

/-- `RCSteps.height_one` (tex 4909–5205, 5703–5704). -/
def HeightOneTarget : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    InLamHalf (D.uTilde F x)

/-- `RCSteps.clearing` ((5.9), tex 5487–5645). -/
def ClearingTarget : Prop :=
  ∃ cdet dK : ℕ, ∀ M : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (C : CoordData F.b) (c : ℕ),
      (∀ x j, C.u x j = PowerSeries.coeff j (D.uTilde F x)) ∧ c ≤ cdet ∧
      (∀ g, Tendsto (C.F g) atBot (𝓝 0)) ∧
      (∀ x (n : ℤ), HasSum (fun j : ℕ => (signEval C.F x (n - j) : ℚ_[2]) * C.u x j)
        (signEval C.D x n : ℚ_[2])) ∧
      PoleBound C (16 * (dK + 5) * M) M ∧ BaseRegular C c

/-- `RCSteps.base_zero` (tex 4330–4376). -/
def BaseZeroTarget : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ProductOrderGeTwo (Ecurve ℓ) D.kfin → ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      central (D.uTilde F 0) = 0

/-- **`RCSteps` from its fields** (the targets). -/
theorem rcSteps_of_targets (h1 : LstarTarget D) (h2 : GenusPartnerTarget D)
    (h3 : VisibilityTarget D) (h4 : Tendsto D.Mθ (D.stages : Filter ℕ) atTop)
    (h5 : ∀ θ : ℕ, D.admissible θ 1) (h6 : CompanionTarget D) (h7 : GzFinalTarget D)
    (h8 : FinalFamilyTarget D) (h9 : CalibrationTarget D) (h10 : CommonCoordinateTarget D)
    (h11 : HeightOneTarget D) (h12 : ClearingTarget D) (h13 : BaseZeroTarget D) :
    RCSteps D :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Targets

/-! ## The inputs of batch 3's `FinalFamilyField`, over the data -/

section FinalFamilyInputs

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The rough companion with (F.3)** (Proposition `ex:sec7-rough-companion`, tex 2343–2401;
App G 10131–10146): constants `A` (a bound for `ω(k')`) and `C_E`, and for every known simple zero
`h` of the prepared filter a rough companion `k'` with `ω(k') ≤ A`, `L_*(hk') ≠ 0` and
`v₂L_*(hk') ≤ 2ω(h) + 2ω(k') + s(hk') + C_E`. -/
def F3Target : Prop :=
  ∃ (A : ℕ) (CE : ℤ), ∀ h : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 →
    ∃ k' : ℤ, W.IsRoughCompanion h k' ∧ (omega k' : ℤ) ≤ A ∧ W.Lstar (h * k') ≠ 0 ∧
      padicValRat 2 (W.Lstar (h * k')) ≤ 2 * omega h + 2 * omega k' + sFun ℓ (h * k') + CE

/-- **(3.4) with one period constant** (tex 2436–2440; the fixed initial period convention is one
constant `C_per`): at every rough companion `k'` of a known simple zero `h` of the prepared filter
(the form of `FinalFamilyField`), and at the final `k` (the form of `RCSteps.gz_comparison`, used at
tex 2692–2693). -/
def Gz34Target : Prop :=
  ∃ Cper : ℤ,
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * W.jrc h k' - 2 * W.jgen h =
        padicValRat 2 (W.Lstar (h * k')) - padicValRat 2 (W.Lstar W.hstar) + Cper + ε) ∧
    (∀ h : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 →
      W.Lstar (h * W.kfin) ≠ 0 →
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ W.S ∧ jacobiSym W.kfin q = 1) →
      ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * W.jrc h W.kfin - 2 * W.jgen h =
        padicValRat 2 (W.Lstar (h * W.kfin)) - padicValRat 2 (W.Lstar W.hstar) + Cper + ε)

/-- **(3.5) for each fixed `A`** (tex 2441–2446; Section 9's arithmetic estimate, from (5.5) and
(4.6), tex 5197–5202): at every rough companion `k'` with `ω(k') ≤ A` of a known simple zero `h` of
the prepared filter, `2j_rc(h,k') ≥ 4ω(h) + s(h) + s(hk') − C_R(E,A)`. -/
def Eq35Target : Prop :=
  ∀ A : ℕ, ∃ CR : ℤ, ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 →
    W.IsRoughCompanion h k' → (omega k' : ℤ) ≤ A →
      4 * (omega h : ℤ) + sFun ℓ h + sFun ℓ (h * k') - CR ≤ 2 * W.jrc h k'

/-- **Admissible theta parameters lie in the prepared filter** (GLUE, tex 2404–2410, 8408–8429). -/
def PreparedGlue : Prop := ∀ θ : ℕ, ∀ Dd : ℤ, W.admissible θ Dd → W.prepared Dd

/-- **`δ_o` is the attained odd minimum** (tex 2536–2551, App G (F.6), 10151–10256; batch 3's
`DepthSet`). -/
def OddMinimumTarget : Prop :=
  IsLeast (AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible) W.δo

/-- **The address input at `δ_o`** (App G `ex:app-odd-stabilization`, `ex:app-simultaneous-address`,
`ex:app-final-family`, tex 10508–10791; batch 3's `AddressInput`; lane RC2 with RC3's seed). In
Branch 2, for one `C_{e,final}` and the coarse constant `C_coarse = C_gen/2 + C_det` of (F.5). -/
def AddressTarget (A CR CE Cper Cdet : ℤ) : Prop :=
  ¬ W.OddEmptyUnit → ∃ CeFinal : ℤ,
    AppGEndpoints.AddressInput W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible W.prepared
      W.Lstar W.kfin W.δo CeFinal
      (((2 * A + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 + Cdet)
      Family Family.b Family.h (Family.Admissible W.S W.kfin)

end FinalFamilyInputs

end ZInQ.Manuscript.RC.Wiring
