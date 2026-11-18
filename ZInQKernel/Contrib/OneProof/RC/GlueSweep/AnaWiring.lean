import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel

/-!
# Lane RC22 (glue sweep): lane RC0's `RCLeaves` without the GLUE field `levelSupport`

Lane RC0 (round 2, `RC/Wiring/Leaves.lean`) collects every remaining hypothesis of Theorem 5.3 in
the structure `RCLeaves`, and proves `restrictedConverseGenuine_of_leaves : Prints → RCLeaves →
RestrictedConverseGenuine`. One of its fields is lane RC13's GLUE
`levelSupport : Nonvanishing.FromRC8.LevelSupport` ("the level of the functional equation is
supported on the bad primes"), used only for BFH's twist sign (`RCLeaves.twistSign`).

`levelSupport_of_modularNewform` proves that GLUE from the field `modularNewform` of the same
structure (lane RC8's print `ModularNewform`). So the field is redundant:

* `RCLeavesReduced`: the fields of `RCLeaves` other than `levelSupport`, with the same types;
* `RCLeavesReduced.toRCLeaves` (PROVED): the structure rebuilt, `levelSupport` supplied by
  `levelSupport_of_modularNewform`;
* `restrictedConverseGenuine_of_reducedLeaves` (PROVED): **Theorem 5.3** (tex 1005–1011) from
  `Prints` and `RCLeavesReduced`.

The other analytic field `RootNumberExists` is already derived inside RC0's wiring from
`modularNewform` and `hasse` (`RCLeaves.rootNumberExists`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Ana

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Wiring

/-- **Lane RC0's `RCLeaves` without the GLUE field `levelSupport`**: the remaining hypotheses of
Theorem 5.3 beyond `Prints`, each field with the type (and the tex lines, kind and owner given in
`RC/Wiring/Leaves.lean`) of the field of `RCLeaves` of the same name. -/
structure RCLeavesReduced where
  /-- Hoffstein–Luo over newforms (PRINT; tex 1985–1991, App G 9996; lane RC8). -/
  hlPrint : PrintsAnalytic.HoffsteinLuoTheorem
  /-- The twisted functional equation over newforms (PRINT; Hoffstein–Luo p. 435 (1); lane RC8). -/
  twistedFE : PrintsAnalytic.TwistedFunctionalEquation
  /-- Modularity in newform form (PRINT: BCDT Theorem A; Milne Theorem 11.19, Proposition 11.21;
  lane RC8). -/
  modularNewform : PrintsAnalytic.ModularNewform
  /-- Absolute convergence of `L(E, s)` on `Re s > 3/2` (GLUE: Hasse's bound; lane RC8). -/
  hasse : PrintsAnalytic.HasseConvergence
  /-- The interface data, given the genus partner `h_*`. -/
  data : ∀ ℓ : ℕ, ℤ → WData ℓ
  /-- The leaves not involving `δ_o`, at every genus partner. -/
  pre : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    PreLeaves ((data ℓ h).withHstar h)
  /-- The leaves at the chosen `h_*` and the attained odd minimum `δ_o`. -/
  post : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    ∀ δ : ℤ, IsLeast (data ℓ h).depthSet δ → PostLeaves ((data ℓ h).withChoices h δ)

/-- **`RCLeaves` from `RCLeavesReduced`** (PROVED): the field `levelSupport` is
`levelSupport_of_modularNewform` applied to the field `modularNewform`. -/
def RCLeavesReduced.toRCLeaves (L : RCLeavesReduced) : RCLeaves where
  hlPrint := L.hlPrint
  twistedFE := L.twistedFE
  modularNewform := L.modularNewform
  hasse := L.hasse
  levelSupport := levelSupport_of_modularNewform L.modularNewform
  data := L.data
  pre := L.pre
  post := L.post

/-- Every `RCLeaves` is the rebuilt structure of its reduction (PROVED: `levelSupport` is a
proposition, so the two structures agree field by field). -/
theorem RCLeaves.eq_toRCLeaves (L : RCLeaves) :
    L = (RCLeavesReduced.toRCLeaves ⟨L.hlPrint, L.twistedFE, L.modularNewform, L.hasse, L.data,
      L.pre, L.post⟩) := rfl

/-- **Theorem 5.3 (`hyp:RC`) from `Prints` and `RCLeavesReduced`** (PROVED; tex 1005–1011): lane
RC0's `restrictedConverseGenuine_of_leaves` with the GLUE field `levelSupport` discharged by
`levelSupport_of_modularNewform`. -/
theorem restrictedConverseGenuine_of_reducedLeaves (P : Prints) (L : RCLeavesReduced) :
    RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_leaves P L.toRCLeaves

end ZInQ.Manuscript.RC.GlueSweep.Ana
