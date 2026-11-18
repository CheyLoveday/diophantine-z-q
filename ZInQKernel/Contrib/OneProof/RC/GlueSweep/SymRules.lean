import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.RC12Bridge
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressInputBridge
import ZInQKernel.Contrib.OneProof.RC.Symbols.EvenUpper
import ZInQKernel.Contrib.OneProof.RC.Symbols.OddStage

/-!
# Lane RC22 (glue sweep, symbols): the coefficient rules of lane RC2, discharged

Lane RC2 (`RC/Symbols/`) proves the finite combinatorics of §7.3 and App G
(tex 2006–2341, 10508–10790) for an abstract symbol `A : Config L → ZMod 2` that is assumed to
obey the coefficient rules of Lemma `ex:sec7-coefficient-rules` (tex 2102–2136): the hypothesis
`CoefficientRules ε A` (ELLIOT; proof in App F `ex:app-coefficient-rules`, tex 9884–9976), and,
for the odd stage tables, `RulesUpTo ε (A i) W` on an ultrafilter (tex 10533–10538).

The coefficient dictionary of the shared top layer proves these rules for the actual symbol
`symb T R` (the reading `R` of any prime realization of a typed graph, `T` the type data of
primes): `coefficientRules_symb` and `rulesUpTo_symb` (`CoefficientDictionary/Rules.lean`), from
lane RC12's readings on prime sets (`FixedUFactorization`, `O12Reading`, `PrimaryReading`, at
every budget, resp. at the budget `W + 1`) and the GLUE `ApEven`. Here these hypotheses are
bundled as `RC12Readings` / `RC12ReadingsUpTo` (jointly satisfiable: `rc12Readings_zero`), and the
consumers' statements are written with `A := symb T R` and the rule hypotheses removed (PROVED
bridges).

**The trace-module model is inconsistent.** The second discharger of the dictionary,
`coefficientRules_of_model` / `TraceModel.rulesUpTo_of_model` (`CoefficientDictionary/RC12Bridge.lean`),
takes a `TraceModel T R ap B`; this structure has no inhabitant (`traceModel_false`): its field
`chebotarev` at `g = 1` gives a good prime `q` with `Fr_q = 1`, so `bit_frob` forces `(q/s) = 1` at
every good prime `s ≠ q`, while CRT and Dirichlet (`realizeNat`) and reciprocity give a good `s` with
`(q/s) = −1`. (In the manuscript the Galois group is a finite quotient seeing only the characters of
finitely many `ℚ(√s*)`; the field `bit_frob` quantifies over all good `s`.) So the bridges below
are based on `coefficientRules_symb` / `rulesUpTo_symb`, not on the trace model.

| consumer (lane RC2) | tex | bridge |
|---|---|---|
| `diff_eq_forest` | 2188–2207 | `diff_eq_forest_symb` |
| `minSeed_bits_irrelevant` | 2188–2200 | `minSeed_bits_irrelevant_symb` |
| `partitionable_terminalNonzero` | 2191–2202 | `partitionable_terminalNonzero_symb` |
| `partitionable_of_anchors` | 2192–2206 | `partitionable_of_anchors_symb` |
| `one_symbol_address` | 2222–2238 | `one_symbol_address_symb` |
| `two_symbol_address` | 2240–2288 | `two_symbol_address_symb` |
| `address_general` | 10554–10790 | `address_general_symb` |
| `even_upper_cubes` | 2311–2322 | `even_upper_cubes_symb` |
| `netOp_expansion` | 10635–10650 | `netOp_expansion_symb` |
| `limSymbol_rules`, `cutoff_table_stabilizes`, `odd_stabilization` | 10508–10552 | `limSymbol_rules_symb`, `odd_stabilization_symb` |
| `final_family_graphs` | 2656–2701, 10587–10623 | `final_family_graphs_symb` |
| `addressInput_of_address` (its `hlimRules`, `hevRules`, `hlim`) | 10508–10850 | `addressInput_of_readings` |

The remaining hypotheses are those of the discharging theorems: lane RC12's readings on prime
sets (App F tex 9745–9750, 9905–9953) and the GLUE `ApEven` (`a_p` even at good primes; for the
actual curve it is PROVED in `SymApEven.lean`).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Sym

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ### The dischargers' hypotheses, bundled -/

/-- **The hypotheses of `CoefficientDictionary.coefficientRules_symb`**, bundled: lane RC12's
readings on prime sets at every budget (the fixed-`U` factorization, tex 9745–9750; (O.12) at
coefficient one with the product-label rule, tex 9905–9945; primary isolation, tex 9947–9948) and
the GLUE `ApEven` (tex 9585, 9593). These are the even source's inputs. -/
structure RC12Readings (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) : Prop where
  swap : ∀ B, FixedUFactorization T R B
  o12 : ∀ B, O12Reading T R ap B
  apEven : ApEven T ap
  prim : ∀ B, PrimaryReading T R B

/-- **The hypotheses of `CoefficientDictionary.rulesUpTo_symb`** at the cutoff `W` (budget
`W + 1`), bundled: the inputs of one odd stage (tex 2104–2107, 10533–10538). -/
structure RC12ReadingsUpTo (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (W : ℕ) :
    Prop where
  swap : FixedUFactorization T R (W + 1)
  o12 : O12Reading T R ap (W + 1)
  apEven : ApEven T ap
  prim : PrimaryReading T R (W + 1)

/-- The coefficient rules of the actual symbol from the readings (`coefficientRules_symb`).
Kind: PROVED. -/
theorem RC12Readings.rules {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (h : RC12Readings T R ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_symb T R ap h.swap h.o12 h.apEven h.prim

/-- The stage rules of an actual stage symbol from the readings (`rulesUpTo_symb`).
Kind: PROVED. -/
theorem RC12ReadingsUpTo.rules {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {W : ℕ}
    (h : RC12ReadingsUpTo T R ap W) : RulesUpTo ε (symb T R) W :=
  rulesUpTo_symb T R ap W h.swap h.o12 h.apEven h.prim

/-- **Non-vacuity**: the bundled readings hold for the sign type data and the zero reading (from
the dictionary's `CoefficientDictionary/NonVacuity.lean`). Kind: PROVED. -/
theorem rc12Readings_zero :
    RC12Readings signTypeData (fun _ => (0 : ZMod 2)) (fun _ => (0 : ℤ)) where
  swap _ := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  o12 B := o12Reading_zero signTypeData _ B
  apEven _ _ := ⟨0, rfl⟩
  prim _ := fun _ _ _ _ _ _ _ _ => rfl

/-- **The trace-module model of the coefficient dictionary has no inhabitant** (status record for
`CoefficientDictionary.TraceModel`, `RC12Bridge.lean`; App F tex 9641–9945): `chebotarev` at the
identity gives a good prime `q` with `Fr_q = 1`, so `bit_frob` gives `(q/s) = 1` for every good prime
`s ≠ q`; but a good prime `s` of trivial type with `(s/q) = −1` exists (`realizeNat`: CRT and
Dirichlet), and reciprocity (`TypeData.legBit_rev`) gives `(q/s) = −1`. Hence
`coefficientRules_of_model` and `TraceModel.rulesUpTo_of_model` are vacuous. Kind: PROVED. -/
theorem traceModel_false {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
    (X : TraceModel T R ap B) : False := by
  obtain ⟨q, h, hq, -, hfq⟩ := X.chebotarev 1 ∅
  rw [mul_one, mul_inv_cancel] at hfq
  obtain ⟨x, -, hx, hold, -⟩ := realizeNat T {q} ∅ (by simpa using hq) (fun _ => 0)
    (fun _ _ => 1) (fun _ _ => 0) 1
  obtain ⟨hs, hsq, -, hts⟩ := hx 0 (by norm_num)
  have hne : q ≠ x 0 := fun h => hsq (by simp [h])
  have hbit := X.bit_frob q (x 0) hq hs hne
  rw [hfq, map_one] at hbit
  have hrev := T.legBit_rev hq hs hne
  rw [hold 0 (by norm_num) q (by simp), hts, map_zero, mul_zero, add_zero] at hrev
  rw [hrev] at hbit
  exact absurd hbit (by decide)

/-! ### The seed certificate (`ex:sec7-seed-certificate`) -/

open Classical in
/-- **Forest differences of the actual symbol** (Lemma `ex:sec7-seed-certificate`,
tex 2188–2207: "a certificate gives a nonzero polynomial; iterate contraction along a forest").
Kind: PROVED, from lane RC12's readings at every budget and `ApEven` (`RC12Readings`).
Consumer: lane RC2's `diff_eq_forest` (hypothesis `CoefficientRules ε A` removed); discharger:
`CoefficientDictionary.coefficientRules_symb`. -/
theorem diff_eq_forest_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hR : RC12Readings T R ap) {Γ : Config L} (hΓ : Γ.Compatible ε)
    {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs Γ.V) :
    diff (symb T R) Γ S = if IsForest Γ.V S then symb T R (Γ.contractBy S) else 0 :=
  diff_eq_forest (hR.rules) hΓ hS

/-- **A minimum seed of the actual symbol does not depend on its internal bits**
(Lemma `ex:sec7-seed-certificate`, tex 2188–2191, 2198–2200). Kind: PROVED, from lane RC12's readings at every
budget and `ApEven` (`RC12Readings`). Consumer: lane RC2's
`minSeed_bits_irrelevant`; discharger: `CoefficientDictionary.coefficientRules_symb`. -/
theorem minSeed_bits_irrelevant_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hR : RC12Readings T R ap) {Γ : Config L}
    (hmin : IsMinSeed ε (symb T R) Γ) {Δ : Config L} (hΔ : Δ.Compatible ε) (hV : Δ.V = Γ.V)
    (ht : ∀ v ∈ Γ.V, Δ.t v = Γ.t v) : symb T R Δ = 1 :=
  minSeed_bits_irrelevant (hR.rules) hmin hΔ hV ht

/-- **A partitionable list of the actual symbol has a nonzero terminal polynomial**
(Lemma `ex:sec7-seed-certificate`, tex 2191–2192, 2200–2202). Kind: PROVED, from lane RC12's readings at every
budget and `ApEven` (`RC12Readings`). Consumer: lane RC2's
`partitionable_terminalNonzero`; discharger: `CoefficientDictionary.coefficientRules_symb`. -/
theorem partitionable_terminalNonzero_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} (hR : RC12Readings T R ap) {Γ : Config L}
    (hΓ : Γ.Compatible ε) (hP : IsPartitionable ε (symb T R) Γ) :
    TerminalNonzero (symb T R) Γ :=
  partitionable_terminalNonzero (hR.rules) hΓ hP

/-- **Anchors and a nonempty remainder make a list partitionable, for the actual symbol**
(Lemma `ex:sec7-seed-certificate`, tex 2192–2195, 2203–2206). Kind: PROVED, from lane RC12's readings at every
budget and `ApEven` (`RC12Readings`). Consumer: lane RC2's
`partitionable_of_anchors`; discharger: `CoefficientDictionary.coefficientRules_symb`. -/
theorem partitionable_of_anchors_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hR : RC12Readings T R ap) {Γ₀ Γ : Config L}
    (hmin : IsMinSeed ε (symb T R) Γ₀) (hΓ : Γ.Compatible ε) (htot : Γ.total = Γ₀.total)
    (s : ℕ) (hs : s ∈ Γ₀.V) (anc : ℕ → ℕ) (hanc : Set.InjOn anc (Γ₀.V.erase s))
    (hancV : ∀ v ∈ Γ₀.V.erase s, anc v ∈ Γ.V) (hanct : ∀ v ∈ Γ₀.V.erase s, Γ.t (anc v) = Γ₀.t v)
    (hrem : (Γ.V \ (Γ₀.V.erase s).image anc).Nonempty) : IsPartitionable ε (symb T R) Γ :=
  partitionable_of_anchors (hR.rules) hmin hΓ htot s hs anc hanc hancV
    hanct hrem

/-! ### Addresses (`ex:sec7-one-symbol-address`, `ex:sec7-two-symbol-address`, App G) -/

/-- **One-symbol address lemma for the actual symbol** (Lemma `ex:sec7-one-symbol-address`,
tex 2222–2238). Kind: PROVED, from lane RC12's readings at every
budget and `ApEven` (`RC12Readings`). Consumer: lane RC2's `one_symbol_address`; discharger:
`CoefficientDictionary.coefficientRules_symb`. -/
theorem one_symbol_address_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hR : RC12Readings T R ap) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (hne : Γ.V.Nonempty) (hP : TerminalNonzero (symb T R) Γ) (b : ℕ) (hb : 1 ≤ b) :
    AddressConclusion ε ![symb T R, symb T R] Γ (fun _ => (none : Option (Fin b → ZMod 2))) :=
  one_symbol_address (hR.rules) Γ hΓ hne hP b hb

/-- **Two-symbol address lemma for two actual symbols** (Lemma `ex:sec7-two-symbol-address`,
tex 2240–2288). Kind: PROVED, from lane RC12's readings for both symbols (`RC12Readings`). Consumer: lane RC2's `two_symbol_address` (hypotheses `hA₁`, `hA₂` removed);
discharger: `CoefficientDictionary.coefficientRules_symb` (twice). -/
theorem two_symbol_address_symb {T : TypeData L ε} {R₁ R₂ : Finset ℕ → ZMod 2}
    {ap₁ ap₂ : ℕ → ℤ} (hR₁ : RC12Readings T R₁ ap₁)
    (hR₂ : RC12Readings T R₂ ap₂) (b : ℕ) (hb : 1 ≤ b)
    (Γ : Config L) (hΓ : Γ.Compatible ε) (act' : ℕ → Option (Fin b → ZMod 2))
    (hact : ∀ v ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' v = some w)
    (hall : ∀ w : Fin b → ZMod 2, w ≠ 0 → ∃ v ∈ Γ.V, act' v = some w)
    (hP₁ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero (symb T R₁) (Γ.at act' x))
    (hP₂ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero (symb T R₂) (Γ.at act' x)) :
    AddressConclusion ε ![symb T R₁, symb T R₂] Γ act' :=
  two_symbol_address (hR₁.rules) (hR₂.rules) b hb
    Γ hΓ act' hact hall hP₁ hP₂

/-- **The simultaneous address construction for two actual symbols** (App G Proposition
`ex:app-simultaneous-address`, tex 10554–10790, with anchors and balanced sets as hypotheses).
Kind: PROVED, from lane RC12's readings for both symbols (`RC12Readings`).
Consumer: lane RC2's `address_general`; discharger:
`CoefficientDictionary.coefficientRules_symb` (twice). -/
theorem address_general_symb {T : TypeData L ε} {R₁ R₂ : Finset ℕ → ZMod 2} {ap₁ ap₂ : ℕ → ℤ}
    (hR₁ : RC12Readings T R₁ ap₁)
    (hR₂ : RC12Readings T R₂ ap₂) (b : ℕ) (hb : 0 < b)
    (Γ : Config L) (hΓ : Γ.Compatible ε) (act' : ℕ → Option (Fin b → ZMod 2))
    (hanc : ∀ w : Fin b → ZMod 2, w ≠ 0 → ∃ u ∈ Γ.V, ∀ x : Fin b → ZMod 2,
      ∑ k : Fin b, w k * x k = 1 → u ∈ (Γ.at act' x).V)
    (hbal : ∀ y : Fin b → ZMod 2, y ≠ 0 → ∀ e ∈ pairs (Γ.at act' y).V,
      ∃ R ⊆ Γ.V, (∀ x : Fin b → ZMod 2, Even ((R.filter (· ∈ (Γ.at act' x).V)).card)) ∧
        ∀ a ∈ (Γ.at act' y).V, ∀ c ∈ (Γ.at act' y).V, a ≠ c → (a ∈ R ∧ c ∈ R ↔ s(a, c) = e))
    (hP₁ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero (symb T R₁) (Γ.at act' x))
    (hP₂ : ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero (symb T R₂) (Γ.at act' x)) :
    AddressConclusion ε ![symb T R₁, symb T R₂] Γ act' :=
  address_general (hR₁.rules) (hR₂.rules) b hb Γ
    hΓ act' hanc hbal hP₁ hP₂

/-- **The cubes of the even upper estimate, for the actual symbol** (Proposition
`ex:sec7-even-upper`, tex 2311–2322). Kind: PROVED, from lane RC12's readings at
every budget and `ApEven` (`RC12Readings`). Consumer: lane RC2's `even_upper_cubes`; discharger:
`CoefficientDictionary.coefficientRules_symb`. -/
theorem even_upper_cubes_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hR : RC12Readings T R ap) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (hpart : IsPartitionable ε (symb T R) Γ) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (Γ' : Config L) (act'' : ℕ → Option (Fin b → ZMod 2)),
      Γ'.Compatible ε ∧ Γ.Extends Γ' ∧ symb T R (Γ'.at act'' 0) = symb T R Γ ∧
      (∀ v ∈ Γ'.V, v ∉ Γ.V → Γ'.t v = 0 ∧ ∃ w, w ≠ 0 ∧ act'' v = some w) ∧
      ∀ x : Fin b → ZMod 2, x ≠ 0 → symb T R (Γ'.at act'' x) = 1 :=
  even_upper_cubes (hR.rules) Γ hΓ hpart b hb

/-- **The network operator expansion, for the actual symbol** (App G, tex 10635–10650).
Kind: PROVED, from lane RC12's readings at every budget and `ApEven` (`RC12Readings`).
Consumer: lane RC2's `netOp_expansion`; discharger:
`CoefficientDictionary.coefficientRules_symb`. -/
theorem netOp_expansion_symb {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hR : RC12Readings T R ap) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (Tm Xm : Finset ℕ) (hV : Γ.V = Tm ∪ Xm) (hTX : Disjoint Tm Xm)
    (hX : ∀ x ∈ Xm, Γ.t x = 0) :
    symb T R Γ = act (netOp Γ Tm Xm) (fun U => symb T R ((Γ.restrict Tm).flipBy U)) ∅ :=
  netOp_expansion (hR.rules) Γ hΓ Tm Xm hV hTX hX

/-! ### Odd stabilization (`ex:app-odd-stabilization`) -/

/-- The stage rules of actual odd stage symbols, from lane RC12's readings at the
budget `W + 1` on an ultrafilter-large set of stages for every cutoff (tex 10533–10538). Kind:
PROVED (from `RC12ReadingsUpTo`); discharger: `CoefficientDictionary.rulesUpTo_symb`. -/
theorem rulesUpTo_eventually {I : Type*} (𝒰 : Ultrafilter I) {T : TypeData L ε}
    {R : I → Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hX : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RC12ReadingsUpTo T (R i) ap W) : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RulesUpTo ε (symb T (R i)) W := by
  intro W
  filter_upwards [hX W] with i hi
  exact hi.rules

/-- **The odd limit symbol obeys the coefficient rules** (Proposition `ex:app-odd-stabilization`,
tex 10518–10519, 10545–10546), for the actual odd stage symbols `symb T (R i)`. Kind: PROVED,
from lane RC12's stage readings (`RC12ReadingsUpTo`, on a set of stages in
the ultrafilter, for every cutoff). Consumer: lane RC2's `limSymbol_rules` (hypothesis `hvalid` removed);
discharger: `CoefficientDictionary.rulesUpTo_symb`. -/
theorem limSymbol_rules_symb {I : Type*} (𝒰 : Ultrafilter I) {T : TypeData L ε}
    {R : I → Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hX : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RC12ReadingsUpTo T (R i) ap W) : CoefficientRules ε (limSymbol 𝒰 (fun i => symb T (R i))) :=
  limSymbol_rules 𝒰 ε _ (rulesUpTo_eventually 𝒰 hX)

/-- **Proposition `ex:app-odd-stabilization` for the actual odd stage symbols** (tex 10508–10552):
the limit symbol `limSymbol 𝒰 (symb T ∘ R)` obeys the coefficient rules, and any finite family of
compatible tests is read by the stage symbols as by the limit symbol on a set of stages in the
ultrafilter. Kind: PROVED, from lane RC12's stage readings (`RC12ReadingsUpTo`).
Consumers: lane RC2's `odd_stabilization`, `limSymbol_rules`, `cutoff_table_stabilizes`
(hypothesis `hvalid` removed, the limit symbol named); discharger:
`CoefficientDictionary.rulesUpTo_symb`. -/
theorem odd_stabilization_symb [Finite L] {I : Type*} (𝒰 : Ultrafilter I) {T : TypeData L ε}
    {R : I → Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (hX : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RC12ReadingsUpTo T (R i) ap W) :
    CoefficientRules ε (limSymbol 𝒰 (fun i => symb T (R i))) ∧
      ∀ (n : ℕ) (Γs : Fin n → Config L), (∀ k, (Γs k).Compatible ε) →
        ∀ᶠ i in (𝒰 : Filter I), ∀ k,
          symb T (R i) (Γs k) = limSymbol 𝒰 (fun i => symb T (R i)) (Γs k) := by
  have hvalid := rulesUpTo_eventually (ε := ε) 𝒰 hX
  refine ⟨limSymbol_rules 𝒰 ε _ hvalid, fun n Γs hΓs => ?_⟩
  filter_upwards [cutoff_table_stabilizes 𝒰 ε _ hvalid (∑ k, (Γs k).V.card)] with i hi k
  have hk : (Γs k).V.card ≤ ∑ k, (Γs k).V.card :=
    Finset.single_le_sum (f := fun k => (Γs k).V.card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  exact hi (Γs k) (le_trans hk (Nat.le_succ _)) (hΓs k)

/-! ### The final family (App G zero-total packets and `ex:app-final-family`) -/

/-- **The finite typed graphs of the final family, for the actual odd limit symbol and the actual
even source** (tex 2656–2672, 2695–2701; App G 10587–10623): the odd symbol is the limit
`limSymbol 𝒰 (symb T₁ ∘ R₁)` of actual odd stage symbols, the even symbol is `symb T₂ R₂`.
Kind: PROVED, from lane RC12's odd stage readings (`RC12ReadingsUpTo`, on the
ultrafilter, every cutoff) and even readings (`RC12Readings`). Consumer: lane RC2's
`final_family_graphs` (hypotheses `hA₁`, `hA₂` removed); dischargers:
`CoefficientDictionary.rulesUpTo_symb` (through `limSymbol_rules`) and
`CoefficientDictionary.coefficientRules_symb`. -/
theorem final_family_graphs_symb [Fintype L] [DecidableEq L] (hL : ∀ x : L, x + x = 0)
    {L₁ L₂ : Type*} [AddCommGroup L₁] [AddCommGroup L₂]
    {ε₁ : L₁ →+ ZMod 2} {ε₂ : L₂ →+ ZMod 2}
    (π₁ : L →+ L₁) (π₂ : L →+ L₂) (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (hε₁ : ∀ x, ε₁ (π₁ x) = ε x) (hε₂ : ∀ x, ε₂ (π₂ x) = ε x)
    {I : Type*} (𝒰 : Ultrafilter I) {T₁ : TypeData L₁ ε₁} {R₁ : I → Finset ℕ → ZMod 2}
    {ap₁ : ℕ → ℤ}
    (hX₁ : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RC12ReadingsUpTo T₁ (R₁ i) ap₁ W)
    {T₂ : TypeData L₂ ε₂} {R₂ : Finset ℕ → ZMod 2} {ap₂ : ℕ → ℤ}
    (hR₂ : RC12Readings T₂ R₂ ap₂)
    {Γ₁ : Config L₁} {Γ₂ : Config L₂}
    (hm₁ : IsMinSeed ε₁ (limSymbol 𝒰 (fun i => symb T₁ (R₁ i))) Γ₁)
    (hm₂ : IsMinSeed ε₂ (symb T₂ R₂) Γ₂) (ht₁ : Γ₁.total = 0) (ht₂ : Γ₂.total = 0)
    (b : ℕ) (hb : 1 ≤ b) :
    ∃ (Γ : Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε ∧ (∀ v ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' v = some w) ∧
      AddressConclusion ε ![fun Δ => limSymbol 𝒰 (fun i => symb T₁ (R₁ i)) (Δ.mapType π₁),
        fun Δ => symb T₂ R₂ (Δ.mapType π₂)] Γ act' ∧
      ∀ x : Fin b → ZMod 2, x ≠ 0 → (Γ.at act' x).total = 0 :=
  final_family_graphs hL π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ (limSymbol_rules_symb 𝒰 hX₁)
    (hR₂.rules) hm₁ hm₂ ht₁ ht₂ b hb

open ZInQ.Contrib.CloudB3RC53.AppGEndpoints (AddressInput omega) in
/-- **`AddressInput` from the address construction, the coefficient rules and the common stage
discharged** (bridge for Proposition `ex:app-final-family`, tex 10792–10850, consuming tex
10508–10791). The odd stage tables are the actual stage symbols `Aodd θ = symb T₁ (Rodd θ)`, the
odd limit symbol is `limSymbol U Aodd`, and the even symbol is `symb T₂ Rev`. Kind: PROVED, from
lane RC12's odd stage readings (`RC12ReadingsUpTo`, on the ultrafilter, every cutoff) and even
readings (`RC12Readings`), finiteness of the odd type alphabet, and the remaining
hypotheses of lane RC2's `addressInput_of_address` (minimum seeds of total zero, prime
realization at a stage, the odd and even readings). Consumer: lane RC2's
`addressInput_of_address`, whose hypotheses `hlimRules`, `hevRules` and `hlim` are removed;
dischargers: `limSymbol_rules_symb` and `odd_stabilization_symb` (from
`CoefficientDictionary.rulesUpTo_symb`) and
`CoefficientDictionary.coefficientRules_symb`. -/
theorem addressInput_of_readings
    (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (prepared : ℤ → Prop) (Lstar : ℤ → ℚ) (k δ CeFinal : ℤ) (Ccoarse : ℚ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop)
    {L L₁ L₂ : Type*} [AddCommGroup L] [Fintype L] [DecidableEq L] [AddCommGroup L₁]
    [Finite L₁] [AddCommGroup L₂] (hL : ∀ x : L, x + x = 0) (ε : L →+ ZMod 2)
    (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) (hε₁ : ∀ x, ε₁ (π₁ x) = ε x)
    (hε₂ : ∀ x, ε₂ (π₂ x) = ε x)
    (T₁ : TypeData L₁ ε₁) (Rodd : ℕ → Finset ℕ → ZMod 2) (ap₁ : ℕ → ℤ)
    (hX₁ : ∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), RC12ReadingsUpTo T₁ (Rodd θ) ap₁ W)
    (T₂ : TypeData L₂ ε₂) (Rev : Finset ℕ → ZMod 2) (ap₂ : ℕ → ℤ)
    (hR₂ : RC12Readings T₂ Rev ap₂)
    {Γ₁ : Config L₁} {Γ₂ : Config L₂}
    (hm₁ : IsMinSeed ε₁ (limSymbol U (fun θ => symb T₁ (Rodd θ))) Γ₁)
    (hm₂ : IsMinSeed ε₂ (symb T₂ Rev) Γ₂) (ht₁ : Γ₁.total = 0) (ht₂ : Γ₂.total = 0)
    (Realizes : ℕ → Config L → ℤ → Prop)
    (hreal : ∀ (θ b : ℕ) (Γ : Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Fam, ∃ hdim : dim F = b, FamAdm F ∧ ∀ x : Fin b → ZMod 2, x ≠ 0 →
        Realizes θ (Γ.at act' x) (hfam F (x ∘ Fin.cast hdim)))
    (hrealω : ∀ (θ : ℕ) (Δ : Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      omega D = Δ.V.card ∧ prepared D)
    (hodd : ∀ (θ T W : ℕ) (Δ : Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ W → W + 1 ≤ T → (((max 0 (δ + W) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', adm θ D' → omega D' ≤ T → v θ D' < M θ →
        (((omega D' : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D') →
      max 0 (δ + W) + 2 ≤ (M θ : ℤ) → (T : ℤ) + δ < M θ →
      symb T₁ (Rodd θ) (Δ.mapType π₁) = 1 → adm θ D ∧
        v θ D = (((omega D : ℤ) + δ : ℤ) : WithTop ℤ))
    (hev : ∀ (θ : ℕ) (Δ : Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      symb T₂ Rev (Δ.mapType π₂) = 1 →
      Lstar (D * k) ≠ 0 ∧ padicValRat 2 (Lstar (D * k)) ≤ 2 * (omega D : ℤ) + CeFinal) :
    AddressInput U M v adm prepared Lstar k δ CeFinal Ccoarse Fam dim hfam FamAdm :=
  addressInput_of_address U M v adm prepared Lstar k δ CeFinal Ccoarse Fam dim hfam FamAdm hL ε
    ε₁ ε₂ π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ (fun θ => symb T₁ (Rodd θ))
    (limSymbol U (fun θ => symb T₁ (Rodd θ))) (symb T₂ Rev)
    (odd_stabilization_symb U hX₁).1 (hR₂.rules)
    (odd_stabilization_symb U hX₁).2 hm₁ hm₂ ht₁ ht₂ Realizes hreal hrealω hodd hev

end ZInQ.Manuscript.RC.GlueSweep.Sym
