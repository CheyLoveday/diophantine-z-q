import ZInQKernel.Contrib.OneProof.RC.Wiring.FinalFamily
import ZInQKernel.Contrib.OneProof.RC.Symbols.AddressInputBridge
import ZInQKernel.Contrib.OneProof.RC.Symbols.Stabilization
import ZInQKernel.Contrib.OneProof.RC.KSplit.B3
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-!
# Theorem 5.3, Lane RC0 round 2: the address input from lane RC2's construction (App G)

The leaf `AddressLeaf W` (`FinalFamily.lean`) asks, in Branch 2 and for every choice of the
constants of (F.3), (3.4) at the companions, (3.5) and (O.8), for batch 3's
`AppGEndpoints.AddressInput` at `δ_o` with the coarse constant
`C_coarse = C_gen/2 + C_det`, `C_gen = 2A + C_R + C_E − v₂L_*(h_*) + (C_per + 2)` of (F.4), (F.5)
(App G `ex:app-odd-stabilization`, `ex:app-simultaneous-address`, `ex:app-final-family`, tex
10508–10861). Lane RC2 proved (`Symbols.addressInput_of_address`) that `AddressInput` follows
from its address construction (PROVED from the coefficient rules: zero-total packets, the
two-symbol address lemma, the network operators, (G.1a)) and explicit hypotheses. This file:

* states those hypotheses over the round-2 data as one proposition `AddressPackage W C_coarse`,
  every conjunct with its tex lines, kind and owner (docstring of `AddressPackage`), and proves
  `addressInput_of_package` (from RC2's theorem) and `addressLeaf_of_package`;
* wires lane RC3's `K`-split seed (`KSplit.ksplit_seed_b3`, Lemma `ex:sec7-ksplit-seed`, tex
  2628–2654): the nonempty unit seed of the even source of `E^{(k)}` is no longer a hypothesis.
  What remains of it is Elliot's conditional App G congruence `a_p(E^{(k)}) ≡ p + 1 (mod 8)` under
  the assumed absence of a nonempty unit seed (tex 2636–2641, 10319–10481; lane RC3 reduces it
  further to its `NoSeedTraceData` interface, `ksplitCongruence_of_traceData`) and the arithmetic
  side conditions on `ℓ` and `k` (tex 2596–2601). The elementary half — a fresh good `K`-split
  prime with `v₂(p + 1 − a_p(E^{(k)})) = 2`, tex 2643–2653, 10482–10500 — is lane RC3's PROVED
  `exists_ksplit_prime_v2_eq_two_b3`;
* proves the minimum nonempty seeds of total type zero, for both symbols, from nonempty unit seeds
  and the filter conditions (well-ordering of the vertex counts; tex 2176–2180, 2590–2593, 10504,
  10589–10596);
* corrects one hypothesis of RC2's bridge: RC2 asks that **every** realized compatible
  configuration keep the fixed local types (`prepared`), which fails for configurations of nonzero
  total type (their products lie outside the prepared positive filter); only the active
  configurations of the address construction, of total type zero, need it.
  `addressInput_of_address_zeroTotal` is RC2's argument with that one change, and
  `AddressPackageZeroTotal` (weaker than `AddressPackage`, `addressPackageZeroTotal_of_package`)
  is the dischargeable form;
* gives a finer form `AddressPackageStaged`, in which the odd limit symbol, its coefficient rules
  and the common-stage property are produced by lane RC2's PROVED `Symbols.odd_stabilization`
  from the stage tables (tex 10508–10552), with `addressPackageZeroTotal_of_staged` (PROVED);
* gives the finest form `AddressPackageDict`, in which both coefficient rules are batch 3's
  PROVED `CoefficientDictionary.rulesUpTo_symb` (odd stage tables) and `coefficientRules_symb`
  (even source of `E^{(k)}`) from lane RC12's readings on prime sets, with
  `addressPackageStaged_of_dict` (PROVED).

Kinds: `PROVED` (Lean proof), `ELLIOT` (Elliot's step, stated), `GLUE` (textbook fact),
`definition` (a property the construction of the object gives by definition).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter

/-! ## Minimum seeds and the `K`-split seed -/

section Seeds

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {A : Symbols.Config L → ZMod 2}

/-- **A least nonempty unit seed exists once a nonempty unit seed exists** (PROVED:
well-ordering of the vertex counts). Definition `ex:sec7-seed-partition` (tex 2176–2180: "A
minimum nonempty seed has the least positive vertex count among such seeds"); "take a least
nonempty odd unit seed" (tex 2590–2593, 10504); the even seed "of least positive size" (tex
2659–2662). -/
theorem exists_minSeed_of_unitSeed
    (h : ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε A Γ ∧ Γ.V.Nonempty) :
    ∃ Γ : Symbols.Config L, Symbols.IsMinSeed ε A Γ := by
  classical
  have hex : ∃ n : ℕ, ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε A Γ ∧ Γ.V.Nonempty ∧
      Γ.V.card = n := by
    obtain ⟨Γ, hu, hne⟩ := h
    exact ⟨_, Γ, hu, hne, rfl⟩
  obtain ⟨Γ, hu, hne, hcard⟩ := Nat.find_spec hex
  refine ⟨Γ, hu, hne, fun Δ hΔ hΔne => ?_⟩
  rw [hcard]
  exact Nat.find_min' hex ⟨Δ, hΔ, hΔne, rfl⟩

/-- **A minimum nonempty seed of total type zero** (PROVED), from a nonempty unit seed and the
filter condition: every unit seed lies in the symbol's filter, whose total type is that of `1`,
i.e. zero (tex 2042–2044, 2079, 10589–10596: "Both final symbols have projected total label
zero … Every nonzero coefficient, and hence every unit seed, lies in its respective filter"). -/
theorem exists_minSeed_total_zero
    (h : ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε A Γ ∧ Γ.V.Nonempty)
    (hfilt : ∀ Γ : Symbols.Config L, Symbols.IsUnitSeed ε A Γ → Γ.total = 0) :
    ∃ Γ : Symbols.Config L, Symbols.IsMinSeed ε A Γ ∧ Γ.total = 0 := by
  obtain ⟨Γ, hm⟩ := exists_minSeed_of_unitSeed h
  exact ⟨Γ, hm, hfilt Γ hm.1⟩

/-- **The nonempty `K`-split seed of the even source of `E^{(k)}`** (PROVED from lane RC3's
`KSplit.ksplit_seed_b3`; Lemma `ex:sec7-ksplit-seed`, tex 2628–2654, and the nonempty even seed of
Proposition `ex:app-nonempty-seeds`, tex 10259–10267, 10482–10501). For admissible `ℓ`, odd
squarefree `k` with a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` (fresh ramification of `K = ℚ(√k)`, tex
2600–2601, 10484–10486): if the absence of a nonempty unit seed of the symbol `A` forced the App G
congruence `a_p(E^{(k)}) ≡ p + 1 (mod 8)` at every good `K`-split prime outside a finite support
(Elliot's coefficient calculation, tex 2636–2641, 10319–10481), then a nonempty unit seed exists:
RC3's fresh `K`-split prime with `v₂(p + 1 − a_p(E^{(k)})) = 2` (tex 2643–2653, 10482–10500)
contradicts the congruence. -/
theorem exists_unitSeed_of_ksplit {ℓ : ℕ} (hℓ : Adm ℓ) {k : ℤ} (hk_odd : Odd k)
    (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k)
    (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (Sev : Finset ℕ)
    (hG : (¬ ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε A Γ ∧ Γ.V.Nonempty) →
      KSplit.AppGCongruenceB3 ℓ k Sev) :
    ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε A Γ ∧ Γ.V.Nonempty := by
  by_contra hno
  exact KSplit.ksplit_seed_b3 hℓ hk_odd hk_sf hq₀ hq₀k hq₀ℓ Sev _ hG hno

end Seeds

/-- **The `K`-split conjunct from lane RC3's no-seed trace data** (PROVED from
`KSplit.appGCongruence_of_traceData`; tex 10319–10481): if the absence of a nonempty unit seed
gives, at every fresh good `K`-split prime `p` outside the support, lane RC3's `NoSeedTraceData`
of the transported source with `a_p = a_p(E^{(k)})` ((E.12), `a(1) = 1`, `ψ/η = χ₋₁`, integrality
of `H` (O.11), the trace identity, the `d(φ)` block action, the Hecke formula at `p′`, (G.4a),
(G.4b), `v₂ a(pp′) ≥ 3`), then it gives the App G congruence used by
`exists_unitSeed_of_ksplit`. -/
theorem ksplitCongruence_of_traceData {Fc : Type*} [Field Fc] [CharZero Fc] (O : Subring Fc)
    {ℓ : ℕ} {k : ℤ} {S : Finset ℕ} (NoSeed : Prop)
    (hD : NoSeed → ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S → ¬ (p : ℤ) ∣ 6 * (k * ℓ) →
      jacobiSym k p = 1 → Nonempty (@KSplit.NoSeedTraceData Fc _ O p ⟨hp⟩
        ((ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p))) :
    NoSeed → KSplit.AppGCongruenceB3 ℓ k S := fun h =>
  (KSplit.appGCongruenceB3_iff ℓ k S).mpr (KSplit.appGCongruence_of_traceData O (hD h))

/-- **The side conditions of the `K`-split seed are satisfiable** (PROVED; non-vacuity of
conjuncts 1–4 of `AddressPackage`): `ℓ = 11`, `k = −7`, `q₀ = 7` (as in lane RC3's
`exists_ksplit_prime_example`). -/
theorem ksplit_sideConditions_example :
    Adm 11 ∧ Odd (-7 : ℤ) ∧ Squarefree (-7 : ℤ) ∧
      ∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ -7 ∧ ¬ q₀ ∣ 2 * 11 := by
  have h11 : Nat.Prime 11 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  refine ⟨⟨by norm_num, (Nat.prime_iff.mp h11).squarefree, by norm_num⟩, ⟨-4, by norm_num⟩,
    ?_, 7, h7, by norm_num, by norm_num⟩
  rw [← Int.squarefree_natAbs]
  exact (Nat.prime_iff.mp h7).squarefree

/-! ## The address package (lane RC2's hypotheses, verbatim instance) -/

/-- **The address package at `C_coarse`**: lane RC2's hypotheses of
`Symbols.addressInput_of_address`, instantiated with the round-2 data (`U = 𝒰` the stage
ultrafilter `W.stages`, `M = M_θ`, `v θ D = v₂ a_{M_θ}(D)`, `adm = W.admissible`,
`prepared = W.prepared`, `L_* = W.Lstar`, `k = W.kfin`, `δ = δ_o = W.δo`, `Fam = Family`,
`dim = Family.b`, `hfam = Family.h`, `FamAdm = Family.Admissible W.S W.kfin`), with the seed
hypotheses split: the minimum seeds of total type zero are PROVED from nonempty unit seeds and the
filters (`exists_minSeed_total_zero`), and the nonempty even seed is lane RC3's `K`-split seed
(`exists_unitSeed_of_ksplit`), whose side conditions on `ℓ` and `k` come first. `ω` is batch 3's
`AppGEndpoints.omega` (the skeleton's `omega`, `omega_eq_appG`).

The abstract objects have no Mathlib counterpart (DEPARTURE of form, lane RC2's D1–D10) and are
existentially quantified; the package is discharged by exhibiting the genuine ones and proving the
conjuncts: `L` the common alphabet of realizable types of good `K`-split primes outside the support
(an additive group with the sign coordinate `ε_v = (p_v − 1)/2`), `L₁, L₂` the intrinsic odd and
even alphabets with the projections `π₁, π₂`, `Aodd θ` the odd stage table at stage `θ`, `AoddLim`
the odd limit symbol, `Aev` the normalized even source of `E^{(k)}` as a symbol on typed graphs,
`Realizes θ Δ D`: `D = ∏ q^*` over a prime realization of the active typed graph `Δ` at stage `θ`.

| # | conjunct | tex | kind | owner |
|---|---|---|---|---|
| 1 | `Adm ℓ` | 1005–1011 | hypothesis of Theorem 5.3 | top layer |
| 2 | `k` odd (`k` is a square at `2`) | 2596 | ELLIOT (choice of the companion) | companion: RC2 / RC11 / RC13 |
| 3 | `k` squarefree | 2596–2599 | ELLIOT (as in `CompanionLeaf`) | companion |
| 4 | a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` | 2600–2601, 2613–2614, 10277–10278, 10484–10486 | ELLIOT (fresh ramification; lane RC3's form) | companion |
| 5 | `C_{e,final}`, the constant of the normalized even unit | 10320–10322, 10854–10857 | definition (one fixed period normalization) | RC11 |
| 6 | `L` finite with `x + x = 0`; the signs `ε` | 2015–2041, 2656–2657, 10525–10532 | definition (RC2 D2) | RC2 |
| 7 | `π₁, π₂` separately surjective; `ε₁ ∘ π₁ = ε`, `ε₂ ∘ π₂ = ε` | 2060–2065, 2656–2658, 10270–10273, 10283–10286, 10519–10521, 10549–10551 | ELLIOT (fresh ramification lifts each old odd label to a `K`-split label, 2600–2608) | RC2; stabilized alphabet batch 3 / RC2 |
| 8 | `CoefficientRules ε₁ AoddLim` | 2102–2136; App F 9447–9976; inherited by the limit 10545–10547 | ELLIOT (PROVED by RC2's `odd_stabilization` from the stage rules: `AddressPackageStaged`) | RC12 (App F), RC2 |
| 9 | `CoefficientRules ε₂ Aev` | 2102–2136; App F 9447–9976 (transported source 10288–10318) | ELLIOT | RC12 (App F), RC11 (source) |
| 10 | common stage: on finitely many compatible graphs, `Aodd θ = AoddLim` on a set of `𝒰` | 10512–10523, 10533–10548 | ELLIOT (PROVED by RC2's `odd_stabilization`: `AddressPackageStaged`) | RC2, RC12 |
| 11 | a nonempty unit seed of `AoddLim` | 2588–2593, 10268–10270, 10501–10505 | ELLIOT (bounded-weight witness; the odd empty configuration is not a unit) | RC3 seeds; batch 3 GenusOdd (witness) |
| 12 | unit seeds of `AoddLim` have total type `0` | 2042–2044, 2079, 10236–10240, 10589–10596 | definition (zero off the filter containing `1`) | RC2, RC12 |
| 13 | unit seeds of `Aev` have total type `0` | 2042–2044, 2079, 10264–10265, 10591–10594 | definition (positive square-unit filter containing `1`) | RC11, RC2 |
| 14 | no nonempty unit seed of `Aev` ⇒ `a_p(E^{(k)}) ≡ p + 1 (mod 8)` at the good `K`-split `p` outside a finite support | 2636–2641, 10319–10481 | ELLIOT (App G calculation; RC3 reduces it to `NoSeedTraceData`: `ksplitCongruence_of_traceData`) | RC3; RC11 (transported source); RC2 (abstract seeds as `K`-split products) |
| 15 | prime realization, at any stage, of a compatible typed graph with nonzero activations by an admissible family | 2151–2174, 2670–2672, 10582–10585, 10785–10788, 10825–10828 | GLUE/ELLIOT (finite CRT, Dirichlet, reciprocity PROVED: RC2's `finite_realization`) | RC2 |
| 16 | a realization has `ω(D) = |V(Δ)|` and keeps the fixed local types (`prepared D`) | 2678–2686, 10795–10804 | definition/GLUE — **as stated by RC2, too strong: see below** | RC2 |
| 17 | odd reading at a valid stage: `Aodd θ = 1` ⇒ `D` admissible and `v₂a_M(D) = δ_o + ω(D)` | 2068–2079, 9670–9704, 10236–10249 (F.7), 10846–10850 | ELLIOT/definition | RC12; batch 3 AppGEndpoints |
| 18 | even reading: `Aev = 1` ⇒ `L_*(Dk) ≠ 0`, `v₂L_*(Dk) ≤ 2ω(D) + C_{e,final}` | (E.11) 8141, (F.1) 10079–10094, 10288–10322, 10854–10855 | ELLIOT | RC11 |

Given conjuncts 1–4, conjunct 14 is equivalent to the existence of a nonempty unit seed of `Aev`
(lane RC3's `not_appGCongruence`: the congruence fails for every finite support); the wiring
removes the elementary half of Lemma `ex:sec7-ksplit-seed` (PROVED by lane RC3) and leaves the
owner Elliot's conditional derivation, the form in which the text proves the lemma.

**Conjunct 16 as RC2 states it cannot hold for the genuine objects.** It asks `prepared D` for the
realization of *every* compatible configuration, while conjunct 15 realizes every compatible typed
graph at every nonzero address. A faithful realization of a configuration of nonzero total type
lies outside the prepared positive filter (`PreparedSpec`: prepared ⇒ positive and prime to the
support; e.g. one active vertex of sign type `1` realizes to `q^* < 0`), and an unfaithful one
breaks the readings 17, 18 at the zero-total addresses of the same graph. RC2's proof uses
conjunct 16 only at the active configurations of the address construction, which have total type
zero (RC2's `final_family_graphs`). The dischargeable form is `AddressPackageZeroTotal`. -/
def AddressPackage {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4) the side conditions of the `K`-split seed
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  -- (5) the constant of the normalized even unit, and the abstract objects
  ∃ CeFinal : ℤ,
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (Aodd : ℕ → Symbols.Config L₁ → ZMod 2) (AoddLim : Symbols.Config L₁ → ZMod 2)
    (Aev : Symbols.Config L₂ → ZMod 2) (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7) the common alphabet and its two projections
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x) = ε x) ∧
    -- (8), (9) the coefficient rules
    Symbols.CoefficientRules ε₁ AoddLim ∧ Symbols.CoefficientRules ε₂ Aev ∧
    -- (10) the common stage
    (∀ (n : ℕ) (Γs : Fin n → Symbols.Config L₁), (∀ i, (Γs i).Compatible ε₁) →
      ∀ᶠ θ in (W.stages : Filter ℕ), ∀ i, Aodd θ (Γs i) = AoddLim (Γs i)) ∧
    -- (11), (12) the odd seed and the odd filter
    (∃ Γ₁ : Symbols.Config L₁, Symbols.IsUnitSeed ε₁ AoddLim Γ₁ ∧ Γ₁.V.Nonempty) ∧
    (∀ Γ : Symbols.Config L₁, Symbols.IsUnitSeed ε₁ AoddLim Γ → Γ.total = 0) ∧
    -- (13) the even filter
    (∀ Γ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ Aev Γ → Γ.total = 0) ∧
    -- (14) the `K`-split seed: Elliot's conditional congruence
    (∃ Sev : Finset ℕ,
      (¬ ∃ Γ₂ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ Aev Γ₂ ∧ Γ₂.V.Nonempty) →
        KSplit.AppGCongruenceB3 ℓ W.kfin Sev) ∧
    -- (15), (16) prime realization at a stage
    (∀ (θ b : ℕ) (Γ : Symbols.Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Family, ∃ hdim : F.b = b, Family.Admissible W.S W.kfin F ∧
        ∀ x : Fin b → ZMod 2, x ≠ 0 → Realizes θ (Γ.at act' x) (F.h (x ∘ Fin.cast hdim))) ∧
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      AppGEndpoints.omega D = Δ.V.card ∧ W.prepared D) ∧
    -- (17) the odd reading at a valid stage
    (∀ (θ T Wb : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ Wb → Wb + 1 ≤ T → (((max 0 (W.δo + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', W.admissible θ D' → AppGEndpoints.omega D' ≤ T → vZ (W.aθ θ D') < W.Mθ θ →
        (((AppGEndpoints.omega D' : ℤ) + W.δo : ℤ) : WithTop ℤ) ≤ vZ (W.aθ θ D')) →
      max 0 (W.δo + Wb) + 2 ≤ (W.Mθ θ : ℤ) → (T : ℤ) + W.δo < W.Mθ θ →
      Aodd θ (Δ.mapType π₁) = 1 →
      W.admissible θ D ∧
        vZ (W.aθ θ D) = (((AppGEndpoints.omega D : ℤ) + W.δo : ℤ) : WithTop ℤ)) ∧
    -- (18) the even reading
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Aev (Δ.mapType π₂) = 1 →
      W.Lstar (D * W.kfin) ≠ 0 ∧
        padicValRat 2 (W.Lstar (D * W.kfin)) ≤ 2 * (AppGEndpoints.omega D : ℤ) + CeFinal)

/-- **The address input from the package** (PROVED from lane RC2's
`Symbols.addressInput_of_address`, lane RC3's `KSplit.ksplit_seed_b3` through
`exists_unitSeed_of_ksplit`, and `exists_minSeed_total_zero`). -/
theorem addressInput_of_package {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackage W Ccoarse) :
    ∃ CeFinal : ℤ, AppGEndpoints.AddressInput W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd))
      W.admissible W.prepared W.Lstar W.kfin W.δo CeFinal Ccoarse Family Family.b Family.h
      (Family.Admissible W.S W.kfin) := by
  obtain ⟨hℓ, hk_odd, hk_sf, ⟨q₀, hq₀, hq₀k, hq₀ℓ⟩, CeFinal, L, L₁, L₂, _, _, _, _, _, ε, ε₁,
    ε₂, π₁, π₂, Aodd, AoddLim, Aev, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, hlimRules, hevRules, hlim,
    hseed₁, hfilt₁, hfilt₂, ⟨Sev, hG⟩, hreal, hrealω, hodd, hev⟩ := h
  obtain ⟨Γ₁, hm₁, ht₁⟩ := exists_minSeed_total_zero hseed₁ hfilt₁
  obtain ⟨Γ₂, hm₂, ht₂⟩ := exists_minSeed_total_zero
    (exists_unitSeed_of_ksplit hℓ hk_odd hk_sf hq₀ hq₀k hq₀ℓ Sev hG) hfilt₂
  exact ⟨CeFinal, Symbols.addressInput_of_address W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd))
    W.admissible W.prepared W.Lstar W.kfin W.δo CeFinal Ccoarse Family Family.b Family.h
    (Family.Admissible W.S W.kfin) hL ε ε₁ ε₂ π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ Aodd AoddLim Aev hlimRules
    hevRules hlim hm₁ hm₂ ht₁ ht₂ Realizes hreal hrealω hodd hev⟩

/-- **The address package, for every choice of the constants supplied by the other inputs**
(App G tex 10508–10861; ELLIOT; owners as in `AddressPackage`): in Branch 2, for all constants
`A, C_E, C_R, C_per, C_det` satisfying (F.3), (3.4) at the companions, (3.5) and (O.8), the
package at the coarse constant `C_coarse = C_gen/2 + C_det` of (F.5). -/
def AddressPackageLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackage W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **`AddressLeaf` from the package** (PROVED). -/
theorem addressLeaf_of_package {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf W) :
    AddressLeaf W := by
  intro A CE CR Cper Cdet h33 h34 h35 hvis hU
  exact addressInput_of_package W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

/-! ## The dischargeable form: fixed local types at zero total type only -/

/-- **`AddressInput` from the address construction, the fixed local types being required only
at configurations of total type zero** (PROVED; lane RC2's proof of
`Symbols.addressInput_of_address` with one change). The hypotheses are RC2's, except that the
realization keeps the fixed local types (`prepared`) only for configurations of total type zero
(the filter containing `1`, tex 2042–2044, 2686, 10589–10596, 10804). The proof reads it at the
active configurations of the final graph: they have total type zero (RC2's
`final_family_graphs`, last clause, carried to the extended graph by RC2's `total_at_of_extends`:
the adjoined auxiliaries are primary, tex 10622–10623). -/
theorem addressInput_of_address_zeroTotal
    (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (prepared : ℤ → Prop) (Lstar : ℤ → ℚ) (k δ CeFinal : ℤ) (Ccoarse : ℚ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop)
    {L L₁ L₂ : Type*} [AddCommGroup L] [Fintype L] [DecidableEq L] [AddCommGroup L₁]
    [AddCommGroup L₂] (hL : ∀ x : L, x + x = 0) (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2)
    (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂) (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) (hε₁ : ∀ x, ε₁ (π₁ x) = ε x) (hε₂ : ∀ x, ε₂ (π₂ x) = ε x)
    (Aodd : ℕ → Symbols.Config L₁ → ZMod 2) (AoddLim : Symbols.Config L₁ → ZMod 2)
    (Aev : Symbols.Config L₂ → ZMod 2)
    (hlimRules : Symbols.CoefficientRules ε₁ AoddLim)
    (hevRules : Symbols.CoefficientRules ε₂ Aev)
    (hlim : ∀ (n : ℕ) (Γs : Fin n → Symbols.Config L₁), (∀ i, (Γs i).Compatible ε₁) →
      ∀ᶠ θ in (U : Filter ℕ), ∀ i, Aodd θ (Γs i) = AoddLim (Γs i))
    {Γ₁ : Symbols.Config L₁} {Γ₂ : Symbols.Config L₂} (hm₁ : Symbols.IsMinSeed ε₁ AoddLim Γ₁)
    (hm₂ : Symbols.IsMinSeed ε₂ Aev Γ₂) (ht₁ : Γ₁.total = 0) (ht₂ : Γ₂.total = 0)
    (Realizes : ℕ → Symbols.Config L → ℤ → Prop)
    (hreal : ∀ (θ b : ℕ) (Γ : Symbols.Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Fam, ∃ hdim : dim F = b, FamAdm F ∧ ∀ x : Fin b → ZMod 2, x ≠ 0 →
        Realizes θ (Γ.at act' x) (hfam F (x ∘ Fin.cast hdim)))
    (hrealω : ∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      AppGEndpoints.omega D = Δ.V.card ∧ (Δ.total = 0 → prepared D))
    (hodd : ∀ (θ T Wb : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ Wb → Wb + 1 ≤ T → (((max 0 (δ + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', adm θ D' → AppGEndpoints.omega D' ≤ T → v θ D' < M θ →
        (((AppGEndpoints.omega D' : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D') →
      max 0 (δ + Wb) + 2 ≤ (M θ : ℤ) → (T : ℤ) + δ < M θ →
      Aodd θ (Δ.mapType π₁) = 1 →
      adm θ D ∧ v θ D = (((AppGEndpoints.omega D : ℤ) + δ : ℤ) : WithTop ℤ))
    (hev : ∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Aev (Δ.mapType π₂) = 1 →
      Lstar (D * k) ≠ 0 ∧
        padicValRat 2 (Lstar (D * k)) ≤ 2 * (AppGEndpoints.omega D : ℤ) + CeFinal) :
    AppGEndpoints.AddressInput U M v adm prepared Lstar k δ CeFinal Ccoarse Fam dim hfam
      FamAdm := by
  classical
  refine ⟨1, fun b hb => ?_⟩
  obtain ⟨Γ, act', -, hact, ⟨Γ', act'', hΓ', hext, hactΓ, hnew, hunit⟩, htot⟩ :=
    Symbols.final_family_graphs hL π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ hlimRules hevRules hm₁ hm₂ ht₁ ht₂ b hb
  have hact' : ∀ u ∈ Γ'.V, ∃ w, w ≠ 0 ∧ act'' u = some w := by
    intro u hu
    by_cases huΓ : u ∈ Γ.V
    · rw [hactΓ u huΓ]; exact hact u huΓ
    · exact (hnew u hu huΓ).2
  let eY := Fintype.equivFin {x : Fin b → ZMod 2 // x ≠ 0}
  let Γs : Fin (Fintype.card {x : Fin b → ZMod 2 // x ≠ 0}) → Symbols.Config L₁ :=
    fun i => (Γ'.at act'' (eY.symm i).1).mapType π₁
  have hΓs : ∀ i, (Γs i).Compatible ε₁ := fun i =>
    (Symbols.Config.at_compatible hΓ' act'' _).mapType' π₁ hε₁
  refine ⟨Γ'.V.card, 1, fun _ => {θ | ∀ i, Aodd θ (Γs i) = AoddLim (Γs i)},
    fun _ => hlim _ Γs hΓs, ?_⟩
  intro T hT1 hT2 θ hθ hF6 hM1 hM2
  have hθ' : ∀ i, Aodd θ (Γs i) = AoddLim (Γs i) := Set.mem_iInter.mp hθ 0
  obtain ⟨F, hdim, hFadm, hR⟩ := hreal θ b Γ' act'' hΓ' hact'
  refine ⟨F, hdim, hFadm, fun y hy => ?_⟩
  set x : Fin b → ZMod 2 := y ∘ Fin.cast hdim.symm with hxdef
  have hxy : x ∘ Fin.cast hdim = y := by
    funext i
    simp [hxdef]
  have hx : x ≠ 0 := by
    intro h0
    apply hy
    rw [← hxy, h0]
    rfl
  have hRx := hR x hx
  rw [hxy] at hRx
  have hcx : (Γ'.at act'' x).Compatible ε := Symbols.Config.at_compatible hΓ' act'' x
  have htx : (Γ'.at act'' x).total = 0 := by
    rw [Symbols.total_at_of_extends Γ Γ' act' act'' hext hactΓ
      (fun u hu hu' => (hnew u hu hu').1) x]
    exact htot x hx
  obtain ⟨hω, hprep⟩ := hrealω θ _ _ hcx hRx
  have hcard : (Γ'.at act'' x).V.card ≤ Γ'.V.card := Finset.card_filter_le _ _
  have hu1 := hunit x hx 0
  have hu2 := hunit x hx 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu1 hu2
  have hi : Aodd θ ((Γ'.at act'' x).mapType π₁) = 1 := by
    have h := hθ' (eY ⟨x, hx⟩)
    simp only [Γs, Equiv.symm_apply_apply] at h
    rw [h, hu1]
  obtain ⟨hadm, hv⟩ := hodd θ T Γ'.V.card _ _ hcx hRx hcard hT1 hT2 hF6 hM1 hM2 hi
  obtain ⟨hL0, hLe⟩ := hev θ _ _ hcx hRx hu2
  exact ⟨by rw [hω]; exact hcard, hprep htx, hadm, hv, hL0, hLe⟩

/-- **The address package, dischargeable form**: `AddressPackage` with conjunct 16 replaced by

* (16₀) a realization has `ω(D) = |V(Δ)|`, and keeps the fixed local types when `Δ` has total
  type zero (tex 2042–2044, 2678–2686, 10589–10596, 10795–10804; definition/GLUE; owner RC2):
  the product `∏ q^*` of a faithful realization has the local types, sign and squareclasses of
  the total type, so total type zero is the prepared filter containing `1`.

All other conjuncts (1–15, 17, 18) are those of `AddressPackage`, verbatim (same tex lines, kinds
and owners). It is implied by `AddressPackage` (`addressPackageZeroTotal_of_package`). -/
def AddressPackageZeroTotal {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4)
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  -- (5)
  ∃ CeFinal : ℤ,
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (Aodd : ℕ → Symbols.Config L₁ → ZMod 2) (AoddLim : Symbols.Config L₁ → ZMod 2)
    (Aev : Symbols.Config L₂ → ZMod 2) (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7)
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x) = ε x) ∧
    -- (8), (9)
    Symbols.CoefficientRules ε₁ AoddLim ∧ Symbols.CoefficientRules ε₂ Aev ∧
    -- (10)
    (∀ (n : ℕ) (Γs : Fin n → Symbols.Config L₁), (∀ i, (Γs i).Compatible ε₁) →
      ∀ᶠ θ in (W.stages : Filter ℕ), ∀ i, Aodd θ (Γs i) = AoddLim (Γs i)) ∧
    -- (11), (12)
    (∃ Γ₁ : Symbols.Config L₁, Symbols.IsUnitSeed ε₁ AoddLim Γ₁ ∧ Γ₁.V.Nonempty) ∧
    (∀ Γ : Symbols.Config L₁, Symbols.IsUnitSeed ε₁ AoddLim Γ → Γ.total = 0) ∧
    -- (13)
    (∀ Γ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ Aev Γ → Γ.total = 0) ∧
    -- (14)
    (∃ Sev : Finset ℕ,
      (¬ ∃ Γ₂ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ Aev Γ₂ ∧ Γ₂.V.Nonempty) →
        KSplit.AppGCongruenceB3 ℓ W.kfin Sev) ∧
    -- (15)
    (∀ (θ b : ℕ) (Γ : Symbols.Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Family, ∃ hdim : F.b = b, Family.Admissible W.S W.kfin F ∧
        ∀ x : Fin b → ZMod 2, x ≠ 0 → Realizes θ (Γ.at act' x) (F.h (x ∘ Fin.cast hdim))) ∧
    -- (16₀) the fixed local types at total type zero
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      AppGEndpoints.omega D = Δ.V.card ∧ (Δ.total = 0 → W.prepared D)) ∧
    -- (17)
    (∀ (θ T Wb : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ Wb → Wb + 1 ≤ T → (((max 0 (W.δo + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', W.admissible θ D' → AppGEndpoints.omega D' ≤ T → vZ (W.aθ θ D') < W.Mθ θ →
        (((AppGEndpoints.omega D' : ℤ) + W.δo : ℤ) : WithTop ℤ) ≤ vZ (W.aθ θ D')) →
      max 0 (W.δo + Wb) + 2 ≤ (W.Mθ θ : ℤ) → (T : ℤ) + W.δo < W.Mθ θ →
      Aodd θ (Δ.mapType π₁) = 1 →
      W.admissible θ D ∧
        vZ (W.aθ θ D) = (((AppGEndpoints.omega D : ℤ) + W.δo : ℤ) : WithTop ℤ)) ∧
    -- (18)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Aev (Δ.mapType π₂) = 1 →
      W.Lstar (D * W.kfin) ≠ 0 ∧
        padicValRat 2 (W.Lstar (D * W.kfin)) ≤ 2 * (AppGEndpoints.omega D : ℤ) + CeFinal)

/-- **`AddressPackage` implies its dischargeable form** (PROVED: conjunct 16 implies 16₀). -/
theorem addressPackageZeroTotal_of_package {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackage W Ccoarse) : AddressPackageZeroTotal W Ccoarse := by
  obtain ⟨h1, h2, h3, h4, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₂, ε, ε₁, ε₂, π₁, π₂, Aodd,
    AoddLim, Aev, Realizes, h6, h7a, h7b, h7c, h7d, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₂, ε, ε₁, ε₂, π₁, π₂, Aodd,
    AoddLim, Aev, Realizes, h6, h7a, h7b, h7c, h7d, h8, h9, h10, h11, h12, h13, h14, h15,
    fun θ Δ D hc hR => ⟨(h16 θ Δ D hc hR).1, fun _ => (h16 θ Δ D hc hR).2⟩, h17, h18⟩

/-- **The address input from the dischargeable package** (PROVED from
`addressInput_of_address_zeroTotal`, lane RC3's `KSplit.ksplit_seed_b3` through
`exists_unitSeed_of_ksplit`, and `exists_minSeed_total_zero`). -/
theorem addressInput_of_packageZeroTotal {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackageZeroTotal W Ccoarse) :
    ∃ CeFinal : ℤ, AppGEndpoints.AddressInput W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd))
      W.admissible W.prepared W.Lstar W.kfin W.δo CeFinal Ccoarse Family Family.b Family.h
      (Family.Admissible W.S W.kfin) := by
  obtain ⟨hℓ, hk_odd, hk_sf, ⟨q₀, hq₀, hq₀k, hq₀ℓ⟩, CeFinal, L, L₁, L₂, _, _, _, _, _, ε, ε₁,
    ε₂, π₁, π₂, Aodd, AoddLim, Aev, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, hlimRules, hevRules, hlim,
    hseed₁, hfilt₁, hfilt₂, ⟨Sev, hG⟩, hreal, hrealω, hodd, hev⟩ := h
  obtain ⟨Γ₁, hm₁, ht₁⟩ := exists_minSeed_total_zero hseed₁ hfilt₁
  obtain ⟨Γ₂, hm₂, ht₂⟩ := exists_minSeed_total_zero
    (exists_unitSeed_of_ksplit hℓ hk_odd hk_sf hq₀ hq₀k hq₀ℓ Sev hG) hfilt₂
  exact ⟨CeFinal, addressInput_of_address_zeroTotal W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd))
    W.admissible W.prepared W.Lstar W.kfin W.δo CeFinal Ccoarse Family Family.b Family.h
    (Family.Admissible W.S W.kfin) hL ε ε₁ ε₂ π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ Aodd AoddLim Aev hlimRules
    hevRules hlim hm₁ hm₂ ht₁ ht₂ Realizes hreal hrealω hodd hev⟩

/-- **The dischargeable package for every choice of the constants** (as `AddressPackageLeaf`). -/
def AddressPackageZeroTotalLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackageZeroTotal W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **`AddressLeaf` from the dischargeable package** (PROVED). -/
theorem addressLeaf_of_packageZeroTotal {ℓ : ℕ} (W : WData ℓ)
    (h : AddressPackageZeroTotalLeaf W) : AddressLeaf W := by
  intro A CE CR Cper Cdet h33 h34 h35 hvis hU
  exact addressInput_of_packageZeroTotal W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

/-! ## The finer form: the odd limit symbol from the stage tables (lane RC2's stabilization) -/

/-- **The dischargeable package with the odd limit symbol constructed** (Proposition
`ex:app-odd-stabilization`, tex 10508–10552): as `AddressPackageZeroTotal`, except that the odd
limit symbol `AoddLim`, its coefficient rules (conjunct 8) and the common-stage property (conjunct
10) are not assumed; lane RC2's PROVED `Symbols.odd_stabilization` builds them from

* (8′) the coefficient rules of the stage tables on all compatible graphs with at most `W + 1`
  vertices at the valid stages of a set of `𝒰`, for every cutoff `W` (`Symbols.RulesUpTo`; tex
  10533–10540; ELLIOT, App F 9447–9976; owner RC12), the odd alphabet `L₁` being finite (bounded
  label groups, tex 10525–10532);

and conjuncts 11, 12 are read through the stage tables:

* (11′) a nonempty compatible typed graph at which the stage tables are one on a set of `𝒰` (the
  bounded-weight witness, tex 2588–2593, 10501–10505, 10547; ELLIOT; owner RC3 seeds / batch 3
  GenusOdd);
* (12′) a compatible typed graph at which the stage tables are one on a set of `𝒰` has total type
  `0` (tex 10236–10240, 10589–10596; definition; owner RC2 / RC12).

Conjuncts 1–7, 9, 13–15, 16₀, 17, 18 are those of `AddressPackageZeroTotal`, verbatim. -/
def AddressPackageStaged {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4)
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  -- (5)
  ∃ CeFinal : ℤ,
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : Fintype L₁) (_ : DecidableEq L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (Aodd : ℕ → Symbols.Config L₁ → ZMod 2) (Aev : Symbols.Config L₂ → ZMod 2)
    (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7)
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x) = ε x) ∧
    -- (8′) the rules at the valid stages of every cutoff; (9)
    (∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ), Symbols.RulesUpTo ε₁ (Aodd θ) Wc) ∧
    Symbols.CoefficientRules ε₂ Aev ∧
    -- (11′), (12′) the odd seed and the odd filter through the stage tables
    (∃ Γ₁ : Symbols.Config L₁, Γ₁.Compatible ε₁ ∧ Γ₁.V.Nonempty ∧
      ∀ᶠ θ in (W.stages : Filter ℕ), Aodd θ Γ₁ = 1) ∧
    (∀ Γ : Symbols.Config L₁, Γ.Compatible ε₁ →
      (∀ᶠ θ in (W.stages : Filter ℕ), Aodd θ Γ = 1) → Γ.total = 0) ∧
    -- (13)
    (∀ Γ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ Aev Γ → Γ.total = 0) ∧
    -- (14)
    (∃ Sev : Finset ℕ,
      (¬ ∃ Γ₂ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ Aev Γ₂ ∧ Γ₂.V.Nonempty) →
        KSplit.AppGCongruenceB3 ℓ W.kfin Sev) ∧
    -- (15)
    (∀ (θ b : ℕ) (Γ : Symbols.Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Family, ∃ hdim : F.b = b, Family.Admissible W.S W.kfin F ∧
        ∀ x : Fin b → ZMod 2, x ≠ 0 → Realizes θ (Γ.at act' x) (F.h (x ∘ Fin.cast hdim))) ∧
    -- (16₀)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      AppGEndpoints.omega D = Δ.V.card ∧ (Δ.total = 0 → W.prepared D)) ∧
    -- (17)
    (∀ (θ T Wb : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ Wb → Wb + 1 ≤ T → (((max 0 (W.δo + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', W.admissible θ D' → AppGEndpoints.omega D' ≤ T → vZ (W.aθ θ D') < W.Mθ θ →
        (((AppGEndpoints.omega D' : ℤ) + W.δo : ℤ) : WithTop ℤ) ≤ vZ (W.aθ θ D')) →
      max 0 (W.δo + Wb) + 2 ≤ (W.Mθ θ : ℤ) → (T : ℤ) + W.δo < W.Mθ θ →
      Aodd θ (Δ.mapType π₁) = 1 →
      W.admissible θ D ∧
        vZ (W.aθ θ D) = (((AppGEndpoints.omega D : ℤ) + W.δo : ℤ) : WithTop ℤ)) ∧
    -- (18)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Aev (Δ.mapType π₂) = 1 →
      W.Lstar (D * W.kfin) ≠ 0 ∧
        padicValRat 2 (W.Lstar (D * W.kfin)) ≤ 2 * (AppGEndpoints.omega D : ℤ) + CeFinal)

/-- **The dischargeable package from its finer form** (PROVED from lane RC2's
`Symbols.odd_stabilization`): the limit symbol satisfies the coefficient rules and agrees with the
stage tables on any finite collection of compatible graphs on a set of `𝒰`; a graph that is one
at the stages of a set of `𝒰` is a unit of the limit symbol, and a unit of the limit symbol is one
at the stages of a set of `𝒰` (tex 10515–10517, 10540–10548). -/
theorem addressPackageZeroTotal_of_staged {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackageStaged W Ccoarse) : AddressPackageZeroTotal W Ccoarse := by
  obtain ⟨hℓ, hk_odd, hk_sf, hq₀, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁,
    ε₂, π₁, π₂, Aodd, Aev, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, hvalid, hevRules,
    ⟨Γ₁, hc₁, hne₁, hu₁⟩, hfilt₁, hrest⟩ := h
  obtain ⟨AoddLim, hrules, hagree⟩ := Symbols.odd_stabilization W.stages ε₁ Aodd hvalid
  have hlim1 : ∀ Γ : Symbols.Config L₁, Γ.Compatible ε₁ →
      ∀ᶠ θ in (W.stages : Filter ℕ), Aodd θ Γ = AoddLim Γ := fun Γ hΓ =>
    (hagree 1 (fun _ => Γ) (fun _ => hΓ)).mono fun θ hθ => hθ 0
  have hunit₁ : AoddLim Γ₁ = 1 := by
    obtain ⟨θ, hθ1, hθ2⟩ := ((hlim1 Γ₁ hc₁).and hu₁).exists
    exact hθ1.symm.trans hθ2
  exact ⟨hℓ, hk_odd, hk_sf, hq₀, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₂, ε, ε₁, ε₂, π₁, π₂,
    Aodd, AoddLim, Aev, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, hrules, hevRules, hagree,
    ⟨Γ₁, ⟨hc₁, hunit₁⟩, hne₁⟩,
    fun Γ hΓ => hfilt₁ Γ hΓ.1 ((hlim1 Γ hΓ.1).mono fun θ hθ => hθ.trans hΓ.2), hrest⟩

/-- **The finer leaf**: `AddressPackageStaged` for every choice of the constants (as
`AddressPackageLeaf`). -/
def AddressPackageStagedLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackageStaged W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **`AddressLeaf` from the finer leaf** (PROVED). -/
theorem addressLeaf_of_stagedPackage {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageStagedLeaf W) :
    AddressLeaf W :=
  addressLeaf_of_packageZeroTotal W fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
    addressPackageZeroTotal_of_staged W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

/-! ## The finest form: the coefficient rules from batch 3's coefficient dictionary -/

/-- **The address package with both coefficient rules discharged** (batch 3's
`CoefficientDictionary`: `rulesUpTo_symb`, `coefficientRules_symb`, PROVED from lane RC12's
readings; Lemma `ex:sec7-coefficient-rules`, tex 2102–2149, App F `ex:app-coefficient-rules`,
9884–9976): as `AddressPackageStaged`, with the odd stage tables `Aodd θ = symb (T₁ θ) (Rodd θ)`
and the even symbol `Aev = symb T₂ Rev` the dictionary's symbols (the reading of any prime
realization, tex 2093–2096) of type data `T₁ θ, T₂` (GLUE: types read from residue classes, the
sign coordinate, tex 2017–2039) and readings on prime sets `Rodd θ, Rev`; conjuncts 8′ and 9 are
replaced by

* (8″) at the valid stages of a set of `𝒰`, for every cutoff `W`, lane RC12's readings of the
  odd stage source within the budget `W + 1`: the fixed-`U` factorization (tex 9745–9750), (O.12)
  at coefficient one with the product-label rule (tex 9905–9945), `a_p` even (GLUE, tex 9585,
  9593), primary isolation read on prime sets (tex 9947–9948) (ELLIOT/GLUE; owner RC12; the rules
  `RulesUpTo` are batch 3's PROVED `rulesUpTo_symb`);
* (9″) the same readings of the even source of `E^{(k)}` at every size (ELLIOT/GLUE; owners RC12,
  RC11; `CoefficientRules` is batch 3's PROVED `coefficientRules_symb`).

The odd limit symbol's rules (conjunct 8 of `AddressPackage`) do not match
`coefficientRules_symb` directly (the limit symbol is not the reading of one source at all
sizes, tex 2097–2100, 10543–10544); they come from `rulesUpTo_symb` at the valid stages and lane
RC2's `odd_stabilization` (`addressPackageZeroTotal_of_staged`). All other conjuncts are those of
`AddressPackageStaged`, verbatim, with `Aodd θ`, `Aev` replaced by the dictionary's symbols. -/
def AddressPackageDict {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4)
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  -- (5)
  ∃ CeFinal : ℤ,
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : Fintype L₁) (_ : DecidableEq L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (T₁ : ℕ → CoefficientDictionary.TypeData L₁ ε₁) (Rodd : ℕ → Finset ℕ → ZMod 2)
    (apo : ℕ → ℕ → ℤ) (T₂ : CoefficientDictionary.TypeData L₂ ε₂)
    (Rev : Finset ℕ → ZMod 2) (apk : ℕ → ℤ) (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7)
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x) = ε x) ∧
    -- (8″) RC12's readings of the odd stage source, within the budget of every cutoff
    (∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
      CoefficientDictionary.FixedUFactorization (T₁ θ) (Rodd θ) (Wc + 1) ∧
      CoefficientDictionary.O12Reading (T₁ θ) (Rodd θ) (apo θ) (Wc + 1) ∧
      CoefficientDictionary.ApEven (T₁ θ) (apo θ) ∧
      CoefficientDictionary.PrimaryReading (T₁ θ) (Rodd θ) (Wc + 1)) ∧
    -- (9″) RC12's readings of the even source of `E^{(k)}`, at every size
    ((∀ B, CoefficientDictionary.FixedUFactorization T₂ Rev B) ∧
      (∀ B, CoefficientDictionary.O12Reading T₂ Rev apk B) ∧
      CoefficientDictionary.ApEven T₂ apk ∧
      (∀ B, CoefficientDictionary.PrimaryReading T₂ Rev B)) ∧
    -- (11′), (12′)
    (∃ Γ₁ : Symbols.Config L₁, Γ₁.Compatible ε₁ ∧ Γ₁.V.Nonempty ∧
      ∀ᶠ θ in (W.stages : Filter ℕ), CoefficientDictionary.symb (T₁ θ) (Rodd θ) Γ₁ = 1) ∧
    (∀ Γ : Symbols.Config L₁, Γ.Compatible ε₁ →
      (∀ᶠ θ in (W.stages : Filter ℕ), CoefficientDictionary.symb (T₁ θ) (Rodd θ) Γ = 1) →
        Γ.total = 0) ∧
    -- (13)
    (∀ Γ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ (CoefficientDictionary.symb T₂ Rev) Γ →
      Γ.total = 0) ∧
    -- (14)
    (∃ Sev : Finset ℕ,
      (¬ ∃ Γ₂ : Symbols.Config L₂,
        Symbols.IsUnitSeed ε₂ (CoefficientDictionary.symb T₂ Rev) Γ₂ ∧ Γ₂.V.Nonempty) →
        KSplit.AppGCongruenceB3 ℓ W.kfin Sev) ∧
    -- (15)
    (∀ (θ b : ℕ) (Γ : Symbols.Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Family, ∃ hdim : F.b = b, Family.Admissible W.S W.kfin F ∧
        ∀ x : Fin b → ZMod 2, x ≠ 0 → Realizes θ (Γ.at act' x) (F.h (x ∘ Fin.cast hdim))) ∧
    -- (16₀)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      AppGEndpoints.omega D = Δ.V.card ∧ (Δ.total = 0 → W.prepared D)) ∧
    -- (17)
    (∀ (θ T Wb : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ Wb → Wb + 1 ≤ T → (((max 0 (W.δo + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', W.admissible θ D' → AppGEndpoints.omega D' ≤ T → vZ (W.aθ θ D') < W.Mθ θ →
        (((AppGEndpoints.omega D' : ℤ) + W.δo : ℤ) : WithTop ℤ) ≤ vZ (W.aθ θ D')) →
      max 0 (W.δo + Wb) + 2 ≤ (W.Mθ θ : ℤ) → (T : ℤ) + W.δo < W.Mθ θ →
      CoefficientDictionary.symb (T₁ θ) (Rodd θ) (Δ.mapType π₁) = 1 →
      W.admissible θ D ∧
        vZ (W.aθ θ D) = (((AppGEndpoints.omega D : ℤ) + W.δo : ℤ) : WithTop ℤ)) ∧
    -- (18)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      CoefficientDictionary.symb T₂ Rev (Δ.mapType π₂) = 1 →
      W.Lstar (D * W.kfin) ≠ 0 ∧
        padicValRat 2 (W.Lstar (D * W.kfin)) ≤ 2 * (AppGEndpoints.omega D : ℤ) + CeFinal)

/-- **The staged package from the dictionary form** (PROVED from batch 3's `rulesUpTo_symb` and
`coefficientRules_symb`). -/
theorem addressPackageStaged_of_dict {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackageDict W Ccoarse) : AddressPackageStaged W Ccoarse := by
  obtain ⟨hℓ, hk_odd, hk_sf, hq₀, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁,
    ε₂, π₁, π₂, T₁, Rodd, apo, T₂, Rev, apk, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, hodd8,
    ⟨hsw, hO12, hap, hprim⟩, hrest⟩ := h
  exact ⟨hℓ, hk_odd, hk_sf, hq₀, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁,
    ε₂, π₁, π₂, fun θ => CoefficientDictionary.symb (T₁ θ) (Rodd θ),
    CoefficientDictionary.symb T₂ Rev, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂,
    fun Wc => (hodd8 Wc).mono fun θ hθ =>
      CoefficientDictionary.rulesUpTo_symb (T₁ θ) (Rodd θ) (apo θ) Wc hθ.1 hθ.2.1 hθ.2.2.1
        hθ.2.2.2,
    CoefficientDictionary.coefficientRules_symb T₂ Rev apk hsw hO12 hap hprim, hrest⟩

/-- **The dictionary leaf**: `AddressPackageDict` for every choice of the constants (as
`AddressPackageLeaf`). -/
def AddressPackageDictLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackageDict W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **`AddressLeaf` from the dictionary leaf** (PROVED). -/
theorem addressLeaf_of_dictPackage {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageDictLeaf W) :
    AddressLeaf W :=
  addressLeaf_of_stagedPackage W fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
    addressPackageStaged_of_dict W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

end ZInQ.Manuscript.RC.Wiring
