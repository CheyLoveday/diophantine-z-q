import Mathlib

/-!
# App G endpoints: the odd minimum before the final family (Proposition `ex:app-odd-minimum`)

Manuscript `diophantine_zq.tex`, Appendix G, Proposition `ex:app-odd-minimum` and its proof
(tex L10151–10256); the same argument in Section 7 at L2531–2551.

The objects (index valuations `j_gen`, `j_rc`, normalized central values `L_*`, the theta
coefficients `a_M(D)` of the actual stages, the companion conditions) are not in Mathlib. Every
node below is therefore stated **generically**: universally quantified over that data, with the
manuscript's inputs as explicit hypotheses in the form in which the manuscript states them. The
nodes are then discharged by application to the genuine data. `ω` is genuine (`omega`).

Conventions (those of the Theorem 5.3 interface data, so that the nodes apply to it verbatim):
* stages are natural numbers, with one ultrafilter `U : Ultrafilter ℕ` on them;
* `M θ : ℕ` is the precision `M_θ` of stage `θ`;
* `v θ D : WithTop ℤ` is `v₂ a_{M_θ}(D)` of the phase-removed integer coefficient (`⊤` at `0`);
  `v θ D < M θ` means `D` is *visible* at stage `θ`;
* `adm θ D` is the stage support (admissible `D`, `(D/ℓ₀) = 1`);
* (O.8) enters as its visibility clause: `v θ D < M θ → ord_{s=1} L(E^D,s) = 1 ∧
  j_gen(D) ≤ v θ D + C_det`. Its first clause (`v₂ a_M(D) ≥ min{M, j_gen(D) − C_det}` at simple
  zeros) is a consequence of the visibility clause and is not needed separately.

Nodes (all PROVED, standard axioms):

| node | tex | kind |
|---|---|---|
| `GenusLowerF4` | L10171–10178 | PROVED (inequality chain from (3.4), (3.5), (F.3)) |
| `CoarseF5` | L10180–10187 | PROVED (from (F.4) and (O.8)) |
| `OddMinimumF6` | L10189–10209, L2538–2546 | PROVED (ultrafilter minimum `δ_o` and (F.6)) |
| `TruncatedF6` | L10208–10209 | PROVED (invisible coefficients) |
| `StageChoice` | L10211–10220 | PROVED (stage for a finite operator budget) |
| `BudgetDivision` | L10221–10232 | PROVED (the division by `2^{n_U}`, arithmetic part) |
| `UnitSymbolF7` | L10236–10256 | PROVED (exhaustive range and (F.7)) |

ELLIOT findings recorded here:
* `C_H` in (F.4) (L10176) is not defined anywhere in the manuscript. It is the bound on the error
  of the native comparison (3.4) (L2427–2439): `|ε| ≤ 2` "up to the one fixed initial period
  convention". We fill it as `C_H = C_per + 2`, where `C_per` is that fixed period convention
  (with `C_per = 0` this is the `+2` of (3.6), L2449–2452).
-/

namespace ZInQ.Contrib.CloudB3RC53.AppGEndpoints

open Filter

/-- `ω(h)`: the number of distinct prime factors of `|h|`. -/
def omega (h : ℤ) : ℕ := ArithmeticFunction.cardDistinctFactors h.natAbs

/-- `r ≤ v` for a rational `r` and an extended integer valuation `v` (`r ≤ ⊤` always). Used for
the bound `v₂ a_M(D) ≥ min{M, ω(D) − C_coarse}` of (F.5), whose constant `C_coarse = C_gen/2 + C_det`
need not be an integer. -/
def QLe (r : ℚ) (v : WithTop ℤ) : Prop := ∀ n : ℤ, v = (n : WithTop ℤ) → r ≤ (n : ℚ)

/-! ## (F.4) -/

/-- **(F.4)** (Proposition `ex:app-odd-minimum`, proof, tex L10171–10178; PROVED). "The arithmetic
result (3.5) and the two native-lattice height comparisons (3.4) give, using (F.3),
`2 j_gen(h) ≥ 2ω(h) + s(h) − C_gen`, `C_gen = 2A + C_R + C_E − v₂L_*(h_*) + C_H`. The variable
`s(hk')` cancels."

Generic data: `prepared h` (the prepared odd-sign filter containing one, prime to the fixed
support), `simpleZero h` (`ord_{s=1} L(E^{(h)},s) = 1`), `companion h k'` (the conditions on the
rough companion of Proposition `ex:sec7-rough-companion` / `ex:app-rough-companion`: negative odd
fundamental discriminant, square at `2Nh`, avoiding the exclusions), `L_*`, `j_gen`, `j_rc`, and
`s` (`s(h) = length Ш(E^{(h)}/ℚ)[2^∞]`, a natural number). Hypotheses, as the manuscript states
them:
* the rough companion with (F.3) (L2343–2401, L10131–10146): at each known simple zero `h` of the
  filter there is a companion `k'` with `ω(k') ≤ A`, `L_*(hk') ≠ 0` and
  `v₂L_*(hk') ≤ 2ω(h) + 2ω(k') + s(hk') + C_E`;
* (3.4) (L2427–2439): `2j_rc(h,k') − 2j_gen(h) = v₂L_*(hk') − v₂L_*(h_*) + C_per + ε`, `|ε| ≤ 2`
  (`C_per` the one fixed initial period convention);
* (3.5) (L2443–2446): `2j_rc(h,k') ≥ 4ω(h) + s(h) + s(hk') − C_R` for companions with `ω(k') ≤ A`.

ELLIOT: `C_H` is undefined in the text; here `C_H = C_per + 2` (see the module docstring). -/
def GenusLowerF4 : Prop :=
  ∀ (prepared simpleZero : ℤ → Prop) (companion : ℤ → ℤ → Prop) (Lstar : ℤ → ℚ)
    (jgen : ℤ → ℤ) (jrc : ℤ → ℤ → ℤ) (s : ℤ → ℕ) (hstar A CR CE Cper : ℤ),
    (∀ h, prepared h → simpleZero h → ∃ k', companion h k' ∧ (omega k' : ℤ) ≤ A ∧
      Lstar (h * k') ≠ 0 ∧
      padicValRat 2 (Lstar (h * k')) ≤ 2 * omega h + 2 * omega k' + s (h * k') + CE) →
    (∀ h k', prepared h → simpleZero h → companion h k' → ∃ ε : ℤ, |ε| ≤ 2 ∧
      2 * jrc h k' - 2 * jgen h =
        padicValRat 2 (Lstar (h * k')) - padicValRat 2 (Lstar hstar) + Cper + ε) →
    (∀ h k', prepared h → simpleZero h → companion h k' → (omega k' : ℤ) ≤ A →
      4 * (omega h : ℤ) + s h + s (h * k') - CR ≤ 2 * jrc h k') →
    ∀ h, prepared h → simpleZero h →
      2 * (omega h : ℤ) + s h - (2 * A + CR + CE - padicValRat 2 (Lstar hstar) + (Cper + 2))
        ≤ 2 * jgen h

theorem genusLowerF4_proof : GenusLowerF4 := by
  intro prepared simpleZero companion Lstar jgen jrc s hstar A CR CE Cper h33 h34 h35 h hp hz
  obtain ⟨k', hc, hA, -, hE⟩ := h33 h hp hz
  obtain ⟨ε, hε, heq⟩ := h34 h k' hp hz hc
  have hR := h35 h k' hp hz hc hA
  have hε' := (abs_le.mp hε).2
  linarith

/-! ## (F.5) -/

/-- **(F.5)** (proof of `ex:app-odd-minimum`, tex L10180–10187; PROVED). "Combining (F.4) with
(O.8) gives on all admissible `D`: `v₂a_M(D) ≥ min{M, ω(D) − C_coarse}`,
`C_coarse = C_gen/2 + C_det`. At visible coefficients (O.8) first gives a simple zero, allowing
(F.4); at the other odd-sign parameters the coefficient is zero modulo `2^M`."

One stage, of precision `M`, with valuations `v D = v₂ a_M(D)`. Hypotheses: (O.8) in its
visibility form (App F `ex:app-visibility`, L9407–9445), and (F.4) at admissible simple zeros
(GLUE: admissible theta parameters lie in the prepared filter of (F.4)). -/
def CoarseF5 : Prop :=
  ∀ (adm simpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (s : ℤ → ℕ) (v : ℤ → WithTop ℤ) (M : ℕ)
    (Cdet Cgen : ℤ),
    (∀ D, adm D → v D < M → simpleZero D ∧ (jgen D : WithTop ℤ) ≤ v D + Cdet) →
    (∀ D, adm D → simpleZero D → 2 * (omega D : ℤ) + s D - Cgen ≤ 2 * jgen D) →
    ∀ D, adm D → QLe (min (M : ℚ) (omega D - ((Cgen : ℚ) / 2 + Cdet))) (v D)

theorem coarseF5_proof : CoarseF5 := by
  intro adm simpleZero jgen s v M Cdet Cgen hvis hF4 D hD n hn
  by_cases hlt : n < (M : ℤ)
  · have hv : v D < M := by
      rw [hn]
      exact_mod_cast hlt
    obtain ⟨hz, hj⟩ := hvis D hD hv
    rw [hn] at hj
    have hj' : jgen D ≤ n + Cdet := by exact_mod_cast hj
    have h4 := hF4 D hD hz
    have hs : (0 : ℤ) ≤ s D := by positivity
    have h5 : (2 * (omega D : ℤ) - Cgen : ℚ) ≤ 2 * (jgen D : ℚ) := by
      have : 2 * (omega D : ℤ) - Cgen ≤ 2 * jgen D := by linarith
      exact_mod_cast this
    have h6 : (jgen D : ℚ) ≤ n + Cdet := by exact_mod_cast hj'
    push_cast at h5
    refine (min_le_right _ _).trans ?_
    linarith
  · push Not at hlt
    refine (min_le_left _ _).trans ?_
    exact_mod_cast hlt

/-! ## The attained ultrafilter minimum `δ_o` and (F.6) -/

/-- The set of integers `r` for which a bounded-weight sequence of visible `D_θ` has
`v₂a_{M_θ}(D_θ) − ω(D_θ) = r` on a set in the ultrafilter (tex L10189–10193, L2538–2542). -/
def DepthSet (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop) :
    Set ℤ :=
  {r | ∃ (W : ℕ) (Ds : ℕ → ℤ), ∀ᶠ θ in (U : Filter ℕ), adm θ (Ds θ) ∧ omega (Ds θ) ≤ W ∧
    v θ (Ds θ) < M θ ∧ v θ (Ds θ) = (((omega (Ds θ) : ℤ) + r : ℤ) : WithTop ℤ)}

/-- **The attained odd minimum `δ_o` and (F.6)** (proof of `ex:app-odd-minimum`, tex
L10189–10207; Section 7, L2538–2546; PROVED). "Consider the integers `r` for which a
bounded-weight sequence of visible `D_M` has `v₂a_M(D_M) − ω(D_M) = r` on a set in the
ultrafilter. The fixed witness `D_w` and (O.2), (O.7) make this set nonempty. Equation (F.5)
bounds it below. Let its attained minimum be `δ_o`. For every fixed `W`, on a set in the same
ultrafilter, `v₂a_M(D) ≥ ω(D) + δ_o` for every visible `D`, `ω(D) ≤ W`. (F.6) Otherwise choose a
violating `D_M` at each bad stage. One of the finitely many integers between `−C_coarse` and
`δ_o − 1` would occur on an ultrafilter-large set, a contradiction."

Hypotheses: (F.5) at every stage (`CoarseF5`), and the fixed visible witness: some admissible
`D_w` with a fixed valuation `c < M_θ` on a set in the ultrafilter ((3.7), (O.2), (O.7):
`v₂ a_M(D_w) = c_θ + c_w` for `M > c_θ + c_w`, L9384–9390). Conclusion: `δ_o` is the least
element of `DepthSet`, and (F.6) holds for every weight bound `W`. -/
def OddMinimumF6 : Prop :=
  ∀ (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (Ccoarse : ℚ),
    (∀ θ D, adm θ D → QLe (min (M θ : ℚ) (omega D - Ccoarse)) (v θ D)) →
    (∃ Dw c : ℤ, ∀ᶠ θ in (U : Filter ℕ), adm θ Dw ∧ v θ Dw = (c : WithTop ℤ) ∧
      (c : WithTop ℤ) < M θ) →
    ∃ δ : ℤ, IsLeast (DepthSet U M v adm) δ ∧
      ∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W → v θ D < M θ →
        (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D

/-- A visible valuation is a finite integer. -/
theorem exists_eq_coe_of_lt {v : WithTop ℤ} {M : ℕ} (h : v < M) : ∃ n : ℤ, v = n ∧ n < M := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
  refine ⟨n, hn.symm, ?_⟩
  rw [← hn] at h
  exact_mod_cast h

/-- On a visible coefficient, (F.5) bounds `v₂a_M(D) − ω(D)` below by `−C_coarse`. -/
theorem neg_le_of_visible {M : ℕ} {ω : ℕ} {Cc : ℚ} {n : ℤ}
    (hF5 : QLe (min (M : ℚ) (ω - Cc)) (n : WithTop ℤ)) (hn : n < M) : -Cc ≤ (n : ℚ) - ω := by
  have h := hF5 n rfl
  have hn' : (n : ℚ) < M := by exact_mod_cast hn
  rcases min_choice (M : ℚ) (ω - Cc) with h' | h'
  · rw [h'] at h; linarith
  · rw [h'] at h; linarith

/-- **(F.6) at the attained minimum** (tex L10194–10207, L2543–2546; PROVED). If `δ` is the least
element of `DepthSet` and (F.5) holds at every stage, then for every weight bound `W`, on a set of
stages in the ultrafilter, every visible admissible `D` with `ω(D) ≤ W` has
`v₂a_M(D) ≥ ω(D) + δ`. -/
theorem f6_of_isLeast {U : Ultrafilter ℕ} {M : ℕ → ℕ} {v : ℕ → ℤ → WithTop ℤ}
    {adm : ℕ → ℤ → Prop} {Cc : ℚ} {δ : ℤ}
    (hF5 : ∀ θ D, adm θ D → QLe (min (M θ : ℚ) (omega D - Cc)) (v θ D))
    (hδ : IsLeast (DepthSet U M v adm) δ) (W : ℕ) :
    ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W → v θ D < M θ →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D := by
  classical
  have hmin : ∀ r, r ∈ DepthSet U M v adm → δ ≤ r := fun r hr => hδ.2 hr
  by_contra hbad
  have hbad' : ∀ᶠ θ in (U : Filter ℕ), ∃ D, adm θ D ∧ omega D ≤ W ∧ v θ D < M θ ∧
      ¬ (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D := by
    have := Ultrafilter.eventually_not.mpr hbad
    refine this.mono fun θ hθ => ?_
    push Not at hθ
    obtain ⟨D, h1, h2, h3, h4⟩ := hθ
    exact ⟨D, h1, h2, h3, not_le.mpr h4⟩
  -- a violating index at each stage
  let Ds : ℕ → ℤ := fun θ =>
    if h : ∃ D, adm θ D ∧ omega D ≤ W ∧ v θ D < M θ ∧
      ¬ (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D then h.choose else 0
  have hDs : ∀ᶠ θ in (U : Filter ℕ), adm θ (Ds θ) ∧ omega (Ds θ) ≤ W ∧ v θ (Ds θ) < M θ ∧
      ¬ (((omega (Ds θ) : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ (Ds θ) := by
    refine hbad'.mono fun θ hθ => ?_
    simp only [Ds]
    split_ifs
    exact hθ.choose_spec
  -- the finitely many values between `⌈−C_coarse⌉` and `δ − 1`
  let I : Set ℤ := Set.Ico ⌈-Cc⌉ δ
  have hI : I.Finite := Set.finite_Ico _ _
  have hcover : (⋃ r ∈ I, {θ | adm θ (Ds θ) ∧ omega (Ds θ) ≤ W ∧ v θ (Ds θ) < M θ ∧
      v θ (Ds θ) = (((omega (Ds θ) : ℤ) + r : ℤ) : WithTop ℤ)}) ∈ (U : Filter ℕ) := by
    refine Filter.mem_of_superset hDs fun θ ⟨ha, hW, hvis, hviol⟩ => ?_
    obtain ⟨n, hn, hnM⟩ := exists_eq_coe_of_lt hvis
    have hlow := neg_le_of_visible (hn ▸ hF5 θ (Ds θ) ha) hnM
    have hup : n < (omega (Ds θ) : ℤ) + δ := by
      rw [hn] at hviol
      exact_mod_cast not_le.mp hviol
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨n - omega (Ds θ), ⟨?_, ?_⟩, ha, hW, hvis, ?_⟩
    · have : -Cc ≤ ((n - omega (Ds θ) : ℤ) : ℚ) := by push_cast; linarith
      exact Int.ceil_le.mpr this
    · linarith
    · rw [hn]; congr 1; ring
  obtain ⟨r, hrI, hr⟩ := (Ultrafilter.finite_biUnion_mem_iff hI).mp hcover
  have hrD : r ∈ DepthSet U M v adm := ⟨W, Ds, hr⟩
  exact absurd (hmin r hrD) (not_le.mpr hrI.2)

theorem oddMinimumF6_proof : OddMinimumF6 := by
  classical
  intro U M v adm Cc hF5 hw
  -- bounded below by `⌈−C_coarse⌉`
  have hbdd : ∃ b : ℤ, ∀ r, r ∈ DepthSet U M v adm → b ≤ r := by
    refine ⟨⌈-Cc⌉, fun r hr => ?_⟩
    obtain ⟨W, Ds, hev⟩ := hr
    obtain ⟨θ, hadm, -, hvis, heq⟩ := hev.exists
    rw [heq] at hvis
    have hlt : (omega (Ds θ) : ℤ) + r < M θ := by exact_mod_cast hvis
    have hq := hF5 θ (Ds θ) hadm
    rw [heq] at hq
    have h := neg_le_of_visible hq hlt
    have h' : -Cc ≤ (r : ℚ) := by push_cast at h; linarith
    exact Int.ceil_le.mpr h'
  -- nonempty by the witness
  have hne : ∃ r, r ∈ DepthSet U M v adm := by
    obtain ⟨Dw, c, hev⟩ := hw
    refine ⟨c - omega Dw, omega Dw, fun _ => Dw, hev.mono fun θ ⟨ha, hv, hlt⟩ => ?_⟩
    refine ⟨ha, le_rfl, hv ▸ hlt, ?_⟩
    rw [hv]
    congr 1
    ring
  obtain ⟨δ, hδ, hmin⟩ := Int.exists_least_of_bdd hbdd hne
  exact ⟨δ, ⟨hδ, fun r hr => hmin r hr⟩, fun W => f6_of_isLeast hF5 ⟨hδ, fun r hr => hmin r hr⟩ W⟩

/-- **Invisible coefficients** (tex L10208–10209; PROVED). "Invisible coefficients satisfy the
required truncated inequality once `M > W + δ_o`." With the stage precision tending to infinity
along the ultrafilter ((3.7) and the nonprincipal ultrafilter, L2491–2500, L2536–2551), (F.6)
for visible coefficients gives `v₂a_M(D) ≥ ω(D) + δ_o` for *every* admissible `D` of weight at
most `W`, on a set in the ultrafilter. -/
def TruncatedF6 : Prop :=
  ∀ (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop) (δ : ℤ),
    Tendsto M (U : Filter ℕ) atTop →
    (∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W → v θ D < M θ →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D) →
    ∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D

/-- Eventually along `U` the precision exceeds any fixed integer. -/
theorem eventually_lt_M {U : Ultrafilter ℕ} {M : ℕ → ℕ} (hM : Tendsto M (U : Filter ℕ) atTop)
    (z : ℤ) : ∀ᶠ θ in (U : Filter ℕ), z < (M θ : ℤ) := by
  refine (tendsto_atTop.mp hM (z + 1).toNat).mono fun θ hθ => ?_
  have : ((z + 1).toNat : ℤ) ≤ (M θ : ℤ) := by exact_mod_cast hθ
  have := Int.self_le_toNat (z + 1)
  omega

theorem truncatedF6_proof : TruncatedF6 := by
  intro U M v adm δ hM hF6 W
  filter_upwards [hF6 W, eventually_lt_M hM (W + δ)] with θ hθ hMθ D hD hW
  by_cases hvis : v θ D < M θ
  · exact hθ D hD hW hvis
  · push Not at hvis
    refine le_trans ?_ hvis
    have : (omega D : ℤ) + δ ≤ (M θ : ℤ) := by
      have : (omega D : ℤ) ≤ W := by exact_mod_cast hW
      omega
    exact_mod_cast this

/-! ## The stage for a finite operator budget -/

/-- **The stage choice for a finite operator budget** (proof of `ex:app-odd-minimum`, tex
L10211–10225; PROVED). "For a fixed finite operator budget `|U| ≤ W_U`, put
`N_0 = max(0, δ_o + W_U)` and fix `R ≥ 2`. Choose an integer `T ≥ W_U + 1` with
`T − C_coarse ≥ N_0 + R`, then choose a stage in the ultrafilter-large set where (F.6) holds
through weight `T`, with `M ≥ N_0 + R` and `M > T + δ_o`. … If `ω(D) > T`, (F.5) gives [the
valuation bound `N_0 + R`]. If `ω(D) ≤ T`, (F.6) for visible coefficients and `v₂a_M(D) ≥ M` for
invisible ones instead give [the bound `ω(D) + δ_o`]." Also "`M − n_U − 1 ≥ 1` for every reading"
(L10232), with `n_U = δ_o + |U| ≤ δ_o + W_U` (L9492, all primes split).

Conclusion: such a `T` exists, and on a set of stages in the ultrafilter all the stage conditions
hold together with the two coefficient bounds at every admissible `D` (on the originating
coefficient `a_M(D)`; the passage to `B_U[J r m²]` is App F, (O.9)–(O.11), and its arithmetic is
`BudgetDivision`). -/
def StageChoice : Prop :=
  ∀ (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (Ccoarse : ℚ) (δ : ℤ) (WU R : ℕ),
    2 ≤ R → Tendsto M (U : Filter ℕ) atTop →
    (∀ θ D, adm θ D → QLe (min (M θ : ℚ) (omega D - Ccoarse)) (v θ D)) →
    (∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W → v θ D < M θ →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D) →
    ∃ T : ℕ, WU + 1 ≤ T ∧ (((max 0 (δ + WU) + R : ℤ)) : ℚ) ≤ T - Ccoarse ∧
      ∀ᶠ θ in (U : Filter ℕ),
        (∀ D, adm θ D → omega D ≤ T → v θ D < M θ →
          (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D) ∧
        max 0 (δ + WU) + R ≤ (M θ : ℤ) ∧ (T : ℤ) + δ < M θ ∧ δ + WU + 2 ≤ (M θ : ℤ) ∧
        ∀ D, adm θ D →
          (T < omega D → ((max 0 (δ + WU) + R : ℤ) : WithTop ℤ) ≤ v θ D) ∧
          (omega D ≤ T → (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D)

theorem stageChoice_proof : StageChoice := by
  intro U M v adm Cc δ WU R hR hM hF5 hF6
  set N0 : ℤ := max 0 (δ + WU) with hN0
  let T : ℕ := max (WU + 1) (⌈(N0 + R : ℚ) + Cc⌉.toNat)
  have hT1 : WU + 1 ≤ T := le_max_left _ _
  have hT2 : ((N0 + R : ℤ) : ℚ) ≤ T - Cc := by
    have h0 : ⌈(N0 + R : ℚ) + Cc⌉.toNat ≤ T := le_max_right _ _
    have h1 : (⌈(N0 + R : ℚ) + Cc⌉.toNat : ℤ) ≤ (T : ℤ) := by exact_mod_cast h0
    have h2 : ⌈(N0 + R : ℚ) + Cc⌉ ≤ (⌈(N0 + R : ℚ) + Cc⌉.toNat : ℤ) := Int.self_le_toNat _
    have h3 : (N0 + R : ℚ) + Cc ≤ (⌈(N0 + R : ℚ) + Cc⌉ : ℚ) := Int.le_ceil _
    have h4 : ((⌈(N0 + R : ℚ) + Cc⌉ : ℤ) : ℚ) ≤ (T : ℚ) := by exact_mod_cast h2.trans h1
    push_cast
    linarith
  refine ⟨T, hT1, hT2, ?_⟩
  have hN0nn : 0 ≤ N0 := le_max_left _ _
  have hN0ge : δ + WU ≤ N0 := le_max_right _ _
  filter_upwards [hF6 T, eventually_lt_M hM (N0 + R), eventually_lt_M hM (T + δ)]
    with θ hθ hMθ hMθ'
  have hRz : (2 : ℤ) ≤ R := by exact_mod_cast hR
  have hTz : (0 : ℤ) ≤ T := by positivity
  have hMa : N0 + R ≤ (M θ : ℤ) := by omega
  have hMb : (T : ℤ) + δ < M θ := by omega
  refine ⟨hθ, hMa, hMb, by omega, fun D hD => ⟨fun hbig => ?_, fun hsmall => ?_⟩⟩
  · -- large weight: (F.5)
    induction hv : v θ D using WithTop.recTopCoe with
    | top => exact le_top
    | coe n =>
      have h := hF5 θ D hD n hv
      have hω : (T : ℚ) + 1 ≤ (omega D : ℚ) := by exact_mod_cast hbig
      have hMq : ((N0 + R : ℤ) : ℚ) ≤ (M θ : ℚ) := by exact_mod_cast hMa
      have hmin : ((N0 + R : ℤ) : ℚ) ≤ min (M θ : ℚ) (omega D - Cc) :=
        le_min hMq (by linarith)
      have : ((N0 + R : ℤ) : ℚ) ≤ (n : ℚ) := hmin.trans h
      exact_mod_cast this
  · -- bounded weight: (F.6) when visible, `v ≥ M` otherwise
    by_cases hvis : v θ D < M θ
    · exact hθ D hD hsmall hvis
    · push Not at hvis
      refine le_trans ?_ hvis
      have : (omega D : ℤ) + δ ≤ (M θ : ℤ) := by
        have : (omega D : ℤ) ≤ T := by exact_mod_cast hsmall
        omega
      exact_mod_cast this

/-- **The division by `2^{n_U}`** (tex L10221–10225; PROVED, arithmetic part). "Consequently
`v₂B_U[Jrm²] ≥ min{R, ω(r)}` for every Fourier index and every `U` in the budget at this one
stage." Here `x = v₂(2^{n_U} B_U[Jrm²])` satisfies one of the two displayed bounds
`x ≥ N_0 + R` (large weight) or `x ≥ min{M, n_U + ω(r)}` (bounded weight), with `n_U ≤ N_0`
(as `n_U = δ_o + |U|`, `|U| ≤ W_U`) and `M ≥ N_0 + R`. The conclusion is
`x − n_U ≥ min{R, ω(r)}`, i.e. `v₂ B_U[Jrm²] ≥ min{R, ω(r)}`. -/
def BudgetDivision : Prop :=
  ∀ (x : WithTop ℤ) (nU N0 R M ωr : ℤ), nU ≤ N0 → N0 + R ≤ M →
    (((N0 + R : ℤ) : WithTop ℤ) ≤ x ∨ ((min M (nU + ωr) : ℤ) : WithTop ℤ) ≤ x) →
    ((min R ωr + nU : ℤ) : WithTop ℤ) ≤ x

theorem budgetDivision_proof : BudgetDivision := by
  intro x nU N0 R M ωr h1 h2 h
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h' : N0 + R ≤ n ∨ min M (nU + ωr) ≤ n := by
      rcases h with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    have : min R ωr + nU ≤ n := by
      rcases h' with h' | h'
      · have := min_le_left R ωr; omega
      · rcases min_choice M (nU + ωr) with hm | hm
        · rw [hm] at h'; have := min_le_left R ωr; omega
        · rw [hm] at h'; have := min_le_right R ωr; omega
    exact_mod_cast this

/-! ## The unit symbol and (F.7) -/

/-- **The exhaustive unit symbol and (F.7)** (proof of `ex:app-odd-minimum`, tex L10236–10256;
PROVED). "Fix a squarefree-output cutoff `L`. On a set of stages in the same ultrafilter, (F.6)
holds through `L` and `M_θ > δ_o + L`. Define `𝒜_{M_θ,L}(D)` … one when
`v₂a_{M_θ}(D) = δ_o + ω(D)` on that filter, and zero otherwise. This is exhaustive on the tested
range: visible coefficients satisfy (F.6), while invisible ones have valuation at least
`M_θ > δ_o + ω(D)`. In particular a unit in this range is visible and satisfies
`ord_{s=1}L(E^D,s) = 1`, `j_gen(D) ≤ ω(D) + C_o`, `C_o = δ_o + C_det`. (F.7)"

Conclusion, on a set of stages in the ultrafilter: `M_θ > δ_o + L`, every admissible `D` with
`ω(D) ≤ L` has `v₂a_{M_θ}(D) ≥ ω(D) + δ_o` (so the symbol is the indicator of equality), and
equality gives the simple zero and `j_gen(D) ≤ ω(D) + (δ_o + C_det)`. `C_o` is independent of `L`
and of the stage. -/
def UnitSymbolF7 : Prop :=
  ∀ (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (simpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (δ Cdet : ℤ) (L : ℕ),
    Tendsto M (U : Filter ℕ) atTop →
    (∀ θ D, adm θ D → v θ D < M θ → simpleZero D ∧ (jgen D : WithTop ℤ) ≤ v θ D + Cdet) →
    (∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W → v θ D < M θ →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D) →
    ∀ᶠ θ in (U : Filter ℕ), δ + L < (M θ : ℤ) ∧ ∀ D, adm θ D → omega D ≤ L →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D ∧
      (v θ D = (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) →
        simpleZero D ∧ jgen D ≤ (omega D : ℤ) + (δ + Cdet))

theorem unitSymbolF7_proof : UnitSymbolF7 := by
  intro U M v adm simpleZero jgen δ Cdet L hM hvis hF6
  filter_upwards [truncatedF6_proof U M v adm δ hM hF6 L, eventually_lt_M hM (δ + L)]
    with θ hθ hMθ
  refine ⟨hMθ, fun D hD hL => ⟨hθ D hD hL, fun heq => ?_⟩⟩
  have hlt : v θ D < M θ := by
    rw [heq]
    have : (omega D : ℤ) ≤ L := by exact_mod_cast hL
    have : (omega D : ℤ) + δ < (M θ : ℤ) := by omega
    exact_mod_cast this
  obtain ⟨hz, hj⟩ := hvis θ D hD hlt
  rw [heq] at hj
  refine ⟨hz, ?_⟩
  have : jgen D ≤ (omega D : ℤ) + δ + Cdet := by exact_mod_cast hj
  linarith

end ZInQ.Contrib.CloudB3RC53.AppGEndpoints
