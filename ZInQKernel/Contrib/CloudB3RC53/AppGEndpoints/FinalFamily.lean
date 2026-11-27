import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.OddMinimum

/-!
# App G endpoints: one actual stage for the final family (Proposition `ex:app-final-family`)

Manuscript `diophantine_zq.tex`, Appendix G, Proposition `ex:app-final-family` and its proof
(tex L10792–10861), which supplies (3.9) of Proposition `ex:sec7-final-family` (L2674–2713);
the consequence `2 j_rc(h_x,k) ≤ 4ω(h_x) + C_J` (L2704–2705, L10866–10870).

As in `OddMinimum.lean`, the nodes are generic over the non-Mathlib data, in the conventions of
the Theorem 5.3 interface data (stages `ℕ`, one `Ultrafilter ℕ`, precisions `M θ`, valuations
`v θ D = v₂ a_{M_θ}(D) : WithTop ℤ`, the visibility clause of (O.8)). A binary family is given
generically by a type `Fam` with a dimension `dim F` and members `h_x = hfam F x` for
`x ∈ 𝔽₂^{dim F}`; for the interface's `Family` take `dim = Family.b`, `hfam = Family.h`.

**The input from the address construction** (Lemma `ex:sec7-two-symbol-address`, Propositions
`ex:app-simultaneous-address`, `ex:app-odd-stabilization`, the prime realization by CRT,
Dirichlet and reciprocity; lanes owning §7.3 and App G L10508–10791) enters as one explicit
hypothesis `AddressInput`, in the form in which the proof of `ex:app-final-family` uses it
(L10800–10850): for every sufficiently large `b` there are a finite budget `W_b` and finitely many
selected truth-table sets `A_1, …, A_t` in the ultrafilter such that, at every stage in their
intersection that is valid for the operator budget `|U| ≤ W_b` with `R = 2` (the stage conditions
of `StageChoice`: (F.6) through a threshold `T ≥ W_b + 1` with `T − C_coarse ≥ N_0 + 2`,
`M ≥ max(0, δ_o + W_b) + 2`, `M > T + δ_o`), the construction is realized by a family over `𝔽₂^b`
whose every nonzero address is a unit of both sources: `ω(h_x) ≤ W_b` (the tested range),
`h_x` keeps the fixed local types and is admissible at the stage, `v₂a_M(h_x) = δ_o + ω(h_x)`
(odd unit), and `L_*(h_x k) ≠ 0`, `v₂L_*(h_x k) ≤ 2ω(h_x) + C_{e,final}` (normalized even unit).

What is PROVED here is Elliot's own part of L10808–10861: the finite intersection of ultrafilter
sets, the choice of one stage, the strict inequality from the tested-range precision, and the
application of (O.8), giving (3.9) with `C_o = δ_o + C_det`, `C_e = C_{e,final}` fixed before `b`.

| node | tex | kind |
|---|---|---|
| `FiniteIntersection` | L10829–10838 | PROVED |
| `FinalFamily39` | L10792–10861 | PROVED (from `AddressInput`, (O.8), (F.5), (F.6)) |
| `RcUpperCJ` | L2704–2705, L10866–10870 | PROVED (from (3.9) and (3.4)) |
| `OddMinimumToFinalFamily` | L10151–10256, L10792–10861 | PROVED (composite) |
-/

namespace ZInQ.Contrib.CloudB3RC53.AppGEndpoints

open Filter

/-- **The finite intersection** (proof of `ex:app-final-family`, tex L10829–10838; PROVED). "Let
`𝒰` be the chosen ultrafilter and let `A_1, …, A_t ∈ 𝒰` be the selected truth-table sets used by
that program … Let `B ∈ 𝒰` impose … Then `B ∩ ⋂_{i=1}^t A_i ∈ 𝒰`, hence is nonempty." -/
def FiniteIntersection : Prop :=
  ∀ (U : Ultrafilter ℕ) (t : ℕ) (A : Fin t → Set ℕ) (B : Set ℕ),
    (∀ i, A i ∈ (U : Filter ℕ)) → B ∈ (U : Filter ℕ) →
    (B ∩ ⋂ i, A i) ∈ (U : Filter ℕ) ∧ (B ∩ ⋂ i, A i).Nonempty

theorem finiteIntersection_proof : FiniteIntersection := by
  intro U t A B hA hB
  have h : (B ∩ ⋂ i, A i) ∈ (U : Filter ℕ) := Filter.inter_mem hB (Filter.iInter_mem.mpr hA)
  exact ⟨h, Ultrafilter.nonempty_of_mem h⟩

/-- **The input from the address construction**, at the odd minimum `δ` (see the module
docstring; tex L10794–10806, L10808–10850). Not proved here: owned by the lanes of the address
lemmas and the prime realization. -/
def AddressInput (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (prepared : ℤ → Prop) (Lstar : ℤ → ℚ) (k δ CeFinal : ℤ) (Ccoarse : ℚ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop) : Prop :=
  ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∃ (Wb t : ℕ) (A : Fin t → Set ℕ), (∀ i, A i ∈ (U : Filter ℕ)) ∧
    ∀ T : ℕ, Wb + 1 ≤ T → (((max 0 (δ + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
    ∀ θ ∈ ⋂ i, A i,
      (∀ D, adm θ D → omega D ≤ T → v θ D < M θ →
        (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D) →
      max 0 (δ + Wb) + 2 ≤ (M θ : ℤ) → (T : ℤ) + δ < M θ →
      ∃ F : Fam, dim F = b ∧ FamAdm F ∧ ∀ x : Fin (dim F) → ZMod 2, x ≠ 0 →
        omega (hfam F x) ≤ Wb ∧ prepared (hfam F x) ∧ adm θ (hfam F x) ∧
        v θ (hfam F x) = (((omega (hfam F x) : ℤ) + δ : ℤ) : WithTop ℤ) ∧
        Lstar (hfam F x * k) ≠ 0 ∧
        padicValRat 2 (Lstar (hfam F x * k)) ≤ 2 * (omega (hfam F x) : ℤ) + CeFinal

/-- **(3.9): one actual stage for the final family** (Proposition `ex:app-final-family`, tex
L10792–10861, giving (3.9) of `ex:sec7-final-family`, L2674–2700; PROVED from its inputs).
"For every sufficiently large `b`, the address construction is realized at one actual theta stage
by a finite set `Q` of distinct good odd primes split in `K` … it gives exactly the family in
(3.9) … for every `x ≠ 0`, `ord_{s=1}L(E^{h_x},s) = 1`, `L_*(h_xk) ≠ 0`,
`j_gen(h_x) ≤ ω(h_x) + C_o`, `v₂L_*(h_xk) ≤ 2ω(h_x) + C_e`. The constants precede `b`."
Proof (L10829–10861): the stage conditions form one set `B ∈ 𝒰` (`StageChoice` with `R = 2`);
`B ∩ ⋂ A_i ∈ 𝒰` is nonempty; at a stage there every nonzero address is a unit of both sources,
`v₂a_M(h_x) = δ_o + ω(h_x) < M` by the tested-range precision; (O.8) gives the simple zero and
`j_gen(h_x) ≤ ω(h_x) + δ_o + C_det`; so `C_o = δ_o + C_det`, `C_e = C_{e,final}`.

Hypotheses: the stage precision tends to infinity along `𝒰` (L2491–2500, L2536–2551); (O.8)
(visibility clause, App F L9407–9445); (F.5) at every stage (`CoarseF5`); (F.6) for every weight
bound (`OddMinimumF6`); `AddressInput`. The conclusion, unfolded, is the interface's
`FinalFamilyAt (δ + C_det) C_{e,final}` minus its admissibility conjunct, which is `FamAdm`. -/
def FinalFamily39 : Prop :=
  ∀ (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (simpleZero prepared : ℤ → Prop) (jgen : ℤ → ℤ) (Lstar : ℤ → ℚ)
    (k δ Cdet CeFinal : ℤ) (Ccoarse : ℚ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop),
    Tendsto M (U : Filter ℕ) atTop →
    (∀ θ D, adm θ D → v θ D < M θ → simpleZero D ∧ (jgen D : WithTop ℤ) ≤ v θ D + Cdet) →
    (∀ θ D, adm θ D → QLe (min (M θ : ℚ) (omega D - Ccoarse)) (v θ D)) →
    (∀ W : ℕ, ∀ᶠ θ in (U : Filter ℕ), ∀ D, adm θ D → omega D ≤ W → v θ D < M θ →
      (((omega D : ℤ) + δ : ℤ) : WithTop ℤ) ≤ v θ D) →
    AddressInput U M v adm prepared Lstar k δ CeFinal Ccoarse Fam dim hfam FamAdm →
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∃ F : Fam, dim F = b ∧ FamAdm F ∧
      ∀ x : Fin (dim F) → ZMod 2, x ≠ 0 →
        prepared (hfam F x) ∧ simpleZero (hfam F x) ∧ Lstar (hfam F x * k) ≠ 0 ∧
        jgen (hfam F x) ≤ (omega (hfam F x) : ℤ) + (δ + Cdet) ∧
        padicValRat 2 (Lstar (hfam F x * k)) ≤ 2 * (omega (hfam F x) : ℤ) + CeFinal

theorem finalFamily39_proof : FinalFamily39 := by
  intro U M v adm simpleZero prepared jgen Lstar k δ Cdet CeFinal Cc Fam dim hfam FamAdm
    hM hvis hF5 hF6 hAddr
  obtain ⟨b₀, hb⟩ := hAddr
  refine ⟨b₀, fun b hb₀ => ?_⟩
  obtain ⟨Wb, t, A, hA, hreal⟩ := hb b hb₀
  -- the stage set `B` for the budget `W_b` with `R = 2`
  obtain ⟨T, hT1, hT2, hB⟩ := stageChoice_proof U M v adm Cc δ Wb 2 le_rfl hM hF5 hF6
  obtain ⟨-, θ, hθB, hθA⟩ := finiteIntersection_proof U t A _ hA hB
  obtain ⟨hF6T, hMa, hMb, -, -⟩ := hθB
  obtain ⟨F, hdim, hFadm, hunit⟩ := hreal T hT1 (by exact_mod_cast hT2) θ hθA hF6T
    (by exact_mod_cast hMa) hMb
  refine ⟨F, hdim, hFadm, fun x hx => ?_⟩
  obtain ⟨hW, hprep, hadm, hv, hL, hLe⟩ := hunit x hx
  -- the tested-range precision makes the odd unit visible
  have hlt : v θ (hfam F x) < M θ := by
    rw [hv]
    have h1 : (omega (hfam F x) : ℤ) ≤ Wb := by exact_mod_cast hW
    have h2 : δ + Wb ≤ max 0 (δ + Wb) := le_max_right _ _
    have : (omega (hfam F x) : ℤ) + δ < (M θ : ℤ) := by omega
    exact_mod_cast this
  obtain ⟨hz, hj⟩ := hvis θ (hfam F x) hadm hlt
  rw [hv] at hj
  have hj' : jgen (hfam F x) ≤ (omega (hfam F x) : ℤ) + δ + Cdet := by exact_mod_cast hj
  exact ⟨hprep, hz, hL, by linarith, hLe⟩

/-- **`2 j_rc(h_x,k) ≤ 4ω(h_x) + C_J`** (Proposition `ex:sec7-final-family`, tex L2704–2705: "By
(3.4), now with fixed `k`, `2j_rc(h_x,k) ≤ 4ω(h_x) + C_J`"; App G L10866–10870:
`C_J = 2C_o + C_{e,final} − v₂L_*(h_*) + C_{H,final}`; PROVED). From the two bounds of (3.9) at
`h = h_x` and (3.4) in the form `2j_rc(h,k) − 2j_gen(h) = v₂L_*(hk) − v₂L_*(h_*) + C_per + ε`,
`|ε| ≤ 2`. ELLIOT: `C_{H,final}` is not defined in the text; it is `C_per + 2` (cf. `C_H` in
(F.4)). -/
def RcUpperCJ : Prop :=
  ∀ (jgen : ℤ → ℤ) (jrc : ℤ → ℤ → ℤ) (Lstar : ℤ → ℚ) (h k hstar Co Ce Cper : ℤ),
    jgen h ≤ (omega h : ℤ) + Co →
    padicValRat 2 (Lstar (h * k)) ≤ 2 * (omega h : ℤ) + Ce →
    (∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * jrc h k - 2 * jgen h =
      padicValRat 2 (Lstar (h * k)) - padicValRat 2 (Lstar hstar) + Cper + ε) →
    2 * jrc h k ≤ 4 * (omega h : ℤ) + (2 * Co + Ce - padicValRat 2 (Lstar hstar) + (Cper + 2))

theorem rcUpperCJ_proof : RcUpperCJ := by
  intro jgen jrc Lstar h k hstar Co Ce Cper hj hL ⟨ε, hε, heq⟩
  have := (abs_le.mp hε).2
  linarith

/-- **From the inputs of `ex:app-odd-minimum` to (3.9)** (tex L10151–10256 and L10792–10861;
PROVED composite). The inputs: (3.4), (3.5) and the rough companion with (F.3) at the known simple
zeros of the prepared filter (for (F.4)); (O.8) (visibility clause); admissible theta parameters
lie in the prepared filter (GLUE); the fixed visible witness `D_w` ((3.7), (O.2), (O.7)); the
precision tends to infinity along the ultrafilter; and the address input at the attained odd
minimum. Conclusion: there is an attained odd minimum `δ_o` (`IsLeast (DepthSet …)`), and the
final family (3.9) exists for every sufficiently large `b` with `C_o = δ_o + C_det` and
`C_e = C_{e,final}`. The coarse constant is
`C_coarse = C_gen/2 + C_det`, `C_gen = 2A + C_R + C_E − v₂L_*(h_*) + (C_per + 2)`. -/
def OddMinimumToFinalFamily : Prop :=
  ∀ (U : Ultrafilter ℕ) (M : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ) (adm : ℕ → ℤ → Prop)
    (simpleZero prepared : ℤ → Prop) (companion : ℤ → ℤ → Prop) (Lstar : ℤ → ℚ)
    (jgen : ℤ → ℤ) (jrc : ℤ → ℤ → ℤ) (s : ℤ → ℕ) (hstar A CR CE Cper Cdet k CeFinal : ℤ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop),
    -- (F.3) with the rough companion, (3.4), (3.5)
    (∀ h, prepared h → simpleZero h → ∃ k', companion h k' ∧ (omega k' : ℤ) ≤ A ∧
      Lstar (h * k') ≠ 0 ∧
      padicValRat 2 (Lstar (h * k')) ≤ 2 * omega h + 2 * omega k' + s (h * k') + CE) →
    (∀ h k', prepared h → simpleZero h → companion h k' → ∃ ε : ℤ, |ε| ≤ 2 ∧
      2 * jrc h k' - 2 * jgen h =
        padicValRat 2 (Lstar (h * k')) - padicValRat 2 (Lstar hstar) + Cper + ε) →
    (∀ h k', prepared h → simpleZero h → companion h k' → (omega k' : ℤ) ≤ A →
      4 * (omega h : ℤ) + s h + s (h * k') - CR ≤ 2 * jrc h k') →
    -- (O.8), the prepared filter, the witness, advancing stages
    (∀ θ D, adm θ D → v θ D < M θ → simpleZero D ∧ (jgen D : WithTop ℤ) ≤ v θ D + Cdet) →
    (∀ θ D, adm θ D → prepared D) →
    (∃ Dw c : ℤ, ∀ᶠ θ in (U : Filter ℕ), adm θ Dw ∧ v θ Dw = (c : WithTop ℤ) ∧
      (c : WithTop ℤ) < M θ) →
    Tendsto M (U : Filter ℕ) atTop →
    -- the address construction at the attained minimum
    (∀ δ : ℤ, IsLeast (DepthSet U M v adm) δ →
      AddressInput U M v adm prepared Lstar k δ CeFinal
        (((2 * A + CR + CE - padicValRat 2 (Lstar hstar) + (Cper + 2) : ℤ) : ℚ) / 2 + Cdet)
        Fam dim hfam FamAdm) →
    ∃ δ : ℤ, IsLeast (DepthSet U M v adm) δ ∧
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∃ F : Fam, dim F = b ∧ FamAdm F ∧
        ∀ x : Fin (dim F) → ZMod 2, x ≠ 0 →
          prepared (hfam F x) ∧ simpleZero (hfam F x) ∧ Lstar (hfam F x * k) ≠ 0 ∧
          jgen (hfam F x) ≤ (omega (hfam F x) : ℤ) + (δ + Cdet) ∧
          padicValRat 2 (Lstar (hfam F x * k)) ≤ 2 * (omega (hfam F x) : ℤ) + CeFinal

theorem oddMinimumToFinalFamily_proof : OddMinimumToFinalFamily := by
  intro U M v adm simpleZero prepared companion Lstar jgen jrc s hstar A CR CE Cper Cdet k
    CeFinal Fam dim hfam FamAdm h33 h34 h35 hvis hprep hw hM hAddr
  set Cgen : ℤ := 2 * A + CR + CE - padicValRat 2 (Lstar hstar) + (Cper + 2) with hCgen
  -- (F.4) at admissible simple zeros
  have hF4 : ∀ D, (∃ θ, adm θ D) → simpleZero D → 2 * (omega D : ℤ) + s D - Cgen ≤ 2 * jgen D :=
    fun D ⟨θ, hD⟩ hz =>
      genusLowerF4_proof prepared simpleZero companion Lstar jgen jrc s hstar A CR CE Cper
        h33 h34 h35 D (hprep θ D hD) hz
  -- (F.5) at every stage
  have hF5 : ∀ θ D, adm θ D →
      QLe (min (M θ : ℚ) (omega D - (((Cgen : ℤ) : ℚ) / 2 + Cdet))) (v θ D) :=
    fun θ D hD => coarseF5_proof (adm θ) simpleZero jgen s (v θ) (M θ) Cdet Cgen
      (fun D' hD' hlt => hvis θ D' hD' hlt) (fun D' hD' hz => hF4 D' ⟨θ, hD'⟩ hz) D hD
  -- the attained minimum and (F.6)
  obtain ⟨δ, hδ, hF6⟩ := oddMinimumF6_proof U M v adm _ hF5 hw
  exact ⟨δ, hδ, finalFamily39_proof U M v adm simpleZero prepared jgen Lstar k δ Cdet CeFinal _
    Fam dim hfam FamAdm hM hvis hF5 hF6 (hAddr δ hδ)⟩

end ZInQ.Contrib.CloudB3RC53.AppGEndpoints
