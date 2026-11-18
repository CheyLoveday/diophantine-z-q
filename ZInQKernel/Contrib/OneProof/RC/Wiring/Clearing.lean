import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Determinant.Genuine
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Bridges

/-!
# Theorem 5.3, Lane RC0 round 2: the determinant clearing (5.9) from lane RC7

`ClearingTarget D` is the field `RCSteps.clearing` (Proposition `ex:limits-fixed-field-clearing`,
display (5.9), tex 5487–5645). This file proves it, `clearingTarget_of_inputs`, from lane RC7's
`clearing_nodes` (PROVED from named inputs; tex 5487–5645) and the remaining inputs of that
theorem, collected in `ClearingInputs D`. How the inputs of `clearing_nodes` are instantiated:

* **The coefficient ring** is lane RC7's genuine `𝒪 = (Λ_{(2)})^ = lim_n (ℤ/2ⁿ)((t))` (`OO`, tex
  2747–2748, 3728) with its pole filtration `genuinePole` and Laurent coefficients
  `genuineLaurent`; all of this, and `2 ≠ 0` in `𝒪`, is PROVED by lane RC7. The variant
  `ClearingInputsGeneric` allows any coefficient ring with these structures
  (`clearingInputsGeneric_of_inputs`, `clearingTarget_of_generic`).
* **The paired-functional exponent is `a = 0`** (Proposition `ex:arith-paired-functional`, tex
  3864–3869; batch 3 PairedFunctional, `pairedFunctionalIntegral_proof`: the closed functional
  `λ_z` is integral over `S = 𝒪[G]` itself). Hence `c_det = 4(h_K + 2c_E + 2t_K)` and
  `c = v₂ f₀(0) = 4h₁`. The `μ`-coordinates of RC7's `ScalarData` can be taken to be the coordinates
  of that integral closed functional (`scalarData_of_pairedFunctional`, not used by
  `clearingTarget_of_complex`, where the scalar data are existential; from batch 3's
  `exists_closed_pairedFunctional` and `scalarDataMuIntegral_proof`, with the unit premise of the
  tame local models over `𝒪[G]` supplied by lane RC7's augmentation criterion,
  `tame_unit_of_aug`). No PairedFunctional input remains in `ClearingInputs`.
* **The coordinates** are those of the data: `u x j = [tʲ] ũ_x = PowerSeries.coeff j (D.uTilde F x)`
  for every final family `F`. RC7's input `hu` (`ũ_x = g_x / 2^{e_x}`, `g_x ∈ Λ`) is supplied by
  height-one regularity, which is exactly `HeightOneTarget D` (the field `RCSteps.height_one`,
  lane RC16). Elliot's coordinate identity is stated for every such representation of `ũ_x`; this
  is equivalent to RC7's form for one representation (`forall_clearingCoordIdentity_iff`, from
  `uK_eq_of_coeff_eq`: the element `ũ_x` of `Frac 𝒪` does not depend on the representation).
* **The constants** `d_K, h_K, c_E, t_K` are fixed before the family (tex 5641–5643: "The constants
  `d_K, t_K, h_K` are fixed only after the final `K` is fixed; `a` and `c_E` precede that choice.
  None depends on the graph or binary dimension."). The auxiliary objects of RC7 (Smith blocks,
  scalar data, `κ, ε, η`, the two generic patterns) are existential per family. They do not depend
  on the precision `M`: RC7's pole input holds for every `M`, as in the text.

Non-vacuity (PROVED): `ClearingInputs D` holds for every datum whose corrected coordinates are
`ũ_x = 1` (`clearingInputs_of_uTilde_eq_one`, with unit Smith disks), in particular for lane RC0's
`toyData` (`clearingInputs_toyData`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData PoleData
  LaurentCoeffData aug sgnChar evK uK cleanT genuinePole genuineLaurent)

/-! ## The inputs of RC7's (5.9), one `Prop` each -/

section Inputs

variable {O : Type} [CommRing O] [Algebra Lam O] {b : ℕ}

/-- **E3: the central Smith model of the remaining complex `D`** (tex 5517, 5522–5538; ELLIOT,
lane RC7, open). `B` is the central Smith data of the complex `D` over `S = 𝒪[G]` left by the
simultaneous new-local cancellation of Lemma `ex:limits-fixed-field-budget` (tex 5394–5427):
`A_i` the actual differential submatrix from `E_i` to `B_{i+1}`, with augmentation `A0 i` over `Λ`
whose central reduction is the diagonal of the nonzero Smith entries (`SmithBlocks`). The
conjuncts: the disks are indexed by the source degrees `i < n`, `n ≥ 3` (RC7's indexing
convention, DEPARTURE D3 of form: degrees `0–3`, `α` uses `A_0`, `β` uses `A_2`), and "the
augmentation of `D` is the old complex over `Λ`" (tex 5517, 5537–5538). -/
def ClearingSmithModel (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) : Prop :=
  2 < B.n ∧ ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam O)

/-- **E2 (exhaustiveness): only two generic patterns** (tex 5615–5617, "These are the only generic
patterns in the present family, by central specialization and the central corank-one bound";
ELLIOT, lane RC7, open): every constituent has the rank-one cohomology pattern or is generically
acyclic. -/
def ClearingPatterns (RankOne Acyclic : Addr b → Prop) : Prop :=
  ∀ x, RankOne x ∨ Acyclic x

/-- **E1, E2: Elliot's determinant-coordinate identity and the acyclic pattern** (tex 5586–5617;
ELLIOT, lane RC7, open: the determinant-line contribution `δ_i^{(-1)^i}` of a based disk needs the
determinant functor of complexes, which is not in Mathlib). Verbatim the hypotheses `hrank`,
`hacyc` of RC7's `clearing_nodes`, at the exponent `a`, for the representation `ũ_x = g_x / 2^{e_x}`
(viewed in `Frac 𝒪` as `uK (e x) (g x)`): where `Δ_x ≠ 0`, in the rank-one pattern
`ũ_x = η_x κ_x α_x (2^{-a} β_x) T_x` (tex 5605–5609), and in the acyclic pattern `α_x = 0` and
`ũ_x = 0` (tex 5613–5615). Here `α, β` are computed from the scalar data `sd` (the transported
cycle `z` and closed functional `μ = 2^a λ_z`, tex 5513–5516, 5577–5584), `T = ε ∏ δ_i^{(-1)^i}`
(tex 5591–5593), `κ` is the determinant comparison factor of the new-local cancellation (tex
5509–5513), `ε` the integral unit of the fixed basis ordering (tex 5595–5597), `η` the universal
correction of Lemma `ex:arith-common-coordinate` (lane RC15). -/
def ClearingCoordIdentity [IsDomain O] (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O)
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O (SignGroup b)) (a : ℕ) (e : Addr b → ℕ)
    (g : Addr b → Lam) (RankOne Acyclic : Addr b → Prop) : Prop :=
  (∀ x : Addr b, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing O) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε) ∧
  (∀ x : Addr b, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing O))

/-- **The entry pole bound at every sign character** (tex 5517–5519, "each sign-evaluated
differential entry has pole at most `4M` modulo `2^M`"; lane RC7): every sign-evaluated entry of
every `A_i` lies in `t^{-4M} Λ + 2^M 𝒪`, for every `M`. Kind: ELLIOT for the identification of the
entries of `D_x` (E3); the bound itself is RC7's PROVED (5.8) (`newLocal_family_pole_genuine`,
`PoleData.newLocal_schur_pole`) transported by `entry_pole_of_differential`. -/
def ClearingEntryPoles (P : PoleData Lam O) (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) :
    Prop :=
  ∀ (x : Addr b) (M i : ℕ), ∀ j k,
    ((B.A i).map (Determinant.signEval (sgnChar x))) j k ∈ P.poleModLE M (4 * M)

/-- **The budget (5.7)** (tex 5251–5392, display at 5384–5392): `m ≤ d_K + 5` and
`h₁ ≤ h_K + 2c_E + 2t_K`. PROVED by lane RC7's `budget_57` from the cohomological counts of batch 3
RankCounts ((5.7a)–(5.7d), `H⁰(D_c) = 0`, minimality of the model, `J_r`, the torsion
identification; prints: Nekovář, *Selmer complexes*, Astérisque 310 (2006), §§5.1.1–5.1.6,
6.3.4, 7.8.8(ii), locators as quoted in the manuscript, UNVERIFIED) and the moving-character
bound `v₂(r + 1 − a_k) ≤ c_E` (Proposition `ex:arith-moving-character`, lane RC4). (Lane RC6's
`ResidualRankCounts` concerns the residual bound (5.1), tex 4453–4648, not (5.7).) -/
def ClearingBudget {S : Type} [CommRing S] (B : SmithBlocks S O) (dK hK cE tK : ℕ) : Prop :=
  B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK

end Inputs

/-- **The representation `ũ_x = g_x / 2^{e_x}`** (`g_x ∈ Λ`) of the corrected coordinates of the
family `F` (tex 5703–5706, 5710–5715): RC7's input `hu` with `u x j = [tʲ] ũ_x`. -/
def UTildeRep {ℓ : ℕ} (D : RCData ℓ) (F : Family) (e : Addr F.b → ℕ) (g : Addr F.b → Lam) :
    Prop :=
  ∀ x j, PowerSeries.coeff j (D.uTilde F x) =
    ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x

/-- **The per-family inputs of RC7's (5.9) over a coefficient ring `O`** (with pole filtration
`P`), at the paired-functional exponent `a = 0` and the constants `d_K, h_K, c_E, t_K`: central
Smith data `B` of the remaining complex, scalar data `sd`, the elements `κ, ε, η` of `O[G]`,
`G = 𝔽₂^b`, and the two generic patterns, with E3 (`ClearingSmithModel`), E2
(`ClearingPatterns`), E1–E2 for every representation of the coordinates (`ClearingCoordIdentity`),
the entry pole bound (`ClearingEntryPoles`) and (5.7) (`ClearingBudget`). -/
def ClearingModelOver {O : Type} [CommRing O] [IsDomain O] [Algebra Lam O] (P : PoleData Lam O)
    {ℓ : ℕ} (D : RCData ℓ) (dK hK cE tK : ℕ) (F : Family) : Prop :=
  ∃ (B : SmithBlocks (MonoidAlgebra O (SignGroup F.b)) O) (sd : ScalarData B)
    (κ ε η : MonoidAlgebra O (SignGroup F.b)) (RankOne Acyclic : Addr F.b → Prop),
    ClearingSmithModel B ∧ ClearingPatterns RankOne Acyclic ∧
    (∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g →
      ClearingCoordIdentity B sd κ ε η 0 e g RankOne Acyclic) ∧
    ClearingEntryPoles P B ∧ ClearingBudget B dK hK cE tK

/-- **The model inputs of (5.9) over the genuine `𝒪`** (tex 5487–5645): constants
`d_K, h_K, c_E, t_K` fixed before the family (tex 5641–5643) and, at every final family `F`, the
per-family inputs `ClearingModelOver genuinePole` (E3, E2, E1–E2, the entry pole bound, (5.7)).
Together with `HeightOneTarget D` these are `ClearingInputs D`. -/
def ClearingModel {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ClearingModelOver genuinePole D dK hK cE tK F

/-- **The remaining inputs of the determinant clearing (5.9)** (Proposition
`ex:limits-fixed-field-clearing`, tex 5487–5645): exactly the hypotheses of lane RC7's
`clearing_nodes` that are not discharged here, with the coordinates `u x j = [tʲ] ũ_x` of the data
at every final family, the genuine `𝒪`, and the exponent `a = 0`.

| conjunct | tex | kind | owner |
|---|---|---|---|
| `HeightOneTarget D`: every `ũ_x` of a final family lies in `Λ[1/2]` (RC7's `hu`, E6) | 4909–5205, 5703–5704 | ELLIOT | RC16 (it is the field `RCSteps.height_one`) |
| `ClearingModel D`: `∃ dK hK cE tK`, before the family | 5251–5267, 5641–5643 | definition | (content in (5.7)) |
| per final family `F`, over the genuine `𝒪`: `∃ B sd κ ε η RankOne Acyclic` | 5509–5603 | definition | RC7 |
| `ClearingSmithModel B` (E3: `2 < n`, augmentation `A_i ↦ A0 i`) | 5517, 5522–5538 | ELLIOT (+ DEPARTURE D3 of form) | RC7 (open: Selmer-complex model of `D`; print (5.6) Nekovář 7.8.8(ii) UNVERIFIED; GLUE 5409–5411) |
| `ClearingPatterns` (E2: only two generic patterns) | 5615–5617 | ELLIOT | RC7 (open) |
| `ClearingCoordIdentity … 0 e g …` for every representation `ũ = g/2^e` (E1, E2) | 5586–5617 | ELLIOT | RC7 (open: determinant functor); `η` RC15; `μ` batch 3 PairedFunctional (`scalarData_of_pairedFunctional`, `a = 0`) |
| `ClearingEntryPoles genuinePole B` (pole `≤ 4M` mod `2^M` of the entries) | 5517–5519 | ELLIOT (E3) + PROVED (5.8) | RC7 |
| `ClearingBudget B dK hK cE tK` ((5.7)) | 5251–5392 | PROVED from inputs (`budget_57`) | batch 3 RankCounts, RC4 (`c_E`) |

Discharged here (not inputs): the ring `𝒪`, its pole filtration and Laurent coefficients, `2 ≠ 0`
(lane RC7, PROVED); the exponent `a = 0` (batch 3 PairedFunctional,
`pairedFunctionalIntegral_proof`, tex 3864–3869); the integrality of the `μ`-coordinates (by type;
`scalarDataMuIntegral_proof`); the representation `ũ_x = g_x/2^{e_x}` (from `HeightOneTarget D`);
`u = [tʲ] ũ`. The combined content
of `ClearingPatterns` and `ClearingCoordIdentity` is: where `Δ_x ≠ 0`, either
`ũ_x = η_x κ_x α_x β_x T_x`, or `α_x = 0` and `ũ_x = 0`. -/
def ClearingInputs {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  HeightOneTarget D ∧ ClearingModel D

/-- **The inputs of (5.9) over any coefficient ring** (the form of RC7's generic `clearing_nodes`):
as `ClearingInputs`, but the coefficient ring `O` (a domain with `2 ≠ 0`, a `Λ`-algebra with a pole
filtration `P` and a Laurent-coefficient realization) is existential per family. Implied by
`ClearingInputs` (`clearingInputsGeneric_of_inputs`). -/
def ClearingInputsGeneric {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  HeightOneTarget D ∧
    ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra Lam O) (P : PoleData Lam O)
        (_ : LaurentCoeffData P), (2 : O) ≠ 0 ∧ ClearingModelOver P D dK hK cE tK F

/-! ## (5.9) from the inputs -/

/-- **`RCSteps.clearing` from the inputs over any coefficient ring** (PROVED from lane RC7's
`clearing_nodes`; tex 5487–5645). The constants are `c_det = 0 + 4(h_K + 2c_E + 2t_K)` and `d_K`;
for a final family `F`, height-one regularity gives `ũ_x = g_x / 2^{e_x}`, and `clearing_nodes`
gives coefficient data `C` with `C.u = [tʲ] ũ`, the clearing identity, the pole bound
`L_T(M) = 16(d_K + 5)M` for every `M`, and a regular base with `c = 0 + 4h₁ ≤ c_det`. -/
theorem clearingTarget_of_generic {ℓ : ℕ} (D : RCData ℓ) (h : ClearingInputsGeneric D) :
    ClearingTarget D := by
  obtain ⟨hH, dK, hK, cE, tK, hM⟩ := h
  refine ⟨0 + 4 * (hK + 2 * cE + 2 * tK), dK, fun M Co Ce F hF => ?_⟩
  obtain ⟨O, _, _, _, P, LC, h2O, B, sd, κ, ε, η, RankOne, Acyclic, ⟨hn, haug⟩, hpat, hcoord,
    hpole, hm, hh⟩ := hM Co Ce F hF
  -- height-one regularity: `ũ_x = g_x / 2^{e_x}` with `g_x ∈ Λ`
  have hreg : ∀ x : Addr F.b, ∃ (e : ℕ) (g : ℕ → ℤ_[2]),
      ∀ n : ℕ, PowerSeries.coeff n (D.uTilde F x) = (g n : ℚ_[2]) / 2 ^ e :=
    fun x => hH Co Ce F hF x
  choose e g hg using hreg
  have hu : UTildeRep D F e (fun x => PowerSeries.mk (g x)) := by
    intro x j
    rw [PowerSeries.coeff_mk]
    exact hg x j
  obtain ⟨hrank, hacyc⟩ := hcoord e _ hu
  obtain ⟨C, hCu, ⟨hdec, -, hsum⟩, hpl, hbase, hle⟩ :=
    Determinant.clearing_nodes LC B hn haug sd κ ε η 0
      (fun x j => PowerSeries.coeff j (D.uTilde F x)) e (fun x => PowerSeries.mk (g x)) hu h2O
      RankOne Acyclic hpat hrank hacyc hpole dK hK cE tK hm hh
  exact ⟨C, 0 + 4 * B.hSmith, fun x j => by rw [hCu], hle, hdec, hsum, hpl M, hbase⟩

/-- **The genuine `𝒪` instantiates the generic inputs** (PROVED; lane RC7's `OO`, `genuinePole`,
`genuineLaurent`, `two_pow_ne_zero_OO`). -/
theorem clearingInputsGeneric_of_inputs {ℓ : ℕ} (D : RCData ℓ) (h : ClearingInputs D) :
    ClearingInputsGeneric D := by
  obtain ⟨hH, dK, hK, cE, tK, hM⟩ := h
  refine ⟨hH, dK, hK, cE, tK, fun Co Ce F hF => ?_⟩
  exact ⟨OO, inferInstance, inferInstance, inferInstance, genuinePole, genuineLaurent,
    by simpa using Determinant.two_pow_ne_zero_OO 1, hM Co Ce F hF⟩

/-- **`RCSteps.clearing`, display (5.9), from the remaining inputs** (Proposition
`ex:limits-fixed-field-clearing`, tex 5487–5645; PROVED from `ClearingInputs` through lane RC7's
`clearing_nodes` over the genuine `𝒪`). -/
theorem clearingTarget_of_inputs {ℓ : ℕ} (D : RCData ℓ) (h : ClearingInputs D) :
    ClearingTarget D :=
  clearingTarget_of_generic D (clearingInputsGeneric_of_inputs D h)

/-- **`RCSteps.clearing` from `RCSteps.height_one` and the model inputs** (PROVED; the form in
which the wiring uses it: the height-one input is the field `height_one`). -/
theorem clearingTarget_of_model {ℓ : ℕ} (D : RCData ℓ) (h1 : HeightOneTarget D)
    (h2 : ClearingModel D) : ClearingTarget D :=
  clearingTarget_of_inputs D ⟨h1, h2⟩

/-! ## The coordinate identity does not depend on the representation of `ũ_x` -/

/-- **`ũ_x ∈ Frac 𝒪` is well defined** (PROVED): two representations `u = g/2^e = g'/2^{e'}`
(`g, g' ∈ Λ`) of the same `u ∈ ℚ₂[[t]]` give the same element `uK e g = uK e' g'` of the fraction
field of any domain `O ⊇ Λ` with `2 ≠ 0`. -/
theorem uK_eq_of_coeff_eq {O : Type} [CommRing O] [IsDomain O] [Algebra Lam O]
    (h2 : (2 : O) ≠ 0) {u : PowerSeries ℚ_[2]} {e e' : ℕ} {g g' : Lam}
    (hg : ∀ j, PowerSeries.coeff j u = ((PowerSeries.coeff j g : ℤ_[2]) : ℚ_[2]) / 2 ^ e)
    (hg' : ∀ j, PowerSeries.coeff j u = ((PowerSeries.coeff j g' : ℤ_[2]) : ℚ_[2]) / 2 ^ e') :
    (uK e g : FractionRing O) = uK e' g' := by
  -- `2^{e'} g = 2^e g'` in `Λ`
  have hΛ : PowerSeries.C ((2 : ℤ_[2]) ^ e') * g = PowerSeries.C ((2 : ℤ_[2]) ^ e) * g' := by
    ext j
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    have h1 := (hg j).symm.trans (hg' j)
    rw [div_eq_div_iff (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)] at h1
    have h1' : (((2 : ℤ_[2]) ^ e' * PowerSeries.coeff j g : ℤ_[2]) : ℚ_[2]) =
        (((2 : ℤ_[2]) ^ e * PowerSeries.coeff j g' : ℤ_[2]) : ℚ_[2]) := by
      have h2c : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := map_ofNat PadicInt.Coe.ringHom 2
      push_cast
      rw [h2c]
      linear_combination h1
    exact_mod_cast h1'
  have h2K : (2 : FractionRing O) ≠ 0 := by
    intro h
    apply h2
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_ofNat, h, map_zero]
  have hO : algebraMap O (FractionRing O) (algebraMap Lam O g) * 2 ^ e' =
      algebraMap O (FractionRing O) (algebraMap Lam O g') * 2 ^ e := by
    have h' := congrArg (fun y => algebraMap O (FractionRing O) (algebraMap Lam O y)) hΛ
    simp only [map_mul, map_pow, map_ofNat] at h'
    linear_combination h'
  show algebraMap O (FractionRing O) (algebraMap Lam O g) / 2 ^ e =
    algebraMap O (FractionRing O) (algebraMap Lam O g') / 2 ^ e'
  rw [div_eq_div_iff (pow_ne_zero _ h2K) (pow_ne_zero _ h2K)]
  exact hO

/-- The coordinate identity transfers between representations of the same coordinates (PROVED). -/
theorem clearingCoordIdentity_congr {O : Type} [CommRing O] [IsDomain O] [Algebra Lam O]
    (h2 : (2 : O) ≠ 0) {b : ℕ} {B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O}
    {sd : ScalarData B} {κ ε η : MonoidAlgebra O (SignGroup b)} {a : ℕ}
    {RankOne Acyclic : Addr b → Prop} (U : Addr b → PowerSeries ℚ_[2])
    {e e' : Addr b → ℕ} {g g' : Addr b → Lam}
    (hu : ∀ x j, PowerSeries.coeff j (U x) =
      ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x)
    (hu' : ∀ x j, PowerSeries.coeff j (U x) =
      ((PowerSeries.coeff j (g' x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e' x)
    (h : ClearingCoordIdentity B sd κ ε η a e g RankOne Acyclic) :
    ClearingCoordIdentity B sd κ ε η a e' g' RankOne Acyclic := by
  have hx : ∀ x, (uK (e x) (g x) : FractionRing O) = uK (e' x) (g' x) :=
    fun x => uK_eq_of_coeff_eq h2 (hu x) (hu' x)
  obtain ⟨h1, h3⟩ := h
  refine ⟨fun x hΔ hR => ?_, fun x hΔ hA => ?_⟩
  · rw [← hx x]
    exact h1 x hΔ hR
  · rw [← hx x]
    exact h3 x hΔ hA

/-- **The `∀`-representation form of E1–E2 is RC7's form** (PROVED): given one representation
`ũ = g₀/2^{e₀}` of the coordinates of `F`, the coordinate identity for every representation is
equivalent to RC7's hypotheses `hrank`, `hacyc` for that one. -/
theorem forall_clearingCoordIdentity_iff {O : Type} [CommRing O] [IsDomain O] [Algebra Lam O]
    (h2 : (2 : O) ≠ 0) {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (B : SmithBlocks (MonoidAlgebra O (SignGroup F.b)) O) (sd : ScalarData B)
    (κ ε η : MonoidAlgebra O (SignGroup F.b)) (a : ℕ) (RankOne Acyclic : Addr F.b → Prop)
    {e₀ : Addr F.b → ℕ} {g₀ : Addr F.b → Lam} (h₀ : UTildeRep D F e₀ g₀) :
    (∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g →
        ClearingCoordIdentity B sd κ ε η a e g RankOne Acyclic) ↔
      ClearingCoordIdentity B sd κ ε η a e₀ g₀ RankOne Acyclic :=
  ⟨fun h => h e₀ g₀ h₀, fun h _ _ hu => clearingCoordIdentity_congr h2 (D.uTilde F) h₀ hu h⟩

/-! ## The paired functional supplies the `μ`-coordinates of `ScalarData` (exponent `a = 0`) -/

section PairedFunctionalBridge

open CategoryTheory Limits

/-- **The unit premise of the tame local models over `𝒪[G]`, from lane RC7's augmentation
criterion** (PROVED; tex 5404–5414): for local models on free modules `𝒪[G]^r` given by matrices,
the premise `(A, D units) ∨ (C a unit)` of batch 3's `PairedFunctionalIntegral` follows from the
same condition on the augmented determinants (`matrix_isUnit_of_isUnit_aug`, with
`isUnit_one_add_two_mul_OO` and `signGroup_mul_self`). -/
theorem tame_unit_of_aug {b r : ℕ}
    (A Cm Dm : Matrix (Fin r) (Fin r) (MonoidAlgebra OO (SignGroup b)))
    (h : (IsUnit (A.map aug).det ∧ IsUnit (Dm.map aug).det) ∨ IsUnit (Cm.map aug).det) :
    (IsUnit (Matrix.toLinAlgEquiv' A) ∧ IsUnit (Matrix.toLinAlgEquiv' Dm)) ∨
      IsUnit (Matrix.toLinAlgEquiv' Cm) := by
  have key : ∀ X : Matrix (Fin r) (Fin r) (MonoidAlgebra OO (SignGroup b)),
      IsUnit (X.map aug).det → IsUnit (Matrix.toLinAlgEquiv' X) := fun X hX =>
    (Determinant.matrix_isUnit_of_isUnit_aug Determinant.isUnit_one_add_two_mul_OO
      Determinant.signGroup_mul_self X hX).map _
  rcases h with ⟨hA, hD⟩ | hC
  · exact Or.inl ⟨key A hA, key Dm hD⟩
  · exact Or.inr (key Cm hC)

/-- **RC7's `ScalarData` with the `μ`-coordinates of the integral closed paired functional**
(PROVED from batch 3's `exists_closed_pairedFunctional` (from `pairedFunctionalIntegral_proof`)
and `scalarDataMuIntegral_proof`, at the exponent `a = 0`, tex 3850–3869, 5513–5516, 5577–5584).
Over `S = 𝒪[G]`, under the hypotheses of `PairedFunctionalIntegral` (whose cone hypothesis,
tex 3842–3846, remains batch 3 PairedFunctional's own input), with tame local models on free
modules whose unit premise is checked on augmentations (`tame_unit_of_aug`): for any `H₂`, `E₂`
vectors `eH`, `eE` of `C_U^2` and any other coordinates, there is `ScalarData` whose `μ_H, μ_E`
are the values of the closed functional `λ_z = PD(−, j⁻¹ c(z))` (integral over `S`). This is the
scalar data entering `ClearingCoordIdentity` with `a = 0`. -/
theorem scalarData_of_pairedFunctional {b : ℕ} (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO)
    (CU C' C Z : CochainComplex (ModuleCat.{0} (MonoidAlgebra OO (SignGroup b))) ℤ)
    (j : C' ⟶ C) (c : Z ⟶ C) (z : Z.X 1)
    (pd1 : CU.X 1 →ₗ[MonoidAlgebra OO (SignGroup b)] C'.X 2 →ₗ[MonoidAlgebra OO (SignGroup b)]
      MonoidAlgebra OO (SignGroup b))
    (pd2 : CU.X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] C'.X 1 →ₗ[MonoidAlgebra OO (SignGroup b)]
      MonoidAlgebra OO (SignGroup b))
    (pd3 : CU.X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] C'.X 0 →ₗ[MonoidAlgebra OO (SignGroup b)]
      MonoidAlgebra OO (SignGroup b))
    (ε ε' : MonoidAlgebra OO (SignGroup b)) (ι : Type) [Fintype ι] (r : ι → ℕ)
    (Am Cm Dm : ∀ v, Matrix (Fin (r v)) (Fin (r v)) (MonoidAlgebra OO (SignGroup b)))
    (hDC : ∀ v, Matrix.toLinAlgEquiv' (Dm v) * Matrix.toLinAlgEquiv' (Cm v) =
      Matrix.toLinAlgEquiv' (Cm v) * Matrix.toLinAlgEquiv' (Am v))
    (haug : ∀ v, (IsUnit ((Am v).map aug).det ∧ IsUnit ((Dm v).map aug).det) ∨
      IsUnit ((Cm v).map aug).det)
    (n : ι → ℤ)
    (hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (PairedFunctional.tameComplex (Matrix.toLinAlgEquiv' (Am v))
        (Matrix.toLinAlgEquiv' (Cm v)) (Matrix.toLinAlgEquiv' (Dm v)) (hDC v))⟦n v⟧)))
    (hz : (Z.d 1 2).hom z = 0)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (hL2 : ∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y)
    (zH : MonoidAlgebra OO (SignGroup b)) (zB Cr : Fin (B.m 0) → MonoidAlgebra OO (SignGroup b))
    (BH : Fin (B.m 2) → MonoidAlgebra OO (SignGroup b)) (eH : CU.X 2) (eE : Fin (B.m 2) → CU.X 2) :
    ∃ (e : HomotopyEquiv C' C) (sd : ScalarData B), e.hom = j ∧
      sd.zH = zH ∧ sd.zB = zB ∧ sd.C = Cr ∧ sd.BH = BH ∧
      sd.μH = PairedFunctional.pairedFunctional pd2 e.inv ((c.f 1).hom z) eH ∧
      (∀ i, sd.μE i = PairedFunctional.pairedFunctional pd2 e.inv ((c.f 1).hom z) (eE i)) ∧
      ∀ w : CU.X 1,
        PairedFunctional.pairedFunctional pd2 e.inv ((c.f 1).hom z) ((CU.d 1 2).hom w) = 0 := by
  obtain ⟨e, he, hcl⟩ := PairedFunctional.exists_closed_pairedFunctional
    (MonoidAlgebra OO (SignGroup b)) CU C' C Z j c z pd1 pd2 pd3 ε ε' ι
    (fun v => Fin (r v) → MonoidAlgebra OO (SignGroup b))
    (fun v => Matrix.toLinAlgEquiv' (Am v)) (fun v => Matrix.toLinAlgEquiv' (Cm v))
    (fun v => Matrix.toLinAlgEquiv' (Dm v)) hDC n
    (fun v => tame_unit_of_aug (Am v) (Cm v) (Dm v) (haug v)) hcone hz hL1 hL2
  obtain ⟨μH, μE, hμH, hμE, -⟩ := PairedFunctional.scalarDataMuIntegral_proof
    (MonoidAlgebra OO (SignGroup b)) CU
    (PairedFunctional.pairedFunctional pd2 e.inv ((c.f 1).hom z)) hcl 0 (B.m 2) eH eE
  refine ⟨e, ⟨zH, zB, Cr, μH, μE, BH⟩, he, rfl, rfl, rfl, rfl, ?_, fun i => ?_, hcl⟩
  · simpa using hμH
  · simpa using hμE i

end PairedFunctionalBridge

/-! ## Non-vacuity -/

/-- Degenerate central Smith data over the genuine `𝒪[𝔽₂^b]`: one unit disk `[ℤ₂ --1--> ℤ₂]` in
each of the degrees `0, 1, 2` (`A_i = (1)`, so `Δ = 1`, `m = 3`, `h₁ = 0`). -/
def unitBlocks (b : ℕ) : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO where
  n := 3
  m _ := 1
  A _ := 1
  A0 _ := 1
  s _ _ := 1
  s_ne _ _ := one_ne_zero
  central _ := by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.diagonal_one.symm

/-- The degenerate scalar data: `z_H = μ_H = 1`, all other coordinates zero. -/
def unitScalars (b : ℕ) : ScalarData (unitBlocks b) where
  zH := 1
  zB := 0
  C := 0
  μH := 1
  μE := 0
  BH := 0

theorem unitBlocks_δ (b i : ℕ) : (unitBlocks b).δ i = 1 :=
  Matrix.det_one

theorem unitBlocks_mTot (b : ℕ) : (unitBlocks b).mTot = 3 := rfl

theorem unitBlocks_hSmith (b : ℕ) : (unitBlocks b).hSmith = 0 := by
  simp [SmithBlocks.hSmith, unitBlocks]

/-- `ũ = 1` is represented by `g = 1`, `e = 0` (PROVED). -/
theorem uTildeRep_one {ℓ : ℕ} (D : RCData ℓ) (F : Family) (h1 : ∀ x, D.uTilde F x = 1) :
    UTildeRep D F (fun _ => 0) (fun _ => 1) := by
  intro x j
  rw [h1 x, PowerSeries.coeff_one, PowerSeries.coeff_one]
  split_ifs <;> simp

/-- **Non-vacuity of `ClearingInputs`** (PROVED): every datum whose corrected coordinates are
`ũ_x = 1` satisfies all the inputs, with unit Smith disks (`Δ = 1`, `c = 0`), `η = κ = ε = 1`,
`z_H = μ_H = 1`, the rank-one pattern everywhere, and `d_K = h_K = c_E = t_K = 0`. -/
theorem clearingInputs_of_uTilde_eq_one {ℓ : ℕ} (D : RCData ℓ)
    (h1 : ∀ (F : Family) (x : Addr F.b), D.uTilde F x = 1) : ClearingInputs D := by
  refine ⟨fun Co Ce F _ x => ⟨0, fun n => PowerSeries.coeff n (1 : Lam), fun n => ?_⟩,
    0, 0, 0, 0, fun Co Ce F _ => ?_⟩
  · exact uTildeRep_one D F (h1 F) x n
  · refine ⟨unitBlocks F.b, unitScalars F.b, 1, 1, 1, fun _ => True, fun _ => False,
      ⟨show (2 : ℕ) < 3 by norm_num, fun i => ?_⟩, fun _ => Or.inl trivial, fun e g hu => ?_, ?_,
      ?_, ?_⟩
    · show (1 : Matrix (Fin 1) (Fin 1) (MonoidAlgebra OO (SignGroup F.b))).map aug =
        (1 : Matrix (Fin 1) (Fin 1) Lam).map (algebraMap Lam OO)
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
    · refine clearingCoordIdentity_congr (by simpa using Determinant.two_pow_ne_zero_OO 1)
        (D.uTilde F) (uTildeRep_one D F (h1 F)) hu ?_
      refine ⟨fun x _ _ => ?_, fun x _ hA => hA.elim⟩
      have hδ : ∀ i, evK (sgnChar x) ((unitBlocks F.b).δ i) = (1 : FractionRing OO) := by
        intro i
        rw [unitBlocks_δ, map_one]
      simp only [uK, cleanT, ScalarData.αK, ScalarData.βK, unitScalars, hδ, map_one,
        pow_zero, inv_one, mul_one, one_zpow, Finset.prod_const_one, Pi.zero_apply,
        map_zero, zero_dotProduct', sub_zero, div_one]
    · intro x M i j k
      show ((1 : Matrix (Fin 1) (Fin 1) (MonoidAlgebra OO (SignGroup F.b))).map
        (Determinant.signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M)
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact genuinePole.poleLE_le_poleModLE M _
        (genuinePole.poleLE_mono (Nat.zero_le _) (genuinePole.one_mem_poleLE_entries j k))
    · rw [unitBlocks_mTot]; norm_num
    · rw [unitBlocks_hSmith]

/-- **Lane RC0's toy data satisfy `ClearingInputs`** (PROVED; `toyData` has `ũ_x = 1`). -/
theorem clearingInputs_toyData (ℓ : ℕ) (a : ℤ) : ClearingInputs (toyData ℓ a) :=
  clearingInputs_of_uTilde_eq_one _ fun _ _ => rfl

/-- `RCSteps.clearing` for lane RC0's toy data (PROVED, through `clearingTarget_of_inputs`). -/
theorem clearingTarget_toyData (ℓ : ℕ) (a : ℤ) : ClearingTarget (toyData ℓ a) :=
  clearingTarget_of_inputs _ (clearingInputs_toyData ℓ a)

end ZInQ.Manuscript.RC.Wiring
