import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudget
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudgetRank
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LimitDeterminant
import ZInQKernel.Contrib.OneProof.RC.Determinant.Budget
import ZInQKernel.Contrib.OneProof.RC.Rings.Wiring
import ZInQKernel.Contrib.OneProof.RC.Moving.Trace

/-!
# Lane RC22 (glue sweep), share `Unif`: lane RC7's budget and clearing without their count inputs

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:limits-fixed-field-budget` (tex 5207–5484) and
Proposition `ex:limits-fixed-field-clearing` (tex 5486–5664).

Lane RC7 (`RC/Determinant/`) takes the cohomological counts behind the budget (5.7) as hypotheses
(the "RankCounts" inputs), and its (5.9) theorems take the budget itself as the two hypotheses
`hm : B.mTot ≤ dK + 5`, `hh : B.hSmith ≤ hK + 2 * cE + 2 * tK`. Several of these are now theorems of
the shared top layer (`ZInQ.Contrib.CloudB3RC53.RankCounts`), for the central Smith complex of
RC7's `SmithBlocks` data. This file states RC7's theorems with those hypotheses discharged. Every
theorem here is a bridge: kind `PROVED` from the hypotheses that remain, which are listed in each
docstring.

* `budget_57_centralSmith`: RC7's `budget_57` with `hmodel`, `hsmith`, `[Subsingleton H0D]` and
  `htors` discharged (`RankCounts.sum_finrank_centralRed`, `RankCounts.subsingleton_centralH_zero`,
  `RankCounts.sum_length_torsion_centralH`, `RankCounts.sum_length_coker`, the components of
  `RankCounts.rc7Budget57Inputs_proof`); `budget_57_centralSmithRank`: the same for RC7's Smith data
  as it stands (unit disks allowed), discharging `hsmith`, `[Subsingleton H0D]`, `htors` by the
  components of `RankCounts.rc7Budget57InputsRank_proof`, with `hmodel` (minimality) remaining.
* `moving_bound_of_not_dvd`: lane RC4's integer form of the moving-character bound gives RC7's
  `hne`, `hcE` (`v₂(r + 1 − a) ≤ c_E`).
* `singular_complexes_total_length_le_of_limit`, `limit_J_length_le_of_moving_character`: RC7's
  `singular_complexes_total_length_le` for the limit matrices of (5.7c), with its determinant
  hypotheses discharged by `RankCounts.singularDiskLimit_proof` (and, for the moving Frobenius,
  by lane RC4's bound).
* `clearingNodes_lambdaHalf_smithBudget`: (5.9) for the shared top layer (RC7's
  `clearing_nodes_genuine` in lane RC20's form `Rings.clearing_nodes_of_lambdaHalf`, where the
  corrected coordinates are genuine elements of `Λ[1/2]`) with `hm`, `hh` discharged by
  `RankCounts.fixedFieldBudgetSmith_proof`; `clearingNodes_lambdaHalf_smithBudget_limit` also
  discharges that node's input `hJ` (`length J_r ≤ 2 c_E`) by the limit argument of tex 5336–5343.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Unif

open ZInQ.Manuscript.RC.Determinant ZInQ.Contrib.CloudB3RC53

/-! ## The budget (5.7) for the central Smith complex -/

set_option maxHeartbeats 1000000 in
/-- **RC7's budget (5.7) with its RankCounts inputs discharged** (tex 5251–5392, consumer step
tex 5355–5387). Lane RC7's `budget_57` (`RC/Determinant/Budget.lean`) proves
`m = B.mTot ≤ d_K + 5` and `h₁ = B.hSmith ≤ h_K + 2 c_E + 2 t_K` from, among others, four inputs
linking the Smith data `B` to the cohomology `HD n = H^n(D_c ⊗ 𝔽₂)`, `H^n D = H^n(D_c)`:
`hmodel`, `hsmith`, `[Subsingleton H0D]` and `htors`. Here `D_c` is the central Smith complex
built from `B` with free generators `fr` (`RankCounts.centralRed`, `RankCounts.centralH`; in the
bases of `SmithBlocks` the complex `D_c` is this explicit complex, tex 5522–5527), and the four
inputs are discharged by the shared top layer's theorems `RankCounts.sum_finrank_centralRed`
(`hmodel`, `hsmith` with `rank_total = 2 + 2 m`), `RankCounts.subsingleton_centralH_zero`
(`H⁰(D_c) = 0`), `RankCounts.sum_length_torsion_centralH` and `RankCounts.sum_length_coker`
(`htors`); together these are `RankCounts.rc7Budget57Inputs_proof`.

Kind: PROVED, from the remaining hypotheses of `budget_57`: the shape of the central data
(`B.n ≤ 3`, central Smith entries in `(2)` (`hpos`, minimality at `(2, t)`, tex 5357–5359), free
generators `fr = (0, 1, 1, 0)`, tex 5379–5380), the reduced triangle (5.7c) (`f`, `g`, `hfg`), (5.7a)
(`h57a`), the two singular disks mod two (`hQ`), (5.7d) (`e`, `i`, `j`, `δ`, `l`, `h57d`), `t_K`,
(5.7b), `h_K` (`ht₁`, `ht₃`, `hh`), and the moving Frobenius data with `J_r` (`Φ₁`, `Φ₂`, `a₁`, `a₂`,
`r`, …, `eJ`). Consumer: `ZInQ.Manuscript.RC.Determinant.budget_57`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.rc7Budget57Inputs_proof` (by its components). -/
theorem budget_57_centralSmith
    {HC HQ : Fin 4 → Type*} [∀ n, AddCommGroup (HC n)] [∀ n, Module (ZMod 2) (HC n)]
    [∀ n, AddCommGroup (HQ n)] [∀ n, Module (ZMod 2) (HQ n)]
    [∀ n, FiniteDimensional (ZMod 2) (HC n)] [∀ n, FiniteDimensional (ZMod 2) (HQ n)]
    {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ)
    (hn : B.n ≤ 3) (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    (hfr0 : fr 0 = 0) (hfr1 : fr 1 = 1) (hfr2 : fr 2 = 1) (hfr3 : fr 3 = 0)
    (f : ∀ n : Fin 4, HC n →ₗ[ZMod 2] RankCounts.centralRed B fr n)
    (g : ∀ n : Fin 4, RankCounts.centralRed B fr n →ₗ[ZMod 2] HQ n)
    (hfg : ∀ n, Function.Exact (f n) (g n))
    {dK : ℕ} (h57a : ∀ n, Module.finrank (ZMod 2) (HC n) = (![2, dK, dK, 2] : Fin 4 → ℕ) n)
    (hQ : ∑ n, Module.finrank (ZMod 2) (HQ n) ≤ 8)
    {H1C H2C J H3C : Type*} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (Φ₁ Φ₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a₁ a₂ r : ℤ_[2]) (hr : IsUnit r)
    (htr₁ : Φ₁.trace = a₁) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = a₂) (hdet₂ : Φ₂.det = r)
    (hne₁ : r + 1 - a₁ ≠ 0) (hne₂ : r + 1 - a₂ ≠ 0)
    (hcE₁ : (r + 1 - a₁).valuation ≤ cE) (hcE₂ : (r + 1 - a₂).valuation ≤ cE)
    (eJ : J ≃ₗ[ℤ_[2]]
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₁ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) ×
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₂ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin)) :
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK := by
  have : Subsingleton (RankCounts.centralH B fr 0) :=
    RankCounts.subsingleton_centralH_zero B fr hfr0
  -- `hmodel` with `rankTotal = 2 + 2 * B.mTot` (so `hsmith` is `rfl`)
  have hmodel : 2 + 2 * B.mTot ≤
      ∑ n : Fin 4, Module.finrank (ZMod 2) (RankCounts.centralRed B fr n) := by
    rw [RankCounts.sum_finrank_centralRed B fr hn hpos]
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 4) : ℕ) = 3 from rfl, hfr0, hfr1, hfr2, hfr3]
    omega
  -- `htors`: the torsion of `H^*(D_c)` is the cokernel of the central Smith blocks
  have htors : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 0)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 1)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 2)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 3)) =
      ∑ i ∈ Finset.range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
        LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin) := by
    have hS := RankCounts.sum_length_torsion_centralH B fr hn
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two] at hS
    exact hS.trans (RankCounts.sum_length_coker B).symm
  exact budget_57 (k := ZMod 2) (HD := fun n : Fin 4 => RankCounts.centralRed B fr (n : ℕ))
    f g hfg h57a hQ B hmodel rfl (H0D := RankCounts.centralH B fr 0)
    (H1D := RankCounts.centralH B fr 1) (H2D := RankCounts.centralH B fr 2)
    (H3D := RankCounts.centralH B fr 3) e i j δ l h57d ht₁ ht₃ hh Φ₁ Φ₂ a₁ a₂ r hr
    htr₁ hdet₁ htr₂ hdet₂ hne₁ hne₂ hcE₁ hcE₂ eJ htors

set_option maxHeartbeats 1000000 in
/-- **RC7's budget (5.7) for its Smith data as they stand (unit disks allowed)** (tex 5251–5392,
consumer step tex 5375–5387). Lane RC7's `budget_57` with three of its RankCounts inputs discharged
for the central Smith complex of `B` with free generators `fr = (0, 1, 1, 0)` and `rank_total` its
total rank (every disk counted, including unit disks `e = 0`): `hsmith : rank_total = 2 + 2 m`
(`RankCounts.sum_finrank_centralCx`), `[Subsingleton H0D]` (`RankCounts.subsingleton_centralH_zero`)
and `htors` (`RankCounts.sum_length_torsion_centralH_amp`, `RankCounts.sum_length_coker`); together
these are `RankCounts.rc7Budget57InputsRank_proof`. The degree range `hamp` replaces `B.n ≤ 3` and no
positivity of the central entries is assumed. RC7's `hmodel` (the total rank of the model is at most
the total dimension of `H^*(D_c ⊗ 𝔽₂)`, minimality, tex 5357–5359) remains, for the abstract `HD`.

Kind: PROVED, from `hamp`, the values of `fr`, `hmodel` and RC7's remaining hypotheses of
`budget_57` (`f`, `g`, `hfg`, `h57a`, `hQ`, `e`, `i`, `j`, `δ`, `l`, `h57d`, `ht₁`, `ht₃`, `hh`, the
moving Frobenius data and `eJ`). Consumer: `ZInQ.Manuscript.RC.Determinant.budget_57`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.rc7Budget57InputsRank_proof` (by its components). -/
theorem budget_57_centralSmithRank
    {k : Type*} [Field k] {HC HD HQ : Fin 4 → Type*}
    [∀ n, AddCommGroup (HC n)] [∀ n, Module k (HC n)]
    [∀ n, AddCommGroup (HD n)] [∀ n, Module k (HD n)]
    [∀ n, AddCommGroup (HQ n)] [∀ n, Module k (HQ n)]
    [∀ n, FiniteDimensional k (HC n)] [∀ n, FiniteDimensional k (HQ n)]
    (f : ∀ n, HC n →ₗ[k] HD n) (g : ∀ n, HD n →ₗ[k] HQ n) (hfg : ∀ n, Function.Exact (f n) (g n))
    {dK : ℕ} (h57a : ∀ n, Module.finrank k (HC n) = (![2, dK, dK, 2] : Fin 4 → ℕ) n)
    (hQ : ∑ n, Module.finrank k (HQ n) ≤ 8)
    {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O) (fr : ℕ → ℕ)
    (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0)
    (hfr0 : fr 0 = 0) (hfr1 : fr 1 = 1) (hfr2 : fr 2 = 1) (hfr3 : fr 3 = 0)
    (hmodel : ∑ n : Fin 4, Module.finrank ℤ_[2] (RankCounts.centralCx B fr n) ≤
      ∑ n, Module.finrank k (HD n))
    {H1C H2C J H3C : Type*} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (Φ₁ Φ₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a₁ a₂ r : ℤ_[2]) (hr : IsUnit r)
    (htr₁ : Φ₁.trace = a₁) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = a₂) (hdet₂ : Φ₂.det = r)
    (hne₁ : r + 1 - a₁ ≠ 0) (hne₂ : r + 1 - a₂ ≠ 0)
    (hcE₁ : (r + 1 - a₁).valuation ≤ cE) (hcE₂ : (r + 1 - a₂).valuation ≤ cE)
    (eJ : J ≃ₗ[ℤ_[2]]
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₁ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) ×
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₂ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin)) :
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK := by
  have : Subsingleton (RankCounts.centralH B fr 0) :=
    RankCounts.subsingleton_centralH_zero B fr hfr0
  -- `hsmith` with `rankTotal` the total rank of the central Smith complex
  have hsmith : ∑ n : Fin 4, Module.finrank ℤ_[2] (RankCounts.centralCx B fr n) =
      2 + 2 * B.mTot := by
    rw [RankCounts.sum_finrank_centralCx B fr hamp]
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 4) : ℕ) = 3 from rfl, hfr0, hfr1, hfr2, hfr3]
  -- `htors`: the torsion of `H^*(D_c)` is the cokernel of the central Smith blocks
  have htors : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 0)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 1)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 2)) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (RankCounts.centralH B fr 3)) =
      ∑ i ∈ Finset.range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
        LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin) := by
    have hS := RankCounts.sum_length_torsion_centralH_amp B fr hamp
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two] at hS
    exact hS.trans (RankCounts.sum_length_coker B).symm
  exact budget_57 f g hfg h57a hQ B hmodel hsmith (H0D := RankCounts.centralH B fr 0)
    (H1D := RankCounts.centralH B fr 1) (H2D := RankCounts.centralH B fr 2)
    (H3D := RankCounts.centralH B fr 3) e i j δ l h57d ht₁ ht₃ hh Φ₁ Φ₂ a₁ a₂ r hr
    htr₁ hdet₁ htr₂ hdet₂ hne₁ hne₂ hcE₁ hcE₂ eJ htors

/-! ## The moving singular disks and their limit (tex 5315–5352) -/

/-- **Lane RC4's moving-character bound in lane RC7's form** (tex 3686–3693 for the bound; consumer
step tex 5326–5334). Lane RC4's `Moving.moving_character` gives, for the good split moving prime
`r` with Frobenius trace `a_r`, the integer statement `¬ 2^{c_E+1} ∣ 1 − a_r + r`. This gives the
hypotheses `hne : r + 1 − a ≠ 0` and `hcE : v₂(r + 1 − a) ≤ c_E` of RC7's `singular_det_valuation`,
`moving_J_length_le` and `budget_57` (with `a = a_r`, `r` read in `ℤ₂`).
Kind: PROVED (from the integer non-divisibility; the transfer of divisibility from `ℤ` to `ℤ₂` is
lane RC4's `Moving.int_two_pow_dvd_iff`). Consumers: `Determinant.budget_57` (`hne₁`, `hne₂`,
`hcE₁`, `hcE₂`), `Determinant.moving_J_length_le`, `Determinant.singular_det_valuation`; discharger:
the conclusion `¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 1 - M.ap r + r` of `Moving.moving_character`. -/
theorem moving_bound_of_not_dvd (c : ℕ) (ar r : ℤ) (h : ¬ (2 : ℤ) ^ (c + 1) ∣ 1 - ar + r) :
    ((r : ℤ_[2]) + 1 - (ar : ℤ_[2])) ≠ 0 ∧
      ((r : ℤ_[2]) + 1 - (ar : ℤ_[2])).valuation ≤ c := by
  have hcast : ((r : ℤ_[2]) + 1 - (ar : ℤ_[2])) = ((1 - ar + r : ℤ) : ℤ_[2]) := by
    push_cast; ring
  have hnd : ¬ (2 : ℤ_[2]) ^ (c + 1) ∣ ((1 - ar + r : ℤ) : ℤ_[2]) := by
    rw [Moving.int_two_pow_dvd_iff]; exact h
  rw [hcast]
  have hne : ((1 - ar + r : ℤ) : ℤ_[2]) ≠ 0 := by
    intro h0; apply hnd; rw [h0]; exact dvd_zero _
  refine ⟨hne, ?_⟩
  by_contra hlt
  apply hnd
  have hmem := (PadicInt.mem_span_pow_iff_le_valuation _ hne (c + 1)).mpr (by omega)
  exact Ideal.mem_span_singleton.mp (by exact_mod_cast hmem)

/-- **RC7's singular-disk length bound for the limit matrices** (tex 5336–5343, consumer step
tex 5326–5334, 5350–5351). Lane RC7's `singular_complexes_total_length_le` bounds the total
length of the degree-two cokernels of two singular complexes `[ℤ₂² --Y--> ℤ₂²]` by `2c`, given
`det Y ≠ 0` and `v₂ det Y ≤ c`. In (5.7c) the matrices are limits of stage matrices `X`
(`Φ_{r_i} − r_i`), congruent to them modulo `2^{c+1}` ("the property is determined modulo
`2^{c_E+1}`"). The determinant hypotheses on the limit are discharged by
`RankCounts.singularDiskLimit_proof` from the same hypotheses on the stage matrices.
Kind: PROVED, from the congruences `h₁`, `h₂` and the stage bounds `hX₁`, `hX₁c`, `hX₂`, `hX₂c`.
Consumer: `ZInQ.Manuscript.RC.Determinant.singular_complexes_total_length_le`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.singularDiskLimit_proof`. -/
theorem singular_complexes_total_length_le_of_limit (X₁ X₂ Y₁ Y₂ : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (c : ℕ) (h₁ : ∀ i j, X₁ i j - Y₁ i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (c + 1)})
    (h₂ : ∀ i j, X₂ i j - Y₂ i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (c + 1)})
    (hX₁ : X₁.det ≠ 0) (hX₁c : X₁.det.valuation ≤ c)
    (hX₂ : X₂.det ≠ 0) (hX₂c : X₂.det.valuation ≤ c) :
    Module.length ℤ_[2] (((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y₁.mulVecLin) ×
        ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y₂.mulVecLin)) ≤ 2 * c := by
  obtain ⟨hY₁, hY₁c⟩ := RankCounts.singularDiskLimit_proof X₁ Y₁ c h₁ hX₁ hX₁c
  obtain ⟨hY₂, hY₂c⟩ := RankCounts.singularDiskLimit_proof X₂ Y₂ c h₂ hX₂ hX₂c
  exact singular_complexes_total_length_le Y₁ Y₂ hY₁ hY₂ c hY₁c hY₂c

/-- **`length J_r ≤ 2 c_E` in the limit, from the moving-character bound** (tex 5315–5352). At
either place over the good split moving prime `r`, arithmetic Frobenius `Φ` on `T` has trace `a_r`
and determinant `r`, so `det(Φ − r) = r(r + 1 − a_r)` (RC7's `singular_det_valuation`) is nonzero of
valuation at most `c_E` by lane RC4's bound; the limit matrices `Y₁`, `Y₂` of (5.7c) are congruent
to `Φ₁ − r`, `Φ₂ − r` modulo `2^{c_E+1}`, so their cokernels have total length at most `2 c_E`.
Kind: PROVED, from the Frobenius data (`hr`, `htr₁`, `hdet₁`, `htr₂`, `hdet₂`), lane RC4's
integer bound `hmov` and the limit congruences `h₁`, `h₂`. Consumer:
`ZInQ.Manuscript.RC.Determinant.singular_complexes_total_length_le` (equivalently the input `hJ` of
`RankCounts.fixedFieldBudgetSmith_proof`); dischargers: `moving_bound_of_not_dvd` (lane RC4's
`Moving.moving_character`), `Determinant.singular_det_valuation`,
`RankCounts.singularDiskLimit_proof`. -/
theorem limit_J_length_le_of_moving_character (Φ₁ Φ₂ Y₁ Y₂ : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (ar r : ℤ) (hr : IsUnit (r : ℤ_[2]))
    (htr₁ : Φ₁.trace = ar) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = ar) (hdet₂ : Φ₂.det = r)
    (cE : ℕ) (hmov : ¬ (2 : ℤ) ^ (cE + 1) ∣ 1 - ar + r)
    (h₁ : ∀ i j, (Φ₁ - (r : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])) i j - Y₁ i j ∈
      Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (h₂ : ∀ i j, (Φ₂ - (r : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])) i j - Y₂ i j ∈
      Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)}) :
    Module.length ℤ_[2] (((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y₁.mulVecLin) ×
        ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y₂.mulVecLin)) ≤ 2 * cE := by
  obtain ⟨hne, hc⟩ := moving_bound_of_not_dvd cE ar r hmov
  obtain ⟨hX₁, hX₁c⟩ := singular_det_valuation Φ₁ (ar : ℤ_[2]) (r : ℤ_[2]) hr htr₁ hdet₁ cE hne hc
  obtain ⟨hX₂, hX₂c⟩ := singular_det_valuation Φ₂ (ar : ℤ_[2]) (r : ℤ_[2]) hr htr₂ hdet₂ cE hne hc
  exact singular_complexes_total_length_le_of_limit _ _ Y₁ Y₂ cE h₁ h₂ hX₁ hX₁c hX₂ hX₂c

/-! ## (5.9) for the shared top layer, with the budget discharged -/

/-- **Proposition `ex:limits-fixed-field-clearing` (5.9) with the budget (5.7) discharged**
(tex 5486–5664; consumer step tex 5384–5386, 5627–5634). Lane RC20's
`Rings.clearing_nodes_of_lambdaHalf` is lane RC7's `clearing_nodes_genuine` for genuine corrected
coordinates `ũ_x ∈ Λ[1/2]` (RC7's input `hu` already discharged there); it still takes the budget
as `hm : B.mTot ≤ dK + 5` and `hh : B.hSmith ≤ hK + 2 * cE + 2 * tK`. Both are discharged here by
the shared top layer's `RankCounts.fixedFieldBudgetSmith_proof`, which proves them for the central
Smith complex of `B` from the (5.7) exact sequences.

Kind: PROVED, from: RC7's ELLIOT inputs `hrank`, `hacyc`, `hpat` (determinant-coordinate identity
and generic patterns, tex 5586–5617) and `haug`, `hpole` (the model of `D`, tex 5394–5427,
5517–5538); and exactly the inputs of `RankCounts.fixedFieldBudgetSmith_proof`: `hn3 : B.n ≤ 3`,
`hpos` (central entries in `(2)`), free generators `fr`, `fm`, `gm`, `hfg` (reduced (5.7c)),
`h57a` ((5.7a)), `hQ` (singular disks mod two), `e`, `i`, `j`, `δ`, `l`, `h57d` ((5.7d)), `ht₁`, `ht₃`,
`hh` (`t_K`, (5.7b), `h_K`), `hJ` (`length J_r ≤ 2 c_E`) and the free ranks `hr₁`, `hr₂` of
`H¹(C_K)`, `H²(C_K)` (tex 5303–5311). Consumer: `ZInQ.Manuscript.RC.Rings.clearing_nodes_of_lambdaHalf`
(hence RC7's `clearing_nodes_genuine`); discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.fixedFieldBudgetSmith_proof`. -/
theorem clearingNodes_lambdaHalf_smithBudget {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (ũ : Addr b → Uniform.LambdaHalf)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      Rings.halfToFracO (ũ x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ Rings.halfToFracO (ũ x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    -- the inputs of `RankCounts.fixedFieldBudgetSmith_proof`
    (fr : ℕ → ℕ) (hn3 : B.n ≤ 3) (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    {HC HQ : Fin 4 → Type} [∀ k, AddCommGroup (HC k)] [∀ k, Module (ZMod 2) (HC k)]
    [∀ k, AddCommGroup (HQ k)] [∀ k, Module (ZMod 2) (HQ k)]
    [∀ k, FiniteDimensional (ZMod 2) (HC k)] [∀ k, FiniteDimensional (ZMod 2) (HQ k)]
    (fm : ∀ k : Fin 4, HC k →ₗ[ZMod 2] RankCounts.centralRed B fr k)
    (gm : ∀ k : Fin 4, RankCounts.centralRed B fr k →ₗ[ZMod 2] HQ k)
    (hfg : ∀ k, Function.Exact (fm k) (gm k))
    {dK : ℕ} (h57a : ∀ k, Module.finrank (ZMod 2) (HC k) = (![2, dK, dK, 2] : Fin 4 → ℕ) k)
    (hQ : ∑ k, Module.finrank (ZMod 2) (HQ k) ≤ 8)
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    ∃ C : CoordData b, C.u = (fun x j => Rings.coeffHalf (ũ x) j) ∧
      ClearingIdentity C ∧
      (∀ M : ℕ, PoleBound C (16 * (dK + 5) * M) M) ∧
      BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
      ∀ x, C.u x 0 = Uniform.centralSpecialization (ũ x) := by
  obtain ⟨hm, hbud⟩ := RankCounts.fixedFieldBudgetSmith_proof _ _ B fr hn3 hpos HC HQ fm gm hfg
    dK h57a hQ H1C H2C J H3C e i j δ l h57d tK hK cE ht₁ ht₃ hh hJ hr₁ hr₂
  exact Rings.clearing_nodes_of_lambdaHalf B hn haug sd κ ε η a ũ RankOne Acyclic hpat hrank
    hacyc hpole dK hK cE tK hm hbud

/-- **(5.9) with the budget and `length J_r ≤ 2 c_E` discharged** (tex 5486–5664; consumer steps
tex 5326–5352, 5384–5386). As `clearingNodes_lambdaHalf_smithBudget`, with the input `hJ` of
`RankCounts.fixedFieldBudgetSmith_proof` replaced by its source in the text: `J_r ≅ coker Y₁ ×
coker Y₂` for the limit singular disks (`eJ`, tex 5348–5351), whose matrices are congruent modulo
`2^{c_E+1}` (`hlim₁`, `hlim₂`, tex 5336–5343) to `Φ_k − r` for arithmetic Frobenius `Φ_k` at the two
places over the good split moving prime `r` (trace `a_r`, determinant `r`, tex 5323–5331), with lane
RC4's bound `hmov : ¬ 2^{c_E+1} ∣ 1 − a_r + r` (`Moving.moving_character`).
Kind: PROVED, from the hypotheses listed for `clearingNodes_lambdaHalf_smithBudget` except `hJ`, and
`Φ₁`, `Φ₂`, `Y₁`, `Y₂`, `ar`, `r`, `hr`, `htr₁`, `hdet₁`, `htr₂`, `hdet₂`, `hmov`, `hlim₁`, `hlim₂`, `eJ`.
Consumer: `ZInQ.Manuscript.RC.Rings.clearing_nodes_of_lambdaHalf`; dischargers:
`RankCounts.fixedFieldBudgetSmith_proof`, `limit_J_length_le_of_moving_character`. -/
theorem clearingNodes_lambdaHalf_smithBudget_limit {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (ũ : Addr b → Uniform.LambdaHalf)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      Rings.halfToFracO (ũ x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ Rings.halfToFracO (ũ x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    (fr : ℕ → ℕ) (hn3 : B.n ≤ 3) (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    {HC HQ : Fin 4 → Type} [∀ k, AddCommGroup (HC k)] [∀ k, Module (ZMod 2) (HC k)]
    [∀ k, AddCommGroup (HQ k)] [∀ k, Module (ZMod 2) (HQ k)]
    [∀ k, FiniteDimensional (ZMod 2) (HC k)] [∀ k, FiniteDimensional (ZMod 2) (HQ k)]
    (fm : ∀ k : Fin 4, HC k →ₗ[ZMod 2] RankCounts.centralRed B fr k)
    (gm : ∀ k : Fin 4, RankCounts.centralRed B fr k →ₗ[ZMod 2] HQ k)
    (hfg : ∀ k, Function.Exact (fm k) (gm k))
    {dK : ℕ} (h57a : ∀ k, Module.finrank (ZMod 2) (HC k) = (![2, dK, dK, 2] : Fin 4 → ℕ) k)
    (hQ : ∑ k, Module.finrank (ZMod 2) (HQ k) ≤ 8)
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1)
    -- the moving singular disks and their limit, replacing `hJ`
    (Φ₁ Φ₂ Y₁ Y₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (ar r : ℤ) (hr : IsUnit (r : ℤ_[2]))
    (htr₁ : Φ₁.trace = ar) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = ar) (hdet₂ : Φ₂.det = r)
    (hmov : ¬ (2 : ℤ) ^ (cE + 1) ∣ 1 - ar + r)
    (hlim₁ : ∀ i j, (Φ₁ - (r : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])) i j - Y₁ i j ∈
      Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hlim₂ : ∀ i j, (Φ₂ - (r : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])) i j - Y₂ i j ∈
      Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (eJ : J ≃ₗ[ℤ_[2]] ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y₁.mulVecLin) ×
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range Y₂.mulVecLin)) :
    ∃ C : CoordData b, C.u = (fun x j => Rings.coeffHalf (ũ x) j) ∧
      ClearingIdentity C ∧
      (∀ M : ℕ, PoleBound C (16 * (dK + 5) * M) M) ∧
      BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
      ∀ x, C.u x 0 = Uniform.centralSpecialization (ũ x) := by
  have hJ : Module.length ℤ_[2] J ≤ 2 * (cE : ℕ∞) := by
    rw [eJ.length_eq]
    exact limit_J_length_le_of_moving_character Φ₁ Φ₂ Y₁ Y₂ ar r hr htr₁ hdet₁ htr₂ hdet₂ cE hmov
      hlim₁ hlim₂
  exact clearingNodes_lambdaHalf_smithBudget B hn haug sd κ ε η a ũ RankOne Acyclic hpat hrank
    hacyc hpole fr hn3 hpos fm gm hfg h57a hQ e i j δ l h57d ht₁ ht₃ hh hJ hr₁ hr₂

end ZInQ.Manuscript.RC.GlueSweep.Unif
