import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudgetRank
import ZInQKernel.Contrib.OneProof.RC.Determinant.BudgetLength
import ZInQKernel.Contrib.OneProof.RC.Wiring.Clearing

/-!
# Lane RC22 (glue sweep), share `Unif`: the budget input of the (5.9) wiring, discharged

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:limits-fixed-field-budget`, display (5.7)
(tex 5251–5392), as consumed by Proposition `ex:limits-fixed-field-clearing` (tex 5486–5664).

Lane RC0's wiring of (5.9) (`ZInQ.Manuscript.RC.Wiring`, `RC/Wiring/Clearing.lean`) keeps lane RC7's
budget as the input `Wiring.ClearingBudget B dK hK cE tK`
(`B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK`, a conjunct of `Wiring.ClearingModelOver`,
hence of `Wiring.ClearingInputs`). The shared top layer proves it for the central Smith complex of
`B` in two forms, and this file states both as theorems with conclusion `Wiring.ClearingBudget`:

* `clearingBudget_of_smithBudget`: from `RankCounts.budget` (minimal central data: entries in `(2)`,
  `B.n ≤ 3`; the reduced triangle (5.7c) and (5.7a) as RC7 states them);
* `clearingBudget_of_smithBudgetRank`: from `RankCounts.budget_rank` (RC7's `SmithBlocks` as it
  stands, unit disks allowed, the degree range `hamp`; input `hrank`, Elliot's first bound
  `rank_total ≤ 2 d_K + 12`);
* `clearingBudget_of_rank_model`: as the previous one, with `hrank` itself discharged by lane RC7's
  `total_rank_budget` from (5.7a), the reduced triangle (5.7c), the two singular disks mod two and
  the minimality of the model (`hmodel`, tex 5357–5359), as in the text.

Every theorem here is a bridge of kind `PROVED` from the hypotheses that remain.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Unif

open ZInQ.Manuscript.RC.Determinant ZInQ.Contrib.CloudB3RC53

/-- **The wiring's budget input from the shared top layer's Smith count (minimal data)**
(tex 5355–5387; consumer step tex 5384–5386). Lane RC0's input `Wiring.ClearingBudget` is
discharged by `RankCounts.budget` for the central Smith complex of `B` (free generators `fr`).
Kind: PROVED, from exactly the inputs of `RankCounts.budget`: `hn3 : B.n ≤ 3`, `hpos` (central
entries in `(2)`, tex 5357–5359), `fm`, `gm`, `hfg` (reduced (5.7c)), `h57a` ((5.7a)), `hQ` (singular
disks mod two), `eH1`, `i`, `j`, `δ`, `l`, `h57d` ((5.7d)), `ht₁`, `ht₃`, `hh` (`t_K`, (5.7b), `h_K`),
`hJ` (`length J_r ≤ 2 c_E`) and `hr₁`, `hr₂` (free ranks one, tex 5303–5311).
Consumer: `ZInQ.Manuscript.RC.Wiring.ClearingBudget` (in `Wiring.ClearingModelOver`); discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.budget`. -/
theorem clearingBudget_of_smithBudget {S O : Type} [CommRing S] [CommRing O] [Algebra Lam O]
    (B : SmithBlocks S O) (fr : ℕ → ℕ) (hn3 : B.n ≤ 3) (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
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
    (eH1 : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    Wiring.ClearingBudget B dK hK cE tK :=
  RankCounts.budget B fr hn3 hpos fm gm hfg h57a hQ eH1 i j δ l h57d ht₁ ht₃ hh hJ hr₁ hr₂

/-- **The wiring's budget input from the shared top layer's rank count (unit disks allowed)**
(tex 5375–5387, 5530–5541; consumer step tex 5384–5386). Lane RC0's input `Wiring.ClearingBudget`
is discharged by `RankCounts.budget_rank` for RC7's `SmithBlocks` as they stand (central entries
only nonzero).
Kind: PROVED, from exactly the inputs of `RankCounts.budget_rank`: the degree range `hamp` (no disk
with source degree `≥ 3`), Elliot's first (5.7) bound `hrank : rank_total ≤ 2 d_K + 12` for the
central Smith complex (every disk counted), `eH1`, `i`, `j`, `δ`, `l`, `h57d` ((5.7d)), `ht₁`, `ht₃`,
`hh`, `hJ` and `hr₁`, `hr₂`. Consumer: `ZInQ.Manuscript.RC.Wiring.ClearingBudget`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.budget_rank`. -/
theorem clearingBudget_of_smithBudgetRank {S O : Type} [CommRing S] [CommRing O] [Algebra Lam O]
    (B : SmithBlocks S O) (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0) {dK : ℕ}
    (hrank : ∑ k : Fin 4, Module.finrank ℤ_[2] (RankCounts.centralCx B fr k) ≤ 2 * dK + 12)
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (eH1 : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    Wiring.ClearingBudget B dK hK cE tK :=
  RankCounts.budget_rank B fr hamp hrank eH1 i j δ l h57d ht₁ ht₃ hh hJ hr₁ hr₂

/-- **The wiring's budget input, unit disks allowed, from (5.7a), (5.7c) and minimality**
(tex 5355–5387; consumer step tex 5384–5386). As `clearingBudget_of_smithBudgetRank`, with its input
`hrank` (`rank_total ≤ 2 d_K + 12`) discharged by lane RC7's `total_rank_budget`: the total
dimension of `H^*(D_c ⊗ 𝔽₂)` is at most `2 d_K + 12` by the reduced long exact sequence of (5.7c)
(`f`, `g`, `hfg`), (5.7a) (`h57a`) and the two singular disks mod two (`hQ`), and the total rank of
the central Smith complex is at most that dimension by the minimality of the model ("by cancelling
unit entries at its maximal ideal `(2, t)`", tex 5357–5359; input `hmodel`, RC7's `hmodel` with
`rank_total` the total rank of the central Smith complex).
Kind: PROVED, from `hamp`, `f`, `g`, `hfg`, `h57a`, `hQ`, `hmodel` and the (5.7d)/(5.7b) inputs `eH1`,
`i`, `j`, `δ`, `l`, `h57d`, `ht₁`, `ht₃`, `hh`, `hJ`, `hr₁`, `hr₂`. Consumer:
`ZInQ.Manuscript.RC.Wiring.ClearingBudget` (and the input `hrank` of `RankCounts.budget_rank`);
dischargers: `ZInQ.Contrib.CloudB3RC53.RankCounts.budget_rank`,
`ZInQ.Manuscript.RC.Determinant.total_rank_budget`. -/
theorem clearingBudget_of_rank_model {S O : Type} [CommRing S] [CommRing O] [Algebra Lam O]
    (B : SmithBlocks S O) (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0)
    {k : Type*} [Field k] {HC HD HQ : Fin 4 → Type*}
    [∀ n, AddCommGroup (HC n)] [∀ n, Module k (HC n)]
    [∀ n, AddCommGroup (HD n)] [∀ n, Module k (HD n)]
    [∀ n, AddCommGroup (HQ n)] [∀ n, Module k (HQ n)]
    [∀ n, FiniteDimensional k (HC n)] [∀ n, FiniteDimensional k (HQ n)]
    (f : ∀ n, HC n →ₗ[k] HD n) (g : ∀ n, HD n →ₗ[k] HQ n) (hfg : ∀ n, Function.Exact (f n) (g n))
    {dK : ℕ} (h57a : ∀ n, Module.finrank k (HC n) = (![2, dK, dK, 2] : Fin 4 → ℕ) n)
    (hQ : ∑ n, Module.finrank k (HQ n) ≤ 8)
    (hmodel : ∑ n : Fin 4, Module.finrank ℤ_[2] (RankCounts.centralCx B fr n) ≤
      ∑ n, Module.finrank k (HD n))
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (eH1 : RankCounts.centralH B fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] RankCounts.centralH B fr 2) (j : RankCounts.centralH B fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] RankCounts.centralH B fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    Wiring.ClearingBudget B dK hK cE tK :=
  RankCounts.budget_rank B fr hamp (hmodel.trans (total_rank_budget f g hfg h57a hQ)) eH1 i j δ l
    h57d ht₁ ht₃ hh hJ hr₁ hr₂

end ZInQ.Manuscript.RC.GlueSweep.Unif
