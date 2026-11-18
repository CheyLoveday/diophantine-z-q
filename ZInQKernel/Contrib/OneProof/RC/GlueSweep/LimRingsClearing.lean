import ZInQKernel.Contrib.OneProof.RC.Rings.Wiring
import ZInQKernel.Contrib.OneProof.RC.Determinant.Budget
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudget
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudgetRank
import ZInQKernel.Contrib.OneProof.RC.Wiring.Clearing
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.UnifDeterminant

/-!
# Lane RC22 (glue sweep): (5.9) with genuine `ũ_x ∈ Λ[1/2]` and the budget (5.7) discharged

Manuscript (`diophantine_zq.tex`, 11/5 version): Lemma `ex:limits-fixed-field-budget`, tex 5208ff.
(the budget (5.7): `m ≤ d_K + 5`, `h₁ ≤ h_K + 2c_E + 2t_K`, tex 5384–5386; the Smith count, tex
5355–5387); Proposition `ex:limits-fixed-field-clearing`, (5.9), tex 5487–5664.

Lane RC20's `ZInQ.Manuscript.RC.Rings.clearing_nodes_of_lambdaHalf` (lane RC7's
`clearing_nodes_genuine` with the corrected coordinates given as genuine `ũ_x ∈ Λ[1/2]`) still takes
lane RC7's budget hypotheses

    (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK)

The RankCounts area proves exactly these two statements, in RC7's types, from the (5.7) inputs on the
central Smith complex of `B` (`ZInQ.Contrib.CloudB3RC53.RankCounts.fixedFieldBudgetSmith_proof`).
This file removes `hm`, `hh` (the form with the (5.7) inputs of `FixedFieldBudgetSmith`, including
the bound `hJ : length J_r ≤ 2c_E`, is `GlueSweep.Unif.clearingNodes_lambdaHalf_smithBudget`):
* `clearing_nodes_of_lambdaHalf_budget_frob_rings`: moreover `hJ` derived, as in lane RC7's
  `budget_57`, from the two moving Frobenius matrices and the moving-character bound
  (`ZInQ.Manuscript.RC.Determinant.moving_J_length_le`, tex 5315–5334, 5350–5351);
* `clearing_nodes_of_lambdaHalf_budgetRank_rings`, `clearing_nodes_of_lambdaHalf_budgetRank_frob_rings`:
  the same with the RankCounts budget for RC7's `SmithBlocks` as they stand (unit disks allowed,
  `fixedFieldBudgetSmithRank_proof`, Elliot's total-rank count, tex 5375–5387, 5530–5541): no
  minimality hypothesis, the degree range `hamp`, and Elliot's first (5.7) bound
  `rank_total ≤ 2d_K + 12` as an input;
(The conjunct `ClearingBudget` of the top-level wiring from the same RankCounts inputs is
`GlueSweep.Unif.clearingBudget_of_smithBudgetRank`, and lane RC16's bounded-denominator clause from
genuine coordinates in `Λ[1/2]` is `GlueSweep.Unif.clearing_boundedDenominators_of_lambdaHalf`.)

Every theorem here is `PROVED` (from the remaining hypotheses named in its docstring).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open ZInQ.Manuscript.RC.Uniform (LambdaHalf centralSpecialization)
open ZInQ.Manuscript.RC.Rings (halfToFracO coeffHalf clearing_nodes_of_lambdaHalf)
open ZInQ.Manuscript.RC.Determinant
open ZInQ.Contrib.CloudB3RC53.RankCounts (centralRed centralH centralCx fixedFieldBudgetSmith_proof
  fixedFieldBudgetSmithRank_proof)

/-- **(5.9) with genuine `ũ_x ∈ Λ[1/2]`, the budget (5.7) discharged, and the bound on `J_r` from the
moving Frobenius data** (tex 5487–5664; budget tex 5355–5387; `J_r = H²(Q_r)` and the moving singular
differentials `Φ_k − r`: tex 5315–5334, 5350–5351).

Kind: `PROVED` from the remaining hypotheses. Consumer: lane RC20's
`ZInQ.Manuscript.RC.Rings.clearing_nodes_of_lambdaHalf`, through
`GlueSweep.Unif.clearingNodes_lambdaHalf_smithBudget`. Dischargers:
`ZInQ.Contrib.CloudB3RC53.RankCounts.fixedFieldBudgetSmith_proof` (RC7's `hm`, `hh`) and lane RC7's
`ZInQ.Manuscript.RC.Determinant.moving_J_length_le` (the hypothesis `hJ` of `FixedFieldBudgetSmith`,
exactly as in RC7's `budget_57`).

Remaining hypotheses: those of `GlueSweep.Unif.clearingNodes_lambdaHalf_smithBudget` except `hJ`,
plus RC7's moving data of `budget_57`: Frobenius matrices `Φ₁, Φ₂` with traces `a₁, a₂` and common unit
determinant `r` (`hr`, `htr₁`, `hdet₁`, `htr₂`, `hdet₂`), `r + 1 − a_k ≠ 0` with valuation at most
`c_E` (`hne₁`, `hne₂`, `hcE₁`, `hcE₂`; Proposition `ex:arith-moving-character`), and the
identification `eJ` of `J_r` with the product of the two cokernels. -/
theorem clearing_nodes_of_lambdaHalf_budget_frob_rings {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (ũ : Addr b → LambdaHalf)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      halfToFracO (ũ x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ halfToFracO (ũ x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    (fr : ℕ → ℕ) (hn3 : B.n ≤ 3) (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    (HC HQ : Fin 4 → Type) [∀ k, AddCommGroup (HC k)] [∀ k, Module (ZMod 2) (HC k)]
    [∀ k, AddCommGroup (HQ k)] [∀ k, Module (ZMod 2) (HQ k)]
    [∀ k, FiniteDimensional (ZMod 2) (HC k)] [∀ k, FiniteDimensional (ZMod 2) (HQ k)]
    (fm : ∀ k : Fin 4, HC k →ₗ[ZMod 2] (centralRed B) fr k)
    (gm : ∀ k : Fin 4, (centralRed B) fr k →ₗ[ZMod 2] HQ k)
    (hfg : ∀ k, Function.Exact (fm k) (gm k))
    (dK : ℕ) (h57a : ∀ k, Module.finrank (ZMod 2) (HC k) = (![2, dK, dK, 2] : Fin 4 → ℕ) k)
    (hQ : ∑ k, Module.finrank (ZMod 2) (HQ k) ≤ 8)
    (H1C H2C J H3C : Type) [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    (tK hK cE : ℕ) (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (Φ₁ Φ₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a₁ a₂ r : ℤ_[2]) (hr : IsUnit r)
    (htr₁ : Φ₁.trace = a₁) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = a₂) (hdet₂ : Φ₂.det = r)
    (hne₁ : r + 1 - a₁ ≠ 0) (hne₂ : r + 1 - a₂ ≠ 0)
    (hcE₁ : (r + 1 - a₁).valuation ≤ cE) (hcE₂ : (r + 1 - a₂).valuation ≤ cE)
    (eJ : J ≃ₗ[ℤ_[2]]
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₁ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) ×
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₂ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin))
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b, C.u = (fun x j => coeffHalf (ũ x) j) ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (dK + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
      ∀ x, C.u x 0 = centralSpecialization (ũ x) := by
  have hJ : Module.length ℤ_[2] J ≤ 2 * (cE : ℕ∞) := by
    rw [eJ.length_eq]
    exact_mod_cast moving_J_length_le Φ₁ Φ₂ a₁ a₂ r hr htr₁ hdet₁ htr₂ hdet₂ cE hne₁ hne₂ hcE₁ hcE₂
  exact ZInQ.Manuscript.RC.GlueSweep.Unif.clearingNodes_lambdaHalf_smithBudget B hn haug sd κ ε η a ũ
    RankOne Acyclic hpat hrank hacyc hpole fr hn3 hpos fm gm hfg h57a hQ e i j δ l h57d ht₁ ht₃ hh hJ
    hr₁ hr₂

/-- **(5.9) with genuine `ũ_x ∈ Λ[1/2]` and the budget (5.7) discharged by the total-rank count,
unit disks allowed** (tex 5487–5664 for (5.9); tex 5375–5387, 5530–5541 for the count; (5.7) at
5384–5386).

Kind: `PROVED` from the remaining hypotheses. Consumer: lane RC20's
`ZInQ.Manuscript.RC.Rings.clearing_nodes_of_lambdaHalf`. Discharger of its hypotheses
`hm : B.mTot ≤ dK + 5` and `hh : B.hSmith ≤ hK + 2 * cE + 2 * tK`:
`ZInQ.Contrib.CloudB3RC53.RankCounts.fixedFieldBudgetSmithRank_proof` (RC7's `SmithBlocks` as they
stand: central Smith entries only nonzero, unit disks allowed).

Remaining hypotheses: lane RC7's inputs of (5.9), verbatim (as in `clearing_nodes_of_lambdaHalf`);
and the inputs of `FixedFieldBudgetSmithRank` on the central Smith complex of `B` with free ranks
`fr`: the degree range `hamp` (no disk of source degree `≥ 3`; compatible with RC7's `2 < B.n`),
Elliot's first (5.7) bound for the total rank of the central Smith complex (`hrk`,
`rank_total ≤ 2d_K + 12`, tex 5355–5359, 5384–5386), the integral sequence (5.7d) `e, i, j, δ, l,
h57d`, the lengths `ht₁, ht₃, hh`, the bound `hJ` on `J_r`, and the free ranks `hr₁, hr₂` of (5.7b).
Each block is non-vacuous on its own (lane RC7's `clearing_nodes_genuine_nonvacuous`; RankCounts'
`fixedFieldBudgetSmithRank_nonvacuous`, with a unit disk); a joint instance is not constructed
here. -/
theorem clearing_nodes_of_lambdaHalf_budgetRank_rings {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (ũ : Addr b → LambdaHalf)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      halfToFracO (ũ x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ halfToFracO (ũ x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0)
    (dK : ℕ) (hrk : ∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr k) ≤ 2 * dK + 12)
    (H1C H2C J H3C : Type) [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    (tK hK cE : ℕ) (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE)
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b, C.u = (fun x j => coeffHalf (ũ x) j) ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (dK + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
      ∀ x, C.u x 0 = centralSpecialization (ũ x) := by
  obtain ⟨hm, hhS⟩ := fixedFieldBudgetSmithRank_proof _ _ B fr hamp dK hrk H1C H2C J H3C e i j δ l
    h57d tK hK cE ht₁ ht₃ hh hJ hr₁ hr₂
  exact clearing_nodes_of_lambdaHalf B hn haug sd κ ε η a ũ RankOne Acyclic hpat hrank hacyc hpole
    dK hK cE tK hm hhS

/-- **(5.9) with genuine `ũ_x ∈ Λ[1/2]`, the budget by the total-rank count (unit disks allowed),
and the bound on `J_r` from the moving Frobenius data** (tex 5487–5664; count tex 5375–5387,
5530–5541; `J_r = H²(Q_r)`: tex 5315–5334, 5350–5351).

Kind: `PROVED` from the remaining hypotheses. Consumer: lane RC20's
`ZInQ.Manuscript.RC.Rings.clearing_nodes_of_lambdaHalf`, through
`clearing_nodes_of_lambdaHalf_budgetRank_rings`. Dischargers:
`ZInQ.Contrib.CloudB3RC53.RankCounts.fixedFieldBudgetSmithRank_proof` (RC7's `hm`, `hh`) and lane
RC7's `ZInQ.Manuscript.RC.Determinant.moving_J_length_le` (the input `hJ`, as in RC7's `budget_57`).

Remaining hypotheses: those of `clearing_nodes_of_lambdaHalf_budgetRank_rings` except `hJ`, plus
RC7's moving data of `budget_57` (`Φ₁, Φ₂, a₁, a₂, r, hr, htr₁, hdet₁, htr₂, hdet₂, hne₁, hne₂,
hcE₁, hcE₂, eJ`; Proposition `ex:arith-moving-character` for `v₂(r + 1 − a_k) ≤ c_E`). -/
theorem clearing_nodes_of_lambdaHalf_budgetRank_frob_rings {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (ũ : Addr b → LambdaHalf)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      halfToFracO (ũ x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ halfToFracO (ũ x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    (fr : ℕ → ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0)
    (dK : ℕ) (hrk : ∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr k) ≤ 2 * dK + 12)
    (H1C H2C J H3C : Type) [AddCommGroup H1C] [Module ℤ_[2] H1C] [AddCommGroup H2C]
    [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J] [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : (centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] (centralH B) fr 2) (j : (centralH B) fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (centralH B) fr 3)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    (tK hK cE : ℕ) (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (Φ₁ Φ₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a₁ a₂ r : ℤ_[2]) (hr : IsUnit r)
    (htr₁ : Φ₁.trace = a₁) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = a₂) (hdet₂ : Φ₂.det = r)
    (hne₁ : r + 1 - a₁ ≠ 0) (hne₂ : r + 1 - a₂ ≠ 0)
    (hcE₁ : (r + 1 - a₁).valuation ≤ cE) (hcE₂ : (r + 1 - a₂).valuation ≤ cE)
    (eJ : J ≃ₗ[ℤ_[2]]
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₁ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) ×
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₂ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin))
    (hr₁ : Module.finrank ℤ_[2] H1C = 1) (hr₂ : Module.finrank ℤ_[2] H2C = 1) :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b, C.u = (fun x j => coeffHalf (ũ x) j) ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (dK + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
      ∀ x, C.u x 0 = centralSpecialization (ũ x) := by
  have hJ : Module.length ℤ_[2] J ≤ 2 * (cE : ℕ∞) := by
    rw [eJ.length_eq]
    exact_mod_cast moving_J_length_le Φ₁ Φ₂ a₁ a₂ r hr htr₁ hdet₁ htr₂ hdet₂ cE hne₁ hne₂ hcE₁ hcE₂
  exact clearing_nodes_of_lambdaHalf_budgetRank_rings B hn haug sd κ ε η a ũ RankOne Acyclic hpat
    hrank hacyc hpole fr hamp dK hrk H1C H2C J H3C e i j δ l h57d tK hK cE ht₁ ht₃ hh hJ hr₁ hr₂

end ZInQ.Manuscript.RC.GlueSweep.Lim
