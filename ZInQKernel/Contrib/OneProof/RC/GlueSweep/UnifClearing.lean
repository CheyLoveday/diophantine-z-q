import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudget
import ZInQKernel.Contrib.OneProof.RC.Determinant.Genuine

/-!
# Lane RC22 (glue sweep), share `Unif`: lane RC7's other (5.9) assemblies with the budget discharged

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:limits-fixed-field-clearing`
(tex 5486–5664), consumer step: the budget (5.7) `m ≤ d_K + 5`, `h₁ ≤ h_K + 2 c_E + 2 t_K`
(tex 5384–5386, 5627–5634).

Lane RC7 states (5.9) three times — in coefficient form over any `O` with Laurent data
(`fixed_field_clearing`, `RC/Determinant/Output.lean`), as the shared top layer's nodes over any such
`O` (`clearing_nodes`, `RC/Determinant/B3Bridge.lean`) and over the genuine `𝒪`
(`clearing_nodes_genuine`, `RC/Determinant/Genuine.lean`) — and each takes the budget as the two
hypotheses `hm : B.mTot ≤ dK + 5`, `hh : B.hSmith ≤ hK + 2 * cE + 2 * tK`. The shared top layer's
`RankCounts.budget` (the theorem behind `RankCounts.fixedFieldBudgetSmith_proof`) proves both for
the central Smith complex of `B`. The bridges below state each assembly with `hm`, `hh` replaced by
exactly the inputs of `RankCounts.budget`. (The form with genuine corrected coordinates in `Λ[1/2]`,
lane RC20's `Rings.clearing_nodes_of_lambdaHalf`, is bridged in `UnifDeterminant.lean`.)

Inputs of `RankCounts.budget` that remain, in every theorem below (tex lines of the displays they
encode): `fr` (free generators), `hn3 : B.n ≤ 3` and `hpos` (central Smith entries in `(2)`,
tex 5357–5359); `fm`, `gm`, `hfg` (the reduced triangle (5.7c)), `h57a` ((5.7a)), `hQ` (the two
singular disks mod two, tex 5355–5356); `eH1`, `i`, `j`, `δ`, `l`, `h57d` ((5.7d), tex 5361–5366);
`ht₁`, `ht₃`, `hh` (`t_K`, (5.7b), `h_K`); `hJ` (`length J_r ≤ 2 c_E`, tex 5331–5351); `hr₁`, `hr₂`
(the free ranks of `H¹(C_K)`, `H²(C_K)`, tex 5303–5311).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Unif

open ZInQ.Manuscript.RC.Determinant ZInQ.Contrib.CloudB3RC53

/-- **(5.9) in coefficient form with the budget discharged** (tex 5486–5664; consumer step
tex 5384–5386, 5627–5634). Lane RC7's `fixed_field_clearing` with its hypotheses `hm`, `hh`
discharged by the shared top layer's `RankCounts.budget` for the central Smith complex of `B`.
Kind: PROVED, from RC7's remaining hypotheses (`hn`, `haug`, `h2O`, the ELLIOT inputs `hpat`,
`hrank`, `hacyc` (tex 5586–5617), the model input `hpole` (tex 5517–5519)) and the inputs of
`RankCounts.budget` listed in the module docstring. Consumer:
`ZInQ.Manuscript.RC.Determinant.fixed_field_clearing`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.budget`. -/
theorem fixedFieldClearing_smithBudget {O : Type*} [CommRing O] [IsDomain O] [Algebra Lam O]
    (D : PoleData Lam O) (LC : LaurentCoeffData D) {G : Type*} [CommMonoid G] [Fintype G]
    {X : Type*} (χ : X → G →* ℤˣ)
    (B : SmithBlocks (MonoidAlgebra O G) O) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam O))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O G) (a : ℕ)
    (e : X → ℕ) (g : X → Lam) (h2O : (2 : O) ≠ 0)
    (RankOne Acyclic : X → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (χ x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (χ x) η * evK (χ x) κ * sd.αK (evK (χ x)) *
        (((2 : FractionRing O) ^ a)⁻¹ * sd.βK (evK (χ x))) * cleanT (evK (χ x)) B ε)
    (hacyc : ∀ x, evK (χ x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (χ x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing O))
    (hpole : ∀ x M i, ∀ j k, ((B.A i).map (signEval (χ x))) j k ∈ D.poleModLE M (4 * M))
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
    (∀ x (n : ℤ), HasSum (fun k : ℕ =>
        ((LC.coeffZ (signEval (χ x) (clearF B a)) (n - k) : ℤ_[2]) : ℚ_[2]) *
        (((PowerSeries.coeff k (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x))
        (LC.coeffZ (signEval (χ x) (sd.dd κ ε η)) n : ℚ_[2])) ∧
    (∀ i : ℤ, i < 0 → LC.coeffZ (aug (clearF B a)) i = 0) ∧
    LC.coeffZ (aug (clearF B a)) 0 ≠ 0 ∧
    (LC.coeffZ (aug (clearF B a)) 0).valuation = a + 4 * B.hSmith ∧
    a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
    (∀ (M : ℕ) x (i : ℤ), i < -((16 * (dK + 5) * M : ℕ) : ℤ) →
      (2 : ℤ_[2]) ^ M ∣ LC.coeffZ (signEval (χ x) (clearF B a)) i) := by
  obtain ⟨hm, hbud⟩ := RankCounts.budget B fr hn3 hpos fm gm hfg h57a hQ eH1 i j δ l h57d
    ht₁ ht₃ hh hJ hr₁ hr₂
  exact fixed_field_clearing D LC χ B hn haug sd κ ε η a e g h2O RankOne Acyclic hpat hrank hacyc
    hpole dK hK cE tK hm hbud

/-- **(5.9) as the shared top layer's nodes, over any `O` with Laurent data, with the budget
discharged** (tex 5486–5664; consumer step tex 5384–5386, 5627–5634). Lane RC7's `clearing_nodes`
with `hm`, `hh` discharged by `RankCounts.budget` for the central Smith complex of `B`.
Kind: PROVED, from RC7's remaining hypotheses (`hn`, `haug`, `hu`, `h2O`, `hpat`, `hrank`,
`hacyc`, `hpole`) and the inputs of `RankCounts.budget` listed in the module docstring.
Consumer: `ZInQ.Manuscript.RC.Determinant.clearing_nodes`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.budget`. -/
theorem clearingNodes_smithBudget {O : Type*} [CommRing O] [Algebra Lam O] [IsDomain O]
    {D : PoleData Lam O} (LC : LaurentCoeffData D) {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam O))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O (SignGroup b)) (a : ℕ)
    (u : Addr b → ℕ → ℚ_[2]) (e : Addr b → ℕ) (g : Addr b → Lam)
    (hu : ∀ x j, u x j = ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x)
    (h2O : (2 : O) ≠ 0)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing O) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing O))
    (hpole : ∀ x M i, ∀ j k, ((B.A i).map (signEval (sgnChar x))) j k ∈ D.poleModLE M (4 * M))
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
    ∃ C : CoordData b, C.u = u ∧ ClearingIdentity C ∧
      (∀ M : ℕ, PoleBound C (16 * (dK + 5) * M) M) ∧
      BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) := by
  obtain ⟨hm, hbud⟩ := RankCounts.budget B fr hn3 hpos fm gm hfg h57a hQ eH1 i j δ l h57d
    ht₁ ht₃ hh hJ hr₁ hr₂
  exact clearing_nodes LC B hn haug sd κ ε η a u e g hu h2O RankOne Acyclic hpat hrank hacyc hpole
    dK hK cE tK hm hbud

/-- **(5.9) over the genuine `𝒪` with the budget discharged** (tex 5486–5664; consumer step
tex 5384–5386, 5627–5634). Lane RC7's `clearing_nodes_genuine` with `hm`, `hh` discharged by
`RankCounts.budget` for the central Smith complex of `B`.
Kind: PROVED, from RC7's remaining hypotheses (`hn`, `haug`, `hu`, `hpat`, `hrank`, `hacyc`,
`hpole`) and the inputs of `RankCounts.budget` listed in the module docstring. Consumer:
`ZInQ.Manuscript.RC.Determinant.clearing_nodes_genuine`; discharger:
`ZInQ.Contrib.CloudB3RC53.RankCounts.budget`. -/
theorem clearingNodesGenuine_smithBudget {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (u : Addr b → ℕ → ℚ_[2]) (e : Addr b → ℕ) (g : Addr b → Lam)
    (hu : ∀ x j, u x j = ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing OO))
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
    ∃ C : CoordData b, C.u = u ∧ ClearingIdentity C ∧
      (∀ M : ℕ, PoleBound C (16 * (dK + 5) * M) M) ∧
      BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) := by
  obtain ⟨hm, hbud⟩ := RankCounts.budget B fr hn3 hpos fm gm hfg h57a hQ eH1 i j δ l h57d
    ht₁ ht₃ hh hJ hr₁ hr₂
  exact clearing_nodes_genuine B hn haug sd κ ε η a u e g hu RankOne Acyclic hpat hrank hacyc hpole
    dK hK cE tK hm hbud

end ZInQ.Manuscript.RC.GlueSweep.Unif
