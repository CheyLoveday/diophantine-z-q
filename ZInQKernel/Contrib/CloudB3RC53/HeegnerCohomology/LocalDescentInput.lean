import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Kummer
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.LocalDescent

/-!
# HeegnerCohomology, part 4: RC10's `LocalDescentInput` over genuine continuous cohomology

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 5,
tex 3058–3086: "If a class `v ∈ H¹(F, B[2^a])` becomes Kummer over `F'`, its image in
`H¹(F, B)[2^a]` belongs to the kernel of restriction.  That kernel is the image of
`H¹(Gal(F'/F), B(F'))`.  Thus `c_B v` is Kummer over `F`, by the Kummer exact sequence and
(H10)."

RC10 records this as the interface `LocalDescentInput` (file
`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Interfaces.lean`, the structure is used
directly) and proves the diagram chase (`LocalDescentInput.kummer`).  Here every
field is constructed from genuine objects, for a topological group `G` (for `G_F`), a normal
subgroup `N` (for `G_{F'}`), and a short exact sequence `0 → A → B → B → 0` of discrete
`G`-modules with second map `2^a` (for `0 → E[2^a] → E → E → 0`):

* `Pt = B^G`, `HV = H¹(G, A)`, `HB = H¹(G, B)`, `κ` the connecting map, `j` induced by `A → B`;
* `Pt' = B^N`, `HV' = H¹(N, A)`, `HB' = H¹(N, B)`, likewise;
* `res`, `resB` restriction to `N`; `infl` inflation from `Hinf = H¹(G/N, B^N)`;
* `exK`, `hκ'`, `hcomm`, `exInf`: `PROVED` (long exact sequence, naturality, inflation–restriction);
* `hH10`: `PROVED` from the (H10) hypotheses on `B^N = B(F')` with `Γ = G/N = Gal(F'/F)`
  (`H10_killH1`; Lang's theorem and the formal-group structure are the hypotheses `hLang`,
  `hπ…`, see `LocalDescent.lean`).
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti.ContCohomology groupCohomology
open ZInQ.Manuscript.RC.HeegnerAlgebra (LocalDescentInput)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- **RC10's `LocalDescentInput` for genuine continuous cohomology** (tex 3034–3086), `PROVED`
from the (H10) hypotheses on `V = B^N` (for `B(F')`) with `Γ = G ⧸ N` (for `Gal(F'/F)`): see
`H10_killH1` for the meaning of `F`, `Q`, `π`, `hLang`, `hInd`, `hcB`. -/
noncomputable def localDescentInputGenuine (N : Subgroup G) [N.Normal]
    (S : DiscreteShortExact G A B B)
    (F : ℕ → AddSubgroup (FixedPoints.addSubgroup N B))
    (hstable : ∀ i (g : G ⧸ N), ∀ x ∈ F i, g • x ∈ F i)
    (hsep : ∀ x, (∀ i, x ∈ F i) → x = 0)
    (hcomplete : ∀ x : ℕ → FixedPoints.addSubgroup N B, (∀ i, x i ∈ F i) →
      ∃ s, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (Q : ℕ → Type*) [∀ i, AddCommGroup (Q i)] [∀ i, DistribMulAction (G ⧸ N) (Q i)]
    (π : ∀ i, F i →+ Q i) (hπs : ∀ i, Function.Surjective (π i))
    (hπk : ∀ i (x : F i), π i x = 0 ↔ (x : FixedPoints.addSubgroup N B) ∈ F (i + 1))
    (hπe : ∀ i (g : G ⧸ N) (x : F i), π i ⟨g • (x : FixedPoints.addSubgroup N B),
      hstable i g x x.2⟩ = g • π i x)
    (hLang : ∀ f : G ⧸ N → Q 0, IsCocycle₁ f → IsCoboundary₁ f)
    (hInd : ∀ i, 1 ≤ i → ∀ f : G ⧸ N → Q i, IsCocycle₁ f → IsCoboundary₁ f)
    (cB : ℤ) (hcB : ∀ x : FixedPoints.addSubgroup N B, cB • x ∈ F 0) :
    LocalDescentInput (H0 G B) (H0 N B) (H1 G A) (H1 N A) (H1 G B) (H1 N B)
      (H1 (G ⧸ N) (FixedPoints.addSubgroup N B)) where
  κ := S.explicitDelta0
  j := explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology
  exK v hv := by
    have : v ∈ (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker :=
      hv
    rw [← S.explicitLongExact_H1A] at this
    exact this
  κ' := (S.restrict N).explicitDelta0
  j' := explicitCoeff1 N A (S.restrict N).inclDistribMulActionHom continuous_of_discreteTopology
  hκ' x' := by
    have : (S.restrict N).explicitDelta0 x' ∈ (S.restrict N).explicitDelta0.range := ⟨x', rfl⟩
    rw [(S.restrict N).explicitLongExact_H1A] at this
    exact this
  res := explicitRes1 G A N
  resB := explicitRes1 G B N
  hcomm v := by
    induction v using QuotientAddGroup.induction_on with
    | H c => rfl
  infl := explicitInfl1 G B N
  exInf w hw := exInf_genuine G B N w hw
  cB := cB
  hH10 := H10_killH1 F hstable hsep hcomplete Q π hπs hπk hπe hLang hInd cB hcB

/-- **Node: integral local descent** (tex 3058–3084), `PROVED` from the (H10) hypotheses: with the
data of `localDescentInputGenuine`, a class `v ∈ H¹(G, A)` (for `H¹(F, B[2^a])`) whose
restriction to `N` (for `F'`) is a Kummer class becomes Kummer over `F` after multiplication by
`c_B` (and then by `m₀ c_B`, tex 3080). -/
theorem localDescent_kummer (N : Subgroup G) [N.Normal]
    (S : DiscreteShortExact G A B B)
    (F : ℕ → AddSubgroup (FixedPoints.addSubgroup N B))
    (hstable : ∀ i (g : G ⧸ N), ∀ x ∈ F i, g • x ∈ F i)
    (hsep : ∀ x, (∀ i, x ∈ F i) → x = 0)
    (hcomplete : ∀ x : ℕ → FixedPoints.addSubgroup N B, (∀ i, x i ∈ F i) →
      ∃ s, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (Q : ℕ → Type*) [∀ i, AddCommGroup (Q i)] [∀ i, DistribMulAction (G ⧸ N) (Q i)]
    (π : ∀ i, F i →+ Q i) (hπs : ∀ i, Function.Surjective (π i))
    (hπk : ∀ i (x : F i), π i x = 0 ↔ (x : FixedPoints.addSubgroup N B) ∈ F (i + 1))
    (hπe : ∀ i (g : G ⧸ N) (x : F i), π i ⟨g • (x : FixedPoints.addSubgroup N B),
      hstable i g x x.2⟩ = g • π i x)
    (hLang : ∀ f : G ⧸ N → Q 0, IsCocycle₁ f → IsCoboundary₁ f)
    (hInd : ∀ i, 1 ≤ i → ∀ f : G ⧸ N → Q i, IsCocycle₁ f → IsCoboundary₁ f)
    (cB : ℤ) (hcB : ∀ x : FixedPoints.addSubgroup N B, cB • x ∈ F 0)
    (v : H1 G A) (hv : ∃ x' : H0 N B, explicitRes1 G A N v = (S.restrict N).explicitDelta0 x') :
    ∃ x : H0 G B, S.explicitDelta0 x = cB • v := by
  set D := localDescentInputGenuine N S F hstable hsep hcomplete Q π hπs hπk hπe hLang hInd cB hcB
  obtain ⟨x', hx'⟩ := hv
  have h1 : D.resB (D.j v) = 0 := by
    rw [← D.hcomm]
    show D.j' (explicitRes1 G A N v) = 0
    rw [hx']
    exact D.hκ' x'
  obtain ⟨z, hz⟩ := D.exInf _ h1
  apply D.exK
  rw [map_zsmul, ← hz, ← map_zsmul, show cB • z = D.cB • z from rfl, D.hH10, map_zero]

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
