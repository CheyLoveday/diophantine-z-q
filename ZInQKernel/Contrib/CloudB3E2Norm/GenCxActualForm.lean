import ZInQKernel.Contrib.CloudB3E2Norm.RingChangeResidual

/-!
# The genuine `C_∅` in actual-conditions form

Manuscript `diophantine_zq.tex`, tex 3455–3498, 4385–4414.

For coefficient modules `M = InflMod hS M₀` with the genuine unramified representations at the
places of the chain and split inclusions along `urId` (as in the staged presentation:
`famM`, `famX`, `famEU`, `famEU_i`), the conditions of the genuine `C_∅` are, place by place,
those of the Galois local conditions `actualFormConds`: the presentation's old conditions at the
places of `S₀` and the unramified conditions `urAt` at the other places of `S` (`urOutside`).

* `condCast` (definition), `condCast_bijective`, `condCast_comp` (PROVED): an equality of
  conditions gives a bijective chain map compatible with the condition maps;
* `oldCond`, `actualFormConds` (definitions);
* **`genCxResidualIso_of_actualForm`** (PROVED): `GenCxResidualIso Rk` from finite residual
  cohomology with ranks `Rk s` of `selCx (galoisSelData K S (StageRing s) M (actualFormConds s))`
  — the place-by-place condition isomorphisms ψ (old places and new places) are discharged.

What remains of `GenCxResidualIso` for the staged presentation: identifying
`selCx (galoisSelData … (actualFormConds s))` over `StageRing s` with the contributor's
standard-old family over `Acoef s` (old conditions against `standardOldAt`, and the degreewise
semilinear identification for `genCxResidualIso_of_ringChange`), and instantiating its producer
bounds.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.St0Shape

open IsLocalRing NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Equal conditions -/

section Cast

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
  [CommRing k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  [ContinuousSMul (GKS K S) M] {v : Places K S}

/-- The chain map of an equality of conditions. Kind: definition. -/
def condCast {c₁ c₂ : CondAt K S k M v} (h : c₁ = c₂) : GHom c₁.U c₂.U :=
  h ▸ ⟨fun i j hij => by subst hij; exact LinearMap.id, fun i i₁ j j₁ hij h₁ h₂ hj x => by
    subst hij hj; rfl⟩

theorem condCast_bijective {c₁ c₂ : CondAt K S k M v} (h : c₁ = c₂) (n : ℤ) :
    Function.Bijective ((condCast h).f n n rfl) := by
  subst h
  exact Function.bijective_id

theorem condCast_comp {c₁ c₂ : CondAt K S k M v} (h : c₁ = c₂) (n : ℤ) (x : c₁.U.X n) :
    c₂.i.f n n rfl ((condCast h).f n n rfl x) = c₁.i.f n n rfl x := by
  subst h
  rfl

end Cast

/-! ### The actual-conditions form -/

section ActualForm

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) [∀ s, TopologicalSpace (StageRing s)] [∀ s, DiscreteTopology (StageRing s)]
  (M₀ : ℕ → Type) [∀ s, AddCommGroup (M₀ s)] [∀ s, Module (StageRing s) (M₀ s)]
  [∀ s, DistribMulAction (GKS K S₀) (M₀ s)] [∀ s, SMulCommClass (GKS K S₀) (StageRing s) (M₀ s)]
  [∀ s, TopologicalSpace (M₀ s)] [∀ s, DiscreteTopology (M₀ s)]
  [∀ s, ContinuousSMul (GKS K S₀) (M₀ s)] [∀ s, Finite (M₀ s)]
  (Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (M₀ s)))

/-- The presentation's old conditions as conditions at the places of `S` in `S₀`.
Kind: definition. -/
def oldCond (s : ℕ) : ∀ v : Places K S, v.1 ∈ S₀ →
    CondAt K S (StageRing s) (InflMod hS (M₀ s)) v :=
  fun v h => ⟨(Δ s).U ⟨v.1, h⟩, (Δ s).i ⟨v.1, h⟩⟩

/-- **The actual-conditions form of the genuine `C_∅`'s conditions**: the old conditions at the
places of `S₀`, the unramified conditions at the other places of `S`. Kind: definition. -/
def actualFormConds (s : ℕ) : GaloisLocalConditions K S (StageRing s) (InflMod hS (M₀ s)) :=
  ofCondAt K S (StageRing s) (InflMod hS (M₀ s))
    (urOutside hS (StageRing s) (M₀ s) (oldCond hS M₀ Δ s))

variable {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S) (hw : ∀ j, (place j).1 ∉ S₀)
  (EU : ∀ s j, SplitInclusion
    (genuineUq K S (StageRing s) (place j) (urRep (StageRing s) (M₀ s) (newPlace (place j) (hw j))))
    (genuineLq K S (StageRing s) (InflMod hS (M₀ s)) (place j)))

/-- The new-place condition as a `CondAt`. Kind: definition. -/
def newCond (s : ℕ) (j : ι × Bool) : CondAt K S (StageRing s) (InflMod hS (M₀ s)) (place j) :=
  ⟨genuineUq K S (StageRing s) (place j) (urRep (StageRing s) (M₀ s) (newPlace (place j) (hw j))),
    (EU s j).i⟩

omit [DecidableEq ι] in
theorem newCond_eq (s : ℕ) (j : ι × Bool)
    (hE : (EU s j).i = (urAt hS (StageRing s) (M₀ s) (place j) (hw j)).i) :
    newCond hS M₀ place hw EU s j = urOutside hS (StageRing s) (M₀ s) (oldCond hS M₀ Δ s)
      (place j) := by
  rw [urOutside, dite_eq_right (hw j)]
  change (⟨_, (EU s j).i⟩ : CondAt K S (StageRing s) (InflMod hS (M₀ s)) (place j)) = ⟨_, _⟩
  rw [hE]
  rfl

theorem oldCond_eq (s : ℕ) (v₀ : Places K S₀) :
    oldCond hS M₀ Δ s ⟨v₀.1, hS v₀.2⟩ v₀.2 =
      urOutside hS (StageRing s) (M₀ s) (oldCond hS M₀ Δ s) ⟨v₀.1, hS v₀.2⟩ := by
  rw [urOutside, dite_eq_left v₀.2]

variable (hE : ∀ s j, (EU s j).i = (urAt hS (StageRing s) (M₀ s) (place j) (hw j)).i)

/-- **The place-by-place condition isomorphisms** of the genuine `C_∅` with the actual-conditions
form. Kind: definition. -/
def actualψ (hinj : Function.Injective place) (hcov : ∀ v ∈ S, v ∈ S₀ ∨ ∃ j, (place j).1 = v)
    (s : ℕ) : ∀ i, GHom ((presCondS K S₀ S (StageRing s) (InflMod hS (M₀ s)) (Δ s) place
      (fun j => urRep (StageRing s) (M₀ s) (newPlace (place j) (hw j))) (EU s) ∅).U i)
      ((actualFormConds hS M₀ Δ s).U (presPlaceEquiv hS hinj hw hcov i))
  | .inl v₀ => condCast (oldCond_eq hS M₀ Δ s v₀)
  | .inr j => condCast (newCond_eq hS M₀ Δ place hw EU s j (hE s j))

include hE in
/-- **`GenCxResidualIso` from the actual-conditions form** (PROVED): the place-by-place condition
isomorphisms are discharged; the input is finite residual cohomology with ranks `Rk s` of the
Selmer complexes of the actual-conditions form. -/
theorem genCxResidualIso_of_actualForm {Rk : ℕ → ℤ → ℕ} (hinj : Function.Injective place)
    (hcov : ∀ v ∈ S, v ∈ S₀ ∨ ∃ j, (place j).1 = v)
    (hfin : ∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (selCx (galoisSelData K S (StageRing s) (InflMod hS (M₀ s))
        (actualFormConds hS M₀ Δ s))) n))
    (hrank : ∀ s [NeZero s] n, Module.finrank (ResidueField (StageRing s))
      (residualCohomologyAt (selCx (galoisSelData K S (StageRing s) (InflMod hS (M₀ s))
        (actualFormConds hS M₀ Δ s))) n) = Rk s n) :
    GenCxResidualIso K S₀ S (fun s => InflMod hS (M₀ s)) Δ place
      (fun s j => urRep (StageRing s) (M₀ s) (newPlace (place j) (hw j))) EU Rk :=
  genCxResidualIso_of_conditions hS hinj hw hcov (actualFormConds hS M₀ Δ)
    (actualψ hS M₀ Δ place hw EU hE hinj hcov)
    (fun s i n => by
      rcases i with v₀ | j
      · exact condCast_bijective _ n
      · exact condCast_bijective _ n)
    (fun s i n x => by
      rcases i with v₀ | j
      · exact condCast_comp (oldCond_eq hS M₀ Δ s v₀) n x
      · exact condCast_comp (newCond_eq hS M₀ Δ place hw EU s j (hE s j)) n x)
    hfin hrank

end ActualForm

end ZInQ.Contrib.CloudB3E2.St0Shape
