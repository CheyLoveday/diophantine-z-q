import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Limits
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents

/-!
# The finite trace quotients

Tex 9663–9668, 9524–9554, 9919–9921. The uniformity argument for the right
periods uses compactness of the absolute Galois group (proved here).

Lane RC24, round 3: adapted to the constituent model on coefficientwise reduced expansions.
`consN` is now read on the reduced trace orbit `redTrace m expand ρ hst F` (tex 9639–9646,
9716–9729). Openness uses that the kernel of coefficientwise reduction contains the open `𝔪Λ`.
`galNOpen_of_consN_open` takes the budget argument of `GalNOpen`. Round 4: the abstract module
of the constituent model is `Mst` (no congruence hypothesis on the operators), and
`galN_eq_N` identifies its `galN` with `consN` within the budget.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {chiType : GalQ →* Multiplicative L}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
variable {m : Ideal O} {F : Finset ℕ → Λ} {C : Type} {expand : Λ →ₗ[O] (C → O)}

/-- Continuity of the type character at one, in terms of the Krull basis. For the
tree's type characters use `exists_fixingSubgroup_le_ker_typChar` or
`exists_fixingSubgroup_le_ker_stageChar` (tex 2016–2025). -/
def OpenTypeKernel (chiType : GalQ →* Multiplicative L) : Prop :=
  ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
    ∀ σ ∈ E.fixingSubgroup, chiType σ = 1

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The defining subgroup `N_U` is open if lattice reduction is discrete and the
constituent trace is continuous (tex 9663–9668). This applies to every finite `U`. The kernel of
coefficientwise reduction contains the open `𝔪Λ`, so it is open. -/
theorem consN_isOpen (hchi : OpenTypeKernel chiType)
    (hmathfrak : IsOpen ((m • (⊤ : Submodule O Λ) : Submodule O Λ) : Set Λ))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ)
    (hcont : ContinuousOperators ρ Λ) (U : Finset ℕ) :
    IsOpen (consN chiType (redTrace m expand ρ hst F) U : Set GalQ) := by
  classical
  let H := (chiType.prod (MonoidHom.pi fun s : U => bitChar s)).ker
  have hH : IsOpen (H : Set GalQ) := by
    obtain ⟨E₀, hE₀, h₀⟩ := hchi
    obtain ⟨E₁, hE₁, h₁⟩ := exists_fixingSubgroup_le_ker_bitChar U
    apply (subgroup_isOpen_iff H).2
    refine ⟨E₀ ⊔ E₁, inferInstance, fun σ hσ => MonoidHom.mem_ker.2 ?_⟩
    exact Prod.ext (h₀ _ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ))
      (funext fun s => h₁ _ (IntermediateField.fixingSubgroup_antitone le_sup_right hσ) s s.2)
  let trace (W : Finset ℕ) (g : GalQ) : Λ := ⟨tV ρ g (F W), hst g _ (F W).2⟩
  let P : Submodule O Λ := LinearMap.ker (redExpOf m expand)
  have hP : IsOpen (P : Set Λ) :=
    AddSubgroup.isOpen_mono (H₁ := (m • (⊤ : Submodule O Λ) : Submodule O Λ).toAddSubgroup)
      (H₂ := P.toAddSubgroup) (le_ker_redExpOf m expand) hmathfrak
  have ht (W : Finset ℕ) : IsOpen {n : GalQ | ∀ g, trace W (g * n) - trace W g ∈ P} :=
    isOpen_rightPeriods (trace W) ((hcont.trace (F W)).subtype_mk _)
      P.toAddSubgroup hP
  convert hH.inter (isOpen_iInter_of_finite (fun W : U.powerset => ht W)) using 1
  ext n
  rw [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro hn
    refine ⟨MonoidHom.mem_ker.2 (Prod.ext hn.1 (funext fun s => hn.2.1 s s.2)), ?_⟩
    intro W g
    have e := hn.2.2 g W (Finset.mem_powerset.1 W.2)
    show trace W (g * n) - trace W g ∈ P
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact e
  · rintro ⟨hn, hp⟩
    have e := MonoidHom.mem_ker.1 hn
    refine ⟨congrArg Prod.fst e, fun s hs => congrFun (congrArg Prod.snd e) ⟨s, hs⟩,
      fun g W hW => ?_⟩
    let w : U.powerset := ⟨W, Finset.mem_powerset.2 hW⟩
    have e' : trace W (g * n) - trace W g ∈ P := hp w g
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at e'
    exact e'

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- An open constituent subgroup has finite index (tex 9663–9668). -/
theorem consN_finiteIndex {hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ} (U : Finset ℕ)
    (hopen : IsOpen (consN chiType (redTrace m expand ρ hst F) U : Set GalQ)) :
    (consN chiType (redTrace m expand ρ hst F) U).FiniteIndex := by
  obtain ⟨E, hE, hEN⟩ := (subgroup_isOpen_iff _).1 hopen
  exact finiteIndex_of_fixingSubgroup_le _ E hEN

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- Inertia outside the fixed support and a good set `U` lies in `N_U` when the
constituent representations are unramified there (tex 9524–9554). -/
theorem inertia_le_consN (T : TypeData L ε) {avoid : Finset ℕ}
    {hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ}
    (htyp : IsTypeChar T chiType) (hunr : UnramifiedConstituents T avoid ρ)
    {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) {q : ℕ} (hq : T.Good q)
    (hqu : q ∉ U) (hqa : q ∉ avoid) {Q : Ideal Zbar} (hQ : Q.IsMaximal)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) :
    Q.inertia GalQ ≤ consN chiType (redTrace m expand ρ hst F) U := by
  intro σ hσ
  obtain ⟨hc, hb⟩ := chars_eq_one_of_mem_inertia T htyp hU hq hqu hQ hqQ hσ
  refine ⟨hc, hb, fun g W _ => ?_⟩
  have e : tV ρ (g * σ) (F W) = tV ρ g (F W) := by
    funext i
    simp [tV, map_mul, hunr q hq hqa Q hQ hqQ σ hσ i]
  show redExpOf m expand (latT ρ Λ hst (g * σ) (F W)) = redExpOf m expand (latT ρ Λ hst g (F W))
  congr 1
  exact Subtype.ext e

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- The constituent model's Chebotarev field follows from the tree's density theorem,
openness and the known ramification of its constituents (tex 9666–9668, 9919–9921). -/
theorem consN_chebotarev (T : TypeData L ε) {avoid : Finset ℕ} {frob : ℕ → GalQ}
    {hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ}
    (htyp : IsTypeChar T chiType) (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hunr : UnramifiedConstituents T avoid ρ) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s)
    (hopen : IsOpen (consN chiType (redTrace m expand ρ hst F) U : Set GalQ)) (g : GalQ)
    (S : Finset ℕ) :
    ∃ q h, ∃ n ∈ consN chiType (redTrace m expand ρ hst F) U, T.Good q ∧ q ∉ S ∧
      frob q = h * g * h⁻¹ * n := by
  obtain ⟨E, hE, hEN⟩ := (subgroup_isOpen_iff _).1 hopen
  obtain ⟨q, h, n, hn, hq, hqa, -, -, e⟩ :=
    exists_frob_eq_conj_mul T hfrob (consN chiType (redTrace m expand ρ hst F) U) U avoid E hEN
      (fun _ hq hqu hqa _ hQ hqQ => inertia_le_consN T htyp hunr hU hq hqu hqa hQ hqQ) g S
  exact ⟨q, h, n, hn, hq, hqa, e⟩

/-- The openness result on constituents gives the tree's `GalNOpen` formulation
for the reduced operators and forms. -/
theorem galNOpen_of_consN_open {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
    (X : GaloisConstituentModel T R ap B chiType)
    (h : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → IsOpen (X.N U : Set GalQ)) :
    letI := X.modMst
    GalNOpen T chiType X.tK X.FK B := by
  letI := X.modMst
  change GalNOpen T chiType X.tK X.FK B
  intro U hU hUB
  rw [X.galN_eq_N U hU hUB]
  exact (subgroup_isOpen_iff _).1 (h U hU)

end ZInQ.Manuscript.RC.TraceLimits
