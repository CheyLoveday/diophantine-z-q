import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Derivative
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps

/-!
# RC53 SwitchInputs: the quasi switch sides from the genuine derivative conditions

Proposition `ex:limits-uniform-lower-bound`, the switch at a new inert derivative prime, tex
L5068–5086 (the conditions `D⁰ ⊂ D⁰ ⊕ F[−1], D⁰ ⊕ S[−1] ⊂ D⁰ ⊕ (F ⊕ S)[−1]`), with the genuine
derivative conditions of `GenuineInst/Derivative.lean` (tex 4561–4573): the strict condition
`τ≤0 C^•_cont = [Z⁰ → 0]`, the relaxed condition `τ≤1 C^•_cont = [C⁰ → Z¹]`.

The quasi switch sides (`QuasiSide.lean`, `GenuineSteps.lean`) need, of the local quotients
`W_rel = relaxed/strict`, `W₁ = side/strict`, `W₂ = relaxed/side`, only homology facts:
`H⁰(W₁) = 0`, `H¹(W₁) → H¹(W_rel)` injective, `ker(H¹(W_rel) → H¹(W₂)) = im(H¹(W₁))`. Here these are
PROVED for the genuine conditions: each quotient of two-term complexes is again a two-term complex
`[A/A' → B/B']` (`quotD`), with `H⁰ = 0` as soon as `f⁻¹(B') ⊆ A'`, and `H¹ = B ⧸ (B' + f A)`.

Nodes (PROVED):
* `QuotientTwoTerm` (generic): `H⁰([A/A' → B/B']) = 0` when `f⁻¹(B') ⊆ A'`; `H¹ ≃ B ⧸ (B' ⊔ f A)`.
* `RelaxedQuotientGenuine` (tex L5072–5074): for the genuine `W_rel = relaxed/strict`,
  `H⁰ = 0` and `H¹ ≃ H¹_cont(G, M)` (all of `F ⊕ S`).
* `SideQuotientsGenuine` (tex L5072–5083): for a side condition `[A_F → B_F]` with
  `Z⁰ ⊆ A_F ⊆ C⁰`, `d(A_F) ⊆ B_F ⊆ Z¹` and the inertia property `d a ∈ B_F → a ∈ A_F` (an
  unramified coboundary comes from an inertia invariant, tex L4561–4566), the genuine quotients
  `W₁ = side/strict`, `W₂ = relaxed/side` satisfy `H⁰(W₁) = 0`, and on the explicit `H¹` models
  `H¹(W₁) = B_F/d(A_F) → H¹(W_rel) = Z¹/dC⁰` is injective and its image is the kernel of
  `H¹(W_rel) → H¹(W₂) = Z¹/(B_F + dC⁰)` — the quasi-side facts `h0`, `hi`, `hpi`.

`ELLIOT`/`GLUE` (stated, not done here): the single-place assembly inside the global Selmer data
(`piCx` of the local conditions with the side condition at the switch place, the others retained),
and the transport of the explicit `H¹` models along `dblH1Iso` to `H1` of the induced chain maps;
the identification of `B_F/d(A_F)` with the finite plane `F ≅ k²` (`dim F = h¹_ur`, Derivative.lean)
and of `Z¹/(B_F + dC⁰)` with `S`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Limits ZInQ.Contrib.CloudB3RC53.GenuineInst

section Generic

variable {k : Type} [Field k] {A B : Type} [AddCommGroup A] [Module k A] [AddCommGroup B]
  [Module k B] (f : A →ₗ[k] B) (A' : Submodule k A) (B' : Submodule k B)
  (hf : A' ≤ B'.comap f)

/-- The quotient two-term map `A/A' → B/B'`. -/
def quotD : (A ⧸ A') →ₗ[k] (B ⧸ B') := A'.mapQ B' f hf

/-- **Quotients of two-term complexes** (tex L5072–5083, the local quotients `W`). `H⁰` of
`[A/A' → B/B']` vanishes when `f⁻¹(B') ⊆ A'`, and `H¹ ≃ B ⧸ (B' ⊔ f A)`. Classification: PROVED. -/
def QuotientTwoTerm : Prop :=
  ∀ (k : Type) [Field k] (A B : Type) [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (A' : Submodule k A) (B' : Submodule k B) (hf : A' ≤ B'.comap f),
    ((∀ a, f a ∈ B' → a ∈ A') → Subsingleton ((dblCx (quotD f A' B' hf)).homology 0)) ∧
    Nonempty (((dblCx (quotD f A' B' hf)).homology 1) ≃ₗ[k] (B ⧸ (B' ⊔ LinearMap.range f)))

theorem ker_quotD_eq_bot (h : ∀ a, f a ∈ B' → a ∈ A') : LinearMap.ker (quotD f A' B' hf) = ⊥ := by
  rw [quotD, Submodule.ker_mapQ, eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact h a ha

theorem range_quotD : LinearMap.range (quotD f A' B' hf) = (LinearMap.range f).map B'.mkQ := by
  rw [quotD, Submodule.range_mapQ]

theorem quotientTwoTerm_proof : QuotientTwoTerm := by
  intro k _ A B _ _ _ _ f A' B' hf
  refine ⟨fun h => ?_, ⟨?_⟩⟩
  · have e := (dblH0Iso (quotD f A' B' hf)).toLinearEquiv
    have hs : Subsingleton (LinearMap.ker (quotD f A' B' hf)) := by
      rw [ker_quotD_eq_bot f A' B' hf h]; infer_instance
    exact e.toEquiv.subsingleton
  · refine (dblH1Iso (quotD f A' B' hf)).toLinearEquiv ≪≫ₗ ?_
    rw [range_quotD]
    exact Submodule.quotientQuotientEquivQuotientSup B' (LinearMap.range f)

end Generic

section Genuine

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- `d⁰` kills the `0`-cocycles: `Z⁰ ⊆ (d⁰)⁻¹(0)`. -/
theorem Z0_le_comap_bot : GenuineInst.Z0 G M ≤ (⊥ : Submodule (ZMod 2) (GenuineInst.Z1 G M)).comap (relaxedD G M) := by
  intro a ha
  simp only [Submodule.mem_comap, Submodule.mem_bot]
  exact Subtype.ext ha

/-- `d⁰ a = 0` only for `a ∈ Z⁰`. -/
theorem relaxedD_eq_zero {a : (ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G M).X 0}
    (h : relaxedD G M a ∈ (⊥ : Submodule (ZMod 2) (GenuineInst.Z1 G M))) : a ∈ GenuineInst.Z0 G M := by
  rw [Submodule.mem_bot] at h
  exact LinearMap.mem_ker.mpr (congrArg Subtype.val h)

/-- The genuine relaxed quotient `W_rel = relaxed/strict = [C⁰/Z⁰ → Z¹]`. -/
abbrev wRelCx : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  dblCx (quotD (relaxedD G M) (GenuineInst.Z0 G M) ⊥ (Z0_le_comap_bot G M))

/-- **The genuine relaxed quotient is quasi-degree-one** (tex L5072–5074): `H⁰(W_rel) = 0` and
`H¹(W_rel) ≃ Z¹ ⧸ d⁰C⁰ ≃ H¹_cont(G, M)`. Classification: PROVED. -/
def RelaxedQuotientGenuine : Prop :=
  Subsingleton ((wRelCx G M).homology 0) ∧
    Nonempty (((wRelCx G M).homology 1) ≃+ TauCeti.ContCohomology.H1 G M)

theorem relaxedQuotientGenuine_proof : RelaxedQuotientGenuine G M := by
  obtain ⟨h0, ⟨e⟩⟩ := quotientTwoTerm_proof (ZMod 2) _ _ (relaxedD G M) (GenuineInst.Z0 G M) ⊥
    (Z0_le_comap_bot G M)
  refine ⟨h0 fun a ha => relaxedD_eq_zero G M ha, ⟨?_⟩⟩
  refine e.toAddEquiv.trans ?_
  rw [bot_sup_eq]
  exact z1QuotEquivH1 G M

/-- A side condition `[A_F → B_F]` inside the relaxed one (tex L5068–5072, `D⁰ ⊕ F[−1]`): submodules
`Z⁰ ⊆ A_F ⊆ C⁰`, `B_F ⊆ Z¹` with `d(A_F) ⊆ B_F`, and the inertia property `d a ∈ B_F → a ∈ A_F`. -/
structure SideCond where
  AF : Submodule (ZMod 2) ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G M).X 0)
  BF : Submodule (ZMod 2) (GenuineInst.Z1 G M)
  hZ0 : GenuineInst.Z0 G M ≤ AF
  hd : AF ≤ BF.comap (relaxedD G M)
  hcob : ∀ a, relaxedD G M a ∈ BF → a ∈ AF

variable {G M}

/-- `d⁰` restricted to the side: `A_F → B_F`. -/
def SideCond.dF (c : SideCond G M) : c.AF →ₗ[ZMod 2] c.BF :=
  ((relaxedD G M).domRestrict c.AF).codRestrict c.BF fun a => c.hd a.2

/-- `W₁ = side/strict = [A_F/Z⁰ → B_F]`. -/
abbrev SideCond.w1Cx (c : SideCond G M) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  dblCx (quotD c.dF ((GenuineInst.Z0 G M).comap c.AF.subtype) ⊥ (by
    intro a ha
    simp only [Submodule.mem_comap, Submodule.mem_bot, Submodule.coe_subtype] at ha ⊢
    exact Subtype.ext (Subtype.ext ha)))

/-- The explicit `H¹` model of `W₁`: `B_F ⧸ d(A_F)`. -/
abbrev SideCond.H1W1 (c : SideCond G M) : Type := c.BF ⧸ LinearMap.range c.dF

/-- The explicit `H¹` model of `W_rel`: `Z¹ ⧸ d(C⁰)`. -/
abbrev H1Wrel : Type := GenuineInst.Z1 G M ⧸ LinearMap.range (relaxedD G M)

/-- The explicit `H¹` model of `W₂ = relaxed/side`: `Z¹ ⧸ (B_F + d(C⁰))`. -/
abbrev SideCond.H1W2 (c : SideCond G M) : Type := GenuineInst.Z1 G M ⧸ (c.BF ⊔ LinearMap.range (relaxedD G M))

/-- `H¹(i) : H¹(W₁) → H¹(W_rel)`, induced by `B_F ⊆ Z¹`. -/
def SideCond.H1i (c : SideCond G M) : c.H1W1 →ₗ[ZMod 2] (H1Wrel (G := G) (M := M)) :=
  (LinearMap.range c.dF).mapQ (LinearMap.range (relaxedD G M)) c.BF.subtype (by
    rintro _ ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩)

/-- `H¹(p) : H¹(W_rel) → H¹(W₂)`, induced by the identity of `Z¹`. -/
def SideCond.H1p (c : SideCond G M) : (H1Wrel (G := G) (M := M)) →ₗ[ZMod 2] c.H1W2 :=
  (LinearMap.range (relaxedD G M)).mapQ _ LinearMap.id (fun x hx => Submodule.mem_sup_right hx)

/-- **The genuine side quotients** (tex L5072–5083): for a side condition, `H⁰(W₁) = 0`,
`H¹(W₁) ≃ B_F ⧸ d(A_F)`, and on the explicit `H¹` models `H¹(i)` is injective with image the kernel
of `H¹(p)` — the quasi-side facts `h0`, `hi`, `hpi`. Classification: PROVED. -/
def SideQuotientsGenuine (c : SideCond G M) : Prop :=
  Subsingleton (c.w1Cx.homology 0) ∧
    Nonempty ((c.w1Cx.homology 1) ≃ₗ[ZMod 2] c.H1W1) ∧
    Function.Injective c.H1i ∧ LinearMap.ker c.H1p = LinearMap.range c.H1i

theorem sideQuotientsGenuine_proof (c : SideCond G M) : SideQuotientsGenuine c := by
  obtain ⟨h0, ⟨e⟩⟩ := quotientTwoTerm_proof (ZMod 2) _ _ c.dF ((GenuineInst.Z0 G M).comap c.AF.subtype) ⊥
    (by
      intro a ha
      simp only [Submodule.mem_comap, Submodule.mem_bot, Submodule.coe_subtype] at ha ⊢
      exact Subtype.ext (Subtype.ext ha))
  refine ⟨h0 fun a ha => ?_, ⟨e ≪≫ₗ (by rw [bot_sup_eq])⟩, ?_, ?_⟩
  · rw [Submodule.mem_bot] at ha
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    exact relaxedD_eq_zero G M (by
      rw [Submodule.mem_bot]
      exact congrArg Subtype.val ha)
  · -- injectivity: an element of `B_F` that is a coboundary `d a` has `a ∈ A_F`
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H b =>
      rw [LinearMap.mem_ker, SideCond.H1i, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        at hx
      obtain ⟨a, ha⟩ := hx
      have haF : a ∈ c.AF := c.hcob a (by rw [ha]; exact b.2)
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨a, haF⟩, Subtype.ext ha⟩
  · ext x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [LinearMap.mem_ker, SideCond.H1p, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_sup]
      constructor
      · rintro ⟨b, hb, y, ⟨a, rfl⟩, hz⟩
        refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
        rw [SideCond.H1i, Submodule.mapQ_apply, Submodule.Quotient.eq]
        exact ⟨-a, by rw [map_neg, ← hz]; simp⟩
      · rintro ⟨x, hx⟩
        induction x using Submodule.Quotient.induction_on with
        | H b =>
          rw [SideCond.H1i, Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
          obtain ⟨a, ha⟩ := hx
          refine ⟨b.1, b.2, relaxedD G M (-a), ⟨-a, rfl⟩, ?_⟩
          rw [map_neg, ha]
          simp

/-- **Non-vacuity** (non-vacuity): the relaxed condition itself is a side condition (`A_F = C⁰`,
`B_F = Z¹`), for every genuine `G`, `M`; its side quotients satisfy `SideQuotientsGenuine`. -/
def relaxedSide (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M] [SMulCommClass G (ZMod 2) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] : SideCond G M where
  AF := ⊤
  BF := ⊤
  hZ0 := le_top
  hd := fun _ _ => Submodule.mem_top
  hcob := fun _ _ => Submodule.mem_top

/-- The strict condition is also a side condition (`A_F = Z⁰`, `B_F = 0`). -/
def strictSide (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M] [SMulCommClass G (ZMod 2) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] : SideCond G M where
  AF := GenuineInst.Z0 G M
  BF := ⊥
  hZ0 := le_rfl
  hd := Z0_le_comap_bot G M
  hcob := fun a ha => relaxedD_eq_zero G M ha

open NumberField IsDedekindDomain in
/-- The genuine instance: `G = G_{ℚ,∅}` with the trivial `𝔽₂`-module. -/
theorem sideQuotients_nonvacuous :
    let G := ZInQ.Manuscript.RC.SelmerComplex.GKS ℚ (∅ : Set (HeightOneSpectrum (𝓞 ℚ)))
    let M := ZInQ.Manuscript.RC.SelmerComplex.TrivMod G (ZMod 2)
    SideQuotientsGenuine (relaxedSide G M) ∧ SideQuotientsGenuine (strictSide G M) ∧
      RelaxedQuotientGenuine G M :=
  ⟨sideQuotientsGenuine_proof _, sideQuotientsGenuine_proof _,
    relaxedQuotientGenuine_proof _ _⟩

end Genuine

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
