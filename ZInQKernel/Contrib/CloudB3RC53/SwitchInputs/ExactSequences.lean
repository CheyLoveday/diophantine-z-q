import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange
import ZInQKernel.Contrib.OneProof.RC.Uniform.Switch

/-!
# RC53 SwitchInputs: the switch exact sequences (5.5a)

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L5055–5086:

> At the new prime let `C_str` and `C_rel` have the actual truncated conditions `D⁰` and
> `D⁰ ⊕ (F ⊕ S)[−1]`. Put `U = im(H¹(C_rel ⊗ k) → F ⊕ S)`, `K₀ = H¹(C_str ⊗ k)`. [...] The cone
> triangles, with `D⁰` retained, give exact sequences
> `0 → K₀ → V → U ∩ F → 0`, `0 → K₀ → V' → U ∩ S → 0`   (5.5a)
> where `V'` is the switched fiber cohomology. There is no preceding local degree-zero term, since
> the quotient conditions are `F[−1]` and `S[−1]`.

and the nonquadratic case, tex L4997–5003: "The finite localization then has rank two. Exact duality
makes the relaxed localization image equal to the finite plane, so switching to the singular plane
lowers `s` by two."

Everything is over an arbitrary field `k` (the residue field of `R = Λ_𝔭`; the complexes are the
fibers `C ⊗_R k`).

Nodes:
* `DimsOfExact` (PROVED, linear algebra): from the cohomology-level exactness of the two cone
  triangles, `dim V = dim K₀ + dim (U ∩ F)`, with `U ∩ F` computed inside the localization target.
* `SignDimsOfExact` (PROVED, quadratic case, tex L5046–5054, L5083–5086): with compatible
  involutions on all terms and `2 ≠ 0`, the same equation on each sign part (the shape of the
  `hVp`/`hVm`/`hVp'`/`hVm'` fields of the quadratic switch data, before the identification of the
  sign parts of `F ⊕ S` with the axes of `H_±`).
* `SwitchDimsOfSES` (PROVED): the same from the two short exact sequences of complexes
  `0 → C_str → C_F → W_F → 0` (local quotient condition `F[−1]`) and `0 → C_F → C_rel → W_S → 0`,
  via Mathlib's homology long exact sequence; the cohomology of the quotient conditions enters only
  through the stated local hypotheses (`H⁰(W_F) = 0`; `H¹(W_F) → H¹(W_rel) → H¹(W_S)` exact with the
  first map injective). These short exact sequences are those of `RelaxedQuotientNode`
  (`SelmerDuality/SupportChange.lean`) for the inclusions `D⁰ ⊂ D⁰ ⊕ F[−1] ⊂ D⁰ ⊕ (F ⊕ S)[−1]`.
* `SwitchDimsPlanes` (PROVED): transported to `F ⊕ S = k² × k²` by an identification of `H¹(W_rel)`
  under which `H¹(W_F)` is the finite plane and `H¹(W_S)` the singular plane: the fields `hs`, `hs'`
  of the nonquadratic switch data (`NonquadDims` of the UniformSwitch files), with
  `k₀ = dim K₀`.
* `RelaxedImageFinite` (PROVED from the duality input): if `U = U^⊥` for the switch pairing
  (`LocalizationDualityInput`, GLUE: Nekovář 6.3.3–6.3.4, as cited at tex L5068–5072) and the finite
  localization has rank two (`U ∩ F = F`, rank-two detection), then `U = F` (the field `hU`).
* `NonquadSwitchDims` and `nonquadSwitchDims_of_ses`: the full nonquadratic switch data, with the
  drop `s' + 2 = s`.
-/

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform

universe u

/-! ### Linear algebra of the two cone triangles -/

section LinAlg

variable {k : Type*} [Field k] {K₀ V Vr M N Q : Type*}
  [AddCommGroup K₀] [Module k K₀] [AddCommGroup V] [Module k V] [AddCommGroup Vr] [Module k Vr]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q]

/-- The localization image of `V` is `U ∩ A` (`U = im λ`, `A = im ι`). -/
theorem map_range_eq_inf (β : V →ₗ[k] N) (γ : V →ₗ[k] Vr) (lam : Vr →ₗ[k] M) (ι : N →ₗ[k] M)
    (π : M →ₗ[k] Q) (hγ : LinearMap.range γ = LinearMap.ker (π ∘ₗ lam))
    (hcomm : lam ∘ₗ γ = ι ∘ₗ β) (_hι : Function.Injective ι)
    (hιπ : LinearMap.ker π = LinearMap.range ι) :
    (LinearMap.range β).map ι = LinearMap.range lam ⊓ LinearMap.range ι := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨⟨γ v, ?_⟩, ⟨β v, rfl⟩⟩
    exact (LinearMap.congr_fun hcomm v)
  · rintro m ⟨⟨r, rfl⟩, ⟨n, hn⟩⟩
    have hr : r ∈ LinearMap.ker (π ∘ₗ lam) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ← hn]
      have : ι n ∈ LinearMap.ker π := by rw [hιπ]; exact ⟨n, rfl⟩
      exact this
    rw [← hγ] at hr
    obtain ⟨v, rfl⟩ := hr
    have h1 : ι (β v) = ι n := by
      rw [hn, ← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply]
    exact ⟨β v, ⟨v, rfl⟩, by rw [h1, hn]⟩

/-- **(5.5a), linear algebra** (tex L5076–5083). Let `α : K₀ → V` be injective with image the kernel
of the finite localization `β : V → N`, let `γ : V → V_rel` (the comparison) have image the kernel of
`π ∘ λ`, where `λ : V_rel → M` is the relaxed localization, `ι : N → M` is injective with image
`ker π`, and `λ γ = ι β`. Then `dim V = dim K₀ + dim (im λ ∩ im ι)`. Classification: PROVED. -/
def DimsOfExact : Prop :=
  ∀ (k : Type u) [Field k] (K₀ V Vr M N Q : Type u)
    [AddCommGroup K₀] [Module k K₀] [AddCommGroup V] [Module k V] [AddCommGroup Vr] [Module k Vr]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q]
    [FiniteDimensional k V] [FiniteDimensional k M]
    (α : K₀ →ₗ[k] V) (β : V →ₗ[k] N) (γ : V →ₗ[k] Vr) (lam : Vr →ₗ[k] M) (ι : N →ₗ[k] M)
    (π : M →ₗ[k] Q),
    Function.Injective α → LinearMap.range α = LinearMap.ker β →
    LinearMap.range γ = LinearMap.ker (π ∘ₗ lam) → lam ∘ₗ γ = ι ∘ₗ β →
    Function.Injective ι → LinearMap.ker π = LinearMap.range ι →
      finrank k V = finrank k K₀ + finrank k ↥(LinearMap.range lam ⊓ LinearMap.range ι)

theorem dimsOfExact_proof : DimsOfExact.{u} := by
  intro k _ K₀ V Vr M N Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ α β γ lam ι π hα hαβ hγ hcomm hι hιπ
  have hK : finrank k K₀ = finrank k ↥(LinearMap.ker β) := by
    rw [← hαβ]
    exact (LinearEquiv.ofInjective α hα).finrank_eq
  have hR : finrank k ↥(LinearMap.range β) =
      finrank k ↥(LinearMap.range lam ⊓ LinearMap.range ι) := by
    rw [← map_range_eq_inf β γ lam ι π hγ hcomm hι hιπ]
    exact (Submodule.equivMapOfInjective ι hι _).finrank_eq
  have := LinearMap.finrank_range_add_finrank_ker β
  omega

end LinAlg

/-! ### Sign parts (quadratic case) -/

section Signs

variable {k : Type u} [Field k]

/-- The sign part `{x | σ x = ε x}` of an endomorphism `σ` (`ε = ±1`). -/
def signPart {X : Type u} [AddCommGroup X] [Module k X] (σ : X →ₗ[k] X) (ε : k) : Submodule k X :=
  LinearMap.ker (σ - ε • LinearMap.id)

theorem mem_signPart {X : Type u} [AddCommGroup X] [Module k X] {σ : X →ₗ[k] X} {ε : k} {x : X} :
    x ∈ signPart σ ε ↔ σ x = ε • x := by
  simp [signPart, sub_eq_zero]

theorem map_mem_signPart {X Y : Type u} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    {σ : X →ₗ[k] X} {τ : Y →ₗ[k] Y} {ε : k} (f : X →ₗ[k] Y) (hf : f ∘ₗ σ = τ ∘ₗ f) {x : X}
    (hx : x ∈ signPart σ ε) : f x ∈ signPart τ ε := by
  rw [mem_signPart] at hx ⊢
  rw [← LinearMap.comp_apply, ← hf, LinearMap.comp_apply, hx, map_smul]

/-- The projection `x ↦ (x + ε σ x)/2` onto the sign part of an involution (`ε² = 1`, `2 ≠ 0`). -/
theorem proj_mem_signPart {X : Type u} [AddCommGroup X] [Module k X] {σ : X →ₗ[k] X}
    (hσ : σ ∘ₗ σ = LinearMap.id) {ε : k} (hε : ε * ε = 1) (x : X) :
    ((2 : k)⁻¹ • (x + ε • σ x)) ∈ signPart σ ε := by
  rw [mem_signPart, map_smul, map_add, map_smul]
  have : σ (σ x) = x := by rw [← LinearMap.comp_apply, hσ, LinearMap.id_apply]
  rw [this]
  linear_combination (norm := module) (-(2 : k)⁻¹) • hε • σ x

theorem proj_eq_self {X : Type u} [AddCommGroup X] [Module k X] {σ : X →ₗ[k] X} {ε : k}
    (h2 : (2 : k) ≠ 0) (hε : ε * ε = 1) {x : X} (hx : x ∈ signPart σ ε) :
    (2 : k)⁻¹ • (x + ε • σ x) = x := by
  rw [mem_signPart] at hx
  rw [hx, smul_smul, hε, one_smul, ← two_smul k x, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- **(5.5a) on the sign parts** (tex L5046–5054, L5083–5086: "The space `U` is stable under
signs"). If involutions act compatibly on all terms of the data of `DimsOfExact` and `2 ≠ 0`, the
same dimension equation holds on the `ε`-parts (`ε = ±1`): `dim V_ε = dim K₀_ε + dim (U_ε ∩ F_ε)`,
with `U_ε = λ(V_rel,ε)`, `F_ε = ι(N_ε)`. Classification: PROVED. -/
def SignDimsOfExact : Prop :=
  ∀ (k : Type u) [Field k] (K₀ V Vr M N Q : Type u)
    [AddCommGroup K₀] [Module k K₀] [AddCommGroup V] [Module k V] [AddCommGroup Vr] [Module k Vr]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q]
    [FiniteDimensional k V] [FiniteDimensional k M]
    (α : K₀ →ₗ[k] V) (β : V →ₗ[k] N) (γ : V →ₗ[k] Vr) (lam : Vr →ₗ[k] M) (ι : N →ₗ[k] M)
    (π : M →ₗ[k] Q)
    (σK : K₀ →ₗ[k] K₀) (σV : V →ₗ[k] V) (σr : Vr →ₗ[k] Vr) (σM : M →ₗ[k] M) (σN : N →ₗ[k] N)
    (σQ : Q →ₗ[k] Q) (ε : k),
    (2 : k) ≠ 0 → ε * ε = 1 →
    σK ∘ₗ σK = LinearMap.id → σV ∘ₗ σV = LinearMap.id → σr ∘ₗ σr = LinearMap.id →
    σM ∘ₗ σM = LinearMap.id → σN ∘ₗ σN = LinearMap.id →
    α ∘ₗ σK = σV ∘ₗ α → β ∘ₗ σV = σN ∘ₗ β → γ ∘ₗ σV = σr ∘ₗ γ → lam ∘ₗ σr = σM ∘ₗ lam →
    ι ∘ₗ σN = σM ∘ₗ ι → π ∘ₗ σM = σQ ∘ₗ π →
    Function.Injective α → LinearMap.range α = LinearMap.ker β →
    LinearMap.range γ = LinearMap.ker (π ∘ₗ lam) → lam ∘ₗ γ = ι ∘ₗ β →
    Function.Injective ι → LinearMap.ker π = LinearMap.range ι →
      finrank k ↥(signPart σV ε) = finrank k ↥(signPart σK ε) +
        finrank k ↥((signPart σr ε).map lam ⊓ (signPart σN ε).map ι)

theorem signDimsOfExact_proof : SignDimsOfExact.{u} := by
  intro k _ K₀ V Vr M N Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ α β γ lam ι π σK σV σr σM σN σQ ε h2 hε
    hK hV hr hM hN hα' hβ' hγ' hl' hι' hπ' hα hαβ hγ hcomm hι hιπ
  -- restrictions to the sign parts
  let αε := α.restrict (p := signPart σK ε) (q := signPart σV ε) fun x hx => map_mem_signPart α hα' hx
  let βε := β.restrict (p := signPart σV ε) (q := signPart σN ε) fun x hx => map_mem_signPart β hβ' hx
  let γε := γ.restrict (p := signPart σV ε) (q := signPart σr ε) fun x hx => map_mem_signPart γ hγ' hx
  let lε := lam.restrict (p := signPart σr ε) (q := signPart σM ε) fun x hx => map_mem_signPart lam hl' hx
  let ιε := ι.restrict (p := signPart σN ε) (q := signPart σM ε) fun x hx => map_mem_signPart ι hι' hx
  let πε := π.restrict (p := signPart σM ε) (q := signPart σQ ε) fun x hx => map_mem_signPart π hπ' hx
  have key := dimsOfExact_proof k _ _ _ _ _ _ αε βε γε lε ιε πε ?_ ?_ ?_ ?_ ?_ ?_
  · rw [key]
    congr 1
    -- `im lε ⊓ im ιε` inside `M_ε` corresponds to `λ(Vr_ε) ⊓ ι(N_ε)` inside `M`
    have hmap : (LinearMap.range lε ⊓ LinearMap.range ιε).map (signPart σM ε).subtype =
        (signPart σr ε).map lam ⊓ (signPart σN ε).map ι := by
      rw [Submodule.map_inf _ (signPart σM ε).injective_subtype]
      congr 1
      · ext m; constructor
        · rintro ⟨_, ⟨r, rfl⟩, rfl⟩; exact ⟨r.1, r.2, rfl⟩
        · rintro ⟨r, hr, rfl⟩; exact ⟨⟨lam r, map_mem_signPart lam hl' hr⟩, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
      · ext m; constructor
        · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n.1, n.2, rfl⟩
        · rintro ⟨n, hn, rfl⟩; exact ⟨⟨ι n, map_mem_signPart ι hι' hn⟩, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _ (signPart σM ε).injective_subtype _).finrank_eq
  · intro x y h
    exact Subtype.ext (hα (congrArg Subtype.val h))
  · ext ⟨v, hv⟩
    constructor
    · rintro ⟨x, hx⟩
      have hv' : α x.1 = v := congrArg Subtype.val hx
      have h := (hαβ ▸ (LinearMap.mem_range_self α x.1) : α x.1 ∈ LinearMap.ker β)
      rw [hv'] at h
      exact Subtype.ext (LinearMap.mem_ker.mp h)
    · intro hb
      have hb' : v ∈ LinearMap.ker β := congrArg Subtype.val hb
      rw [← hαβ] at hb'
      obtain ⟨x, hx⟩ := hb'
      refine ⟨⟨(2 : k)⁻¹ • (x + ε • σK x), proj_mem_signPart hK hε x⟩, Subtype.ext ?_⟩
      change α ((2 : k)⁻¹ • (x + ε • σK x)) = v
      rw [map_smul, map_add, map_smul, ← LinearMap.comp_apply α σK, hα', LinearMap.comp_apply, hx]
      exact proj_eq_self h2 hε hv
  · ext ⟨v, hv⟩
    constructor
    · rintro ⟨x, hx⟩
      have hv' : γ x.1 = v := congrArg Subtype.val hx
      have h := (hγ ▸ (LinearMap.mem_range_self γ x.1) : γ x.1 ∈ LinearMap.ker (π ∘ₗ lam))
      rw [hv'] at h
      exact Subtype.ext (LinearMap.mem_ker.mp h)
    · intro hb
      have hb' : v ∈ LinearMap.ker (π ∘ₗ lam) := congrArg Subtype.val hb
      rw [← hγ] at hb'
      obtain ⟨x, hx⟩ := hb'
      refine ⟨⟨(2 : k)⁻¹ • (x + ε • σV x), proj_mem_signPart hV hε x⟩, Subtype.ext ?_⟩
      change γ ((2 : k)⁻¹ • (x + ε • σV x)) = v
      rw [map_smul, map_add, map_smul, ← LinearMap.comp_apply γ σV, hγ', LinearMap.comp_apply, hx]
      exact proj_eq_self h2 hε hv
  · ext x
    exact congrArg Subtype.val (show _ from Subtype.ext (LinearMap.congr_fun hcomm x.1))
  · intro x y h
    exact Subtype.ext (hι (congrArg Subtype.val h))
  · ext ⟨m, hm⟩
    constructor
    · intro hb
      have hb' : m ∈ LinearMap.ker π := congrArg Subtype.val hb
      rw [hιπ] at hb'
      obtain ⟨n, hn⟩ := hb'
      refine ⟨⟨(2 : k)⁻¹ • (n + ε • σN n), proj_mem_signPart hN hε n⟩, Subtype.ext ?_⟩
      change ι ((2 : k)⁻¹ • (n + ε • σN n)) = m
      rw [map_smul, map_add, map_smul, ← LinearMap.comp_apply ι σN, hι', LinearMap.comp_apply, hn]
      exact proj_eq_self h2 hε hm
    · rintro ⟨n, hn⟩
      have h : ι n.1 ∈ LinearMap.ker π := by rw [hιπ]; exact ⟨n.1, rfl⟩
      have hm' : ι n.1 = m := congrArg Subtype.val hn
      refine Subtype.ext ?_
      change π m = 0
      rw [← hm']
      exact LinearMap.mem_ker.mp h

end Signs

/-! ### From the short exact sequences of Selmer complexes -/

section SES

variable {k : Type u} [Field k]

/-- **(5.5a) from the cone triangles** (tex L5055–5086). Over a field `k`, let
`0 → C_str --a--> C_F --b--> W_F → 0` and `0 → C_F --c--> C_rel --e--> W_S → 0` be short exact
sequences of cochain complexes (the change of local conditions `D⁰ ⊂ D⁰ ⊕ F[−1] ⊂ D⁰ ⊕ (F ⊕ S)[−1]`,
`RelaxedQuotientNode`), let `λ : C_rel → W_rel` be the relaxed localization (quotient by `D⁰`) and
`i : W_F → W_rel`, `p : W_rel → W_S` the maps of the local quotient conditions, with `c λ = b i` and
`λ p = e`. Assume the local facts `H⁰(W_F) = 0`, `H¹(i)` injective and `ker H¹(p) = im H¹(i)`. Then,
with `V = H¹(C_F)`, `K₀ = H¹(C_str)`, `U = im H¹(λ)` and `F = im H¹(i)`,
`dim V = dim K₀ + dim (U ∩ F)`. Classification: PROVED. -/
def SwitchDimsOfSES : Prop :=
  ∀ (k : Type u) [Field k] (Cs Cf Cr Wf Ws Wr : CochainComplex (ModuleCat.{u} k) ℤ)
    (a : Cs ⟶ Cf) (b : Cf ⟶ Wf) (c : Cf ⟶ Cr) (e : Cr ⟶ Ws) (lam : Cr ⟶ Wr) (i : Wf ⟶ Wr)
    (p : Wr ⟶ Ws) (hab : a ≫ b = 0) (hce : c ≫ e = 0),
    (ShortComplex.mk a b hab).ShortExact → (ShortComplex.mk c e hce).ShortExact →
    c ≫ lam = b ≫ i → lam ≫ p = e →
    Subsingleton (Wf.homology 0) →
    Function.Injective (HomologicalComplex.homologyMap i 1).hom →
    LinearMap.ker (HomologicalComplex.homologyMap p 1).hom =
      LinearMap.range (HomologicalComplex.homologyMap i 1).hom →
    FiniteDimensional k (Cf.homology 1) → FiniteDimensional k (Wr.homology 1) →
      finrank k (Cf.homology 1) = finrank k (Cs.homology 1) +
        finrank k ↥(LinearMap.range (HomologicalComplex.homologyMap lam 1).hom ⊓
          LinearMap.range (HomologicalComplex.homologyMap i 1).hom)

theorem switchDimsOfSES_proof : SwitchDimsOfSES.{u} := by
  intro k _ Cs Cf Cr Wf Ws Wr a b c e lam i p hab hce h1 h2 hcomm hfac hW0 hi hpi _ _
  -- exactness at `H¹(C_F)` and injectivity of `H¹(a)`
  have ex1 := (h1.homology_exact₂ 1).moduleCat_range_eq_ker
  have mono1 : Mono (HomologicalComplex.homologyMap a 1) :=
    (h1.homology_exact₁ 0 1 (by simp)).mono_g
      ((@Limits.IsZero.of_iso _ _ _ _ (ModuleCat.isZero_of_subsingleton _) (Iso.refl _)).eq_of_src
        _ _)
  have hinj : Function.Injective (HomologicalComplex.homologyMap a 1).hom :=
    (ModuleCat.mono_iff_injective _).mp mono1
  -- exactness at `H¹(C_rel)`
  have ex2 := (h2.homology_exact₂ 1).moduleCat_range_eq_ker
  have hγ : LinearMap.range (HomologicalComplex.homologyMap c 1).hom =
      LinearMap.ker ((HomologicalComplex.homologyMap p 1).hom ∘ₗ
        (HomologicalComplex.homologyMap lam 1).hom) := by
    have : (HomologicalComplex.homologyMap p 1).hom ∘ₗ (HomologicalComplex.homologyMap lam 1).hom =
        (HomologicalComplex.homologyMap e 1).hom := by
      rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp, hfac]
    rw [this]; exact ex2
  have hc : (HomologicalComplex.homologyMap lam 1).hom ∘ₗ (HomologicalComplex.homologyMap c 1).hom =
      (HomologicalComplex.homologyMap i 1).hom ∘ₗ (HomologicalComplex.homologyMap b 1).hom := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, hcomm]
  exact dimsOfExact_proof k _ _ _ _ _ _ _ _ _ _ _ _ hinj ex1 hγ hc hi hpi

end SES

/-! ### The finite and singular planes -/

/-- **(5.5a) in the planes `F ⊕ S = k² × k²`** (tex L5076–5083, the fields `hs`, `hs'` of the
nonquadratic switch data). Given an identification `ε : H¹(W_rel) ≃ k² × k²` carrying the image of
`H¹(W_F)` to the finite plane and the image of `H¹(W_S)` (its complement) to the singular plane,
and `U := ε(im H¹(λ))`, the dimension equation of `SwitchDimsOfSES` reads
`dim V = dim K₀ + dim (U ∩ F)`; symmetrically for the switched cohomology `V'` and `U ∩ S`.
Classification: PROVED. -/
def SwitchDimsPlanes : Prop :=
  ∀ (k : Type) [Field k] (Wr : Type) [AddCommGroup Wr] [Module k Wr]
    (εW : Wr ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (U A : Submodule k Wr) (V K₀ : ℕ),
    A.map εW.toLinearMap = finPlane k (Fin 2 → k) (Fin 2 → k) →
    V = K₀ + finrank k ↥(U ⊓ A) →
    V = K₀ + finrank k ↥(U.map εW.toLinearMap ⊓ finPlane k (Fin 2 → k) (Fin 2 → k))

theorem switchDimsPlanes_proof : SwitchDimsPlanes := by
  intro k _ Wr _ _ εW U A V K₀ hA hV
  rw [hV, ← hA, ← Submodule.map_inf _ εW.injective]
  congr 1
  exact (Submodule.equivMapOfInjective _ εW.injective _).finrank_eq

/-! ### The relaxed image is the finite plane (nonquadratic case) -/

/-- **GLUE input: localization duality** (Nekovář, *Selmer complexes*, 6.3.3–6.3.4, as cited at tex
L5068–5072 and L4893–4898): the relaxed localization image is its own annihilator for the transported
local switch pairing `β(x, y) = ε e₂(x, J y)` on `F ⊕ S`. The hypotheses expressible here are in the
type: `ε, σ ≠ 0`, `J² = 1`. Classification: GLUE (assumed input). -/
def LocalizationDualityInput {k : Type} [Field k] (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (_hε : ε ≠ 0) (_hσ : σ ≠ 0) (_hJ2 : J * J = 1)
    (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))) : Prop :=
  (switchPairing ε σ J).orthogonal U = U

/-- **The relaxed image is the finite plane** (tex L4997–5003): if `U = U^⊥`
(`LocalizationDualityInput`) and the finite localization has rank two (`F ≤ U`, rank-two detection
of Lemma `ex:limits-kernel-detection`), then `U = F`. Classification: PROVED (from the input). -/
def RelaxedImageFinite : Prop :=
  ∀ (k : Type) [Field k] (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))),
    LocalizationDualityInput ε σ J hε hσ hJ2 U →
    finPlane k (Fin 2 → k) (Fin 2 → k) ≤ U →
      U = finPlane k (Fin 2 → k) (Fin 2 → k)

theorem finrank_finPlane {k : Type} [Field k] :
    finrank k ↥(finPlane k (Fin 2 → k) (Fin 2 → k)) = 2 := by
  have e : ↥(finPlane k (Fin 2 → k) (Fin 2 → k)) ≃ₗ[k] (Fin 2 → k) :=
    { toFun := fun z => z.1.1
      invFun := fun x => ⟨(x, 0), (mem_finPlane).2 rfl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun z => by
        apply Subtype.ext
        exact Prod.ext rfl ((mem_finPlane).1 z.2).symm
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_fin_fun]

theorem relaxedImageFinite_proof : RelaxedImageFinite := by
  intro k _ ε σ J hε hσ hJ2 U hU hF
  refine (Submodule.eq_of_le_of_finrank_eq hF ?_).symm
  rw [finrank_finPlane, lagrangian_finrank_eq_two hε hσ hJ2 U hU]

/-! ### The nonquadratic switch data -/

/-- The nonquadratic switch data, with the fields of `NonquadDims` of the UniformSwitch files (that
file is not in this base; the fields are copied verbatim). -/
structure NonquadSwitchDims (k : Type) [Field k] (s s' : ℕ) where
  U : Submodule k ((Fin 2 → k) × (Fin 2 → k))
  hU : U = finPlane k (Fin 2 → k) (Fin 2 → k)
  k0 : ℕ
  hs : s = k0 + finrank k ↥(U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k))
  hs' : s' = k0 + finrank k ↥(U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k))

theorem finPlane_inf_singPlane' {k : Type} [Field k] :
    finPlane k (Fin 2 → k) (Fin 2 → k) ⊓ singPlane k (Fin 2 → k) (Fin 2 → k) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hz
  rw [mem_finPlane] at h1
  rw [mem_singPlane] at h2
  rw [Submodule.mem_bot]
  exact Prod.ext h2 h1

/-- The drop of the nonquadratic switch: `s' + 2 = s`. PROVED. -/
theorem NonquadSwitchDims.drop {k : Type} [Field k] {s s' : ℕ} (X : NonquadSwitchDims k s s') :
    s' + 2 = s := by
  have h1 := X.hs
  have h2 := X.hs'
  rw [X.hU, inf_idem, finrank_finPlane] at h1
  rw [X.hU, finPlane_inf_singPlane', finrank_bot] at h2
  omega

/-- **The nonquadratic switch data from the cone triangles and duality** (tex L4997–5003,
L5055–5086). Given the cohomology dimensions `s = dim V`, `s' = dim V'`, `k₀ = dim K₀` and the
relaxed image `U ⊆ F ⊕ S` with the two (5.5a) equations, the localization duality input and rank-two
detection (`F ≤ U`), the nonquadratic switch data exist, so `s' + 2 = s`. Classification: PROVED (from
the duality input). -/
def nonquadSwitchDims_of_inputs {k : Type} [Field k] (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (s s' k₀ : ℕ) (hdual : LocalizationDualityInput ε σ J hε hσ hJ2 U)
    (hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ U)
    (hs : s = k₀ + finrank k ↥(U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k)))
    (hs' : s' = k₀ + finrank k ↥(U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k))) :
    NonquadSwitchDims k s s' :=
  ⟨U, relaxedImageFinite_proof k ε σ J hε hσ hJ2 U hdual hdet, k₀, hs, hs'⟩

/-- Non-vacuity: `U = F` with `k₀ = 0` gives nonquadratic switch data with `s = 2`, `s' = 0`.
PROVED. -/
theorem nonquad_example {k : Type} [Field k] :
    ∃ X : NonquadSwitchDims k 2 0, X.U = finPlane k (Fin 2 → k) (Fin 2 → k) := by
  refine ⟨⟨finPlane k _ _, rfl, 0, ?_, ?_⟩, rfl⟩
  · rw [inf_idem, finrank_finPlane]
  · rw [finPlane_inf_singPlane', finrank_bot]

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
