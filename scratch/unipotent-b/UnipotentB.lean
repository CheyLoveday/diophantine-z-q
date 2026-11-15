import ZInQKernel.OneProof.H.TailZ14

/-!
# unipotent-b: SGA 7 I Exp. IX Prop. 3.5 in printed form over a strictly henselian trait

Task unipotent-b (2026-11-14). The field `semistableUnipotent : ReductSplit.SemistableUnipotent`
(`ZInQKernel/OneProof/H/TailZ7.lean`), its strictly henselian form `ReductGlue.SemistableUnipotentSH`
and the leaf `ReductGlue.StrictHenselizationInside` (`ZInQKernel/OneProof/H/TailZ14.lean`) are
imported; §0 copies them verbatim and checks the copies by `rfl`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open ReductSplit ReductGlue ZInQ.HeightSplit

set_option linter.style.haveILetI false

namespace UnipotentB

/-! ## §0. Verbatim copies of the three Props (checked by `rfl`) -/

/-- verbatim copy of `ReductSplit.SemistableUnipotent` -/
def SemistableUnipotentCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

example : SemistableUnipotentCopy = ReductSplit.SemistableUnipotent := rfl

/-- verbatim copy of `ReductGlue.SemistableUnipotentSH` -/
def SemistableUnipotentSHCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

example : SemistableUnipotentSHCopy = ReductGlue.SemistableUnipotentSH := rfl

/-- verbatim copy of `ReductGlue.StrictHenselizationInside` -/
def StrictHenselizationInsideCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHNeronExt O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

example : StrictHenselizationInsideCopy = ReductGlue.StrictHenselizationInside := rfl

/-! ## §1. Semistability over the residue field `k(s)` (SGA 7 IX Déf. 2.2/3.1 as printed) -/

section ResFibre

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}

/-- `Spec k(s) → Spec O`. -/
abbrev sRes (O : ValuationSubring K) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O)))

/-- The special fibre `𝒩 ×_O k(s)` over the residue field itself (not its algebraic closure). -/
def specialFibre (𝒩 : GroupModelO A O) : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) :=
  (Over.pullback (sRes O)).obj 𝒩.G

instance (𝒩 : GroupModelO A O) : GrpObj (specialFibre 𝒩) := Functor.grpObjObj

/-- **Semistable special fibre over `k(s)`** (SGA 7 IX Déf. 2.2 and 3.1 read over the residue field
`k(s)`, as printed; locators UNVERIFIED): the identity component of `𝒩 ×_O k(s)` is an extension of
an abelian variety by a split torus (`HasSemiAbelianIdentityComponent`). Over a separably closed
`k(s)` every torus is split. -/
def IsSemistableRes (𝒩 : GroupModelO A O) : Prop :=
  HasSemiAbelianIdentityComponent (specialFibre 𝒩)

/-- `A` has semistable reduction at `O` in the printed sense: a Néron model whose special fibre over
`k(s)` is semistable. -/
def HasSemistableReductionRes (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel ∧ IsSemistableRes 𝒩

/-- For an algebraically closed residue field, `k(s) → κ̄` is an isomorphism. -/
def resBarEquiv (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)] :
    IsLocalRing.ResidueField O ≃+* ResBarO O :=
  RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField O) (ResBarO O))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem spec_resBarEquiv_comp (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)] :
    Spec.map (CommRingCat.ofHom ((resBarEquiv O : _ ≃+* _) : _ →+* _)) ≫ sRes O =
      Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **For an algebraically closed residue field, semistability over `k(s)` and over `κ̄` agree**
(fibre identification `κ̄ ≅ k(s)` + `semiAbelianFieldIsoInvariant`). -/
theorem isSemistableRes_iff (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)]
    (𝒩 : GroupModelO A O) : IsSemistableRes 𝒩 ↔ 𝒩.IsSemistable := by
  unfold IsSemistableRes GroupModelO.IsSemistable
  rw [semiAbelianFieldIsoInvariant _ _ (resBarEquiv O) (specialFibre 𝒩)]
  let E := pbCompIso _ _ _ (spec_resBarEquiv_comp O) (Grp.mk 𝒩.G)
  exact ⟨fun h => @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre 𝒩) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h,
    fun h => @hasSemiAbelian_of_iso _ _ (geomSpecialFibre 𝒩) _ _ Functor.grpObjObj
      (isoX E.symm) (inferInstanceAs (IsMonHom E.inv.hom.hom)) h⟩

theorem hasSemistableReductionRes_iff (O : ValuationSubring K)
    [IsAlgClosed (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K) :
    HasSemistableReductionRes A O ↔ HasSemistableReduction A O :=
  ⟨fun ⟨𝒩, h1, h2⟩ => ⟨𝒩, h1, (isSemistableRes_iff O 𝒩).mp h2⟩,
    fun ⟨𝒩, h1, h2⟩ => ⟨𝒩, h1, (isSemistableRes_iff O 𝒩).mpr h2⟩⟩

end ResFibre

/-! ## §2. The printed statement (leaf) and the strictly henselian field -/

/-- `I` acts unipotently on `T_ℓ`: every `σ ∈ I` has `σ - 1` nilpotent on `T_ℓ(A)`. -/
def InertiaUnipotent {K : Type} [Field K] (A : PkgI3.AbVar K) {Ω : Type} [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∃ n : ℕ, (galTΩ A ℓ σ - 1) ^ n = 0

/-- **LEAF (printed form) `SemistableUnipotentPrinted`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5;
the number and the exact wording are from memory, **UNVERIFIED**; no network on this host). Setting
of SGA 7 IX §3 as printed: `O` a strictly henselian discrete valuation ring (a strictly local trait
`S`) with fraction field `K`, `K^s = Ω` a separable closure of `K`, `I` the inertia group (here,
`O` strictly henselian, `I = Gal(K^s/K)`; it is stated with the inertia group of the valuation `w`
of `Ω` over `O`, which is the unique one), `ℓ` a prime different from the residue characteristic,
`T_ℓ(A) = lim A(K^s)[ℓⁿ]`. Semistable reduction is read over the residue field `k(s)` itself
(`HasSemistableReductionRes`). Statement: `A` has semistable reduction iff `I` acts unipotently on
`T_ℓ(A)`, and in that case unipotently of echelon `≤ 2`: `(σ - 1)(τ - 1) = 0` on `T_ℓ(A)` for all
`σ, τ ∈ I`.

Restriction to `[CharZero K]` and `[PerfectField k(s)]` (so the leaf is the print restricted to a
subclass of its hypotheses, hence a consequence of it): in characteristic `0` an algebraic closure
is a separable closure, and over a perfect, separably closed `k(s)` the reading of "semistable"
over `k(s)` and over `κ̄` agree (`isSemistableRes_iff`, proved). Not restricted to number fields: a
strictly henselian DVR has separably closed residue field, so `[NumberField K]` would make the leaf
vacuous. -/
def SemistableUnipotentPrinted : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ [PerfectField (IsLocalRing.ResidueField O)],
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      (HasSemistableReductionRes A O ↔ InertiaUnipotent A w ℓ) ∧
      (HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0)

/-- **The used direction with the echelon clause** (a consequence of `SemistableUnipotentPrinted`). -/
def SemistableUnipotentPrintedEchelon : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ [PerfectField (IsLocalRing.ResidueField O)],
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0

theorem echelon_of_printed (h : SemistableUnipotentPrinted) : SemistableUnipotentPrintedEchelon :=
  fun K _ _ O _ hO _ Ω _ _ _ w hw A ℓ _ hℓ => (h K O hO Ω w hw A ℓ hℓ).2

/-- `ReductGlue.SemistableUnipotentSH` with `[CharZero K]` and `[PerfectField k(s)]` added (the
strictly henselian field after the instances are added). -/
def SemistableUnipotentSH0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- `(σ - 1)² = 0` as an endomorphism gives the field's pointwise form. -/
theorem sq_form {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[ℓ] M] (f : M →ₗ[ℤ_[ℓ]] M)
    (h : (f - 1) * (f - 1) = 0) (t : M) : f (f t) - 2 • f t + t = 0 := by
  have := LinearMap.congr_fun h t
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.zero_apply] at this
  rw [two_nsmul]
  rw [← this]
  abel

/-- **`SemistableUnipotentSH0` from the printed statement** (echelon clause at `σ = τ`; an algebraic
closure is a separable closure in characteristic `0`; `k(s)` separably closed and perfect is
algebraically closed, so semistability over `κ̄` is semistability over `k(s)`). -/
theorem semistableUnipotentSH0_of (h : SemistableUnipotentPrintedEchelon) :
    SemistableUnipotentSH0 := by
  intro K _ _ O _ _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsSepClosed (IsLocalRing.ResidueField O) := hO.2.2
  haveI : IsAlgClosed (IsLocalRing.ResidueField O) := IsSepClosed.isAlgClosed_of_perfectField _
  have hA' : HasSemistableReductionRes A O := (hasSemistableReductionRes_iff O A).mpr hA
  exact sq_form _ (h K O hO Ω w hw A ℓ hℓ hA' σ σ hσ hσ) t

/-! ## §3. The DVR field from the strictly henselian one -/

/-- `ReductSplit.SemistableUnipotent` with `[CharZero K]` and `[PerfectField k(s)]` added (the DVR
field after the instances are added). -/
def SemistableUnipotent0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

open ZInQ.Contrib.AbVarBC in
/-- **SGA 7 IX 3.5 over a general DVR (char. 0 field, perfect residue field) from the strictly
henselian form**: reduct-glue's `unipotentFromSH_of` with the two instances carried along. The
inertia field `E` has characteristic `0`, and its strictly henselian valuation ring has residue
field algebraic over `k(s)`, hence perfect (`Algebra.IsAlgebraic.perfectField`). -/
theorem semistableUnipotent0_of (hIn : StrictHenselizationInside) (hSH : SemistableUnipotentSH0) :
    SemistableUnipotent0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, ⟨hSHP, halg, hbc⟩, hfix⟩ := hIn K O Ω w hw
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : PerfectField (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) := by
    letI := (resMap hE).toAlgebra
    haveI := halg
    exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField O)
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((bcPt A Ω).symm (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((A.baseChange E).galAct σ₁ (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (bcPt A Ω (Additive.toMul (s.1 n))))
    rw [bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

/-- **The DVR field (with the two instances) from the printed leaf and `StrictHenselizationInside`.** -/
theorem semistableUnipotent0_of_printed (hP : SemistableUnipotentPrinted)
    (hIn : StrictHenselizationInside) : SemistableUnipotent0 :=
  semistableUnipotent0_of hIn (semistableUnipotentSH0_of (echelon_of_printed hP))

/-- The old field implies the new one (the new field is weaker: it is the old one restricted). -/
theorem semistableUnipotent0_of_old (h : ReductSplit.SemistableUnipotent) : SemistableUnipotent0 :=
  fun K _ _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t => h K O Ω w hw A hA ℓ hℓ σ hσ t

/-! ## §4. The unrestricted field (every field `K`): reduction to the printed leaf and two named Props

The kernel row r6 (`PkgI2.RaynaudCriterion`, proved by `ReductGlue.raynaudCriterion_leaves` from
`semistableUnipotent`) is quantified over every field, so the field itself cannot gain
`[CharZero K]` without breaking that proof (`docs/research/unipotent-b.md` §4). This section keeps
the field's statement and reduces it to the printed form over every field plus two named Props. -/

/-- **LEAF (printed form, every field) `SemistableUnipotentPrintedGen`** (SGA 7 I, Exp. IX, Prop. 3.5,
**UNVERIFIED** wording, as `SemistableUnipotentPrinted` but without `[CharZero K]` and
`[PerfectField k(s)]`): `O` strictly henselian, `Ω = K^s` a separable closure, semistability over
`k(s)`, `ℓ` invertible in `O`; semistable iff `I` unipotent, then of echelon `≤ 2`. -/
def SemistableUnipotentPrintedGen : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      (HasSemistableReductionRes A O ↔ InertiaUnipotent A w ℓ) ∧
      (HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0)

/-- `SemistableUnipotentPrintedGen` restricts to `SemistableUnipotentPrinted`. -/
theorem printed_of_printedGen (h : SemistableUnipotentPrintedGen) : SemistableUnipotentPrinted :=
  fun K _ _ O _ hO _ Ω _ _ _ w hw A ℓ _ hℓ => h K O hO Ω w hw A ℓ hℓ

/-- **GLUE `SemiAbelianDescendsSepClosed`** (the `k(s)` axis for imperfect residue fields). For a
discrete valuation ring `O` with separably closed residue field `k`, a group model whose geometric
special fibre (over `κ̄`, an algebraic closure of `k`, purely inseparable over `k`) has semi-abelian
identity component already has it over `k`. Needs: the maximal torus of the smooth connected
commutative group `G⁰_k` exists over `k` (SGA 3 II, Exp. XIV, Thm 1.1, UNVERIFIED) and its base change
is the maximal torus of `G⁰_κ̄`; the quotient `G⁰_k / T` is smooth, connected and proper after base
change to `κ̄`, hence an abelian variety (proper descends along field extensions, EGA IV₂ 2.7.1);
tori over a separably closed field are split. Proved here when `k` is perfect
(`isSemistableRes_iff`). Not in Mathlib 4.35. -/
def SemiAbelianDescendsSepClosed : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsSepClosed (IsLocalRing.ResidueField O) →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsSemistable → IsSemistableRes 𝒩

/-- `SemiAbelianDescendsSepClosed` holds for perfect residue fields (proved). -/
theorem semiAbelianDescends_of_perfect (K : Type) [Field K] (O : ValuationSubring K)
    [PerfectField (IsLocalRing.ResidueField O)] (hk : IsSepClosed (IsLocalRing.ResidueField O))
    (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O) (h : 𝒩.IsSemistable) : IsSemistableRes 𝒩 := by
  haveI := hk
  haveI : IsAlgClosed (IsLocalRing.ResidueField O) := IsSepClosed.isAlgClosed_of_perfectField _
  exact (isSemistableRes_iff O 𝒩).mpr h

/-- **GLUE `SepClosureTateRestrict`** (the `K^s` axis). `Ω` an algebraic closure of `K`,
`K^s ⊆ Ω` the separable closure, `w` a valuation ring of `Ω`, `ℓ` invertible in `K`. Every `σ` in
the inertia group of `w` restricts to `σ_s ∈ Aut(K^s/K)` in the inertia group of `w ∩ K^s`, and
`A(K^s) → A(Ω)` induces a `ℤ_ℓ`-linear surjection `T_ℓ(A)_{K^s} → T_ℓ(A)_Ω` intertwining `σ_s` and
`σ`. Needs: `AlgEquiv.restrictNormal` (`K^s/K` is normal) and the residue map of `w ∩ K^s ⊆ w` for
the inertia condition; `A[ℓⁿ]` étale (bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`) and the
version of `ReductGlue.exists_lift_of_etale` with `Ω` separably closed (separable elements of `Ω`
lie in `K^s`) for surjectivity on `A(·)[ℓⁿ]`, then the lift to `T_ℓ` level by level (the transition
maps are injective on the image). In characteristic `0`, `K^s = Ω`. -/
def SepClosureTateRestrict : Prop :=
  ∀ (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
        IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
        ∃ φ : TΩ A (separableClosure K Ω) ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ, Function.Surjective φ ∧
          ∀ s, φ (galTΩ A ℓ σs s) = galTΩ A ℓ σ (φ s)

/-- **The strictly henselian field (unchanged statement, every field) from the printed leaf over every
field and the two named Props.** -/
theorem semistableUnipotentSH_of_gen (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hT : SepClosureTateRestrict) :
    ReductGlue.SemistableUnipotentSH := by
  intro K _ O _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hA' : HasSemistableReductionRes A O := by
    obtain ⟨𝒩, h1, h2⟩ := hA
    exact ⟨𝒩, h1, hD K O hO.2.2 A 𝒩 h2⟩
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isUnit O hℓ
  obtain ⟨σs, hσs, φ, hφ, hcomm⟩ := hT K Ω w A ℓ hℓK σ hσ
  have hws : (w.comap (algebraMap (separableClosure K Ω) Ω)).comap
      (algebraMap K (separableClosure K Ω)) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have key := (hP K O hO (separableClosure K Ω) _ hws A ℓ hℓ).2 hA' σs σs hσs hσs
  obtain ⟨s, rfl⟩ := hφ t
  have h2 := congrArg φ (sq_form _ key s)
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm] at h2
  exact h2

/-- **The field `semistableUnipotent` (unchanged statement, every field)** from the printed leaf over
every field, `StrictHenselizationInside` and the two named Props. -/
theorem semistableUnipotent_of_gen (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hT : SepClosureTateRestrict)
    (hIn : StrictHenselizationInside) : ReductSplit.SemistableUnipotent :=
  unipotentFromSH_of hIn (semistableUnipotentSH_of_gen hP hD hT)

/-! ## §5. `SepClosureTateRestrict` from two smaller Props -/

/-- **A Tate-module surjectivity criterion**: an injective `φ : M →+ N` onto the `ℓ`-power torsion
of `N` induces a surjection `T_ℓ M → T_ℓ N`. -/
theorem tateMap_surjective {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (φ : M →+ N) (hinj : Function.Injective φ)
    (hsurj : ∀ (n : ℕ) (y : N), (ℓ ^ n) • y = 0 → ∃ x : M, φ x = y) :
    Function.Surjective (PkgI3.Tate.map (ℓ := ℓ) φ) := by
  intro t
  choose s hs using fun n => hsurj n (t.1 n) (PkgI3.Tate.pow_smul_eq_zero t.2 n)
  refine ⟨⟨s, ?_, fun n => ?_⟩, Subtype.ext (funext fun n => hs n)⟩
  · apply hinj
    rw [hs, map_zero]
    exact t.2.1
  · apply hinj
    rw [map_nsmul, hs, hs]
    exact t.2.2 n

/-- **GLUE `InertiaRestrictSepClosure`**: an element of the inertia group of `w` in `Aut(Ω/K)`
restricts to an element of the inertia group of `w ∩ K^s` in `Aut(K^s/K)` (`K^s/K` is normal;
decomposition and inertia are compatible with restriction to a normal subextension; Serre,
*Corps locaux*, I §7, UNVERIFIED locator). -/
def InertiaRestrictSepClosure : Prop :=
  ∀ (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω), IsInertia w σ →
      ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
        IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
        ∀ x : separableClosure K Ω, (σs x : Ω) = σ x

/-- **GLUE `TorsionFromSepClosure`**: for `m` invertible in `K`, every point of `A(Ω)[m]` comes from
`A(K^s)` (`A[m]` is étale over `K`, bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`; the points of an
étale `K`-scheme with values in `Ω` have separable coordinates, hence come from `K^s`: the
separably closed version of `ReductGlue.exists_lift_of_etale`). -/
def TorsionFromSepClosure : Prop :=
  ∀ (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ), (m : K) ≠ 0 → ∀ x : A.Pt Ω, x ^ m = 1 →
      ∃ y : A.Pt (separableClosure K Ω),
        ZInQ.Contrib.AbVarBC.extPt A (IsScalarTower.toAlgHom K (separableClosure K Ω) Ω) y = x

open ZInQ.Contrib.AbVarBC in
/-- **`SepClosureTateRestrict` from `InertiaRestrictSepClosure` and `TorsionFromSepClosure`.** -/
theorem sepClosureTateRestrict_of (hI : InertiaRestrictSepClosure) (hT : TorsionFromSepClosure) :
    SepClosureTateRestrict := by
  intro K _ Ω _ _ _ w A ℓ _ hℓ σ hσ
  obtain ⟨σs, hσs, hres⟩ := hI K Ω w σ hσ
  let κ := IsScalarTower.toAlgHom K (separableClosure K Ω) Ω
  let φ0 : Additive (A.Pt (separableClosure K Ω)) →+ Additive (A.Pt Ω) :=
    MonoidHom.toAdditive (extPt A κ)
  refine ⟨σs, hσs, PkgI3.Tate.map φ0, ?_, fun s => ?_⟩
  · refine tateMap_surjective φ0 (extPt_injective A κ) fun n y hy => ?_
    have hℓn : ((ℓ ^ n : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ
    obtain ⟨x, hx⟩ := hT K Ω A (ℓ ^ n) hℓn (Additive.toMul y) (by
      have : Additive.toMul ((ℓ ^ n) • y) = 1 := by rw [hy]; rfl
      rwa [toMul_nsmul] at this)
    exact ⟨Additive.ofMul x, by change Additive.ofMul (extPt A κ x) = y; rw [hx]; rfl⟩
  · apply Subtype.ext
    funext n
    change Additive.ofMul (extPt A κ (A.galAct σs (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (extPt A κ (Additive.toMul (s.1 n))))
    rw [extPt_galAct A κ σs σ (fun x => hres x)]

/-- **The field (unchanged statement) from the printed leaf over every field,
`StrictHenselizationInside`, `SemiAbelianDescendsSepClosed` and the two smaller Props.** -/
theorem semistableUnipotent_of_gen' (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hI : InertiaRestrictSepClosure)
    (hT : TorsionFromSepClosure) (hIn : StrictHenselizationInside) :
    ReductSplit.SemistableUnipotent :=
  semistableUnipotent_of_gen hP hD (sepClosureTateRestrict_of hI hT) hIn

end UnipotentB

#print axioms UnipotentB.isSemistableRes_iff
#print axioms UnipotentB.echelon_of_printed
#print axioms UnipotentB.semistableUnipotentSH0_of
#print axioms UnipotentB.semistableUnipotent0_of
#print axioms UnipotentB.semistableUnipotent0_of_printed
#print axioms UnipotentB.semistableUnipotent0_of_old
#print axioms UnipotentB.printed_of_printedGen
#print axioms UnipotentB.semiAbelianDescends_of_perfect
#print axioms UnipotentB.semistableUnipotentSH_of_gen
#print axioms UnipotentB.semistableUnipotent_of_gen
#print axioms UnipotentB.sepClosureTateRestrict_of
#print axioms UnipotentB.semistableUnipotent_of_gen'
