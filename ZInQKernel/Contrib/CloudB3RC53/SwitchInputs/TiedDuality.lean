import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.QuasiSide

/-!
# RC53 SwitchInputs: the switch duality adjunction, tied to the actual configuration

Proposition `ex:limits-uniform-lower-bound`, proof, tex L5068–5075:

> The retained localization-duality diagrams give `U = U^⊥`. Specifically, localization's connecting
> map is its dual under the strict/relaxed duality, so its kernel is both `U` and `U^⊥`; this is the
> exactness in [Nekovář, 6.3.3–6.3.4] used in Lemma `ex:limits-derivative-switch`.

`QuasiSide.lean`'s GLUE input `SwitchDualityAdjunction` takes an arbitrary strict Selmer datum `Dstr`
and an arbitrary map `δ` (with the exactness `range H¹(λ) = ker δ` as a hypothesis); its consistency
instance used that freedom. Here the input is tightened (truth check):

* `TiedStrict R`: the strict local condition `U_str ⊂ U_rel` of the SAME configuration as the relaxed
  localization `R` (same global complex `G`, local complex `L`), with `U_rel / U_str = W_rel`
  degreewise (`0 → U_str → U_rel → W_rel → 0`). The strict Selmer datum is
  `restrictData R.D fs` (`TiedStrict.Dstr`), and `0 → C(U_str) → C(U_rel) → W_rel → 0` is the actual
  short exact sequence (`TiedStrict.shortExact`, from SelmerDuality's `relaxedQuotientNode_proof`).
* `TiedStrict.δ`: the ACTUAL connecting map `H¹(W_rel) → H²(C(U_str))` of that sequence (Mathlib's
  homology long exact sequence).
* `tied_exact` (PROVED): `range H¹(λ) = ker δ` — the exactness is now proved, not assumed.
* `TiedSwitchDualityAdjunction` (GLUE, new style): only the separating pairing
  `H²(C(U_str)) × H¹(C(U_rel)) → k` and the adjunction `⟨δ w, v⟩ = β(λ v, w)` (Nekovář 6.3.3:
  compatibility of duality with the cone triangle) remain as the input.
* `tied_implies_old`, `localizationDualityInput_of_tied` (PROVED).
* `tied_of_duality`, `tied_iff_duality` (PROVED): when `δ` is surjective, the tied input is
  equivalent to `LocalizationDualityInput` for the actual relaxed image (a finding: the remaining
  GLUE content is exactly the self-annihilation `U = U^⊥`, no more and no less).
* Non-vacuity: `exTied`, a genuinely tied strict condition (`U_str = 0` inside the relaxed condition of
  the degree-one example `exRel`), with `δ` surjective (`exDelta_surjective`, from `H²(C_rel) = 0`),
  `H²(C(U_str)) ≠ 0` coming from the actual sequence (`ex_h2_nontrivial`, dimension `2`), and the
  tied input inhabited (`exTiedAdjunction`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-- **The strict condition of the same configuration** (tex L5070–5072): a local condition
`U_str` with an injection `fs : U_str → U_rel` into the relaxed condition of `R`, whose cokernel is
the relaxed quotient `W_rel` (degreewise exactness of `0 → U_str → U_rel → W_rel → 0`). -/
structure TiedStrict (R : QuasiRelaxedLocalization k) where
  Ustr : GCx k
  fs : GHom Ustr R.D.U
  hfg : ∀ i (u : Ustr.X i), R.gR.f i i rfl (fs.f i i rfl u) = 0
  hinj : ∀ i, Function.Injective (fs.f i i rfl)
  hsurj : ∀ i, Function.Surjective (R.gR.f i i rfl)
  hex : ∀ i (u : R.D.U.X i), R.gR.f i i rfl u = 0 → ∃ u', fs.f i i rfl u' = u

variable {R : QuasiRelaxedLocalization k}

/-- The strict Selmer datum `C(U_str)` of the configuration (same `G`, `L`, local condition
`ι ∘ fs`). -/
abbrev TiedStrict.Dstr (T : TiedStrict R) : SelData k := restrictData R.D T.fs

/-- The actual sequence `0 → C(U_str) → C(U_rel) → W_rel → 0`. -/
abbrev TiedStrict.ses (T : TiedStrict R) := changeSES R.D T.fs R.gR T.hfg

/-- The sequence is short exact (SelmerDuality, `relaxedQuotientNode_proof`). PROVED. -/
theorem TiedStrict.shortExact (T : TiedStrict R) : T.ses.ShortExact :=
  relaxedQuotientNode_proof k R.D T.Ustr R.Wrel T.fs R.gR T.hfg T.hinj T.hsurj T.hex

theorem rel_one_two : (ComplexShape.up ℤ).Rel 1 2 := by
  show (1 : ℤ) + 1 = 2
  norm_num

/-- **The actual connecting map** `δ : H¹(W_rel) → H²(C(U_str))` of the sequence. -/
def TiedStrict.δ (T : TiedStrict R) :
    R.Wrel.toCC.homology 1 →ₗ[k] (selCx T.Dstr).toCC.homology 2 :=
  (T.shortExact.δ 1 2 rel_one_two).hom

/-- **Exactness `H¹(C_rel) → H¹(W_rel) → H²(C_str)`, proved** (homology long exact sequence):
`range H¹(λ) = ker δ`. PROVED. -/
theorem tied_exact (T : TiedStrict R) :
    LinearMap.range (H1 (quotMap R.D R.gR)) = LinearMap.ker T.δ :=
  (T.shortExact.homology_exact₃ 1 2 rel_one_two).moduleCat_range_eq_ker

/-- **GLUE input: the strict/relaxed duality of the configuration is adjoint to localization**
(Nekovář, *Selmer complexes*, 6.3.3–6.3.4, cited at tex L5068–5075). For the relaxed localization
`R` and the strict condition `T` of the same configuration, with `δ` the actual connecting map of
`0 → C(U_str) → C(U_rel) → W_rel → 0`: there is a pairing `H²(C(U_str)) × H¹(C(U_rel)) → k`,
separating in the first variable, with `⟨δ w, v⟩ = β(λ v, w)` for the switch pairing
`β = switchPairing ε σ J` in the coordinates `R.eR`. Stateable hypotheses (`ε, σ ≠ 0`, `J² = 1`) are
in the type; the exactness is proved (`tied_exact`). Classification: GLUE (assumed input). -/
def TiedSwitchDualityAdjunction (T : TiedStrict R) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (_hε : ε ≠ 0) (_hσ : σ ≠ 0) (_hJ2 : J * J = 1) : Prop :=
  ∃ pair : (selCx T.Dstr).toCC.homology 2 →ₗ[k] (selCx R.D).toCC.homology 1 →ₗ[k] k,
    (∀ x, (∀ v, pair x v = 0) → x = 0) ∧
    ∀ w v, pair (T.δ w) v = switchPairing ε σ J (R.eR (H1 (quotMap R.D R.gR) v)) (R.eR w)

/-- **The tied input implies the old one** (for `Dstr = C(U_str)` and the actual `δ`). PROVED. -/
theorem tied_implies_old (T : TiedStrict R) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0)
    (hσ : σ ≠ 0) (hJ2 : J * J = 1) (h : TiedSwitchDualityAdjunction T ε σ J hε hσ hJ2) :
    SwitchDualityAdjunction R T.Dstr ε σ J hε hσ hJ2 T.δ (tied_exact T) :=
  h

/-- **`LocalizationDualityInput` from the tied input** (tex L5068–5075): the actual relaxed image
`R.U` is its own annihilator. PROVED (from the input). -/
theorem localizationDualityInput_of_tied (T : TiedStrict R) (ε σ : k)
    (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (h : TiedSwitchDualityAdjunction T ε σ J hε hσ hJ2) :
    LocalizationDualityInput ε σ J hε hσ hJ2 R.U :=
  localizationDualityInput_of_adjunction R T.Dstr ε σ J hε hσ hJ2 T.δ (tied_exact T)
    (tied_implies_old T ε σ J hε hσ hJ2 h)

/-- **Converse: the tied input from `U = U^⊥`, when `δ` is surjective.** With a section `s` of
`δ`, the pairing `⟨x, v⟩ = β(λ v, s x)` is separating (since `U^⊥ = U = ker δ` after the
coordinates) and adjoint (since `U` is isotropic). PROVED. -/
theorem tied_of_duality (T : TiedStrict R) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1) (hδ : Function.Surjective T.δ)
    (hD : LocalizationDualityInput ε σ J hε hσ hJ2 R.U) :
    TiedSwitchDualityAdjunction T ε σ J hε hσ hJ2 := by
  obtain ⟨s, hs⟩ := T.δ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hδ)
  set lam' := R.eR.toLinearMap ∘ₗ H1 (quotMap R.D R.gR) with hlam'
  have hU : R.U = LinearMap.range lam' := by
    rw [QuasiRelaxedLocalization.U, hlam', LinearMap.range_comp]
  unfold LocalizationDualityInput at hD
  rw [hU] at hD
  set B := switchPairing ε σ J
  refine ⟨(B.compl₁₂ lam' (R.eR.toLinearMap ∘ₗ s)).flip, fun x hx => ?_, fun w v => ?_⟩
  · -- `e(s x) ∈ U^⊥ = U`, so `s x ∈ ker δ`, so `x = δ (s x) = 0`
    have hmem : R.eR (s x) ∈ B.orthogonal (LinearMap.range lam') := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      rintro _ ⟨v, rfl⟩
      exact hx v
    rw [hD] at hmem
    obtain ⟨v, hv⟩ := hmem
    have hv' : H1 (quotMap R.D R.gR) v = s x := by
      apply R.eR.injective
      simpa [hlam'] using hv
    have hk : s x ∈ LinearMap.ker T.δ := by
      rw [← tied_exact T, ← hv']
      exact ⟨v, rfl⟩
    rw [LinearMap.mem_ker] at hk
    have := congrArg (fun f => f x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this
    rw [← this, hk]
  · -- `w − s(δ w) ∈ ker δ = range H¹(λ)`, and `U` is isotropic
    have hk : w - s (T.δ w) ∈ LinearMap.ker T.δ := by
      rw [LinearMap.mem_ker, map_sub]
      have := congrArg (fun f => f (T.δ w)) hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this
      rw [this, sub_self]
    rw [← tied_exact T] at hk
    obtain ⟨v', hv'⟩ := hk
    have hiso : B (lam' v) (R.eR (w - s (T.δ w))) = 0 := by
      have hm : R.eR (w - s (T.δ w)) ∈ B.orthogonal (LinearMap.range lam') := by
        rw [hD, ← hv']
        exact ⟨v', rfl⟩
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hm) _ ⟨v, rfl⟩
    rw [map_sub, map_sub] at hiso
    simp only [LinearMap.flip_apply, LinearMap.compl₁₂_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    change B (lam' v) (R.eR (s (T.δ w))) = B (lam' v) (R.eR w)
    rw [sub_eq_zero] at hiso
    exact hiso.symm

/-- **The tied input is equivalent to `U = U^⊥` when `δ` is surjective** (finding: the remaining
GLUE content is exactly Elliot's self-annihilation of the relaxed image). PROVED. -/
theorem tied_iff_duality (T : TiedStrict R) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1) (hδ : Function.Surjective T.δ) :
    TiedSwitchDualityAdjunction T ε σ J hε hσ hJ2 ↔ LocalizationDualityInput ε σ J hε hσ hJ2 R.U :=
  ⟨localizationDualityInput_of_tied T ε σ J hε hσ hJ2, tied_of_duality T ε σ J hε hσ hJ2 hδ⟩

/-! ### Non-vacuity: a genuinely tied configuration -/

/-- **The tied strict condition of the degree-one example** (`exRel`): `U_str = 0` inside the
relaxed condition `U_rel = F ⊕ S`, with `W_rel = U_rel` (`g_R = id`). -/
def exTied : TiedStrict exQuasiRel where
  Ustr := zGCx Zn
  fs := zHom fun _ => 0
  hfg _ _ := map_zero _
  hinj _ := fun _ _ _ => Subsingleton.elim _ _
  hsurj _ := Function.surjective_id
  hex _ u h := ⟨0, by change (0 : _) = u; exact h.symm⟩

/-- `H²(C_rel) = 0` for the example: every degree-two cochain `(0, 0, x)` is `d(0, (0, −x), 0)`. -/
theorem exRel_h2_subsingleton : Subsingleton ((selCx exRelD).toCC.homology 2) := by
  set K := (selCx exRelD).toCC
  have hexact : K.ExactAt 2 := by
    rw [HomologicalComplex.exactAt_iff' K 1 2 3 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x₂ _
    obtain ⟨a, u, x⟩ := x₂
    refine ⟨((0 : Fin (dimAt 1 1) → ℚ), ((0 : Fin (dimAt 2 1) → ℚ), -x),
      (0 : Fin (dimAt 2 (1 - 1)) → ℚ)), ?_⟩
    change (K.d 1 2).hom _ = _
    erw [GCx.toCC_d_hom _ 1 2 rfl]
    refine Prod.ext ((subsingleton_dimAt 1 (n := 2) (by norm_num)).elim _ _)
      (Prod.ext ?_ ?_)
    · have := subsingleton_dimAt 2 (n := 2) (by norm_num)
      exact Subsingleton.elim (α := (Fin (dimAt 2 2) → ℚ) × (Fin (dimAt 2 2) → ℚ)) _ _
    · show (0 : ↑(exRelD.L.X (2 - 1))) - (-x) - 0 = x
      simp
  exact ModuleCat.isZero_iff_subsingleton.mp hexact.isZero_homology

/-- **`δ` is surjective for the example** (`H²(C_rel) = 0` and the long exact sequence). PROVED. -/
theorem exDelta_surjective : Function.Surjective exTied.δ := by
  have h := (exTied.shortExact.homology_exact₁ 1 2 rel_one_two).moduleCat_range_eq_ker
  rw [← LinearMap.range_eq_top]
  change LinearMap.range (exTied.shortExact.δ 1 2 rel_one_two).hom = ⊤
  rw [h]
  ext x
  simp only [Submodule.mem_top, iff_true, LinearMap.mem_ker]
  exact exRel_h2_subsingleton.elim _ _

/-- **`H²(C(U_str))` is two-dimensional, from the actual sequence**: `δ` is onto with kernel the
relaxed image, of dimension `2` inside `H¹(W_rel) ≅ ℚ⁴`. PROVED. -/
theorem ex_h2_finrank : finrank ℚ ((selCx exTied.Dstr).toCC.homology 2) = 2 := by
  have : FiniteDimensional ℚ (exQuasiRel.Wrel.toCC.homology 1) :=
    LinearEquiv.finiteDimensional exQuasiRel.eR.symm
  have hW : finrank ℚ (exQuasiRel.Wrel.toCC.homology 1) = 4 := by
    rw [exQuasiRel.eR.finrank_eq]; simp
  have hker : finrank ℚ (LinearMap.ker exTied.δ) = 2 := by
    rw [← tied_exact exTied]
    have hU : finrank ℚ exQuasiRel.U = 2 := by
      rw [exQuasiRel_U]; exact finrank_finPlane
    rw [QuasiRelaxedLocalization.U, LinearEquiv.finrank_map_eq] at hU
    exact hU
  have hrn := LinearMap.finrank_range_add_finrank_ker exTied.δ
  rw [LinearMap.range_eq_top.mpr exDelta_surjective, finrank_top, hker, hW] at hrn
  omega

/-- **The tied duality input is inhabited** for the example (with `ε = σ = 1`, `J = diag(1, −1)`),
from `U = F = F^⊥` and the surjectivity of the actual `δ`. PROVED. -/
theorem exTiedAdjunction :
    TiedSwitchDualityAdjunction exTied 1 1 J₀ one_ne_zero one_ne_zero J₀_sq := by
  refine tied_of_duality exTied 1 1 J₀ one_ne_zero one_ne_zero J₀_sq exDelta_surjective ?_
  rw [exQuasiRel_U]
  exact exLocalizationDuality 1 1 one_ne_zero one_ne_zero J₀ J₀_sq

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
