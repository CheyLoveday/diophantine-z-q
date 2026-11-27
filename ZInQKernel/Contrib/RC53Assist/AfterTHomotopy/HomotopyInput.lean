import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LaurentSeries
import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.TransferFinal
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Transfer
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT3
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel
import ZInQKernel.Contrib.RC53Assist.ResidualWitnessAfterT.Witness

/-!
# The homotopy equivalence `L ≃ P'` after inverting `t`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4612–4647, with the
retained inner-limit diagrams of Lemma `ex:limits-inner-limit` (tex 4391–4451) and the local model
(4.4) (tex 3471–3498).

The constructors `residualRankCounts_afterT'`, `residualRankCounts_afterT''`
(`GenuineInst/ResidualAfterT2.lean`) and `residualRankCounts_afterT'''`
(`GenuineInst/ResidualAfterT3.lean`) take as an input a homotopy equivalence
`e : HomotopyEquiv L P'` between the generic minimal model `L` of the original-support complex and
the base change `P'` to `𝔽₂((t))` of the smaller-support model `P` over `𝔽₂[[t]]` (tex 4626–4631:
"the original complex has the same generic residual cohomology as the bounded smaller-support
model"). They use `e` only through `transfer_after_inverting_t'`, which turns it, with the
base-change comparison `ebc` and the minimality `hLmin`, into `rank L ≤ rank P`.

This file constructs `e` from the hypotheses of the text.

**Homological algebra over a field.** Over a field every module is free, so every bounded-above
complex is K-projective (Mathlib's `CochainComplex.isKProjective_of_projective`).
* `exists_homotopyEquiv_of_quasiIso`: a quasi-isomorphism of bounded-above complexes of vector
  spaces is the forward map of a homotopy equivalence; in particular for bounded complexes of
  finite-dimensional vector spaces (`exists_homotopyEquiv_of_quasiIso_finiteDimensional`).
* `nonempty_homotopyEquiv_of_zigzag`: two bounded-above complexes with quasi-isomorphisms to a
  common complex (of arbitrary size) are homotopy equivalent.
* `cohomologyCx`, `cohomologyRep`: the cohomology with zero differentials and a quasi-isomorphism
  from it to the complex; `exists_homotopyEquiv_cohomologyCx`: every bounded-above complex is
  homotopy equivalent to its cohomology, which is a minimal model (`cohomologyCx_minimal`). Over a
  field a minimal complex has zero differentials (`d_eq_zero_of_minimal`), and its ranks are the
  dimensions of the cohomology of any complex receiving a quasi-isomorphism from it
  (`finrank_eq_finrank_homology_of_minimal`).

**The change of condition after inverting `t`.** For a short exact sequence
`0 → P' → Q' → W' → 0` with `W'` acyclic (the active comparison blocks after inverting `t`), the
inclusion is a quasi-isomorphism (`quasiIso_of_change`), a homotopy equivalence with contractible
comparison cone when `Q'` is bounded above (`exists_homotopyEquiv_inclusion`,
`comparisonCone_contractible`), and every minimal model `L` of `Q'` is homotopy equivalent
to `P'` (`nonempty_homotopyEquiv_of_change`, `homotopyEquivOfChange`; variants for `L ≃ Q'`, for a
quasi-isomorphism `Q' → L`, and for a contractible comparison cone). For Selmer data, the change
from the unramified to the full condition with acyclic singular quotient gives the same conclusion
(`nonempty_homotopyEquiv_of_selmerChange`), also composed with the support comparison
(`nonempty_homotopyEquiv_of_supportChange`). The minimal model can be taken to be the cohomology of
`Q'` (`nonempty_homotopyEquiv_cohomologyCx_of_change`).

**From the integral diagram.** For a flat ring map `φ : R → S` and a short exact sequence
`0 → P → Q → W → 0` over `R` whose quotient carries a homotopy `d h + h d = c` with `φ c` a unit
(the retained comparison homotopy; at an oriented active place `c = (1+t)^e − 1`, tex 4619–4626):
the base change is short exact (`baseChangeCx_shortExact`), the base change of `W` is acyclic
(`baseChangeCx_acyclic_of_homotopy`; contractible when `W` is bounded above,
`baseChangeCx_contractible_of_homotopy`), and the cohomology of `S ⊗ Q` is homotopy equivalent to
`S ⊗ P` (`nonempty_homotopyEquiv_of_integralChange`). `𝔽₂((t))` is flat over `𝔽₂[[t]]`
(`laurentSeries_flat`).

**The consumers.** `residualRankCounts_afterT'_ofChange` (and `''`, `'''`): the constructors with
`e` replaced by the change of condition over `𝔽₂((t))` and a quasi-isomorphism `L → Q'`;
`residualRankCounts_afterT'''_ofChangeCohomology`: the same with no minimal model supplied (`L` the
cohomology of `Q'`); `residualRankCounts_afterT'''_ofSelmerChange` and
`residualRankCounts_afterT'''_ofSelmerChangeCohomology`: `e` (and `L`) from the change of local
conditions of Selmer data over `𝔽₂((t))`; `residualRankCounts_afterT'_ofIntegralChange` (and
`'''`): `P'`, `L`, `ebc`, `hLmin` and `e` all built from the integral change of condition over
`𝔽₂[[t]]` and its comparison homotopy (`P' = 𝔽₂((t)) ⊗ P`, `L` the cohomology of `𝔽₂((t)) ⊗ Q`).
Their generic rank is the dimension of the generic cohomology of the original-support model
(`…_genericRank`). The transfer inequality itself, without number-field data:
`sum_finrank_homology_le_of_change`, `sum_finrank_genericHomology_le_of_integralChange`.

**Non-vacuity.** `integralChange_nonvacuous`: for every bounded-above `P` over `𝔽₂[[t]]`, every
complex `K` and every odd `e`, the split model `Q = P ⊞ W` with `W` the cone of multiplication by
`(1+t)^e − 1` on `K` (the active comparison block `activeBlock`, with its homotopy
`activeBlockHomotopy`) satisfies the integral hypotheses; `integralChange_transfer_nonvacuous` gives
the transfer inequality for it. At the active witness of `ResidualWitnessActive/Witness.lean`
(`K = ℚ(i)`, `E₁₁`, derivative prime `7`, active prime `13`; the only reason for importing the
witness modules): `witnessCountsOfChange` applies `residualRankCounts_afterT''_ofChange` to the
witness's generic change of condition (`afterSES_shortExact`, `activeW'_acyclic`) and cohomology
representatives, `witnessCountsOfChangeCohomology` applies
`residualRankCounts_afterT'''_ofChangeCohomology` to the same change of condition alone, and
`witnessCountsOfIntegralChange` applies
`residualRankCounts_afterT'_ofIntegralChange` to the integral change of condition
`afterP → afterP ⊕ activeW → activeW` with the active comparison homotopy; for all three,
`2 ≤ genericRank ≤ rankTot` and `genericRank ≤ 294`, and the integral change of condition is not
acyclic before inverting `t` (`witnessCountsOfIntegralChange_bounds`). Like the witness, these are
model-level instances (the constant extension of the residual cone and a split original-support
model), not the arithmetic cochains with `𝔽₂[[t]]`-coefficients.

**What remains (arithmetic input).** This tree has no Galois cochains with coefficients in
`𝔽₂[[t]]` or `𝔽₂((t))` and no inner limit, so the identification of the models with the actual
complexes stays an input:
* generic form: the original-support complex `Q'` after inverting `t`, with the smaller-support
  model `P'` as a subcomplex whose quotient `W'` (the active comparison blocks) is acyclic, and a
  minimal model `L → Q'`;
* integral form: the model `Q` over `𝔽₂[[t]]` of the original-support complex given by the inner
  limit of the retained diagram (tex 4401–4406, 4626–4628), in which the smaller-support model `P`
  is an actual subcomplex ("the old complex is an actual subcomplex of an upper triangular model",
  tex 3494–3498) with quotient `W`, together with the retained comparison homotopy `d h + h d = c`
  on `W`, `c` a product of the scalars `(1+t)^{±e} − 1` from the reduction of (4.4) at the active
  places (tex 4619–4626; their invertibility after inverting `t` is RC6's
  `isUnit_laurentSeries_one_add_X_pow_sub_one`);
* Selmer form: Selmer data over `𝔽₂((t))`, the acyclicity of the singular quotient after inverting
  `t`, the support comparison after inverting `t` (Nekovář 7.8.8(ii) through the inner limit) and
  the model maps.
No hypothesis equivalent to `e` is assumed.

**Classification.** PROVED (from the inputs in the types).
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AfterTHomotopy

open CategoryTheory CategoryTheory.Limits DerivedCategory

universe u

/-! ## Homological algebra over a field -/

section Field

variable {F : Type u} [Field F]

/-- **A bounded-above complex of vector spaces is K-projective** (tex 4626–4631, 4637–4640: over
the field `𝔽₂((t))` every module is free). Kind: PROVED (Mathlib's
`CochainComplex.isKProjective_of_projective`). -/
theorem isKProjective_of_isStrictlyLE (K : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : K.IsKProjective :=
  CochainComplex.isKProjective_of_projective K b

/-- **Over a field, a quasi-isomorphism of bounded-above complexes is a homotopy equivalence**
(tex 4626–4631: "Every active comparison cone is then contractible"). The quasi-isomorphism `φ` is
the forward map of a homotopy equivalence. Kind: PROVED (both complexes are K-projective). -/
theorem exists_homotopyEquiv_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] (φ : K ⟶ L) [QuasiIso φ] :
    ∃ e : HomotopyEquiv K L, e.hom = φ := by
  have := isKProjective_of_isStrictlyLE K b
  have := isKProjective_of_isStrictlyLE L b
  exact (CochainComplex.IsKProjective.quasiIso_iff φ).1 inferInstance

/-- **Quasi-isomorphisms and homotopy equivalences agree for bounded-above complexes over a field**
(tex 4626–4631). Kind: PROVED. -/
theorem quasiIso_iff_exists_homotopyEquiv {K L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] (φ : K ⟶ L) :
    QuasiIso φ ↔ ∃ e : HomotopyEquiv K L, e.hom = φ := by
  refine ⟨fun _ => exists_homotopyEquiv_of_quasiIso b φ, ?_⟩
  rintro ⟨e, rfl⟩
  infer_instance

/-- **A quasi-isomorphism of bounded complexes of finite-dimensional vector spaces is a homotopy
equivalence** (tex 4626–4631, 4637–4640). The lower bound and the finite dimensions are not used
(`exists_homotopyEquiv_of_quasiIso`). Kind: PROVED. -/
theorem exists_homotopyEquiv_of_quasiIso_finiteDimensional
    {K L : CochainComplex (ModuleCat.{u} F) ℤ} (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ n, FiniteDimensional F (K.X n)] [∀ n, FiniteDimensional F (L.X n)]
    (φ : K ⟶ L) [QuasiIso φ] : ∃ e : HomotopyEquiv K L, e.hom = φ :=
  exists_homotopyEquiv_of_quasiIso b φ

/-- **Lifting through a quasi-isomorphism** (tex 4626–4631): if `l : L → X` and `p : P → X` are
quasi-isomorphisms and `L` is bounded above, there is a quasi-isomorphism `L → P`. The complexes
`P` and `X` are arbitrary. Kind: PROVED (`L` is K-projective; Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective`). -/
theorem exists_quasiIso_lift {L P X : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [L.IsStrictlyLE b] (l : L ⟶ X) [QuasiIso l] (p : P ⟶ X) [QuasiIso p] :
    ∃ g : L ⟶ P, QuasiIso g := by
  have := isKProjective_of_isStrictlyLE L b
  let _ := HasDerivedCategory.standard (ModuleCat.{u} F)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective L
    ((HomotopyCategory.quotient _ _).obj P)).surjective
    ((quotientCompQhIso _).hom.app L ≫ Q.map l ≫ inv (Q.map p) ≫ (quotientCompQhIso _).inv.app P)
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g', ?_⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have h : Q.map g' = (quotientCompQhIso _).inv.app L ≫
      Qh.map ((HomotopyCategory.quotient _ _).map g') ≫ (quotientCompQhIso _).hom.app P := by
    simp
  rw [h, hg]
  infer_instance

/-- **Bounded-above complexes quasi-isomorphic to a common complex are homotopy equivalent** (tex
4626–4631): `L → X ← P` with both maps quasi-isomorphisms, `L`, `P` bounded above, `X` arbitrary.
Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_zigzag {L P X : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [L.IsStrictlyLE b] [P.IsStrictlyLE b] (l : L ⟶ X) [QuasiIso l] (p : P ⟶ X) [QuasiIso p] :
    Nonempty (HomotopyEquiv L P) := by
  obtain ⟨g, hg⟩ := exists_quasiIso_lift b l p
  obtain ⟨e, -⟩ := exists_homotopyEquiv_of_quasiIso b g
  exact ⟨e⟩

/-- **The cohomology of a complex, with zero differentials** (tex 4637–4640: over a field the
minimal model of a complex is its cohomology). Kind: definition. -/
abbrev cohomologyCx (C : CochainComplex (ModuleCat.{u} F) ℤ) :
    CochainComplex (ModuleCat.{u} F) ℤ where
  X n := C.homology n
  d _ _ := 0

/-- The differentials of `cohomologyCx` vanish (tex 4637–4640). Kind: PROVED. -/
theorem cohomologyCx_d (C : CochainComplex (ModuleCat.{u} F) ℤ) (i j : ℤ) :
    (cohomologyCx C).d i j = 0 := rfl

/-- **Linear representatives of cohomology classes** (tex 4637–4640): the chain map
`H(C) → C` given by a linear section of the projection from cycles to cohomology, followed by the
inclusion of cycles. Kind: definition. -/
def cohomologyRep (C : CochainComplex (ModuleCat.{u} F) ℤ) : cohomologyCx C ⟶ C where
  f n := Projective.factorThru (𝟙 (C.homology n)) (C.homologyπ n) ≫ C.iCycles n
  comm' i j _ := by
    rw [cohomologyCx_d, zero_comp, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

/-- Unfolding `cohomologyRep` (tex 4637–4640). Kind: PROVED. -/
theorem cohomologyRep_f (C : CochainComplex (ModuleCat.{u} F) ℤ) (n : ℤ) :
    (cohomologyRep C).f n =
      Projective.factorThru (𝟙 (C.homology n)) (C.homologyπ n) ≫ C.iCycles n :=
  rfl

/-- **The representatives induce the identity on cohomology**: `cohomologyRep C` is a
quasi-isomorphism (tex 4637–4640). Kind: PROVED. -/
instance cohomologyRep_quasiIso (C : CochainComplex (ModuleCat.{u} F) ℤ) :
    QuasiIso (cohomologyRep C) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h1 : IsIso ((cohomologyCx C).iCycles n) :=
    (cohomologyCx C).isIso_iCycles n (n + 1) (by simp) (cohomologyCx_d C n (n + 1))
  have h2 : IsIso ((cohomologyCx C).homologyπ n) :=
    (cohomologyCx C).isIso_homologyπ (n - 1) n (by simp) (cohomologyCx_d C (n - 1) n)
  have hcyc : HomologicalComplex.cyclesMap (cohomologyRep C) n =
      (cohomologyCx C).iCycles n ≫ Projective.factorThru (𝟙 (C.homology n)) (C.homologyπ n) := by
    apply (cancel_mono (C.iCycles n)).1
    rw [HomologicalComplex.cyclesMap_i, Category.assoc, cohomologyRep_f]
  have hmap : (cohomologyCx C).homologyπ n ≫
      HomologicalComplex.homologyMap (cohomologyRep C) n = (cohomologyCx C).iCycles n := by
    rw [HomologicalComplex.homologyπ_naturality, hcyc, Category.assoc, Projective.factorThru_comp]
    exact Category.comp_id _
  have : IsIso ((cohomologyCx C).homologyπ n ≫
      HomologicalComplex.homologyMap (cohomologyRep C) n) := by
    rw [hmap]
    exact h1
  exact IsIso.of_isIso_comp_left ((cohomologyCx C).homologyπ n) _

/-- The cohomology of a complex with cohomology in degrees `≤ b` is strictly `≤ b` (tex
4637–4640). Kind: PROVED. -/
instance cohomologyCx_isStrictlyLE (C : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ)
    [C.IsLE b] : (cohomologyCx C).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact C.isZero_of_isLE b i hi

/-- The cohomology of a complex with cohomology in degrees `≥ a` is strictly `≥ a` (tex
4637–4640). Kind: PROVED. -/
instance cohomologyCx_isStrictlyGE (C : CochainComplex (ModuleCat.{u} F) ℤ) (a : ℤ)
    [C.IsGE a] : (cohomologyCx C).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact C.isZero_of_isGE a i hi

/-- The cohomology of a finite-dimensional term is finite-dimensional (tex 4637–4640).
Kind: PROVED. -/
theorem homology_finite (C : CochainComplex (ModuleCat.{u} F) ℤ) (n : ℤ)
    [Module.Finite F (C.X n)] : Module.Finite F (C.homology n) := by
  have : Module.Finite F (C.cycles n) :=
    Module.Finite.of_injective _ ((ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance)
  exact Module.Finite.of_surjective _
    ((ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance)

/-- **Over a field every bounded-above complex is homotopy equivalent to its cohomology** (tex
4637–4640), by the representative map. Kind: PROVED. -/
theorem exists_homotopyEquiv_cohomologyCx (C : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ)
    [C.IsStrictlyLE b] : ∃ e : HomotopyEquiv (cohomologyCx C) C, e.hom = cohomologyRep C :=
  exists_homotopyEquiv_of_quasiIso b (cohomologyRep C)

/-- A quasi-isomorphism transports a cohomological upper bound (tex 4626–4631). Kind: PROVED. -/
theorem isLE_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (b : ℤ) [K.IsLE b] : L.IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : IsIso (HomologicalComplex.homologyMap φ i) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact (K.isZero_of_isLE b i hi).of_iso (asIso (HomologicalComplex.homologyMap φ i)).symm

/-- A quasi-isomorphism transports a cohomological lower bound (tex 4626–4631). Kind: PROVED. -/
theorem isGE_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (a : ℤ) [K.IsGE a] : L.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : IsIso (HomologicalComplex.homologyMap φ i) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact (K.isZero_of_isGE a i hi).of_iso (asIso (HomologicalComplex.homologyMap φ i)).symm

/-- A quasi-isomorphism from a complex with finite-dimensional terms has finite-dimensional
cohomology in the target (tex 4626–4631). Kind: PROVED. -/
theorem homology_finite_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (φ : K ⟶ L)
    [QuasiIso φ] (n : ℤ) [Module.Finite F (K.X n)] : Module.Finite F (L.homology n) := by
  have := homology_finite K n
  have : IsIso (HomologicalComplex.homologyMap φ n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact Module.Finite.equiv (asIso (HomologicalComplex.homologyMap φ n)).toLinearEquiv

/-- **The cohomology is a minimal model**: its differentials lie in `𝔪 • ⊤` (tex 4637–4640; over a
field `𝔪 = 0`), the form of `hLmin` in the consumers. Kind: PROVED. -/
theorem cohomologyCx_minimal (C : CochainComplex (ModuleCat.{u} F) ℤ) (i j : ℤ)
    (x : (cohomologyCx C).X i) :
    ((cohomologyCx C).d i j).hom x ∈
      IsLocalRing.maximalIdeal F • (⊤ : Submodule F ((cohomologyCx C).X j)) := by
  rw [cohomologyCx_d]
  exact Submodule.zero_mem _

/-- **Over a field a minimal complex has zero differentials** (tex 4637–4640): the hypothesis
`hLmin` of the consumers forces `d = 0`, since the maximal ideal of a field is `0`. Kind: PROVED. -/
theorem d_eq_zero_of_minimal {L : CochainComplex (ModuleCat.{u} F) ℤ}
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal F • (⊤ : Submodule F (L.X j)))
    (i j : ℤ) : L.d i j = 0 := by
  ext x
  have h := hLmin i j x
  rw [IsLocalRing.maximalIdeal_eq_bot, Submodule.bot_smul, Submodule.mem_bot] at h
  simpa using h

/-- **The ranks of a minimal model are the dimensions of the cohomology** (tex 4637–4642: "its
ranks are the dimensions of the cohomology"): if `L` has zero differentials and `l : L → Q` is a
quasi-isomorphism, then `dim Lⁿ = dim Hⁿ(Q)`. Kind: PROVED. -/
theorem finrank_eq_finrank_homology_of_minimal {L Q : CochainComplex (ModuleCat.{u} F) ℤ}
    (hd : ∀ i j, L.d i j = 0) (l : L ⟶ Q) [QuasiIso l] (n : ℤ) :
    Module.finrank F (L.X n) = Module.finrank F (Q.homology n) := by
  have : IsIso (HomologicalComplex.homologyMap l n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  let e : L.X n ≅ Q.homology n :=
    (L.iCyclesIso n (n + 1) (by simp) (hd _ _)).symm ≪≫
      L.isoHomologyπ (n - 1) n (by simp) (hd _ _) ≪≫ asIso (HomologicalComplex.homologyMap l n)
  exact e.toLinearEquiv.finrank_eq

end Field

/-! ## The change of condition after inverting `t` -/

section Change

open ZInQ.Contrib.CloudB3RC53.ResidualTransfer ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- **The change of condition with acyclic quotient is a quasi-isomorphism** (tex 4626–4631; tex
3494–3498: "Replacing the unramified condition by the full condition then gives the singular
quotient"): for `0 → P → Q → W → 0` short exact with `W` acyclic, `P → Q` is a quasi-isomorphism.
Kind: PROVED (long exact sequence, `quasiIso_f_of_shortExact_acyclic`). -/
theorem quasiIso_of_change {R : Type u} [CommRing R] {P Q W : CochainComplex (ModuleCat.{u} R) ℤ}
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W.Acyclic) : QuasiIso ι :=
  quasiIso_f_of_shortExact_acyclic hE hW

/-- **The change of local conditions of Selmer data with acyclic quotient is a
quasi-isomorphism** (tex 3494–3498, 4624–4631): for Selmer data `G → L ← U` and a degreewise short
exact sequence of local conditions `0 → U' → U → W → 0` with `W` acyclic, the comparison
`C(U') → C(U)` is a quasi-isomorphism. Kind: PROVED (`relaxedQuotientNode_proof`). -/
theorem quasiIso_changeMap {R : Type u} [CommRing R] (Dfull : SelData R) (U' W : GCx R)
    (f : GHom U' Dfull.U) (g : GHom Dfull.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) : QuasiIso (GHom.toCC (changeMap Dfull f)) :=
  quasiIso_f_of_shortExact_acyclic (E := changeSES Dfull f g hfg)
    (relaxedQuotientNode_proof R Dfull U' W f g hfg hinj hsurj hex) hW

variable {F : Type u} [Field F]

/-- **The inclusion of the smaller-support model is a homotopy equivalence** (tex 4626–4631): over
a field, for `0 → P' → Q' → W' → 0` short exact with `W'` acyclic and `P'`, `Q'` bounded above, the
inclusion `P' → Q'` is the forward map of a homotopy equivalence. Kind: PROVED. -/
theorem exists_homotopyEquiv_inclusion {P' Q' W' : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [Q'.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) : ∃ e : HomotopyEquiv P' Q', e.hom = ι := by
  have := quasiIso_of_change ι π hιπ hE hW
  exact exists_homotopyEquiv_of_quasiIso b ι

/-- **Every active comparison cone is contractible after inverting `t`** (tex 4628–4629: "Every
active comparison cone is then contractible"): over a field, for `0 → P' → Q' → W' → 0` short exact
with `W'` acyclic and `P'`, `Q'` bounded above, the mapping cone of the inclusion `P' → Q'` is
contractible. Kind: PROVED (`cone_contractible_of_homotopyEquiv`). -/
theorem comparisonCone_contractible {k : Type} [Field k]
    {P' Q' W' : CochainComplex (ModuleCat.{0} k) ℤ} (b : ℤ) [P'.IsStrictlyLE b] [Q'.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone ι)) 0) :=
  cone_contractible_of_homotopyEquiv ι (exists_homotopyEquiv_inclusion b ι π hιπ hE hW)

/-- **The input `L ≃ P'` from the change of condition** (tex 4626–4631): over a field, let
`0 → P' → Q' → W' → 0` be short exact with `W'` acyclic, and let `l : L → Q'` be a
quasi-isomorphism (`L` a minimal model of `Q'`). If `P'` and `L` are bounded above, then `L` and
`P'` are homotopy equivalent. `Q'` and `W'` are arbitrary (no boundedness or finiteness).
Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_change {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (l : L ⟶ Q') [QuasiIso l] : Nonempty (HomotopyEquiv L P') := by
  have := quasiIso_of_change ι π hιπ hE hW
  exact nonempty_homotopyEquiv_of_zigzag b l ι

/-- **The homotopy equivalence `L ≃ P'`** supplied to the consumers (tex 4626–4631): a choice of
the equivalence of `nonempty_homotopyEquiv_of_change`. Kind: definition. -/
def homotopyEquivOfChange {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (l : L ⟶ Q') [QuasiIso l] : HomotopyEquiv L P' :=
  (nonempty_homotopyEquiv_of_change b ι π hιπ hE hW l).some

/-- **`L ≃ P'` when `L` is a minimal model of `Q'` given by a homotopy equivalence** (tex
4626–4640). Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_change_of_homotopyEquiv
    {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (eL : HomotopyEquiv L Q') : Nonempty (HomotopyEquiv L P') :=
  nonempty_homotopyEquiv_of_change b ι π hιπ hE hW eL.hom

/-- **`L ≃ P'` when the minimal model is given by a quasi-isomorphism `Q' → L`** (tex 4626–4640).
Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_change_of_quasiIso_to
    {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (r : Q' ⟶ L) [QuasiIso r] : Nonempty (HomotopyEquiv L P') := by
  have := quasiIso_of_change ι π hιπ hE hW
  obtain ⟨e, -⟩ := exists_homotopyEquiv_of_quasiIso b (ι ≫ r)
  exact ⟨e.symm⟩

/-- **`L ≃ P'` from a contractible comparison cone** (tex 4628–4631: "Every active comparison cone
is then contractible"): if the mapping cone of `j : P' → Q'` is contractible and `l : L → Q'` is a
quasi-isomorphism, `L ≃ P'`. Kind: PROVED (`homotopyEquiv_of_cone_contractible`). -/
theorem nonempty_homotopyEquiv_of_cone_contractible
    {P' Q' L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (j : P' ⟶ Q') (hj : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone j)) 0))
    (l : L ⟶ Q') [QuasiIso l] : Nonempty (HomotopyEquiv L P') := by
  obtain ⟨h⟩ := hj
  obtain ⟨e, he⟩ := homotopyEquiv_of_cone_contractible j h
  have : QuasiIso j := by
    rw [← he]
    infer_instance
  exact nonempty_homotopyEquiv_of_zigzag b l j

/-- **`L ≃ P'` from the change of local conditions of Selmer data** (tex 3494–3498, 4612–4631):
over a field, for Selmer data `Dfull` with the full condition, a degreewise short exact sequence of
local conditions `0 → U' → Dfull.U → W → 0` (`U'` the unramified condition) with `W` acyclic (the
singular quotient after inverting `t`), a quasi-isomorphism `pP : P' → C(U')` and a
quasi-isomorphism `pL : L → C(U_full)`, with `P'`, `L` bounded above: `L ≃ P'`. Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_selmerChange (Dfull : SelData F) (U' W : GCx F)
    (f : GHom U' Dfull.U) (g : GHom Dfull.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) {P' L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] : Nonempty (HomotopyEquiv L P') := by
  have := quasiIso_changeMap Dfull U' W f g hfg hinj hsurj hex hW
  exact nonempty_homotopyEquiv_of_zigzag b pL (pP ≫ GHom.toCC (changeMap Dfull f))

/-- **`L ≃ P'` through the support comparison and the change of condition** (tex 4612–4631): over
a field, `P' → C_{S₀} → C(U^ur) = C(restrictData Dfull f) → C(U_full) ← L`, where `P' → C_{S₀}` is a
quasi-isomorphism (`pP`), the support comparison `C_{S₀} → C(U^ur)` is a quasi-isomorphism (`hT`,
the conclusion of Nekovář 7.8.8(ii) after inverting `t`), the change of condition has acyclic
quotient `W`, and `pL : L → C(U_full)` is a quasi-isomorphism. Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_supportChange (T : SupportChangeData F)
    (hT : QuasiIso (GHom.toCC (supportMap T)))
    (Dfull : SelData F) (W : GCx F) (f : GHom T.Dp.U Dfull.U) (g : GHom Dfull.U W)
    (hDp : T.Dp = restrictData Dfull f)
    (hfg : ∀ i (u : T.Dp.U.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) {P' L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (pP : P' ⟶ (selCx T.D).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] : Nonempty (HomotopyEquiv L P') := by
  have := quasiIso_changeMap Dfull T.Dp.U W f g hfg hinj hsurj hex hW
  let e3 : (selCx T.Dp).toCC ≅ (selCx (restrictData Dfull f)).toCC :=
    eqToIso (congrArg (fun D => (selCx D).toCC) hDp)
  exact nonempty_homotopyEquiv_of_zigzag b pL
    (pP ≫ GHom.toCC (supportMap T) ≫ e3.hom ≫ GHom.toCC (changeMap Dfull f))

/-- **The cohomology of `Q'` is homotopy equivalent to `P'`** (tex 4626–4640): over a field, for
`0 → P' → Q' → W' → 0` short exact with `W'` acyclic and `P'` bounded above, the minimal model
`H(Q')` of `Q'` is homotopy equivalent to `P'`. Kind: PROVED. -/
theorem nonempty_homotopyEquiv_cohomologyCx_of_change
    {P' Q' W' : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ) [P'.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) : Nonempty (HomotopyEquiv (cohomologyCx Q') P') := by
  have := quasiIso_of_change ι π hιπ hE hW
  have : Q'.IsLE b := isLE_of_quasiIso ι b
  exact nonempty_homotopyEquiv_of_zigzag b (cohomologyRep Q') ι

end Change

/-! ## From the integral diagram: base change and the comparison homotopy -/

section BaseChange

open ZInQ.Contrib.CloudB3RC53.GenuineInst TensorProduct

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

/-- **The base change of a chain map** `S ⊗_R g` along `φ : R → S` (tex 4626–4628: "only then
invert `t`"), on the complexes `baseChangeCx` of `GenuineInst/ResidualAfterT2.lean`.
Kind: definition. -/
def baseChangeCxMap {P Q : CochainComplex (ModuleCat.{0} R) ℤ} (g : P ⟶ Q) :
    baseChangeCx φ P ⟶ baseChangeCx φ Q :=
  letI := φ.toAlgebra
  { f := fun n => ModuleCat.ofHom ((g.f n).hom.baseChange S)
    comm' := fun i j _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro (x : S ⊗[R] P.X i)
      change ((Q.d i j).hom.baseChange S) (((g.f i).hom.baseChange S) x) =
        ((g.f j).hom.baseChange S) (((P.d i j).hom.baseChange S) x)
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, g.comm] }

/-- The base change of a composite is the composite of the base changes (tex 4626–4628).
Kind: PROVED. -/
theorem baseChangeCxMap_comp {P Q W : CochainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)
    (g : Q ⟶ W) : baseChangeCxMap φ (f ≫ g) = baseChangeCxMap φ f ≫ baseChangeCxMap φ g := by
  let := φ.toAlgebra
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : S ⊗[R] P.X n)
  change ((f ≫ g).f n).hom.baseChange S x =
    ((g.f n).hom.baseChange S) (((f.f n).hom.baseChange S) x)
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

/-- The base change of the zero map is zero (tex 4626–4628). Kind: PROVED. -/
theorem baseChangeCxMap_zero (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    baseChangeCxMap φ (0 : P ⟶ Q) = 0 := by
  let := φ.toAlgebra
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : S ⊗[R] P.X n)
  change ((0 : P ⟶ Q).f n).hom.baseChange S x = 0
  rw [HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.baseChange_zero,
    LinearMap.zero_apply]

/-- The base change of a complex strictly `≤ b` is strictly `≤ b` (tex 4626–4631). Kind: PROVED. -/
instance baseChangeCx_isStrictlyLE (P : CochainComplex (ModuleCat.{0} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] : (baseChangeCx φ P).IsStrictlyLE b := by
  let := φ.toAlgebra
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero (P.isZero_of_isStrictlyLE b i hi)
  have : Unique (S ⊗[R] P.X i) := TensorProduct.uniqueRight
  have : Subsingleton ((baseChangeCx φ P).X i) := inferInstanceAs (Subsingleton (S ⊗[R] P.X i))
  exact ModuleCat.isZero_of_subsingleton _

/-- The base change of a complex strictly `≥ a` is strictly `≥ a` (tex 4626–4631). Kind: PROVED. -/
instance baseChangeCx_isStrictlyGE (P : CochainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    [P.IsStrictlyGE a] : (baseChangeCx φ P).IsStrictlyGE a := by
  let := φ.toAlgebra
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero (P.isZero_of_isStrictlyGE a i hi)
  have : Unique (S ⊗[R] P.X i) := TensorProduct.uniqueRight
  have : Subsingleton ((baseChangeCx φ P).X i) := inferInstanceAs (Subsingleton (S ⊗[R] P.X i))
  exact ModuleCat.isZero_of_subsingleton _

/-- The base change of a finite term is finite (tex 4626–4631). Kind: PROVED. -/
instance baseChangeCx_finite (P : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)
    [Module.Finite R (P.X n)] : Module.Finite S ((baseChangeCx φ P).X n) := by
  let := φ.toAlgebra
  change Module.Finite S (S ⊗[R] P.X n)
  infer_instance

/-- **Flat base change preserves the change-of-condition sequence** (tex 4626–4628: invert `t`
after the inner limit): if `S` is flat over `R` (through `φ`) and `0 → P → Q → W → 0` is short
exact, so is `0 → S ⊗ P → S ⊗ Q → S ⊗ W → 0`. Kind: PROVED. -/
theorem baseChangeCx_shortExact (hφ : letI := φ.toAlgebra; Module.Flat R S)
    {P Q W : CochainComplex (ModuleCat.{0} R) ℤ} (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) :
    (ShortComplex.mk (baseChangeCxMap φ ι) (baseChangeCxMap φ π)
      (by rw [← baseChangeCxMap_comp, hιπ, baseChangeCxMap_zero])).ShortExact := by
  let := φ.toAlgebra
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact] at hE ⊢
  intro n
  have hn := hE n
  have hinj : Function.Injective (ι.f n).hom := hn.moduleCat_injective_f
  have hsurj : Function.Surjective (π.f n).hom := hn.moduleCat_surjective_g
  have hex : Function.Exact (ι.f n).hom (π.f n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hn.exact
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact lTensor_exact S hex hsurj
  · exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · exact LinearMap.lTensor_surjective S hsurj

/-- **The comparison blocks become acyclic after inverting `c`** (tex 4619–4626: "Both
`((1+t)^e−1)/t` and `((1+t)^{−e}−1)/t` are units of `𝔽₂[[t]]`. Thus the full, unramified and
singular comparison blocks all become contractible after inverting `t`"): if multiplication by `c`
on `W` is null-homotopic (`d h + h d = c`) and `φ c` is a unit, then `S ⊗ W` is acyclic.
Kind: PROVED. -/
theorem baseChangeCx_acyclic_of_homotopy {W : CochainComplex (ModuleCat.{0} R) ℤ} (c : R)
    (H : Homotopy (c • 𝟙 W) 0) (hc : IsUnit (φ c)) : (baseChangeCx φ W).Acyclic := by
  let := φ.toAlgebra
  intro i
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro (x : S ⊗[R] W.X i) hx
  have hx' : ((W.d i (i + 1)).hom.baseChange S) x = 0 := hx
  have hcomm := H.comm i
  rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] at hcomm
  have hlin : c • (LinearMap.id : W.X i →ₗ[R] W.X i) =
      (H.hom (i + 1) i).hom ∘ₗ (W.d i (i + 1)).hom +
        (W.d (i - 1) i).hom ∘ₗ (H.hom i (i - 1)).hom := by
    have := congrArg ModuleCat.Hom.hom hcomm
    simpa using this
  have hbc := congrArg (fun f => LinearMap.baseChange S f x) hlin
  simp only [LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.baseChange_add,
    LinearMap.baseChange_comp, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.add_apply,
    LinearMap.comp_apply, hx', map_zero, zero_add] at hbc
  obtain ⟨u, hu⟩ := hc
  refine ⟨((u⁻¹ : Sˣ) : S) • ((H.hom i (i - 1)).hom.baseChange S) x, ?_⟩
  change ((W.d (i - 1) i).hom.baseChange S)
    (((u⁻¹ : Sˣ) : S) • ((H.hom i (i - 1)).hom.baseChange S) x) = x
  rw [map_smul, ← hbc, ← algebraMap_smul S c x, smul_smul]
  change (((u⁻¹ : Sˣ) : S) * φ c) • x = x
  rw [← hu, Units.inv_mul, one_smul]

end BaseChange

section Integral

open ZInQ.Contrib.CloudB3RC53.GenuineInst

/-- **`L ≃ P'` from the integral change of condition** (tex 4619–4631): for a flat `φ : R → S`
into a field, an integral short exact sequence `0 → P → Q → W → 0` over `R` with `P` bounded above,
and a homotopy `d h + h d = c` on `W` with `φ c` a unit, the cohomology of `S ⊗ Q` (the minimal
model of the generic original-support model) is homotopy equivalent to `S ⊗ P`. Kind: PROVED. -/
theorem nonempty_homotopyEquiv_of_integralChange {R S : Type} [CommRing R] [Field S]
    (φ : R →+* S) (hφ : letI := φ.toAlgebra; Module.Flat R S)
    {P Q W : CochainComplex (ModuleCat.{0} R) ℤ} (b : ℤ) [P.IsStrictlyLE b]
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : R) (H : Homotopy (c • 𝟙 W) 0) (hc : IsUnit (φ c)) :
    Nonempty (HomotopyEquiv (cohomologyCx (baseChangeCx φ Q)) (baseChangeCx φ P)) :=
  nonempty_homotopyEquiv_cohomologyCx_of_change b (baseChangeCxMap φ ι) (baseChangeCxMap φ π) _
    (baseChangeCx_shortExact φ hφ ι π hιπ hE) (baseChangeCx_acyclic_of_homotopy φ c H hc)

/-- **The comparison blocks become contractible after inverting `c`** (tex 4624–4626: "Thus the
full, unramified and singular comparison blocks all become contractible after inverting `t`"): for
`φ : R → S` into a field, a bounded-above `W` over `R` with a homotopy `d h + h d = c` and `φ c` a
unit, the base change `S ⊗ W` is contractible. Kind: PROVED (acyclic and K-projective). -/
theorem baseChangeCx_contractible_of_homotopy {R S : Type} [CommRing R] [Field S] (φ : R →+* S)
    {W : CochainComplex (ModuleCat.{0} R) ℤ} (b : ℤ) [W.IsStrictlyLE b] (c : R)
    (H : Homotopy (c • 𝟙 W) 0) (hc : IsUnit (φ c)) :
    Nonempty (Homotopy (𝟙 (baseChangeCx φ W)) 0) :=
  ZInQ.Contrib.CloudB3RC53.PairedFunctional.contractible_of_acyclic_projective
    (baseChangeCx φ W) b (baseChangeCx_acyclic_of_homotopy φ c H hc)

/-- **`𝔽₂((t))` is flat over `𝔽₂[[t]]`** (tex 4626–4628: inverting `t` is a localization), for the
module structure through `algebraMap`, as used by `baseChangeCx`. Kind: PROVED
(`IsLocalization.flat`). -/
theorem laurentSeries_flat :
    letI := (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))).toAlgebra
    Module.Flat (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) :=
  IsLocalization.flat (LaurentSeries (ZMod 2)) (nonZeroDivisors (PowerSeries (ZMod 2)))

/-- **The generic complex** `𝔽₂((t)) ⊗ Q` of a complex over `𝔽₂[[t]]` (tex 4626–4628).
Kind: definition. -/
abbrev genericCx (Q : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ) :
    CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ :=
  baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) Q

/-- **The generic chain map** `𝔽₂((t)) ⊗ g` (tex 4626–4628). Kind: definition. -/
abbrev genericMap {P Q : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ} (g : P ⟶ Q) :
    genericCx P ⟶ genericCx Q :=
  baseChangeCxMap (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) g

/-- **The generic inclusion of the smaller-support model is a quasi-isomorphism** (tex
4619–4631), from the integral change of condition and its comparison homotopy. Kind: PROVED. -/
theorem genericMap_quasiIso {P Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ}
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    QuasiIso (genericMap ι) :=
  quasiIso_of_change _ _ _ (baseChangeCx_shortExact _ laurentSeries_flat ι π hιπ hE)
    (baseChangeCx_acyclic_of_homotopy _ c H hc)

/-- **The homotopy equivalence `H(𝔽₂((t)) ⊗ Q) ≃ 𝔽₂((t)) ⊗ P`** from the integral data (tex
4619–4640): a choice of the equivalence of `nonempty_homotopyEquiv_of_integralChange` at
`𝔽₂[[t]] → 𝔽₂((t))`. Kind: definition. -/
def genericHomotopyEquiv {P Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ}
    [P.IsStrictlyLE 3]
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    HomotopyEquiv (cohomologyCx (genericCx Q)) (genericCx P) :=
  (nonempty_homotopyEquiv_of_integralChange _ laurentSeries_flat 3 ι π hιπ hE c H hc).some

/-- **The transfer after inverting `t`, from the change of condition** (tex 4626–4647): if `P` is
a bounded free model over `𝔽₂[[t]]`, `P'` its base change (as a complex), and
`0 → P' → Q' → W' → 0` short exact with `W'` acyclic, then the generic cohomology of `Q'` has total
dimension at most the total rank of `P`, over any finite set of degrees. Kind: PROVED. -/
theorem sum_finrank_homology_le_of_change
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)]
    (P' Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ) (a b : ℤ)
    [P'.IsStrictlyGE a] [P'.IsStrictlyLE b] [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n) ≤
      ∑ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n) := by
  have := quasiIso_of_change ι π hιπ hE hW
  have : Q'.IsLE b := isLE_of_quasiIso ι b
  have : Q'.IsGE a := isGE_of_quasiIso ι a
  have : ∀ n, Module.Finite (LaurentSeries (ZMod 2)) ((cohomologyCx Q').X n) :=
    fun n => homology_finite_of_quasiIso ι n
  exact transfer_after_inverting_t' _ P P' (cohomologyCx Q') a b ebc (cohomologyCx_minimal Q')
    (homotopyEquivOfChange b ι π hιπ hE hW (cohomologyRep Q')) s _ _ rfl rfl

/-- **The transfer after inverting `t`, from the integral diagram** (tex 4619–4647): for a bounded
free model `P` over `𝔽₂[[t]]`, an integral short exact sequence `0 → P → Q → W → 0` and a homotopy
`d h + h d = c` on `W` with `c` a unit in `𝔽₂((t))`, the generic cohomology of `Q` has total
dimension at most the total rank of `P`. Kind: PROVED. -/
theorem sum_finrank_genericHomology_le_of_integralChange
    (P Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c))
    (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2)) ((genericCx Q).homology n) ≤
      ∑ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n) :=
  sum_finrank_homology_le_of_change P (genericCx P) (genericCx Q) (genericCx W) a b (Iso.refl _)
    (genericMap ι) (genericMap π) _ (baseChangeCx_shortExact _ laurentSeries_flat ι π hιπ hE)
    (baseChangeCx_acyclic_of_homotopy _ c H hc) s

end Integral

/-! ## The consumers `residualRankCounts_afterT'`, `''`, `'''` -/

section Consumers

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.GenuineInst TensorProduct

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **`residualRankCounts_afterT'` with the homotopy equivalence derived from the change of
condition** (tex 4453–4648; the input `e` of tex 4626–4631): the input `e : L ≃ P'` is replaced by
the change of condition `0 → P' → Q' → W' → 0` over `𝔽₂((t))` with `W'` acyclic (the active
comparison blocks after inverting `t`) and a quasi-isomorphism `l : L → Q'` (`L` a minimal model of
the original-support complex `Q'`); `e := homotopyEquivOfChange 3 ι π hιπ hE hW l`.
Kind: definition (PROVED from the inputs in its type). -/
def residualRankCounts_afterT'_ofChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    ResidualRankCounts :=
  residualRankCounts_afterT' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG hG3 hUm hLm P ered P' L ebc hLmin
    (homotopyEquivOfChange 3 ι π hιπ hE hW l)

open Classical in
/-- **`residualRankCounts_afterT''` with the homotopy equivalence derived from the change of
condition** (tex 4453–4648; the input `e` of tex 4626–4631): as
`residualRankCounts_afterT'_ofChange`, with the degree-`3` identification `eG3` against Mathlib's
continuous `H³`. Kind: definition (PROVED from the inputs in its type). -/
def residualRankCounts_afterT''_ofChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2]
      continuousCohomology 3 (Wrep K (primesAboveSet K (chargedPrimes N r D))))
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    ResidualRankCounts :=
  residualRankCounts_afterT'' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
    (homotopyEquivOfChange 3 ι π hιπ hE hW l)

open Classical in
/-- **`residualRankCounts_afterT'''` with the homotopy equivalence derived from the change of
condition** (tex 4453–4648; the input `e` of tex 4626–4631): as
`residualRankCounts_afterT'_ofChange`, with the degree-`3` identification `eG3` against the genuine
`genH K S₀ 3`. Kind: definition (PROVED from the inputs in its type). -/
def residualRankCounts_afterT'''_ofChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    ResidualRankCounts :=
  residualRankCounts_afterT''' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
    (homotopyEquivOfChange 3 ι π hιπ hE hW l)

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'_ofChange` is the generic cohomology of the
original-support complex** (tex 4637–4642): `∑_{n ∈ [0, 3]} dim Hⁿ(Q')`, since `L` is minimal and
`l : L → Q'` is a quasi-isomorphism. Kind: PROVED. -/
theorem residualRankCounts_afterT'_ofChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    (residualRankCounts_afterT'_ofChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG hG3 hUm hLm P ered P' L ebc hLmin
      Q' W' ι π hιπ hE hW l).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n) := by
  show ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (L.X n) = _
  exact Finset.sum_congr rfl fun n _ =>
    finrank_eq_finrank_homology_of_minimal (d_eq_zero_of_minimal hLmin) l n

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'''_ofChange` is the generic cohomology of the
original-support complex** (tex 4637–4642): `∑_{n ∈ [0, 3]} dim Hⁿ(Q')`, since `L` is minimal and
`l : L → Q'` is a quasi-isomorphism. Kind: PROVED. -/
theorem residualRankCounts_afterT'''_ofChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    (residualRankCounts_afterT'''_ofChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
      Q' W' ι π hιπ hE hW l).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n) := by
  show ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (L.X n) = _
  exact Finset.sum_congr rfl fun n _ =>
    finrank_eq_finrank_homology_of_minimal (d_eq_zero_of_minimal hLmin) l n

open Classical in
/-- **`residualRankCounts_afterT'''` with the homotopy equivalence derived from the change of
local conditions of Selmer data over `𝔽₂((t))`** (tex 3494–3498, 4612–4631): `e` is replaced by
Selmer data `Dfull` over `𝔽₂((t))` with the full condition, a degreewise short exact sequence of
local conditions `0 → U' → Dfull.U → Wc → 0` with acyclic quotient (the singular quotient after
inverting `t`), a quasi-isomorphism `pP : P' → C(U')` (the smaller-support model through the support
comparison) and a quasi-isomorphism `pL : L → C(U_full)` (`L` a minimal model of the
original-support complex). Kind: definition (PROVED from the inputs in its type). -/
def residualRankCounts_afterT'''_ofSelmerChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of local conditions of Selmer data over `𝔽₂((t))`, and the models `P'`, `L`
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] :
    ResidualRankCounts :=
  residualRankCounts_afterT''' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
    (nonempty_homotopyEquiv_of_selmerChange Dfull U' Wc f g hfg hinj hsurj hex hWc 3 pP pL).some

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'''_ofSelmerChange` is the generic cohomology
of the original-support Selmer complex** (tex 4637–4642): `∑_{n ∈ [0, 3]} dim Hⁿ(C(U_full))`.
Kind: PROVED. -/
theorem residualRankCounts_afterT'''_ofSelmerChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of local conditions of Selmer data over `𝔽₂((t))`, and the models `P'`, `L`
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] :
    (residualRankCounts_afterT'''_ofSelmerChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
      Dfull U' Wc f g hfg hinj hsurj hex hWc pP pL).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((selCx Dfull).toCC.homology n) := by
  show ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (L.X n) = _
  exact Finset.sum_congr rfl fun n _ =>
    finrank_eq_finrank_homology_of_minimal (d_eq_zero_of_minimal hLmin) pL n

open Classical in
/-- **`residualRankCounts_afterT'` from the integral change of condition** (tex 4453–4648; tex
4619–4631): the generic models are built: `P' = 𝔽₂((t)) ⊗ P` (`ebc` the identity), `L` the
cohomology of `𝔽₂((t)) ⊗ Q` (minimal, finite, supported in `[0, 3]`), and `e` from the integral
short exact sequence `0 → P → Q → W → 0` over `𝔽₂[[t]]` and the comparison homotopy
`d h + h d = c` on `W`, with `c` a unit in `𝔽₂((t))`. Kind: definition (PROVED from the inputs in
its type). -/
def residualRankCounts_afterT'_ofIntegralChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    ResidualRankCounts :=
  haveI := genericMap_quasiIso ι π hιπ hE c H hc
  haveI : (genericCx Q).IsLE 3 := isLE_of_quasiIso (genericMap ι) 3
  haveI : (genericCx Q).IsGE 0 := isGE_of_quasiIso (genericMap ι) 0
  haveI : ∀ n, Module.Finite (LaurentSeries (ZMod 2)) ((cohomologyCx (genericCx Q)).X n) :=
    fun n => homology_finite_of_quasiIso (genericMap ι) n
  residualRankCounts_afterT' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG hG3 hUm hLm P ered (genericCx P)
    (cohomologyCx (genericCx Q)) (Iso.refl _) (cohomologyCx_minimal _)
    (genericHomotopyEquiv ι π hιπ hE c H hc)

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'_ofIntegralChange` is the generic cohomology
of the integral original-support model** (tex 4626–4642): `∑_{n ∈ [0, 3]} dim Hⁿ(𝔽₂((t)) ⊗ Q)`.
Kind: PROVED. -/
theorem residualRankCounts_afterT'_ofIntegralChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    (residualRankCounts_afterT'_ofIntegralChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG hG3 hUm hLm P ered
      Q W ι π hιπ hE c H hc).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((genericCx Q).homology n) :=
  rfl

open Classical in
/-- **`residualRankCounts_afterT'''` from the integral change of condition** (tex 4453–4648; tex
4619–4631): as `residualRankCounts_afterT'_ofIntegralChange`, with the degree-`3` identification
`eG3` against the genuine `genH K S₀ 3`. Kind: definition (PROVED from the inputs in its type). -/
def residualRankCounts_afterT'''_ofIntegralChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    ResidualRankCounts :=
  haveI := genericMap_quasiIso ι π hιπ hE c H hc
  haveI : (genericCx Q).IsLE 3 := isLE_of_quasiIso (genericMap ι) 3
  haveI : (genericCx Q).IsGE 0 := isGE_of_quasiIso (genericMap ι) 0
  haveI : ∀ n, Module.Finite (LaurentSeries (ZMod 2)) ((cohomologyCx (genericCx Q)).X n) :=
    fun n => homology_finite_of_quasiIso (genericMap ι) n
  residualRankCounts_afterT''' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG eG3 hUm hLm P ered (genericCx P)
    (cohomologyCx (genericCx Q)) (Iso.refl _) (cohomologyCx_minimal _)
    (genericHomotopyEquiv ι π hιπ hE c H hc)

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'''_ofIntegralChange` is the generic
cohomology of the integral original-support model** (tex 4626–4642):
`∑_{n ∈ [0, 3]} dim Hⁿ(𝔽₂((t)) ⊗ Q)`. Kind: PROVED. -/
theorem residualRankCounts_afterT'''_ofIntegralChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    (residualRankCounts_afterT'''_ofIntegralChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered
      Q W ι π hιπ hE c H hc).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((genericCx Q).homology n) :=
  rfl

open Classical in
/-- **`residualRankCounts_afterT'''` with the minimal model and the homotopy equivalence built from
the change of condition** (tex 4453–4648, 4626–4640): no minimal model is supplied; `L` is the
cohomology of `Q'` (finite, supported in `[0, 3]` and minimal, since `P' → Q'` is a
quasi-isomorphism), and `e : L ≃ P'` comes from the change of condition `0 → P' → Q' → W' → 0` with
`W'` acyclic. Kind: definition (PROVED from the inputs in its type). -/
def residualRankCounts_afterT'''_ofChangeCohomology (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of condition after inverting `t`; the minimal model is the cohomology of `Q'`
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic) :
    ResidualRankCounts :=
  haveI := quasiIso_of_change ι π hιπ hE hW
  haveI : Q'.IsLE 3 := isLE_of_quasiIso ι 3
  haveI : Q'.IsGE 0 := isGE_of_quasiIso ι 0
  haveI : ∀ n, Module.Finite (LaurentSeries (ZMod 2)) ((cohomologyCx Q').X n) :=
    fun n => homology_finite_of_quasiIso ι n
  residualRankCounts_afterT''' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P'
    (cohomologyCx Q') ebc (cohomologyCx_minimal Q')
    (homotopyEquivOfChange 3 ι π hιπ hE hW (cohomologyRep Q'))

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'''_ofChangeCohomology` is the generic
cohomology of the original-support complex** (tex 4637–4642): `∑_{n ∈ [0, 3]} dim Hⁿ(Q')`.
Kind: PROVED. -/
theorem residualRankCounts_afterT'''_ofChangeCohomology_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of condition after inverting `t`; the minimal model is the cohomology of `Q'`
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic) :
    (residualRankCounts_afterT'''_ofChangeCohomology K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' ebc
      Q' W' ι π hιπ hE hW).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n) :=
  rfl

open Classical in
/-- **`residualRankCounts_afterT'''` from the change of local conditions of Selmer data over
`𝔽₂((t))`, with the minimal model built** (tex 3494–3498, 4612–4640): the inputs are Selmer data
`Dfull` over `𝔽₂((t))` with the full condition, a degreewise short exact sequence of local
conditions `0 → U' → Dfull.U → Wc → 0` with acyclic quotient (the singular quotient after inverting
`t`), and a quasi-isomorphism `pP : P' → C(U')` (the smaller-support model through the support
comparison). `L` is the cohomology of the original-support Selmer complex `C(U_full)`, and
`e : L ≃ P'` comes from `L → C(U_full) ← C(U') ← P'`. Kind: definition (PROVED from the inputs in
its type). -/
def residualRankCounts_afterT'''_ofSelmerChangeCohomology (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of local conditions of Selmer data over `𝔽₂((t))`; the minimal model is the
    -- cohomology of the original-support Selmer complex
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP] :
    ResidualRankCounts :=
  haveI := quasiIso_changeMap Dfull U' Wc f g hfg hinj hsurj hex hWc
  haveI : QuasiIso (pP ≫ GHom.toCC (changeMap Dfull f)) := inferInstance
  haveI : (selCx Dfull).toCC.IsLE 3 := isLE_of_quasiIso (pP ≫ GHom.toCC (changeMap Dfull f)) 3
  haveI : (selCx Dfull).toCC.IsGE 0 := isGE_of_quasiIso (pP ≫ GHom.toCC (changeMap Dfull f)) 0
  haveI : ∀ n, Module.Finite (LaurentSeries (ZMod 2)) ((cohomologyCx (selCx Dfull).toCC).X n) :=
    fun n => homology_finite_of_quasiIso (pP ≫ GHom.toCC (changeMap Dfull f)) n
  residualRankCounts_afterT''' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P'
    (cohomologyCx (selCx Dfull).toCC) ebc (cohomologyCx_minimal _)
    (nonempty_homotopyEquiv_of_zigzag 3 (cohomologyRep _)
      (pP ≫ GHom.toCC (changeMap Dfull f))).some

open Classical in
/-- **The generic rank of `residualRankCounts_afterT'''_ofSelmerChangeCohomology` is the generic
cohomology of the original-support Selmer complex** (tex 4637–4642):
`∑_{n ∈ [0, 3]} dim Hⁿ(C(U_full))`. Kind: PROVED. -/
theorem residualRankCounts_afterT'''_ofSelmerChangeCohomology_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of local conditions of Selmer data over `𝔽₂((t))`; the minimal model is the
    -- cohomology of the original-support Selmer complex
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP] :
    (residualRankCounts_afterT'''_ofSelmerChangeCohomology K Ew h410 h51 h28 h23 k α hα hK N hN A
      hA r hr D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P'
      ebc Dfull U' Wc f g hfg hinj hsurj hex hWc pP).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((selCx Dfull).toCC.homology n) :=
  rfl

end Consumers

/-! ## Non-vacuity -/

section NonVacuity

open ZInQ.Manuscript.RC.Limits

variable {R : Type u} [CommRing R]

/-- **The active comparison block** (tex 4619–4626): the mapping cone of multiplication by `c` on a
complex `K`. At an oriented active place `K` is `𝔽₂[[t]]²` in one degree and `c = (1+t)^e − 1`
(the reduction of (4.4): `C = 0`, `A = D = ((1+t)^e − 1) I₂`). Kind: definition. -/
abbrev activeBlock (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (c • 𝟙 K)

/-- **The comparison homotopy of the active block** (tex 4619–4628, "retain the comparison maps and
homotopies"): multiplication by `c` on the cone of multiplication by `c` is null-homotopic.
Kind: definition. -/
def activeBlockHomotopy (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) :
    Homotopy (c • 𝟙 (activeBlock K c)) 0 :=
  CochainComplex.mappingCone.descHomotopy (c • 𝟙 K) _ _ 0 (CochainComplex.mappingCone.inl _)
    (by simp) (by simp)

/-- **Non-vacuity of the integral hypotheses** (tex 4619–4631): for every bounded-above `P` over
`𝔽₂[[t]]`, every complex `K` and every odd `e`, the split model `Q = P ⊞ W`, with `W` the active
block of `c = (1+t)^e − 1` on `K`, satisfies the hypotheses of
`nonempty_homotopyEquiv_of_integralChange`; so the cohomology of `𝔽₂((t)) ⊗ Q` is homotopy
equivalent to `𝔽₂((t)) ⊗ P`. Kind: PROVED. -/
theorem integralChange_nonvacuous (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] (K : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    {e : ℕ} (he : Odd e) :
    Nonempty (HomotopyEquiv
      (cohomologyCx (genericCx
        (P ⊞ activeBlock K (((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ e - 1))))
      (genericCx P)) :=
  nonempty_homotopyEquiv_of_integralChange _ laurentSeries_flat b biprod.inl biprod.snd
    (by simp) (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact _
    (activeBlockHomotopy K _) (isUnit_laurentSeries_one_add_X_pow_sub_one he)

/-- **The transfer inequality for the split model with an active block** (tex 4619–4647): for a
bounded free `P` over `𝔽₂[[t]]`, every `K` and every odd `e`, the generic cohomology of
`P ⊞ W` (`W` the active block of `(1+t)^e − 1` on `K`) has total dimension at most the total rank
of `P`. Kind: PROVED. -/
theorem integralChange_transfer_nonvacuous
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (K : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ) {e : ℕ} (he : Odd e)
    (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2))
        ((genericCx (P ⊞ activeBlock K (((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ e
          - 1))).homology n) ≤
      ∑ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n) :=
  sum_finrank_genericHomology_le_of_integralChange P _ _ a b biprod.inl biprod.snd (by simp)
    (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact _ (activeBlockHomotopy K _)
    (isUnit_laurentSeries_one_add_X_pow_sub_one he) s

end NonVacuity

/-! ## Non-vacuity at the active witness -/

section Witness

open NumberField IsDedekindDomain TensorProduct
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.RC53Assist.ResidualWitnessActive
  ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT

open scoped Classical

/-- **A relation-indexed null-homotopy of `c` is a homotopy `c • 𝟙 ≃ 0`** (tex 4619–4628, "retain
the comparison maps and homotopies"): the witness's `CHomotopy C c` (`d h + h d = c`) as Mathlib's
`Homotopy (c • 𝟙 C.toCC) 0`. Kind: definition (PROVED identities). -/
def homotopyOfCHomotopy {R : Type} [CommRing R] {C : GCx R} {c : R} (H : CHomotopy C c) :
    Homotopy (c • 𝟙 C.toCC) 0 :=
  homotopyOfIdentities _ _ (fun a b hab => H.h a b hab) (by
    intro a
    erw [toCC_d_hom_eq C a (a + 1) rfl, toCC_d_hom_eq C (a - 1) a (by omega)]
    apply LinearMap.ext
    intro (x : C.X a)
    change c • x = H.h (a + 1) a rfl (C.d a (a + 1) rfl x) +
      C.d (a - 1) a (by omega) (H.h a (a - 1) (by omega) x) + 0
    rw [add_zero, add_comm]
    exact (H.spec a (a - 1) (a + 1) (by omega) rfl x).symm)

/-- **The integral inclusion of the smaller-support model at the witness** `afterP → afterQ =
afterP ⊕ activeW` over `𝔽₂[[t]]` (tex 3494–3498, 4626–4628). Kind: definition. -/
abbrev witnessIncl : afterP ⟶ afterQ_G.toCC :=
  GHom.toCC (prodLift (idGHom afterP_G) (zeroGHom afterP_G activeW))

/-- **The integral projection onto the active comparison blocks at the witness**
`afterQ → activeW` (tex 3494–3498, 4619–4626). Kind: definition. -/
abbrev witnessProj : afterQ_G.toCC ⟶ activeW.toCC := GHom.toCC (prodSnd afterP_G activeW)

/-- The integral inclusion followed by the projection is zero (tex 3494–3498). Kind: PROVED. -/
theorem witnessIncl_proj : witnessIncl ≫ witnessProj = 0 := by
  ext i x
  rfl

/-- **The integral change of condition at the witness is short exact**:
`0 → afterP → afterP ⊕ activeW → activeW → 0` over `𝔽₂[[t]]` (tex 3494–3498, 4626–4628).
Kind: PROVED. -/
theorem witness_integralSES :
    (ShortComplex.mk witnessIncl witnessProj witnessIncl_proj).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro (z : afterP_G.X i × activeW.X i)
    constructor
    · intro hz
      refine ⟨z.1, ?_⟩
      change (z.1, (0 : activeW.X i)) = z
      have hz' : z.2 = 0 := hz
      rw [← hz']
    · rintro ⟨a, rfl⟩
      rfl
  · intro a b h
    exact congrArg Prod.fst h
  · intro (w : activeW.X i)
    exact ⟨((0 : afterP_G.X i), w), rfl⟩

/-- **`residualRankCounts_afterT''_ofChange` at the active witness** (tex 4453–4648, 4626–4631):
the witness's generic change of condition `0 → afterP' → afterQ' → activeW' → 0`
(`afterSES_shortExact`), whose quotient is acyclic after inverting `t` (`activeW'_acyclic`), and the
cohomology representatives `afterL → afterQ'` (`homologyModelTo_quasiIso`) supply the input `e`.
Kind: definition. -/
def witnessCountsOfChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : ∀ n, Module.Free Rt (afterP.X n) := afterP_free
  letI : ∀ n, Module.Finite Rt (afterP.X n) := afterP_finite h410 h51 h28
  letI : afterP.IsStrictlyGE 0 := (afterP_supported h410 h28).1
  letI : afterP.IsStrictlyLE 3 := (afterP_supported h410 h28).2
  letI : afterP'.IsStrictlyGE 0 := afterP'_ge h410 h28
  letI : afterP'.IsStrictlyLE 3 := afterP'_le h410 h28
  letI : afterL.IsStrictlyGE 0 := afterL_ge h410 h28
  letI : afterL.IsStrictlyLE 3 := afterL_le h410 h28
  letI : ∀ n, Module.Finite Kt (afterP'.X n) := afterP'_finite h410 h51 h28
  letI : ∀ n, Module.Finite Kt (afterL.X n) := afterL_finite h410 h51 h28
  haveI := homologyModelTo_quasiIso afterQ'
  exact residualRankCounts_afterT''_ofChange SmallK smallLocalModels h410 h51 h28 h23
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp) 5 (by decide)
    actD actD_prime actD_odd actCond actCond_derivative actCond_full_torsion
    smallInfinitePlace smallInfinitePlace_complex SmallS actSel actEG_full (witness_eG3 h410)
    (act_hUm_full_eq h28).le (act_hLm_full_eq h28).le afterP witness_ered
    afterP' afterL witness_ebc afterL_minimal afterQ' activeW'.toCC
    (GHom.toCC afterIncl) (GHom.toCC afterProj) afterSES.zero afterSES_shortExact
    activeW'_acyclic (homologyModelTo afterQ')

/-- **The bounds for `witnessCountsOfChange`** (tex 4453–4648): `2 ≤ genericRank ≤ rankTot` and
`genericRank ≤ 294`. Kind: PROVED. -/
theorem witnessCountsOfChange_bounds (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (witnessCountsOfChange h410 h51 h28 h23).genericRank ∧
      (witnessCountsOfChange h410 h51 h28 h23).genericRank ≤
        (witnessCountsOfChange h410 h51 h28 h23).rankTot ∧
      (witnessCountsOfChange h410 h51 h28 h23).genericRank ≤ 294 := by
  have hg : (witnessCountsOfChange h410 h51 h28 h23).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n) := rfl
  refine ⟨?_, (witnessCountsOfChange h410 h51 h28 h23).transfer, ?_⟩
  · rw [hg]
    exact (two_le_afterL_zero h410 h51 h28).trans (Finset.single_le_sum
      (f := fun n => Module.finrank Kt (afterQ'.homology n)) (fun _ _ => Nat.zero_le _)
      (show (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 3 by decide))
  · have hb := (witnessCountsOfChange h410 h51 h28 h23).genericRank_le
    change (witnessCountsOfChange h410 h51 h28 h23).genericRank ≤
      residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
    rwa [activeBound] at hb

/-- **`residualRankCounts_afterT'''_ofChangeCohomology` at the active witness** (tex 4453–4648,
4626–4640): the generic change of condition of the witness (`afterSES_shortExact`,
`activeW'_acyclic`) alone; the minimal model is the cohomology of `afterQ'`, and the degree-`3`
identification against the genuine `genH` is `witness_eG3` composed with `genHEquivAll`.
Kind: definition. -/
def witnessCountsOfChangeCohomology (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : ∀ n, Module.Free Rt (afterP.X n) := afterP_free
  letI : ∀ n, Module.Finite Rt (afterP.X n) := afterP_finite h410 h51 h28
  letI : afterP.IsStrictlyGE 0 := (afterP_supported h410 h28).1
  letI : afterP.IsStrictlyLE 3 := (afterP_supported h410 h28).2
  letI : afterP'.IsStrictlyGE 0 := afterP'_ge h410 h28
  letI : afterP'.IsStrictlyLE 3 := afterP'_le h410 h28
  letI : ∀ n, Module.Finite Kt (afterP'.X n) := afterP'_finite h410 h51 h28
  exact residualRankCounts_afterT'''_ofChangeCohomology SmallK smallLocalModels h410 h51 h28 h23
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp) 5 (by decide)
    actD actD_prime actD_odd actCond actCond_derivative actCond_full_torsion
    smallInfinitePlace smallInfinitePlace_complex SmallS actSel actEG_full
    ((witness_eG3 h410).trans (genHEquivAll SmallK _ 3).symm)
    (act_hUm_full_eq h28).le (act_hLm_full_eq h28).le afterP witness_ered
    afterP' witness_ebc afterQ' activeW'.toCC
    (GHom.toCC afterIncl) (GHom.toCC afterProj) afterSES.zero afterSES_shortExact
    activeW'_acyclic

/-- **The bounds for `witnessCountsOfChangeCohomology`** (tex 4453–4648): `2 ≤ genericRank ≤
rankTot` and `genericRank ≤ 294`. Kind: PROVED. -/
theorem witnessCountsOfChangeCohomology_bounds (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ∧
      (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ≤
        (witnessCountsOfChangeCohomology h410 h51 h28 h23).rankTot ∧
      (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ≤ 294 := by
  have hg : (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n) := rfl
  refine ⟨?_, (witnessCountsOfChangeCohomology h410 h51 h28 h23).transfer, ?_⟩
  · rw [hg]
    exact (two_le_afterL_zero h410 h51 h28).trans (Finset.single_le_sum
      (f := fun n => Module.finrank Kt (afterQ'.homology n)) (fun _ _ => Nat.zero_le _)
      (show (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 3 by decide))
  · have hb := (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank_le
    change (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ≤
      residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
    rwa [activeBound] at hb

/-- **`residualRankCounts_afterT'_ofIntegralChange` at the active witness** (tex 4453–4648,
4619–4631): the integral change of condition `0 → afterP → afterP ⊕ activeW → activeW → 0` over
`𝔽₂[[t]]` (`witness_integralSES`) with the active comparison homotopy `d h + h d = c`,
`c = ∏_q ((1+t)^{±1} − 1)` (`piHomotopy`, `activeHomotopy`), a unit in `𝔽₂((t))`
(`activeProd_isUnit_generic`); `P'`, `L`, `ebc`, `hLmin` and `e` are built.
Kind: definition. -/
def witnessCountsOfIntegralChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : ∀ n, Module.Free Rt (afterP.X n) := afterP_free
  letI : ∀ n, Module.Finite Rt (afterP.X n) := afterP_finite h410 h51 h28
  letI : afterP.IsStrictlyGE 0 := (afterP_supported h410 h28).1
  letI : afterP.IsStrictlyLE 3 := (afterP_supported h410 h28).2
  exact residualRankCounts_afterT'_ofIntegralChange SmallK smallLocalModels h410 h51 h28 h23
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp) 5 (by decide)
    actD actD_prime actD_odd actCond actCond_derivative actCond_full_torsion
    smallInfinitePlace smallInfinitePlace_complex SmallS actSel actEG_full
    (witness_globalDegreeThreeVanishes h410)
    (act_hUm_full_eq h28).le (act_hLm_full_eq h28).le afterP witness_ered
    afterQ_G.toCC activeW.toCC witnessIncl witnessProj witnessIncl_proj witness_integralSES
    activeProd (homotopyOfCHomotopy (piHomotopy _ _ fun _ => activeHomotopy _))
    activeProd_isUnit_generic

/-- **The bounds for `witnessCountsOfIntegralChange`** (tex 4453–4648, 4619–4631): the integral
change of condition is not acyclic before inverting `t` (`activeW_not_acyclic`), and
`2 ≤ genericRank ≤ rankTot`, `genericRank ≤ 294`. Kind: PROVED. -/
theorem witnessCountsOfIntegralChange_bounds (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    ¬ activeW.toCC.Acyclic ∧
      2 ≤ (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ∧
      (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ≤
        (witnessCountsOfIntegralChange h410 h51 h28 h23).rankTot ∧
      (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ≤ 294 := by
  have hg : (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank Kt ((genericCx afterQ_G.toCC).homology n) := rfl
  have hiso : ∀ n, Module.finrank Kt ((genericCx afterQ_G.toCC).homology n) =
      Module.finrank Kt (afterQ'.homology n) := fun n =>
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (bcG_toCC_iso_baseChangeCx afterQ_G)).toLinearEquiv.finrank_eq.symm
  refine ⟨activeW_not_acyclic, ?_, (witnessCountsOfIntegralChange h410 h51 h28 h23).transfer, ?_⟩
  · rw [hg, Finset.sum_congr rfl fun n _ => hiso n]
    exact (two_le_afterL_zero h410 h51 h28).trans (Finset.single_le_sum
      (f := fun n => Module.finrank Kt (afterQ'.homology n)) (fun _ _ => Nat.zero_le _)
      (show (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 3 by decide))
  · have hb := (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank_le
    change (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ≤
      residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
    rwa [activeBound] at hb

end Witness

end ZInQ.Contrib.RC53Assist.AfterTHomotopy
