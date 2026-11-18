import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.QuasiSide
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.StageLink

/-!
# RC53 SwitchInputs: the cone of the connecting map, and a consistency instance of the duality
adjunction

Lemma `ex:limits-derivative-switch`, tex L4888–4906 (the derivative model of the switch lemma:
"generically `H¹(C_str) = 0` and `H²(C_str) = ⟨A, B⟩^∨`; the minimal models of `C_F`, `C_S` are the
cones of the connecting maps `∂_F : F_v → H²(C_str)`, `∂_S : S_v → H²(C_str)`"), and the localization
duality of tex L5068–5075.

**Part A (PROVED): the generic cohomology of `C_F` is that of the cone of `∂`.** For a short exact
sequence of cochain complexes over a field `0 → C_str → C_F → W → 0` with `W` concentrated in degree
one (`W¹ = F_v`) and `H^n(C_str) = 0` for `n ≠ 2` (the generic vanishing), the long exact sequence
gives, with `δ : H¹(W) → H²(C_str)` the connecting map:
* `H¹(C_F) ≅ ker δ` (`finrank_h1_eq_ker`),
* `dim H²(C_F) + rank δ = dim H²(C_str)` (`finrank_h2_add_rank`),
* `H^n(C_F) = 0` for `n ∉ {1, 2}` (`subsingleton_hn`).
These are exactly the cohomology groups of the two-term complex `[F_v --∂--> H²(C_str)]` in degrees
one and two (`∂ = δ ∘ (H¹(W) ≅ W¹)⁻¹`): `ConeCohomology`. With the matrix identification of `∂_F`
with RC16's `oldMat` (`ConnectingMatrixIdentification`, GLUE: the cup-product computation of
`bdryF`), the generic dimensions are `(1, 1)` (`cone_dims_of_matrix`), the generic shadow of
`StageLink.StageConeIdentification`.

**Sharpened remaining GLUE.** `StageConeIdentification` (an integral reduction of the stage model to
`oldMat ⊕ 1`) is not a consequence of generic data: a homotopy equivalence over the fraction field
does not fix the integral lattice. What remains is therefore
(i) `ConnectingMatrixIdentification` (the matrix of `∂_F` in the bases `e_j`, `A^*, B^*` is `oldMat`;
RC16's `bdryF_eq`, from Nekovář's cup products), and
(ii) the integral lattice statement `StageConeIdentification` itself (the stage model is the integral
cone of `∂_F` plus unit disks).
Part A proves everything about the generic fibre that (i) and (ii) assert.

**Part B (non-vacuity): `SwitchDualityAdjunction` is consistent.** `exSwitchDualityAdjunction`
inhabits QuasiSide's GLUE input for the relaxed localization `exQuasiRel` (`U = F`) with a strict
Selmer complex `exStrD` whose `H²` is `ℚ²` (`exH2Equiv`), the connecting map `δ` = the singular
coordinate, and the pairing `⟨x, v⟩ = β(λ v, (0, x))`; hence `LocalizationDualityInput` follows via
`localizationDualityInput_of_adjunction` (`exLocalizationDuality_of_adjunction`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ### Part A: the generic cohomology of `C_F` -/

section ConeCohomology

variable {k : Type} [Field k] (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ))
  (hE : E.ShortExact)

/-- **`H¹(C_F) ≅ ker δ`** (tex L4888–4906): if `H¹(C_str) = 0`, then `H¹(C_F) → H¹(W)` is
injective with image `ker δ`. PROVED. -/
theorem finrank_h1_eq_ker (h1 : Subsingleton (E.X₁.homology 1)) [FiniteDimensional k (E.X₂.homology 1)]
    [FiniteDimensional k (E.X₃.homology 1)] :
    finrank k (E.X₂.homology 1) = finrank k (LinearMap.ker (hE.δ 1 2 (by simp)).hom) := by
  have ex2 := (hE.homology_exact₂ 1).moduleCat_range_eq_ker
  have ex3 := (hE.homology_exact₃ 1 2 (by simp)).moduleCat_range_eq_ker
  have hinj : Function.Injective (HomologicalComplex.homologyMap E.g 1).hom := by
    rw [← LinearMap.ker_eq_bot, ← ex2]
    rw [LinearMap.range_eq_bot]
    ext x
    exact congrArg _ (Subsingleton.elim x 0) |>.trans (map_zero _)
  rw [← ex3]
  exact (LinearMap.finrank_range_of_inj hinj).symm

/-- **`dim H²(C_F) + rank δ = dim H²(C_str)`** (tex L4888–4906): if `H²(W) = 0` (`W` concentrated
in degree one), `H²(C_str) → H²(C_F)` is surjective with kernel `im δ`. PROVED. -/
theorem finrank_h2_add_rank (h2W : Subsingleton (E.X₃.homology 2))
    [FiniteDimensional k (E.X₁.homology 2)] [FiniteDimensional k (E.X₂.homology 2)] :
    finrank k (E.X₂.homology 2) + finrank k (LinearMap.range (hE.δ 1 2 (by simp)).hom) =
      finrank k (E.X₁.homology 2) := by
  have ex1 := (hE.homology_exact₁ 1 2 (by simp)).moduleCat_range_eq_ker
  have ex2 := (hE.homology_exact₂ 2).moduleCat_range_eq_ker
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap E.f 2).hom := by
    rw [← LinearMap.range_eq_top, ex2, LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _
  have := LinearMap.finrank_range_add_finrank_ker (HomologicalComplex.homologyMap E.f 2).hom
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← ex1] at this
  exact this

include hE in
/-- **`H^n(C_F) = 0` for `n ∉ {1, 2}`**, if `H^n(C_str) = 0` and `H^n(W) = 0`. PROVED. -/
theorem subsingleton_hn (n : ℤ) (h1n : Subsingleton (E.X₁.homology n))
    (h3n : Subsingleton (E.X₃.homology n)) : Subsingleton (E.X₂.homology n) := by
  have ex2 := (hE.homology_exact₂ n).moduleCat_range_eq_ker
  constructor
  intro a b
  have hk : ∀ x, x ∈ LinearMap.ker (HomologicalComplex.homologyMap E.g n).hom := fun x => by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  have hz : ∀ x : E.X₂.homology n, x = 0 := fun x => by
    have hx := hk x
    rw [← ex2] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subsingleton.elim y 0, map_zero]
  rw [hz a, hz b]

/-- **The generic cohomology of `C_F` is that of the cone of `∂`** (tex L4888–4906). For a short
exact sequence `0 → C_str → C_F → W → 0` of cochain complexes over a field with `W` concentrated in
degree one (in the sense `H^n(W) = 0` for `n ≠ 1`), finite-dimensional cohomology, and
`H^n(C_str) = 0` for `n ≠ 2`: `H¹(C_F) ≅ ker δ`, `dim H²(C_F) = dim H²(C_str) − rank δ`, and
`H^n(C_F) = 0` for `n ∉ {1, 2}` — the cohomology of the two-term complex
`[H¹(W) --δ--> H²(C_str)]` in degrees one and two. Classification: PROVED. -/
def ConeCohomology : Prop :=
  ∀ (k : Type) [Field k] (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ))
    (hE : E.ShortExact),
    (∀ n, n ≠ 1 → Subsingleton (E.X₃.homology n)) →
    (∀ n, n ≠ 2 → Subsingleton (E.X₁.homology n)) →
    FiniteDimensional k (E.X₁.homology 2) → FiniteDimensional k (E.X₂.homology 1) →
    FiniteDimensional k (E.X₂.homology 2) → FiniteDimensional k (E.X₃.homology 1) →
      finrank k (E.X₂.homology 1) = finrank k (LinearMap.ker (hE.δ 1 2 (by simp)).hom) ∧
      finrank k (E.X₂.homology 2) + finrank k (LinearMap.range (hE.δ 1 2 (by simp)).hom) =
        finrank k (E.X₁.homology 2) ∧
      ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (E.X₂.homology n)

theorem coneCohomology_proof : ConeCohomology := by
  intro k _ E hE h3 h1 _ _ _ _
  exact ⟨finrank_h1_eq_ker E hE (h1 1 (by norm_num)),
    finrank_h2_add_rank E hE (h3 2 (by norm_num)),
    fun n hn1 hn2 => subsingleton_hn E hE n (h1 n hn2) (h3 n hn1)⟩

end ConeCohomology

/-! ### The matrix identification and the generic dimensions -/

section Matrix

variable {k : Type} [Field k]

/-- **GLUE: the matrix of the connecting map `∂_F` is `oldMat`** (tex L4888–4906; RC16's
`bdryF_eq`, from Nekovář's cup-product identities): in bases `bF` of `H¹(W) = F_v` (the `e_j`) and
`bH` of `H²(C_str)` (the dual basis `A^*, B^*`), the matrix of `δ` is `oldMat ε v`.
Classification: GLUE (input). -/
def ConnectingMatrixIdentification {V H : Type} [AddCommGroup V] [Module k V] [AddCommGroup H]
    [Module k H] (δ : V →ₗ[k] H) (bF : Basis (Fin 2) k V) (bH : Basis (Fin 2) k H) (ε : k)
    (v : Fin 2 → k) : Prop :=
  LinearMap.toMatrix bF bH δ = oldMat ε v

/-- `oldMat ε v` has rank one when `ε ≠ 0` and `v ≠ 0`. PROVED. -/
theorem rank_oldMat {ε : k} (hε : ε ≠ 0) {v : Fin 2 → k} (hv : v ≠ 0) :
    (oldMat ε v).rank = 1 := by
  unfold Matrix.rank
  apply le_antisymm
  · -- the range lies in the line spanned by `e₁`
    have hle : LinearMap.range (oldMat ε v).mulVecLin ≤ k ∙ (Pi.single 1 1 : Fin 2 → k) := by
      rintro _ ⟨x, rfl⟩
      rw [Matrix.mulVecLin_apply]
      rw [Submodule.mem_span_singleton]
      refine ⟨ε * v 1 * x 0 - ε * v 0 * x 1, ?_⟩
      ext i; fin_cases i <;>
        simp [oldMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] <;> ring
    calc finrank k (LinearMap.range (oldMat ε v).mulVecLin)
        ≤ finrank k (k ∙ (Pi.single 1 1 : Fin 2 → k)) := Submodule.finrank_mono hle
      _ ≤ 1 := (finrank_span_le_card ({Pi.single 1 1} : Set (Fin 2 → k))).trans (by simp)
  · rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    intro h0
    have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hv (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    rcases hv' with h | h
    · have := congrFun (LinearMap.congr_fun h0 (Pi.single 1 1)) 1
      simp [Matrix.mulVecLin_apply, oldMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] at this
      exact this.elim (fun e => hε e) (fun e => h e)
    · have := congrFun (LinearMap.congr_fun h0 (Pi.single 0 1)) 1
      simp [Matrix.mulVecLin_apply, oldMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] at this
      exact this.elim (fun e => hε e) (fun e => h e)

/-- **The generic dimensions of `C_F` are `(1, 1)`** (tex L4888–4906, L4986–4996): under the GLUE
matrix identification (`ε ≠ 0`, `v ≠ 0`), `rank δ = 1`, so by `ConeCohomology`
`dim H¹(C_F) = 1` and `dim H²(C_F) = 1` — the fibre dimensions of the cone `oldMat ε v`, the generic
shadow of `StageConeIdentification`. Classification: PROVED (from the GLUE). -/
theorem cone_dims_of_matrix (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ))
    (hE : E.ShortExact) (h3 : ∀ n, n ≠ 1 → Subsingleton (E.X₃.homology n))
    (h1 : ∀ n, n ≠ 2 → Subsingleton (E.X₁.homology n))
    [FiniteDimensional k (E.X₁.homology 2)] [FiniteDimensional k (E.X₂.homology 1)]
    [FiniteDimensional k (E.X₂.homology 2)] [FiniteDimensional k (E.X₃.homology 1)]
    (bF : Basis (Fin 2) k (E.X₃.homology 1)) (bH : Basis (Fin 2) k (E.X₁.homology 2)) {ε : k}
    (hε : ε ≠ 0) {v : Fin 2 → k} (hv : v ≠ 0)
    (hmat : ConnectingMatrixIdentification (hE.δ 1 2 (by simp)).hom bF bH ε v) :
    finrank k (E.X₂.homology 1) = 1 ∧ finrank k (E.X₂.homology 2) = 1 := by
  obtain ⟨hA, hB, -⟩ := coneCohomology_proof k E hE h3 h1 inferInstance inferInstance
    inferInstance inferInstance
  set δ := (hE.δ 1 2 (by simp)).hom
  -- `rank δ = rank oldMat = 1`
  have hrank : finrank k (LinearMap.range δ) = 1 := by
    rw [← Matrix.toLin_toMatrix bF bH δ, ← Matrix.rank_eq_finrank_range_toLin, hmat]
    exact rank_oldMat hε hv
  have hdimV : finrank k (E.X₃.homology 1) = 2 := by rw [finrank_eq_card_basis bF, Fintype.card_fin]
  have hdimH : finrank k (E.X₁.homology 2) = 2 := by rw [finrank_eq_card_basis bH, Fintype.card_fin]
  have hrn := LinearMap.finrank_range_add_finrank_ker δ
  refine ⟨?_, ?_⟩ <;> omega

/-- **Non-vacuity: `ConnectingMatrixIdentification` is consistent**: the map with matrix `oldMat ε v`
in the standard bases. PROVED. -/
theorem exConnectingMatrixIdentification (ε : k) (v : Fin 2 → k) :
    ConnectingMatrixIdentification (Matrix.toLin' (oldMat ε v)) (Pi.basisFun k (Fin 2))
      (Pi.basisFun k (Fin 2)) ε v := by
  unfold ConnectingMatrixIdentification
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

end Matrix

/-! ### Part B: a consistency instance of `SwitchDualityAdjunction` -/

/-- `ℚ^a` in degree two, `0` elsewhere. -/
def dimAt2 (a : ℕ) (n : ℤ) : ℕ := if n = 2 then a else 0

abbrev P2n (a : ℕ) (n : ℤ) : ModuleCat.{0} ℚ := ModuleCat.of ℚ (Fin (dimAt2 a n) → ℚ)

theorem subsingleton_dimAt2 (a : ℕ) {n : ℤ} (h : n ≠ 2) : Subsingleton (Fin (dimAt2 a n) → ℚ) := by
  unfold dimAt2; rw [if_neg h]; infer_instance

/-- **The strict Selmer data of the example**: `G = ℚ²` in degree two, `U = L = 0`. Its `H²` is
`ℚ²` (`exH2Equiv`). -/
def exStrD : SelData ℚ where
  G := zGCx (P2n 2)
  U := zGCx Zn
  L := zGCx Zn
  res := zHom fun _ => 0
  ι := zHom fun _ => 0

theorem exStrD_sub (n : ℤ) (hn : n ≠ 2) : Subsingleton ((selCx exStrD).toCC.X n) := by
  have := subsingleton_dimAt2 2 hn
  change Subsingleton ((Fin (dimAt2 2 n) → ℚ) × (Fin 0 → ℚ) × (Fin 0 → ℚ))
  infer_instance

/-- `H²(C_str) ≅ C_str²` (the neighbouring degrees vanish). -/
def exH2Iso : (selCx exStrD).toCC.homology 2 ≅ (selCx exStrD).toCC.X 2 := by
  have h1 : (selCx exStrD).toCC.d 1 2 = 0 := by
    have := exStrD_sub 1 (by norm_num)
    ext x; rw [Subsingleton.elim x 0]; simp
  have h3 : (selCx exStrD).toCC.d 2 3 = 0 := by
    have := exStrD_sub 3 (by norm_num)
    ext x; exact Subsingleton.elim _ _
  exact ((selCx exStrD).toCC.isoHomologyπ 1 2 (by simp) h1).symm ≪≫
    (selCx exStrD).toCC.iCyclesIso 2 3 (by simp) h3

theorem dimAt2_two : dimAt2 2 2 = 2 := by simp [dimAt2]

/-- `C_str² = ℚ² × 0 × 0 ≅ ℚ²`. -/
def exX2Equiv : (selCx exStrD).toCC.X 2 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  letI : Unique ((Fin 0 → ℚ) × (Fin 0 → ℚ)) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  (LinearEquiv.prodUnique (R := ℚ) (M := Fin (dimAt2 2 2) → ℚ)
    (M₂ := (Fin 0 → ℚ) × (Fin 0 → ℚ))).trans
    (LinearEquiv.funCongrLeft ℚ ℚ (finCongr dimAt2_two).symm)

/-- **`H²(C_str) ≅ ℚ²`** for the example. -/
def exH2Equiv : (selCx exStrD).toCC.homology 2 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  exH2Iso.toLinearEquiv.trans exX2Equiv

/-- The localization `λ' = e_R ∘ H¹(λ)` of the example. -/
abbrev exLam' : (selCx exQuasiRel.D).toCC.homology 1 →ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ) :=
  exQuasiRel.eR.toLinearMap ∘ₗ H1 (quotMap exQuasiRel.D exQuasiRel.gR)

theorem exLam'_mem (v : (selCx exQuasiRel.D).toCC.homology 1) :
    exLam' v ∈ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  rw [← exQuasiRel_U]
  exact ⟨_, ⟨v, rfl⟩, rfl⟩

theorem exLam'_surj (f : Fin 2 → ℚ) : ∃ v, exLam' v = (f, 0) := by
  have : ((f, 0) : (Fin 2 → ℚ) × (Fin 2 → ℚ)) ∈ exQuasiRel.U := by
    rw [exQuasiRel_U, mem_finPlane]
  obtain ⟨w, ⟨v, rfl⟩, hw⟩ := this
  exact ⟨v, hw⟩

/-- The connecting map of the example: `δ w = (e_R w)_S` (the singular coordinate). -/
def exDelta : exQuasiRel.Wrel.toCC.homology 1 →ₗ[ℚ] (selCx exStrD).toCC.homology 2 :=
  exH2Equiv.symm.toLinearMap ∘ₗ LinearMap.snd ℚ _ _ ∘ₗ exQuasiRel.eR.toLinearMap

theorem exDelta_hex :
    LinearMap.range (H1 (quotMap exQuasiRel.D exQuasiRel.gR)) = LinearMap.ker exDelta := by
  ext w
  rw [LinearMap.mem_ker]
  simp only [exDelta, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.snd_apply, LinearEquiv.map_eq_zero_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact mem_finPlane.mp (exLam'_mem v)
  · intro h
    have hm : exQuasiRel.eR w ∈ exQuasiRel.U := by rw [exQuasiRel_U, mem_finPlane]; exact h
    obtain ⟨w', hw', he⟩ := hm
    rw [show w = w' from exQuasiRel.eR.injective he.symm]
    exact hw'

/-- **Non-vacuity: `SwitchDualityAdjunction` is consistent** (tex L5068–5075). For the relaxed
localization `exQuasiRel` (`U = F`), the strict data `exStrD` (`H²(C_str) = ℚ²`), the connecting map
`exDelta` and the switch pairing with `ε = σ = 1`, `J = J₀`, the pairing
`⟨x, v⟩ = β(λ' v, (0, x))` is separating and adjoint to localization. PROVED. -/
theorem exSwitchDualityAdjunction :
    SwitchDualityAdjunction exQuasiRel exStrD 1 1 J₀ one_ne_zero one_ne_zero J₀_sq exDelta
      exDelta_hex := by
  set β := switchPairing (1 : ℚ) 1 J₀
  refine ⟨((β.compl₁₂ exLam' ((LinearMap.inr ℚ _ _) ∘ₗ exH2Equiv.toLinearMap))).flip, ?_, ?_⟩
  · intro x hx
    apply exH2Equiv.injective
    rw [map_zero]
    have hperf := crossPairing_isPerfPair (K := ℚ) (ε := 1) one_ne_zero J₀_sq
    apply hperf.bijective_right.injective
    refine LinearMap.ext fun f => ?_
    obtain ⟨v, hv⟩ := exLam'_surj f
    have hx' := hx v
    simp only [LinearMap.flip_apply, LinearMap.compl₁₂_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearMap.inr_apply] at hx'
    rw [show exQuasiRel.eR ((H1 (quotMap exQuasiRel.D exQuasiRel.gR)) v) = (f, 0) from hv] at hx'
    simpa [β] using hx'
  · intro w v
    simp only [LinearMap.flip_apply, LinearMap.compl₁₂_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearMap.inr_apply, exDelta, LinearMap.snd_apply,
      LinearEquiv.apply_symm_apply]
    have hm : (exQuasiRel.eR ((H1 (quotMap exQuasiRel.D exQuasiRel.gR)) v)).2 = 0 :=
      mem_finPlane.mp (exLam'_mem v)
    simp only [β, planePairing_apply, crossPairing_apply]
    rw [hm]
    simp

/-- `LocalizationDualityInput` for the example, derived from the adjunction instance. PROVED. -/
theorem exLocalizationDuality_of_adjunction :
    LocalizationDualityInput 1 1 J₀ one_ne_zero one_ne_zero J₀_sq exQuasiRel.U :=
  localizationDualityInput_of_adjunction exQuasiRel exStrD 1 1 J₀ one_ne_zero one_ne_zero J₀_sq
    exDelta exDelta_hex exSwitchDualityAdjunction

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
