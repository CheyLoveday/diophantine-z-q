import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ConeDuality

/-!
# Genuine instantiations, part 16: the strict generic `H¹` vanishes

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-derivative-switch` (tex L4835–4906): "Over the
stated fraction or test field, suppose the actual old class spans generic `H¹` and has nonzero
finite localization `v`. … The strict generic `H¹` is zero" (tex L4846–4852, L4892–4895).

Elliot's step, as a consequence of the cone triangle `C_str → C_F → F_v[−1] →` (the finite condition
is the old, unramified one at the new prime): `H⁰(W₁) = 0`, so `H¹(C_str) → H¹(C_F)` is injective,
with image the kernel of the finite localization `H¹(C_F) → H¹(W₁)`; if `H¹(C_F)` is spanned by a
class `A` with nonzero localization, that kernel is `0`.

* `subsingleton_h1_of_oldClass` (any short exact sequence over a field): the step above;
* `subsingleton_homology_W₁`: if the side and strict conditions agree in degree `n`, `Hⁿ(W₁) = 0`
  (the derivative conditions differ only in degree one, `U_F = D⁰ ⊕ F_v[−1]`, `U_str = D⁰`);
* `cone_dims_of_matrix'`: `ConeIdent.cone_dims_of_matrix` using only the vanishing it needs
  (`H¹(C_str) = 0`, `H²(W) = 0`);
* **`cone_dims_finite_derived`**: the generic dimensions `(1, 1)` of the genuine finite-side cone
  `C_F`, from the duality data (`γ`, switch coordinates), the localization data of `A`, `B`
  (tex L4892–4894), the old class spanning `H¹(C_F)` with nonzero finite localization (tex
  L4892), the agreement of side and strict conditions in degree two, and the finite-plane
  coordinates. The generic-vanishing hypotheses of `cone_dims_finite` are DERIVED.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open scoped Matrix

open Module CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k]

section Generic

variable (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ)) (hE : E.ShortExact)

include hE in
/-- **The strict `H¹` vanishes** (tex L4892–4895): for `0 → C_str → C_F → W → 0` with
`H⁰(W) = 0`, if `H¹(C_F)` is spanned by a class `A` whose image in `H¹(W)` is nonzero, then
`H¹(C_str) = 0`. PROVED. -/
theorem subsingleton_h1_of_oldClass (h0 : Subsingleton (E.X₃.homology 0))
    (a : E.X₂.homology 1) (hspan : ∀ y : E.X₂.homology 1, ∃ c : k, y = c • a)
    (ha : (HomologicalComplex.homologyMap E.g 1).hom a ≠ 0) :
    Subsingleton (E.X₁.homology 1) := by
  have ex1 := (hE.homology_exact₁ 0 1 (by simp)).moduleCat_range_eq_ker
  have ex2 := (hE.homology_exact₂ 1).moduleCat_range_eq_ker
  have hinj : Function.Injective (HomologicalComplex.homologyMap E.f 1).hom := by
    rw [← LinearMap.ker_eq_bot, ← ex1, LinearMap.range_eq_bot]
    ext x
    exact congrArg _ (Subsingleton.elim x 0) |>.trans (map_zero _)
  constructor
  intro x y
  suffices hz : ∀ x : E.X₁.homology 1, x = 0 by rw [hz x, hz y]
  intro x
  apply hinj
  rw [map_zero]
  obtain ⟨c, hc⟩ := hspan ((HomologicalComplex.homologyMap E.f 1).hom x)
  have hk : (HomologicalComplex.homologyMap E.f 1).hom x ∈
      LinearMap.ker (HomologicalComplex.homologyMap E.g 1).hom := by
    rw [← ex2]; exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker, hc, map_smul] at hk
  rcases smul_eq_zero.mp hk with h | h
  · rw [hc, h, zero_smul]
  · exact absurd h ha

/-- **The cone dimensions from the matrix, with only the vanishing used**: `H¹(C_str) = 0`,
`H²(W) = 0`. PROVED. -/
theorem cone_dims_of_matrix' (h1 : Subsingleton (E.X₁.homology 1))
    (h2W : Subsingleton (E.X₃.homology 2))
    [FiniteDimensional k (E.X₁.homology 2)] [FiniteDimensional k (E.X₂.homology 1)]
    [FiniteDimensional k (E.X₂.homology 2)] [FiniteDimensional k (E.X₃.homology 1)]
    (bF : Basis (Fin 2) k (E.X₃.homology 1)) (bH : Basis (Fin 2) k (E.X₁.homology 2)) {ε : k}
    (hε : ε ≠ 0) {v : Fin 2 → k} (hv : v ≠ 0)
    (hmat : ConnectingMatrixIdentification (hE.δ 1 2 (by simp)).hom bF bH ε v) :
    finrank k (E.X₂.homology 1) = 1 ∧ finrank k (E.X₂.homology 2) = 1 := by
  have hA := finrank_h1_eq_ker E hE h1
  have hB := finrank_h2_add_rank E hE h2W
  set δ := (hE.δ 1 2 (by simp)).hom
  have hrank : finrank k (LinearMap.range δ) = 1 := by
    rw [← Matrix.toLin_toMatrix bF bH δ, ← Matrix.rank_eq_finrank_range_toLin, hmat]
    exact rank_oldMat hε hv
  have hdimV : finrank k (E.X₃.homology 1) = 2 := by
    rw [finrank_eq_card_basis bF, Fintype.card_fin]
  have hdimH : finrank k (E.X₁.homology 2) = 2 := by
    rw [finrank_eq_card_basis bH, Fintype.card_fin]
  have hrn := LinearMap.finrank_range_add_finrank_ker δ
  refine ⟨?_, ?_⟩ <;> omega

end Generic

/-- A relation-indexed complex whose degree-`n` term is trivial has trivial `Hⁿ`. -/
theorem subsingleton_homology_of_subsingleton_X (A : GCx k) (n : ℤ)
    (h : Subsingleton (A.X n)) : Subsingleton (A.toCC.homology n) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := clsAt_surjective A n (n + 1) rfl x
  obtain ⟨b, rfl⟩ := clsAt_surjective A n (n + 1) rfl y
  rw [show a = b from Subtype.ext (Subsingleton.elim _ _)]

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

variable (F : DerivFamily (galLv (k := k) K S M))

/-- **`Hⁿ(W₁) = 0` where the side and strict conditions agree.** PROVED. -/
theorem subsingleton_homology_W₁ (n : ℤ) (hn : ∀ v, (F.side v).S n ≤ (F.str v).S n) :
    Subsingleton (F.W₁.toCC.homology n) := by
  refine subsingleton_homology_of_subsingleton_X F.W₁ n ⟨fun x y => ?_⟩
  have hz : ∀ z : F.W₁.X n, z = 0 := fun z => by
    obtain ⟨b, rfl⟩ := (quotSub F.fs n).mkQ_surjective z
    refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨fun v => ⟨(b v).1, hn v (b v).2⟩, ?_⟩
    funext v
    rfl
  rw [hz x, hz y]

variable (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))

/-- The matrix identification for a sequence `E` whose strict `H²` is identified with that of the
genuine switch data compatibly with the connecting maps. -/
theorem connMatrix_of_eH (X : GenuineSwitch K S k M) {ε σ : k} {J : Matrix (Fin 2) (Fin 2) k}
    (hJ2 : J * J = 1)
    (pair : (selCx X.Dstr).toCC.homology 2 →ₗ[k] (selCx X.toQuasi.D).toCC.homology 1 →ₗ[k] k)
    (hpair : ∀ w v, pair (X.δ w) v =
      switchPairing ε σ J (X.toQuasi.eR (H1 (quotMap X.toQuasi.D X.toQuasi.gR) v))
        (X.toQuasi.eR w))
    (bR : Basis (Fin 2) k ((selCx X.toQuasi.D).toCC.homology 1)) {v : Fin 2 → k}
    (hA : genLam X (bR 0) = (v, 0)) (hB : genLam X (bR 1) = (0, J *ᵥ v))
    (bH : Basis (Fin 2) k ((selCx X.Dstr).toCC.homology 2))
    (hdual : ∀ i j, pair (bH i) (bR j) = if j = i then 1 else 0)
    (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ)) (hE : E.ShortExact)
    (eH : E.X₁.homology 2 ≃ₗ[k] (selCx X.Dstr).toCC.homology 2)
    (bF : Basis (Fin 2) k (E.X₃.homology 1))
    (ι : E.X₃.homology 1 →ₗ[k] X.toQuasi.Wrel.toCC.homology 1)
    (hι : ∀ j, X.toQuasi.eR (ι (bF j)) = (Pi.single j 1, 0))
    (hnat : ∀ x, eH ((hE.δ 1 2 (by simp)).hom x) = X.δ (ι x)) :
    ConnectingMatrixIdentification (hE.δ 1 2 (by simp)).hom bF (bH.map eH.symm) (σ * ε) v := by
  let pair' : E.X₁.homology 2 →ₗ[k] _ →ₗ[k] k := pair ∘ₗ eH.toLinearMap
  exact toMatrix_eq_oldMat hJ2 pair' (genLam X) (eH.symm.toLinearMap ∘ₗ X.δ) X.toQuasi.eR
    (fun w c => by
      simp only [pair', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hpair w c)
    bR hA hB (bH.map eH.symm)
    (fun i j => by
      simp only [pair', LinearMap.comp_apply, Basis.map_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      exact hdual i j)
    (hE.δ 1 2 (by simp)).hom bF ι hι
    (by
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hnat x,
        LinearEquiv.symm_apply_apply])

/-- **The generic dimensions of the genuine finite-side cone, with the generic vanishing derived**
(tex L4835–4906): for a derivative family over the genuine local complexes whose side (finite) and
strict conditions agree in degree two, given
* the duality data: the Selmer duality quasi-isomorphism `γ` (Nekovář 6.3.4) and the switch
  coordinates (tex 2816–2818);
* a basis `A, B` of `H¹(C_rel)` with `λ A = (v, 0)`, `λ B = (0, J v)` (tex L4892–4894);
* the old class: `H¹(C_F)` is spanned by a class with nonzero finite localization (tex L4892,
  "the old actual class `A` spans generic `H¹` and has `f(A) = v ≠ 0`");
* the coordinates of the finite plane (`eR (H¹(i) e_j) = (e_j, 0)`),
`dim H¹(C_F) = dim H²(C_F) = 1`. The strict `H¹` vanishing and `H²(W₁) = 0` are DERIVED
(`subsingleton_h1_of_oldClass`, `subsingleton_homology_W₁`), as is `dim H²(C_str) = 2`. PROVED. -/
theorem cone_dims_finite_derived {ε σ : k} {J : Matrix (Fin 2) (Fin 2) k} (hε : ε ≠ 0)
    (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (Q : SelPairData (derivSwitch F eR).Dstr (derivSwitch F eR).toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : (derivSwitch F eR).SwitchCoordinates Q tr ε σ J)
    (bR : Basis (Fin 2) k ((selCx (derivSwitch F eR).toQuasi.D).toCC.homology 1))
    {v : Fin 2 → k} (hv : v ≠ 0)
    (hA : genLam (derivSwitch F eR) (bR 0) = (v, 0))
    (hB : genLam (derivSwitch F eR) (bR 1) = (0, J *ᵥ v))
    (a : (derivFiniteSES F eR).X₂.homology 1)
    (hspan : ∀ y : (derivFiniteSES F eR).X₂.homology 1, ∃ c : k, y = c • a)
    (ha : (HomologicalComplex.homologyMap (derivFiniteSES F eR).g 1).hom a ≠ 0)
    (hside2 : ∀ w, (F.side w).S 2 ≤ (F.str w).S 2)
    (bF : Basis (Fin 2) k ((derivFiniteSES F eR).X₃.homology 1))
    (hι : ∀ j, eR (H1 F.i (bF j)) = (Pi.single j 1, 0)) :
    finrank k ((derivFiniteSES F eR).X₂.homology 1) = 1 ∧
      finrank k ((derivFiniteSES F eR).X₂.homology 2) = 1 := by
  have hE := derivFiniteSES_shortExact F eR
  obtain ⟨pair, hsep, hpair⟩ :=
    (derivSwitch F eR).adjunction Q tr htr ε σ J hε hσ hJ2 hγ hsw
  obtain ⟨bH, hdual⟩ := exists_dualBasis pair hsep bR
    (finrank_h2_strict_of_duality (derivSwitch F eR) Q tr htr hγ bR)
  let eH := (asIso (HomologicalComplex.homologyMap (derivFiniteToRelaxed F eR).τ₁ 2)).toLinearEquiv
  have hS₂ := switchSES_shortExact (derivSwitch F eR).toQuasi (piMap (derivSwitch F eR).φ)
    (derivSwitch F eR).hfg (derivSwitch F eR).φ_inj (derivSwitch F eR).g_surj (derivSwitch F eR).ex
  have hnat : ∀ x, eH ((hE.δ 1 2 (by simp)).hom x) = (derivSwitch F eR).δ
      ((HomologicalComplex.homologyMap (derivFiniteToRelaxed F eR).τ₃ 1).hom x) := fun x =>
    congrArg (fun f => f.hom x)
      (HomologicalComplex.HomologySequence.δ_naturality (derivFiniteToRelaxed F eR) hE hS₂ 1 2
        (by simp))
  have hmat := connMatrix_of_eH (derivSwitch F eR) hJ2 pair hpair bR hA hB bH hdual _ hE eH bF
    (HomologicalComplex.homologyMap (derivFiniteToRelaxed F eR).τ₃ 1).hom hι hnat
  have h1s := subsingleton_h1_of_oldClass _ hE F.h0_W₁ a hspan ha
  have h2W : Subsingleton ((derivFiniteSES F eR).X₃.homology 2) :=
    subsingleton_homology_W₁ F 2 hside2
  have : FiniteDimensional k ((derivFiniteSES F eR).X₁.homology 2) :=
    (bH.map eH.symm).finiteDimensional_of_finite
  have : FiniteDimensional k ((derivFiniteSES F eR).X₃.homology 1) :=
    bF.finiteDimensional_of_finite
  have : FiniteDimensional k ((derivFiniteSES F eR).X₂.homology 1) :=
    Module.Finite.of_surjective (LinearMap.toSpanSingleton k _ a) (fun y => by
      obtain ⟨c, hc⟩ := hspan y
      exact ⟨c, by rw [LinearMap.toSpanSingleton_apply, hc]⟩)
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (derivFiniteSES F eR).f 2).hom := by
    rw [← LinearMap.range_eq_top, (hE.homology_exact₂ 2).moduleCat_range_eq_ker,
      LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _
  have : FiniteDimensional k ((derivFiniteSES F eR).X₂.homology 2) :=
    Module.Finite.of_surjective _ hsurj
  exact cone_dims_of_matrix' _ hE h1s h2W bF (bH.map eH.symm) (mul_ne_zero hσ hε) hv hmat

end ZInQ.Contrib.CloudB3RC53.GenuineInst
