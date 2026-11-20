import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.ConeIdent
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchDuality

/-!
# Genuine instantiations, part 12: the matrix of the finite connecting map is `oldMat`

Manuscript `diophantine_zq.tex`, tex L4888–4906 (Lemma `ex:limits-derivative-switch`): "At a new
inert prime the finite and singular planes are free of rank two, with cross pairing
`β(x, y) = ε⟨x, J y⟩`. Suppose the old actual class `A` spans generic `H¹` and has `f(A) = v ≠ 0`.
Its derivative `B` satisfies `f(B) = 0`, `s(B) = J v`. … The transported duality and localization
identities [Nekovář 6.3.3–6.3.4] …"; and the cone triangles `C_str → C_F → F_v[−1] →`.

The GLUE `ConnectingMatrixIdentification` of `SwitchInputs/ConeIdent.lean` ("the cup-product
content": the matrix of `∂_F : F_v → H²(C_str)` is RC16's `oldMat`) is derived here from the
**duality adjunction** `⟨δ w, c⟩ = β_sw(λ c, w)` (the other team's `GenuineSwitch.adjunction`,
PROVED from Nekovář 6.3.3 in cochain form; from the PRINT `NekovarProp543` over a finite residue
field, `GenuineSwitch.adjunction_of_prints`) and the localization data of the text:

* `exists_dualBasis`: a pairing `H × R → k` separating in `H`, with `dim H = dim R = 2`, has a basis
  of `H` dual to any basis of `R` (here `H²(C_str) = ⟨A, B⟩^∨`);
* `toMatrix_eq_oldMat` (linear algebra): if `⟨δ w, c⟩ = β_sw(λ c, w)`, `λ A = (v, 0)` (`f(A) = v`,
  `s(A) = 0`), `λ B = (0, J v)` (`f(B) = 0`, `s(B) = J v`), `J² = 1`, and `∂_F = δ ∘ ι` with `ι` the
  inclusion of the finite plane (`ι e_j ↦ (e_j, 0)`), then in the bases `e_j` and the dual basis
  `A^*, B^*` the matrix of `∂_F` is `oldMat (σ ε) v`. (The factor `σ` is the sign of the plane
  pairing `β_sw((x, y), (x', y')) = β(x, y') + σ β(x', y)` in the order of the adjunction; RC16's
  `bdryF` uses the other order. Only `σ ε ≠ 0` matters for the cone.)
* **`connectingMatrixIdentification_genuine`**: for the genuine switch data (`GenuineSwitch`) with
  the adjunction, the conclusion for `δ = GenuineSwitch.δ`, the genuine connecting map of
  `0 → C_str → C_rel → W_rel → 0`;
* **`cone_dims_genuine`**: for any short exact sequence `0 → C_str → C_F → W_F → 0` whose connecting
  map is the restriction of the genuine relaxed one to the finite plane (naturality of connecting
  maps), the generic dimensions of `C_F` are `(1, 1)` — `ConeIdent.cone_dims_of_matrix` with its
  GLUE discharged.

**Classification.** PROVED from the adjunction and the localization data of tex L4892–4894 (which
are the text's hypotheses on the classes `A`, `B`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open Module Matrix CategoryTheory ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-- **A separating pairing between two planes has dual bases.** -/
theorem exists_dualBasis {H R : Type} [AddCommGroup H] [Module k H] [AddCommGroup R] [Module k R]
    (pair : H →ₗ[k] R →ₗ[k] k) (hsep : ∀ x, (∀ c, pair x c = 0) → x = 0)
    (bR : Basis (Fin 2) k R) (hH : finrank k H = 2) :
    ∃ bH : Basis (Fin 2) k H, ∀ i j, pair (bH i) (bR j) = if j = i then 1 else 0 := by
  have : FiniteDimensional k R := bR.finiteDimensional_of_finite
  have : FiniteDimensional k H := Module.finite_of_finrank_eq_succ hH
  have hinj : Function.Injective pair := by
    intro x y hxy
    rw [← sub_eq_zero]
    apply hsep
    intro c
    rw [map_sub, LinearMap.sub_apply, hxy, sub_self]
  have hdim : finrank k H = finrank k (Dual k R) := by
    rw [Subspace.dual_finrank_eq, finrank_eq_card_basis bR, Fintype.card_fin, hH]
  let e : H ≃ₗ[k] Dual k R := LinearEquiv.ofBijective pair
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  refine ⟨bR.dualBasis.map e.symm, fun i j => ?_⟩
  have h1 : pair ((bR.dualBasis.map e.symm) i) = bR.dualBasis i := by
    rw [Basis.map_apply]
    exact e.apply_symm_apply (bR.dualBasis i)
  rw [h1, Basis.dualBasis_apply_self]

/-- In a dual basis, the coordinates are the pairings with the dual vectors. -/
theorem repr_eq_pair {H R : Type} [AddCommGroup H] [Module k H] [AddCommGroup R] [Module k R]
    (pair : H →ₗ[k] R →ₗ[k] k) (bR : Basis (Fin 2) k R) (bH : Basis (Fin 2) k H)
    (hdual : ∀ i j, pair (bH i) (bR j) = if j = i then 1 else 0) (y : H) (i : Fin 2) :
    bH.repr y i = pair y (bR i) := by
  conv_rhs => rw [← bH.sum_repr y]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, LinearMap.smul_apply, hdual]; simp
  · intro l _ hl
    rw [map_smul, LinearMap.smul_apply, hdual]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The matrix of the finite connecting map from the duality adjunction** (tex L4888–4906): with
`⟨δ w, c⟩ = β_sw(λ c, w)`, `λ A = (v, 0)`, `λ B = (0, J v)`, `J² = 1`, `∂_F = δ ∘ ι` with
`ι e_j ↦ (e_j, 0)`, and `A^*, B^*` dual to `A, B`, the matrix of `∂_F` is `oldMat (σ ε) v`.
PROVED. -/
theorem toMatrix_eq_oldMat {H R W V : Type} [AddCommGroup H] [Module k H] [AddCommGroup R]
    [Module k R] [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    {ε σ : k} {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1)
    (pair : H →ₗ[k] R →ₗ[k] k) (lam : R →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (δ : W →ₗ[k] H)
    (eR : W ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (hadj : ∀ w c, pair (δ w) c = switchPairing ε σ J (lam c) (eR w))
    (bR : Basis (Fin 2) k R) {v : Fin 2 → k} (hA : lam (bR 0) = (v, 0))
    (hB : lam (bR 1) = (0, J *ᵥ v)) (bH : Basis (Fin 2) k H)
    (hdual : ∀ i j, pair (bH i) (bR j) = if j = i then 1 else 0)
    (δF : V →ₗ[k] H) (bF : Basis (Fin 2) k V) (ι : V →ₗ[k] W)
    (hι : ∀ j, eR (ι (bF j)) = (Pi.single j 1, 0)) (hδF : δF = δ ∘ₗ ι) :
    LinearMap.toMatrix bF bH δF = oldMat (σ * ε) v := by
  ext i j
  rw [LinearMap.toMatrix_apply, repr_eq_pair pair bR bH hdual, hδF, LinearMap.comp_apply, hadj,
    hι]
  fin_cases i <;> fin_cases j
  · simp [hA, oldMat]
  · simp [hA, oldMat]
  all_goals
    simp only [Fin.mk_one, Fin.isValue] at *
    simp only [hB, switchPairing, planePairing_apply, crossPairing_apply,
      mulVec_mulVec_of_sq hJ2]
    simp [oldMat, weil_apply]
    try ring

/-! ### The genuine switch data -/

section Genuine

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- The genuine relaxed localization `λ : H¹(C_rel) → H¹(W_rel) ≃ F ⊕ S`. -/
abbrev genLam (X : GenuineSwitch K S k M) :
    (selCx X.toQuasi.D).toCC.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  X.toQuasi.eR.toLinearMap ∘ₗ H1 (quotMap X.toQuasi.D X.toQuasi.gR)

/-- **The matrix of the finite connecting map is `oldMat`, for the genuine switch data** (tex
L4888–4906): given the duality adjunction for the genuine connecting map `δ` of
`0 → C_str → C_rel → W_rel → 0` (`GenuineSwitch.adjunction`, Nekovář 6.3.3–6.3.4), a basis `A, B` of
`H¹(C_rel)` with `λ A = (v, 0)` and `λ B = (0, J v)` (tex L4892–4894: `f(A) = v`, and `B` with
`f(B) = 0`, `s(B) = J v`), `dim H²(C_str) = 2` (`H²(C_str) = ⟨A, B⟩^∨`), and any map
`∂_F = δ ∘ ι` with `ι` the inclusion of the finite plane, `∂_F` has matrix `oldMat (σ ε) v` in the
bases `e_j` and `A^*, B^*`: the GLUE `ConnectingMatrixIdentification`. PROVED. -/
theorem connectingMatrixIdentification_genuine (X : GenuineSwitch K S k M) {ε σ : k}
    {J : Matrix (Fin 2) (Fin 2) k} (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hadj : SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex)
    (bR : Basis (Fin 2) k ((selCx X.toQuasi.D).toCC.homology 1)) {v : Fin 2 → k}
    (hA : genLam X (bR 0) = (v, 0)) (hB : genLam X (bR 1) = (0, J *ᵥ v))
    (hH2 : finrank k ((selCx X.Dstr).toCC.homology 2) = 2)
    {V : Type} [AddCommGroup V] [Module k V] (δF : V →ₗ[k] (selCx X.Dstr).toCC.homology 2)
    (bF : Basis (Fin 2) k V) (ι : V →ₗ[k] X.toQuasi.Wrel.toCC.homology 1)
    (hι : ∀ j, X.toQuasi.eR (ι (bF j)) = (Pi.single j 1, 0)) (hδF : δF = X.δ ∘ₗ ι) :
    ∃ bH : Basis (Fin 2) k ((selCx X.Dstr).toCC.homology 2),
      ConnectingMatrixIdentification δF bF bH (σ * ε) v := by
  obtain ⟨pair, hsep, hpair⟩ := hadj
  obtain ⟨bH, hdual⟩ := exists_dualBasis pair hsep bR hH2
  exact ⟨bH, toMatrix_eq_oldMat hJ2 pair (genLam X) X.δ X.toQuasi.eR hpair bR hA hB bH hdual δF
    bF ι hι hδF⟩

/-- **The generic dimensions of `C_F` are `(1, 1)`, for the genuine switch data** (tex L4888–4906,
the cone triangle `C_str → C_F → F_v[−1] →`): for a short exact sequence
`0 → C_str' → C_F → W_F → 0` of cochain complexes over `k` with `H^n(W_F) = 0` (`n ≠ 1`) and
`H^n(C_str') = 0` (`n ≠ 2`), finite-dimensional cohomology, an identification
`H²(C_str') ≃ H²(C_str)` and a basis `e_j` of `H¹(W_F)` mapping to the finite plane `(e_j, 0)` of
`H¹(W_rel)` compatibly with the connecting maps (naturality of the connecting map along
`C_F → C_rel`), the duality adjunction and the localization data of `A`, `B` give
`dim H¹(C_F) = dim H²(C_F) = 1` — `ConeIdent.cone_dims_of_matrix` with its GLUE discharged.
PROVED. -/
theorem cone_dims_genuine (X : GenuineSwitch K S k M) {ε σ : k}
    {J : Matrix (Fin 2) (Fin 2) k} (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hadj : SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex)
    (bR : Basis (Fin 2) k ((selCx X.toQuasi.D).toCC.homology 1)) {v : Fin 2 → k} (hv : v ≠ 0)
    (hA : genLam X (bR 0) = (v, 0)) (hB : genLam X (bR 1) = (0, J *ᵥ v))
    (hH2 : finrank k ((selCx X.Dstr).toCC.homology 2) = 2)
    (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ)) (hE : E.ShortExact)
    (h3 : ∀ n, n ≠ 1 → Subsingleton (E.X₃.homology n))
    (h1 : ∀ n, n ≠ 2 → Subsingleton (E.X₁.homology n))
    [FiniteDimensional k (E.X₁.homology 2)] [FiniteDimensional k (E.X₂.homology 1)]
    [FiniteDimensional k (E.X₂.homology 2)] [FiniteDimensional k (E.X₃.homology 1)]
    (eH : E.X₁.homology 2 ≃ₗ[k] (selCx X.Dstr).toCC.homology 2)
    (bF : Basis (Fin 2) k (E.X₃.homology 1))
    (ι : E.X₃.homology 1 →ₗ[k] X.toQuasi.Wrel.toCC.homology 1)
    (hι : ∀ j, X.toQuasi.eR (ι (bF j)) = (Pi.single j 1, 0))
    (hnat : ∀ x, eH ((hE.δ 1 2 (by simp)).hom x) = X.δ (ι x)) :
    finrank k (E.X₂.homology 1) = 1 ∧ finrank k (E.X₂.homology 2) = 1 := by
  obtain ⟨pair, hsep, hpair⟩ := hadj
  obtain ⟨bH, hdual⟩ := exists_dualBasis pair hsep bR hH2
  let pair' : E.X₁.homology 2 →ₗ[k] _ →ₗ[k] k := pair ∘ₗ eH.toLinearMap
  have hmat := toMatrix_eq_oldMat hJ2 pair' (genLam X) (eH.symm.toLinearMap ∘ₗ X.δ) X.toQuasi.eR
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
  exact cone_dims_of_matrix E hE h3 h1 bF (bH.map eH.symm) (mul_ne_zero hσ hε) hv hmat

/-- **The generic dimensions of `C_F` from a morphism of short exact sequences into the genuine
relaxed one** (tex L4888–4906): for a short exact sequence `0 → C_str' → C_F → W_F → 0` with a
morphism `φ` into `0 → C_str → C_rel → W_rel → 0` inducing an isomorphism on `H²` of the strict
terms, and a basis of `H¹(W_F)` mapping to the finite plane, the naturality of the connecting map
(Mathlib's `HomologySequence.δ_naturality`) supplies the compatibility of `cone_dims_genuine`.
PROVED. -/
theorem cone_dims_genuine_of_hom (X : GenuineSwitch K S k M) {ε σ : k}
    {J : Matrix (Fin 2) (Fin 2) k} (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hadj : SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex)
    (bR : Basis (Fin 2) k ((selCx X.toQuasi.D).toCC.homology 1)) {v : Fin 2 → k} (hv : v ≠ 0)
    (hA : genLam X (bR 0) = (v, 0)) (hB : genLam X (bR 1) = (0, J *ᵥ v))
    (hH2 : finrank k ((selCx X.Dstr).toCC.homology 2) = 2)
    (E : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ)) (hE : E.ShortExact)
    (h3 : ∀ n, n ≠ 1 → Subsingleton (E.X₃.homology n))
    (h1 : ∀ n, n ≠ 2 → Subsingleton (E.X₁.homology n))
    [FiniteDimensional k (E.X₁.homology 2)] [FiniteDimensional k (E.X₂.homology 1)]
    [FiniteDimensional k (E.X₂.homology 2)] [FiniteDimensional k (E.X₃.homology 1)]
    (φ : E ⟶ changeSES X.toQuasi.D (piMap X.φ) X.toQuasi.gR X.hfg)
    [IsIso (HomologicalComplex.homologyMap φ.τ₁ 2)]
    (bF : Basis (Fin 2) k (E.X₃.homology 1))
    (hι : ∀ j, X.toQuasi.eR ((HomologicalComplex.homologyMap φ.τ₃ 1).hom (bF j)) =
      (Pi.single j 1, 0)) :
    finrank k (E.X₂.homology 1) = 1 ∧ finrank k (E.X₂.homology 2) = 1 := by
  have hS₂ := switchSES_shortExact X.toQuasi (piMap X.φ) X.hfg X.φ_inj X.g_surj X.ex
  refine cone_dims_genuine X hε hσ hJ2 hadj bR hv hA hB hH2 E hE h3 h1
    (asIso (HomologicalComplex.homologyMap φ.τ₁ 2)).toLinearEquiv bF
    (HomologicalComplex.homologyMap φ.τ₃ 1).hom hι (fun x => ?_)
  have hnat := congrArg (fun f => f.hom x)
    (HomologicalComplex.HomologySequence.δ_naturality φ hE hS₂ 1 2 (by simp))
  exact hnat

end Genuine

end ZInQ.Contrib.CloudB3RC53.GenuineInst
