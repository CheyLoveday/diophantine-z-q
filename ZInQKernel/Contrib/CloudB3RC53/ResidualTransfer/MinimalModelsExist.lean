import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualAlgebra
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.CochainBridge

/-!
# RC53 ResidualTransfer: minimal models over a local ring (RC6's `MinimalModelsExist`)

Lemma `ex:limits-residual-bound`, tex L4633–4647: "After the inner limit and inversion of `t`, the
ring `𝔽₂((t))[G]` is local with nilpotent augmentation ideal. A finite free model over this ring has
a minimal model obtained by cancelling unit entries; its ranks are the dimensions of the cohomology
after augmentation [...] Finally the minimum ranks over `𝒪` are the dimensions after reduction to
`𝔽₂((t))`". The limits lane records this as the GLUE `ZInQ.Manuscript.RC.Limits.MinimalModelsExist R`
(`RC/Limits/ResidualAlgebra.lean`). This file proves it, in its exact type, for every local ring `R`.

Proof (all PROVED):
* `presIso` (tex L5357–5359, "a finite free model"): a bounded complex `K` of finite free `R`-modules
  is isomorphic to the graded complex `gradedComplex (degI K a b) (dK K a b hK)` of the matrix of its
  differential in chosen bases (`bK`).
* `MinimalModel.lean` / `CochainBridge.lean`: unit-disk cancellation puts that matrix in split form,
  and the complex is homotopy equivalent to its minimal part, whose differential lands in `𝔪`.
* `resF_map_eq_zero`, `finrank_homology_resCx_of_minimal`: after extension of scalars to the residue
  field `k`, a minimal complex has zero differential, so `dim_k Hⁱ(k ⊗ L) = rank Lⁱ`.
* `finrank_homology_resCx_of_homotopyEquiv`: `k ⊗ −` is additive, so it preserves homotopy
  equivalences and hence the dimensions of cohomology.
* `minimalModelsExist_proof`: RC6's `MinimalModelsExist R`.
-/

open CategoryTheory Limits Matrix ZInQ.Contrib.CloudB3RC53.MinimalComplexes

namespace ZInQ.Contrib.CloudB3RC53.ResidualTransfer

universe u


variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem map_mem_smul_top_aux {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) := by
  have h : ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)).map f ≤
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h ⟨x, hx, rfl⟩

/-- Extension of scalars to the residue field. -/
noncomputable abbrev resF (R : Type u) [CommRing R] [IsLocalRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (IsLocalRing.ResidueField R) :=
  ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue R)

theorem resF_additive : (resF R).Additive := by
  haveI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (IsLocalRing.residue R)).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (resF R) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

open scoped ChangeOfRings in
theorem resF_map_eq_zero {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : ∀ x, f.hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :
    (resF R).map f = 0 := by
  ext m
  let ι := ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (IsLocalRing.residue R)).unit.app N).hom
  have hι : ∀ y : N, ι y = (1 : IsLocalRing.ResidueField R) ⊗ₜ[R, IsLocalRing.residue R] y :=
    fun y => rfl
  change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R, IsLocalRing.residue R] f.hom m = 0
  rw [← hι]
  have hm := map_mem_smul_top_aux ι (hf m)
  generalize ι (f.hom m) = z at hm ⊢
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr w _
    rw [ModuleCat.restrictScalars.smul_def, (IsLocalRing.residue_eq_zero_iff r).2 hr, zero_smul]
    rfl
  · intro a b ha hb
    rw [ha, hb]
    exact add_zero (0 : (ModuleCat.restrictScalars (IsLocalRing.residue R)).obj
      ((resF R).obj N))

theorem finrank_resF_obj (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    Module.finrank (IsLocalRing.ResidueField R) ((resF R).obj M) = Module.finrank R M := by
  letI := (IsLocalRing.residue R).toAlgebra
  exact Module.finrank_baseChange

/-- The residual complex `k ⊗_R K`. -/
noncomputable abbrev resCx (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} (IsLocalRing.ResidueField R)) ℤ :=
  ((resF R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

theorem finrank_homology_resCx_of_minimal (L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Free R (L.X i)] [∀ i, Module.Finite R (L.X i)]
    (hmin : ∀ i j (x : L.X i),
      (L.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (L.X j))) (i : ℤ) :
    Module.finrank (IsLocalRing.ResidueField R) ((resCx L).homology i) =
      Module.finrank R (L.X i) := by
  have hd : ∀ a b, (resCx L).d a b = 0 := fun a b => resF_map_eq_zero _ (hmin a b)
  let e : (resCx L).homology i ≅ (resCx L).X i :=
    ((resCx L).isoHomologyπ (i - 1) i (by simp) (hd _ _)).symm ≪≫
      (resCx L).iCyclesIso i (i + 1) (by simp) (hd _ _)
  rw [e.toLinearEquiv.finrank_eq]
  exact finrank_resF_obj (L.X i)

theorem finrank_homology_resCx_of_homotopyEquiv {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv K L) (i : ℤ) :
    Module.finrank (IsLocalRing.ResidueField R) ((resCx K).homology i) =
      Module.finrank (IsLocalRing.ResidueField R) ((resCx L).homology i) := by
  have := resF_additive (R := R)
  exact (((resF R).mapHomotopyEquiv e).toHomologyIso i).toLinearEquiv.finrank_eq



section Present

variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
  [∀ i, Module.Free R (K.X i)] [∀ i, Module.Finite R (K.X i)]

/-- The basis index of the presentation: a basis of every term in `[a, b]`. -/
abbrev Idx : Type u := Σ n : Finset.Icc a b, Module.Free.ChooseBasisIndex R (K.X n)

/-- The degree of a basis vector. -/
abbrev degI : Idx K a b → ℤ := fun x => x.1

noncomputable instance : DecidableEq (Idx K a b) := Classical.decEq _

/-- The fibre of the degree map over `n ∈ [a, b]` is the basis index of `K^n`. -/
def fiberEquiv (n : ℤ) (h : n ∈ Finset.Icc a b) :
    {x : Idx K a b // degI K a b x = n} ≃ Module.Free.ChooseBasisIndex R (K.X n) where
  toFun x := (congrArg (fun m : ℤ => Module.Free.ChooseBasisIndex R (K.X m)) x.2) ▸ x.1.2
  invFun y := ⟨⟨⟨n, h⟩, y⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨m, hm⟩, y⟩, hmn⟩
    simp only [degI] at hmn
    subst hmn
    rfl
  right_inv y := rfl

variable (hK : ∀ i, i < a ∨ b < i → Subsingleton (K.X i))

/-- A basis of `K^n` indexed by the degree-`n` basis vectors. -/
noncomputable def bK (n : ℤ) : Module.Basis {x : Idx K a b // degI K a b x = n} R (K.X n) :=
  if h : n ∈ Finset.Icc a b then
    (Module.Free.chooseBasis R (K.X n)).reindex (fiberEquiv K a b n h).symm
  else
    haveI : Subsingleton (K.X n) := hK n (by simp [Finset.mem_Icc] at h; omega)
    haveI : IsEmpty {x : Idx K a b // degI K a b x = n} :=
      ⟨fun x => h (x.2 ▸ x.1.1.2)⟩
    Module.Basis.empty _

/-- The matrix of the differential in the bases `bK`. -/
noncomputable def dK : Matrix (Idx K a b) (Idx K a b) R := fun y x =>
  (bK K a b hK (degI K a b y)).repr
    ((K.d (degI K a b x) (degI K a b y)).hom (bK K a b hK (degI K a b x) ⟨x, rfl⟩)) ⟨y, rfl⟩

omit [∀ i, Module.Finite R (K.X i)] in
theorem dK_blk (i j : ℤ) (y : {x : Idx K a b // degI K a b x = j})
    (x : {x : Idx K a b // degI K a b x = i}) :
    dK K a b hK y.1 x.1 = (bK K a b hK j).repr ((K.d i j).hom (bK K a b hK i x)) y := by
  obtain ⟨x, rfl⟩ := x
  obtain ⟨y, rfl⟩ := y
  rfl

omit [∀ i, Module.Finite R (K.X i)] in
theorem dK_graded : IsGradedDiff (degI K a b) (dK K a b hK) := by
  intro y x h
  by_contra hne
  apply h
  simp only [dK]
  rw [K.shape _ _ (by simp only [ComplexShape.up_Rel]; omega)]
  simp

theorem dK_sq : dK K a b hK * dK K a b hK = 0 := by
  ext z x
  rw [mul_apply, Matrix.zero_apply]
  rw [sum_subtype_of_zero (fun y => degI K a b y = degI K a b x + 1)]
  · set i := degI K a b x
    set j := degI K a b x + 1
    set n := degI K a b z
    set x' : {w : Idx K a b // degI K a b w = i} := ⟨x, rfl⟩
    set z' : {w : Idx K a b // degI K a b w = n} := ⟨z, rfl⟩
    set w := (K.d i j).hom (bK K a b hK i x')
    have h1 : ∀ y : {y : Idx K a b // degI K a b y = j},
        dK K a b hK z y.1 * dK K a b hK y.1 x =
          (bK K a b hK j).repr w y * (bK K a b hK n).repr ((K.d j n).hom (bK K a b hK j y)) z' := by
      intro y
      rw [show x = x'.1 from rfl, show z = z'.1 from rfl, dK_blk K a b hK i j y x',
        dK_blk K a b hK j n z' y, mul_comm]
    rw [Finset.sum_congr rfl (fun y _ => h1 y)]
    have h2 : (K.d j n).hom w = 0 := by
      simp only [w]
      rw [← ModuleCat.comp_apply, K.d_comp_d]; rfl
    have h3 := congrArg (fun v => (bK K a b hK n).repr ((K.d j n).hom v) z')
      ((bK K a b hK j).sum_repr w)
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at h3
    rw [h3, h2, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  · intro y hy
    have : dK K a b hK y x = 0 := by
      by_contra h
      exact hy (dK_graded K a b hK y x h)
    rw [this, mul_zero]

theorem d_bK (i j : ℤ) (x : {x : Idx K a b // degI K a b x = i}) :
    (K.d i j).hom (bK K a b hK i x) =
      ∑ y : {y : Idx K a b // degI K a b y = j}, dK K a b hK y.1 x.1 • bK K a b hK j y := by
  conv_lhs => rw [← (bK K a b hK j).sum_repr ((K.d i j).hom (bK K a b hK i x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dK_blk K a b hK i j y x]

theorem presComm (i j : ℤ) (v : {x : Idx K a b // degI K a b x = i} → R) :
    (K.d i j).hom ((bK K a b hK i).equivFun.symm v) =
      (bK K a b hK j).equivFun.symm ((blk (degI K a b) (degI K a b) (dK K a b hK) j i) *ᵥ v) := by
  rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, d_bK K a b hK i j, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, blk, submatrix_apply]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **The presentation**: a bounded complex of finite free modules is isomorphic to the graded
complex of the matrix of its differential in chosen bases. -/
noncomputable def presIso :
    gradedComplex (degI K a b) (dK K a b hK) (dK_graded K a b hK) (dK_sq K a b hK) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((bK K a b hK n).equivFun.symm).toModuleIso) (fun i j _ => by
      ext v
      exact presComm K a b hK i j v)

end Present


/-- **RC6's `MinimalModelsExist R`, proved** (tex L4633–4647, L5357–5359): every bounded complex of
finite free modules over a local ring `R` is homotopy equivalent to a minimal one (finite free,
differential into `𝔪`), with ranks at most those of `K` and equal, degree by degree, to the dimensions
over the residue field of the cohomology of `k ⊗_R K`. Classification: PROVED (discharges the GLUE
`ZInQ.Manuscript.RC.Limits.MinimalModelsExist`). -/
theorem minimalModelsExist_proof (R : Type u) [CommRing R] [IsLocalRing R] :
    ZInQ.Manuscript.RC.Limits.MinimalModelsExist R := by
  intro K hfree hbd
  obtain ⟨a, b, hab⟩ := hbd
  haveI : ∀ i, Module.Free R (K.X i) := fun i => (hfree i).1
  haveI : ∀ i, Module.Finite R (K.X i) := fun i => (hfree i).2
  set deg := degI K a b
  set d := dK K a b hab
  have hg : IsGradedDiff deg d := dK_graded K a b hab
  have hd : d * d = 0 := dK_sq K a b hab
  obtain ⟨P, Q, kind, partner, hPQ, hQP, hP, hQ, hS⟩ :=
    minimalModelSplit_proof R (Idx K a b) deg d hg hd
  have hgD := IsGradedDiff.conj hP hg hQ
  have hdD := conj_sq_zero hQP hd
  obtain ⟨⟨e⟩, hmin⟩ := splitFormHomotopyEquiv_proof R (Idx K a b) deg (P * d * Q) kind partner
    hgD hdD hS
  set L := gradedComplex (fun x : MinIdx kind => deg x.1) (dmin (P * d * Q) kind) (dmin_graded hgD)
    (dmin_sq hS hdD)
  have eKG : HomotopyEquiv K (gradedComplex deg (P * d * Q) hgD hdD) :=
    (HomotopyEquiv.ofIso (presIso K a b hab).symm).trans
      (HomotopyEquiv.ofIso (gradedIso deg d P Q hg hd hP hQ hPQ hQP))
  have eKL : HomotopyEquiv K L := eKG.trans e.symm
  haveI : ∀ i, Module.Free R (L.X i) := fun i =>
    inferInstanceAs (Module.Free R ({x : MinIdx kind // deg x.1 = i} → R))
  haveI : ∀ i, Module.Finite R (L.X i) := fun i =>
    inferInstanceAs (Module.Finite R ({x : MinIdx kind // deg x.1 = i} → R))
  refine ⟨L, ⟨eKL⟩, fun i => ⟨inferInstance, inferInstance⟩, hmin, fun i => ?_, fun i => ?_⟩
  · have h1 : Module.finrank R (L.X i) = Fintype.card {x : MinIdx kind // deg x.1 = i} :=
      Module.finrank_fintype_fun_eq_card R
    have h2 : Module.finrank R (K.X i) = Fintype.card {x : Idx K a b // deg x = i} := by
      exact Module.finrank_eq_card_basis (bK K a b hab i)
    rw [h1, h2]
    exact Fintype.card_le_of_injective (fun x => ⟨x.1.1, x.2⟩)
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h)))
  · rw [← finrank_homology_resCx_of_minimal L hmin i]
    exact (finrank_homology_resCx_of_homotopyEquiv eKL i).symm

end ZInQ.Contrib.CloudB3RC53.ResidualTransfer
