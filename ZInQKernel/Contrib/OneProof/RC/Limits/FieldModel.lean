import ZInQKernel.Contrib.OneProof.RC.Limits.GradedFiniteFree
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionCancel

/-!
# Lane RC31, round 4: finite free models over a field

Manuscript `diophantine_zq.tex`, the common-coordinate support triangle (tex 4157–4194) and the
graded model of the inclusion with quotient (tex 5394–5454): "over a field, splitting gives a
minimal model".

Part 1 (models over a field).
* `exists_gradedModel_field`: over a field `F`, a complex with finite residual cohomology has a
  graded finite free model of rank `dim Hⁿ(k ⊗_F X)` (a field is a local ring with nilpotent
  maximal ideal `⊥`, and every module over a field is flat); `exists_minimalGradedModel_field`:
  the model differential can be taken to be zero (a minimal model).
* `fieldCohomologyAt X n`: the actual cohomology `ker dⁿ / im dⁿ⁻¹` over `F`, and
  `fieldCohomologyEquivResidual`: its identification with the residual cohomology along
  `F ≃ F/⊥` and `V ≃ k ⊗_F V`.
* `exists_gradedModel_field_cohomology`, `exists_minimalGradedModel_field_cohomology`: the
  (minimal) model with ranks `dim_F Hⁿ(X)`, and the bounded corollary
  `exists_gradedModel_field_bounded`.

Part 2 (the inclusion with quotient).
* `SplitInclusion`: a degreewise injective chain map with chosen complements `Qⁿ` of the images
  (they exist over a field: `exists_splitInclusion`).
* `SplitInclusion.d_block`, `d_blockEquiv`: in the splitting `C_R = i(C_P) ⊕ Q` the
  differential is upper triangular `[[d_P, *], [0, d_Q]]`; `dQ_dQ`, `d_offDiag_add_offDiag_dQ`:
  its square-zero identities; `quotientCx`, `toQuotient`, `quotientEquivCokernel`,
  `d_sub_dQ_mem`: `(Q, d_Q)` is the cokernel complex; `toMatrix_d_adapted`: the matrix of the
  differential in adapted bases is `fromBlocks d_P * 0 d_Q`.

Part 3 (the full-condition pre-cancellation complex).
* `fullPreOfTriangular`: the `FullPreComplex` with `c⁰ = d⁰`, `Y = 0`, `P = d¹`, `T = 0`,
  `U = d²` from blocks `Q, V, B` with `U Q + V B = 0`; `cancel_fullPreOfTriangular`: cancelling
  `B` returns the old complex.
* `fullPreOfSplit`, `split_sq`, `toMatrix_d_one_fullPreOfSplit`: the blocks read off from a
  split inclusion of a block complex, the identity `U Q + V B = 0`, and `d¹_R = (P Q; T B)` in
  adapted bases; `splitCoordHom`, `splitCoordL_bijective`: the comparison chain map
  `fullPreOfSplit → C_R` is a degreewise isomorphism; `exists_fullPreModel`: the existence
  statement over a field.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory TensorProduct IsLocalRing Module
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

section Field

variable {F : Type} [Field F]

/-- The maximal ideal of a field is nilpotent (it is `⊥`).
Locator: tex 4157–4194. Kind: PROVED. -/
theorem isNilpotent_maximalIdeal_field : IsNilpotent (maximalIdeal F) :=
  ⟨1, by rw [maximalIdeal_eq_bot, pow_one]; rfl⟩

/-- **Graded finite free models over a field** (tex 4157–4194, with Lemma
`ex:limits-inner-limit`, tex 4391–4451): a complex `X` over a field `F` whose residual cohomology
is finite in every degree has a graded finite free model of rank `dim_k Hⁿ(k ⊗_F X)` in degree
`n`. Kind: PROVED. -/
theorem exists_gradedModel_field (X : GCx F)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField F) (residualCohomologyAt X n)) :
    ∃ R : GradedModel X, ∀ n, R.rank n =
      Module.finrank (IsLocalRing.ResidueField F) (residualCohomologyAt X n) :=
  exists_gradedModel isNilpotent_maximalIdeal_field X hfin

/-- **Minimal graded models over a field** (tex 4157–4194: "over a field, splitting gives a
minimal model"): the model of `exists_gradedModel_field` can be taken with zero model
differential. Over a field the perturbation `ε = d − d₀` has entries in the maximal ideal `⊥`,
so it vanishes and Elliot's model differential `p₀ε(1+h₀ε)⁻¹i₀` is zero. Kind: PROVED. -/
theorem exists_minimalGradedModel_field (X : GCx F)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField F) (residualCohomologyAt X n)) :
    ∃ R : GradedModel X, (∀ n, R.rank n =
      Module.finrank (IsLocalRing.ResidueField F) (residualCohomologyAt X n)) ∧
      ∀ a b (h : a + 1 = b), R.dC a b h = 0 := by
  obtain ⟨_, _, B, -, -, -, hε, H⟩ :=
    exists_elliotGradedRetract isNilpotent_maximalIdeal_field X hfin
  refine ⟨gradedModelOfTotal H, fun n => rfl, fun a b hab => ?_⟩
  have hε0 : gTotalDiff X - liftedDiskDifferential B = 0 := LinearMap.ext fun x => by
    have hx := hε x
    rw [maximalIdeal_eq_bot, Submodule.bot_smul, Submodule.mem_bot] at hx
    exact hx
  have hd : perturbedDifferential (gTotalDiff X - liftedDiskDifferential B)
      (liftedDiskHomotopy B) (cohomologyInclusion B) (cohomologyProjection B) = 0 := by
    rw [hε0]
    simp only [perturbedDifferential, LinearMap.zero_comp, LinearMap.comp_zero]
  rw [gradedModelOfTotal_dC]
  simp only [gModelMatrix, hd, LinearMap.zero_comp, LinearMap.comp_zero, map_zero]
  rfl

end Field

/-! ### Subquotients along compatible equivalences -/

section Subquotient

variable {R k : Type*} [CommRing R] [Ring k] [Algebra R k]
variable {V W Z : Type*} [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]
  [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower R k W]
  [AddCommGroup Z] [Module k Z] [Module R Z] [IsScalarTower R k Z]
variable {V' W' Z' : Type*} [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
  [AddCommGroup Z'] [Module R Z']

/-- The `R`-linear map `ker g' / im f' → ker g / im f` induced by `R`-linear equivalences
compatible with `f, f'` and `g, g'` (`f, g` are `k`-linear for an `R`-algebra `k`).
Locator: tex 4157–4194. Kind: definition. -/
def subquotientMapOfEquiv (f : V →ₗ[k] W) (g : W →ₗ[k] Z) (f' : V' →ₗ[R] W')
    (g' : W' →ₗ[R] Z') (eV : V' ≃ₗ[R] V) (eW : W' ≃ₗ[R] W) (eZ : Z' ≃ₗ[R] Z)
    (hf : ∀ v, f (eV v) = eW (f' v)) (hg : ∀ w, g (eW w) = eZ (g' w)) :
    subquotientOf f' g' →ₗ[R] subquotientOf f g :=
  Submodule.liftQ _
    (((Submodule.mkQ _).restrictScalars R) ∘ₗ
      LinearMap.codRestrict ((LinearMap.ker g).restrictScalars R)
        (eW.toLinearMap ∘ₗ (LinearMap.ker g').subtype) (fun w => by
          change g (eW w.1) = 0
          rw [hg, w.2.out, map_zero]))
    (by
      rintro ⟨w, hw⟩ hmem
      obtain ⟨v, hv⟩ := hmem
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨eV v, ?_⟩
      change f (eV v) = eW w
      rw [hf]
      exact congrArg eW hv)

omit [IsScalarTower R k V] [IsScalarTower R k Z] in
/-- `subquotientMapOfEquiv` on a class `[w]` is the class `[eW w]`.
Locator: tex 4157–4194. Kind: PROVED
(definitional). -/
theorem subquotientMapOfEquiv_mk (f : V →ₗ[k] W) (g : W →ₗ[k] Z) (f' : V' →ₗ[R] W')
    (g' : W' →ₗ[R] Z') (eV : V' ≃ₗ[R] V) (eW : W' ≃ₗ[R] W) (eZ : Z' ≃ₗ[R] Z)
    (hf : ∀ v, f (eV v) = eW (f' v)) (hg : ∀ w, g (eW w) = eZ (g' w))
    (w : LinearMap.ker g') :
    subquotientMapOfEquiv f g f' g' eV eW eZ hf hg (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨eW w.1, by
        change g (eW w.1) = 0
        rw [hg, w.2.out, map_zero]⟩ :=
  rfl

omit [IsScalarTower R k V] [IsScalarTower R k Z] in
/-- The map `subquotientMapOfEquiv` is bijective.
Locator: tex 4157–4194. Kind: PROVED. -/
theorem subquotientMapOfEquiv_bijective (f : V →ₗ[k] W) (g : W →ₗ[k] Z) (f' : V' →ₗ[R] W')
    (g' : W' →ₗ[R] Z') (eV : V' ≃ₗ[R] V) (eW : W' ≃ₗ[R] W) (eZ : Z' ≃ₗ[R] Z)
    (hf : ∀ v, f (eV v) = eW (f' v)) (hg : ∀ w, g (eW w) = eZ (g' w)) :
    Function.Bijective (subquotientMapOfEquiv f g f' g' eV eW eZ hf hg) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H w =>
      rw [subquotientMapOfEquiv_mk, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨v, hv⟩ := hx
      refine ⟨eV.symm v, ?_⟩
      apply eW.injective
      rw [← hf, LinearEquiv.apply_symm_apply]
      exact hv
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H w =>
      refine ⟨Submodule.Quotient.mk ⟨eW.symm w.1, ?_⟩, ?_⟩
      · change g' (eW.symm w.1) = 0
        apply eZ.injective
        rw [← hg, LinearEquiv.apply_symm_apply, w.2.out, map_zero]
      · rw [subquotientMapOfEquiv_mk]
        congr 1
        exact Subtype.ext (LinearEquiv.apply_symm_apply _ _)

/-- **Subquotients along compatible equivalences**: `ker g' / im f' ≃ ker g / im f` as
`R`-modules.
Locator: tex 4157–4194. Kind: definition. -/
def subquotientEquivOfEquiv (f : V →ₗ[k] W) (g : W →ₗ[k] Z) (f' : V' →ₗ[R] W')
    (g' : W' →ₗ[R] Z') (eV : V' ≃ₗ[R] V) (eW : W' ≃ₗ[R] W) (eZ : Z' ≃ₗ[R] Z)
    (hf : ∀ v, f (eV v) = eW (f' v)) (hg : ∀ w, g (eW w) = eZ (g' w)) :
    subquotientOf f' g' ≃ₗ[R] subquotientOf f g :=
  LinearEquiv.ofBijective _ (subquotientMapOfEquiv_bijective f g f' g' eV eW eZ hf hg)

end Subquotient

/-! ### The actual cohomology over a field -/

section FieldCohomology

variable {F : Type} [Field F]

/-- **The cohomology in degree `n`** of a complex over a field, `Hⁿ(X) = ker dⁿ / im dⁿ⁻¹`.
Locator: tex 4157–4194. Kind: definition. -/
abbrev fieldCohomologyAt (X : GCx F) (n : ℤ) : Type :=
  subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl)

/-- The residue map of a field is an `F`-linear equivalence `F ≃ F/⊥`.
Locator: tex 4157–4194. Kind: definition. -/
def residueLinearEquiv (F : Type) [Field F] : F ≃ₗ[F] ResidueField F :=
  LinearEquiv.ofBijective (Algebra.linearMap F (ResidueField F))
    ⟨(algebraMap F (ResidueField F)).injective, Ideal.Quotient.mk_surjective⟩

/-- The `F`-linear equivalence `V ≃ k ⊗_F V`, `v ↦ 1 ⊗ v`, for `k = F/⊥`.
Locator: tex 4157–4194. Kind: definition. -/
def residualTensorEquiv (V : Type*) [AddCommGroup V] [Module F V] :
    V ≃ₗ[F] ResidueField F ⊗[F] V :=
  (TensorProduct.lid F V).symm ≪≫ₗ LinearEquiv.rTensor V (residueLinearEquiv F)

/-- `residualTensorEquiv` sends `v` to `1 ⊗ v`.
Locator: tex 4157–4194. Kind: PROVED. -/
theorem residualTensorEquiv_apply (V : Type*) [AddCommGroup V] [Module F V] (v : V) :
    residualTensorEquiv V v = (1 : ResidueField F) ⊗ₜ v := by
  simp only [residualTensorEquiv, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
    LinearEquiv.rTensor_tmul]
  exact congrArg (fun a => a ⊗ₜ[F] v) (map_one (algebraMap F (ResidueField F)))

/-- The residual differential is the base change of `d` along `V ≃ k ⊗_F V`.
Locator: tex 4157–4194. Kind: PROVED. -/
theorem residualDiff_residualTensorEquiv (X : GCx F) (a b : ℤ) (h : a + 1 = b) (v : X.X a) :
    residualDiff X a b h (residualTensorEquiv _ v) = residualTensorEquiv _ (X.d a b h v) := by
  rw [residualTensorEquiv_apply, residualTensorEquiv_apply, residualDiff,
    LinearMap.baseChange_tmul]

/-- **Cohomology equals residual cohomology over a field** (tex 4157–4194): the `F`-linear
identification `Hⁿ(X) ≃ Hⁿ(k ⊗_F X)` for `k = F/⊥`. Kind: definition. -/
def fieldCohomologyEquivResidual (X : GCx F) (n : ℤ) :
    fieldCohomologyAt X n ≃ₗ[F] residualCohomologyAt X n :=
  subquotientEquivOfEquiv _ _ _ _ (residualTensorEquiv _) (residualTensorEquiv _)
    (residualTensorEquiv _) (residualDiff_residualTensorEquiv X _ _ _)
    (residualDiff_residualTensorEquiv X _ _ _)

/-- The ranks of `Hⁿ(X)` over `F` and of `Hⁿ(k ⊗_F X)` over `k` agree.
Locator: tex 4157–4194. Kind: PROVED. -/
theorem rank_fieldCohomology_eq (X : GCx F) (n : ℤ) :
    Module.rank F (fieldCohomologyAt X n) =
      Module.rank (ResidueField F) (residualCohomologyAt X n) :=
  rank_eq_of_equiv_equiv (algebraMap F (ResidueField F))
    (fieldCohomologyEquivResidual X n).toAddEquiv
    (residueLinearEquiv F).bijective (fun r m => by
      change fieldCohomologyEquivResidual X n (r • m) = _
      rw [map_smul, algebraMap_smul]
      rfl)

/-- **Dimension of the cohomology** (tex 4157–4194): `dim_F Hⁿ(X) = dim_k Hⁿ(k ⊗_F X)`.
Kind: PROVED. -/
theorem finrank_fieldCohomology_eq (X : GCx F) (n : ℤ) :
    Module.finrank F (fieldCohomologyAt X n) =
      Module.finrank (ResidueField F) (residualCohomologyAt X n) :=
  congrArg Cardinal.toNat (rank_fieldCohomology_eq X n)

/-- Finiteness of `Hⁿ(X)` over `F` is finiteness of `Hⁿ(k ⊗_F X)` over `k`.
Locator: tex 4157–4194. Kind: PROVED. -/
theorem finite_fieldCohomology_iff (X : GCx F) (n : ℤ) :
    Module.Finite F (fieldCohomologyAt X n) ↔
      Module.Finite (ResidueField F) (residualCohomologyAt X n) := by
  rw [← Module.rank_lt_aleph0_iff, ← Module.rank_lt_aleph0_iff, rank_fieldCohomology_eq]

/-- **Graded finite free models over a field, actual cohomology** (tex 4157–4194: "over a field,
splitting gives a minimal model"): a complex over a field with finite-dimensional cohomology in
every degree has a graded finite free model of rank `dim_F Hⁿ(X)` in degree `n`.
Kind: PROVED. -/
theorem exists_gradedModel_field_cohomology (X : GCx F)
    (hfin : ∀ n, Module.Finite F (fieldCohomologyAt X n)) :
    ∃ R : GradedModel X, ∀ n, R.rank n = Module.finrank F (fieldCohomologyAt X n) := by
  obtain ⟨R, hR⟩ := exists_gradedModel_field X fun n => (finite_fieldCohomology_iff X n).1 (hfin n)
  exact ⟨R, fun n => (hR n).trans (finrank_fieldCohomology_eq X n).symm⟩

/-- **Minimal graded models over a field, actual cohomology** (tex 4157–4194): a complex over a
field with finite-dimensional cohomology has a graded finite free model of rank `dim_F Hⁿ(X)`
in degree `n` with zero model differential. Kind: PROVED. -/
theorem exists_minimalGradedModel_field_cohomology (X : GCx F)
    (hfin : ∀ n, Module.Finite F (fieldCohomologyAt X n)) :
    ∃ R : GradedModel X, (∀ n, R.rank n = Module.finrank F (fieldCohomologyAt X n)) ∧
      ∀ a b (h : a + 1 = b), R.dC a b h = 0 := by
  obtain ⟨R, hR, hd⟩ :=
    exists_minimalGradedModel_field X fun n => (finite_fieldCohomology_iff X n).1 (hfin n)
  exact ⟨R, fun n => (hR n).trans (finrank_fieldCohomology_eq X n).symm, hd⟩

/-- **Bounded graded finite free models over a field** (tex 4157–4194): if moreover `Hⁿ(X) = 0`
outside `[lo, hi]`, the model has rank `0` there. Kind: PROVED. -/
theorem exists_gradedModel_field_bounded (X : GCx F)
    (hfin : ∀ n, Module.Finite F (fieldCohomologyAt X n)) (lo hi : ℤ)
    (hX : ∀ n, n < lo ∨ hi < n → Subsingleton (fieldCohomologyAt X n)) :
    ∃ R : GradedModel X, (∀ n, R.rank n = Module.finrank F (fieldCohomologyAt X n)) ∧
      ∀ n, n < lo ∨ hi < n → R.rank n = 0 := by
  obtain ⟨R, hR⟩ := exists_gradedModel_field_cohomology X hfin
  refine ⟨R, hR, fun n hn => ?_⟩
  have := hX n hn
  rw [hR]
  exact Module.finrank_zero_of_subsingleton

end FieldCohomology

/-! ### Part 2: a degreewise split inclusion has an upper triangular differential -/

section Split

variable {S : Type} [CommRing S]

/-- **A degreewise split inclusion of complexes** (tex 5394–5403): a chain map `i : C_P → C_R`
injective in every degree, together with a complement `Qⁿ` of `im iⁿ` in every degree.
Kind: definition (data). -/
structure SplitInclusion (CP CR : GCx S) where
  /-- The inclusion. -/
  i : GHom CP CR
  /-- Injectivity in every degree. -/
  inj : ∀ n, Function.Injective (i.f n n rfl)
  /-- The chosen complements of the images. -/
  Qc : ∀ n, Submodule S (CR.X n)
  /-- `Qⁿ` is a complement of `im iⁿ`. -/
  compl : ∀ n, IsCompl (LinearMap.range (i.f n n rfl)) (Qc n)

/-- **Splittings exist over a field** (tex 5394–5403: "over a field, splitting"): every
degreewise injective chain map of complexes over a field extends to a `SplitInclusion`.
Kind: PROVED. -/
theorem exists_splitInclusion {F : Type} [Field F] {CP CR : GCx F} (i : GHom CP CR)
    (hi : ∀ n, Function.Injective (i.f n n rfl)) :
    ∃ E : SplitInclusion CP CR, E.i = i := by
  choose Qc hQ using fun n => Submodule.exists_isCompl (LinearMap.range (i.f n n rfl))
  exact ⟨⟨i, hi, Qc, hQ⟩, rfl⟩

namespace SplitInclusion

variable {CP CR : GCx S} (E : SplitInclusion CP CR)

/-- The `C_P`-coordinate `Cⁿ_R → Cⁿ_P` of the splitting `Cⁿ_R = im iⁿ ⊕ Qⁿ`.
Locator: tex 5398–5403. Kind: definition. -/
def coordP (n : ℤ) : CR.X n →ₗ[S] CP.X n :=
  (LinearEquiv.ofInjective _ (E.inj n)).symm.toLinearMap ∘ₗ
    (LinearMap.range (E.i.f n n rfl)).projectionOnto (E.Qc n) (E.compl n)

/-- The `Q`-coordinate `Cⁿ_R → Qⁿ` of the splitting `Cⁿ_R = im iⁿ ⊕ Qⁿ`.
Locator: tex 5398–5403. Kind: definition. -/
def coordQ (n : ℤ) : CR.X n →ₗ[S] E.Qc n :=
  (E.Qc n).projectionOnto (LinearMap.range (E.i.f n n rfl)) (E.compl n).symm

/-- Every element is `i (coordP x) + coordQ x`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem decompose (n : ℤ) (x : CR.X n) :
    E.i.f n n rfl (E.coordP n x) + (E.coordQ n x : CR.X n) = x := by
  have h1 : E.i.f n n rfl (E.coordP n x) =
      (LinearMap.range (E.i.f n n rfl)).projection (E.Qc n) (E.compl n) x :=
    congrArg Subtype.val ((LinearEquiv.ofInjective _ (E.inj n)).apply_symm_apply _)
  rw [h1]
  exact Submodule.projection_add_projection_eq_self (E.compl n) x

/-- `coordP ∘ i = 1`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem coordP_i (n : ℤ) (x : CP.X n) : E.coordP n (E.i.f n n rfl x) = x := by
  change (LinearEquiv.ofInjective _ (E.inj n)).symm
    ((LinearMap.range (E.i.f n n rfl)).projectionOnto (E.Qc n) (E.compl n)
      (E.i.f n n rfl x)) = x
  rw [Submodule.projectionOnto_apply_of_mem_left _ (LinearMap.mem_range_self _ x),
    LinearEquiv.symm_apply_eq]
  rfl

/-- `coordQ ∘ i = 0`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem coordQ_i (n : ℤ) (x : CP.X n) : E.coordQ n (E.i.f n n rfl x) = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _ (LinearMap.mem_range_self _ x)

/-- `coordP` vanishes on `Qⁿ`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem coordP_Q (n : ℤ) (q : E.Qc n) : E.coordP n (q : CR.X n) = 0 := by
  change (LinearEquiv.ofInjective _ (E.inj n)).symm
    ((LinearMap.range (E.i.f n n rfl)).projectionOnto (E.Qc n) (E.compl n) q) = 0
  rw [Submodule.projectionOnto_apply_right, map_zero]

/-- `coordQ` is the identity on `Qⁿ`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem coordQ_Q (n : ℤ) (q : E.Qc n) : E.coordQ n (q : CR.X n) = q :=
  Submodule.projectionOnto_apply_left _ q

/-- Uniqueness of the decomposition: `i u + w = 0` with `w ∈ Qⁿ` forces `u = 0` and `w = 0`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem eq_zero_of_add_eq_zero (n : ℤ) (u : CP.X n) (w : E.Qc n)
    (h : E.i.f n n rfl u + (w : CR.X n) = 0) : u = 0 ∧ w = 0 := by
  constructor
  · have := congrArg (E.coordP n) h
    rwa [map_add, coordP_i, coordP_Q, add_zero, map_zero] at this
  · have := congrArg (E.coordQ n) h
    rwa [map_add, coordQ_i, coordQ_Q, zero_add, map_zero] at this

/-- Where the complement vanishes, `i` is bijective.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem i_bijective (n : ℤ) (h : E.Qc n = ⊥) : Function.Bijective (E.i.f n n rfl) := by
  refine ⟨E.inj n, LinearMap.range_eq_top.1 ?_⟩
  have hc := E.compl n
  rw [h] at hc
  simpa using hc.sup_eq_top

/-- **The quotient block of the differential**: `d_Q = coordQ ∘ d_R` on `Q`, the `(Q, Q)` entry
of the differential in the splitting (tex 5398–5403). Kind: definition. -/
def dQ (a b : ℤ) (h : a + 1 = b) : E.Qc a →ₗ[S] E.Qc b :=
  E.coordQ b ∘ₗ CR.d a b h ∘ₗ (E.Qc a).subtype

/-- **The off-diagonal block of the differential**: `* = coordP ∘ d_R` on `Q`, the `(P, Q)` entry
of the differential in the splitting (tex 5398–5403). Kind: definition. -/
def offDiag (a b : ℤ) (h : a + 1 = b) : E.Qc a →ₗ[S] CP.X b :=
  E.coordP b ∘ₗ CR.d a b h ∘ₗ (E.Qc a).subtype

/-- `i` commutes with the differentials.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem i_d (a b : ℤ) (h : a + 1 = b) (x : CP.X a) :
    E.i.f b b rfl (CP.d a b h x) = CR.d a b h (E.i.f a a rfl x) :=
  E.i.comm a b a b rfl h h rfl x

/-- The differential on `Q` is `i ∘ * + d_Q`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem d_Q (a b : ℤ) (h : a + 1 = b) (q : E.Qc a) :
    CR.d a b h q = E.i.f b b rfl (E.offDiag a b h q) + (E.dQ a b h q : CR.X b) :=
  (E.decompose b _).symm

/-- **The differential is upper triangular** (tex 5398–5403: "the graded model of (5.6) is
`C_old ⊕ ⊕_q Q_q` with an upper triangular differential"): in the splitting
`C_R = i(C_P) ⊕ Q`, `d_R (i x + q) = i (d_P x + * q) + d_Q q`, i.e. `d_R = [[d_P, *], [0, d_Q]]`.
Kind: PROVED. -/
theorem d_block (a b : ℤ) (h : a + 1 = b) (x : CP.X a) (q : E.Qc a) :
    CR.d a b h (E.i.f a a rfl x + q) =
      E.i.f b b rfl (CP.d a b h x + E.offDiag a b h q) + (E.dQ a b h q : CR.X b) := by
  rw [map_add, ← E.i_d, E.d_Q, map_add, add_assoc]

/-- **Square-zero identities of the triangular differential** (tex 5398–5403): `d_Q² = 0` and
`d_P ∘ * + * ∘ d_Q = 0`. Kind: PROVED. -/
theorem dQ_dQ_and_offDiag (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) (q : E.Qc a) :
    E.dQ b c hbc (E.dQ a b hab q) = 0 ∧
      CP.d b c hbc (E.offDiag a b hab q) + E.offDiag b c hbc (E.dQ a b hab q) = 0 := by
  have h0 := CR.d_d a b c hab hbc q
  rw [E.d_Q a b hab, map_add, ← E.i_d, E.d_Q b c hbc, ← add_assoc, ← map_add] at h0
  exact (E.eq_zero_of_add_eq_zero c _ _ h0).symm

/-- `d_Q² = 0`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem dQ_dQ (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) (q : E.Qc a) :
    E.dQ b c hbc (E.dQ a b hab q) = 0 :=
  (E.dQ_dQ_and_offDiag a b c hab hbc q).1

/-- `d_P ∘ * + * ∘ d_Q = 0`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem d_offDiag_add_offDiag_dQ (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c)
    (q : E.Qc a) :
    CP.d b c hbc (E.offDiag a b hab q) + E.offDiag b c hbc (E.dQ a b hab q) = 0 :=
  (E.dQ_dQ_and_offDiag a b c hab hbc q).2

/-- **The quotient complex** `(Q, d_Q)` of the splitting (tex 5398–5403). Kind: definition. -/
def quotientCx : GCx S where
  X n := ModuleCat.of S (E.Qc n)
  d a b h := E.dQ a b h
  d_d a b c hab hbc q := E.dQ_dQ a b c hab hbc q

/-- The projection `C_R → Q` is a chain map.
Locator: tex 5398–5403. Kind: definition. -/
def toQuotient : GHom CR E.quotientCx where
  f a b hab := hab ▸ E.coordQ a
  comm := by
    rintro i _ j _ rfl rfl h rfl x
    change E.coordQ (i + 1) (CR.d i (i + 1) rfl x) = E.dQ i (i + 1) rfl (E.coordQ i x)
    conv_lhs => rw [← E.decompose i x]
    rw [map_add, ← E.i_d, E.d_Q, map_add, E.coordQ_i, zero_add, map_add, E.coordQ_i,
      zero_add, E.coordQ_Q]

/-- **The quotient block is the cokernel** (tex 5398–5403): `Qⁿ ≃ Cⁿ_R / im iⁿ`, and under this
identification `d_Q` is the induced differential: `d_R q − d_Q q ∈ im i`. Kind: definition. -/
def quotientEquivCokernel (n : ℤ) : (CR.X n ⧸ LinearMap.range (E.i.f n n rfl)) ≃ₗ[S] E.Qc n :=
  Submodule.quotientEquivOfIsCompl _ _ (E.compl n)

/-- `d_R q − d_Q q ∈ im i`: `d_Q` induces the cokernel differential.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem d_sub_dQ_mem (a b : ℤ) (h : a + 1 = b) (q : E.Qc a) :
    CR.d a b h q - (E.dQ a b h q : CR.X b) ∈ LinearMap.range (E.i.f b b rfl) :=
  ⟨E.offDiag a b h q, by rw [E.d_Q, add_sub_cancel_right]⟩

/-- **Block equivalence** `Cⁿ_P × Qⁿ ≃ Cⁿ_R`, `(x, q) ↦ i x + q` (tex 5398–5403: "adapted
bases"). Kind: definition. -/
def blockEquiv (n : ℤ) : (CP.X n × E.Qc n) ≃ₗ[S] CR.X n :=
  (LinearEquiv.prodCongr (LinearEquiv.ofInjective _ (E.inj n)) (LinearEquiv.refl S _)) ≪≫ₗ
    Submodule.prodEquivOfIsCompl _ _ (E.compl n)

/-- `blockEquiv (x, q) = i x + q`.
Locator: tex 5398–5403. Kind: PROVED (definitional). -/
theorem blockEquiv_apply (n : ℤ) (x : CP.X n) (q : E.Qc n) :
    E.blockEquiv n (x, q) = E.i.f n n rfl x + q :=
  rfl

/-- **Upper triangular differential in block coordinates** (tex 5398–5403): transported along
`blockEquiv`, the differential of `C_R` is `(x, q) ↦ (d_P x + * q, d_Q q)`. Kind: PROVED. -/
theorem d_blockEquiv (a b : ℤ) (h : a + 1 = b) (x : CP.X a) (q : E.Qc a) :
    CR.d a b h (E.blockEquiv a (x, q)) =
      E.blockEquiv b (CP.d a b h x + E.offDiag a b h q, E.dQ a b h q) :=
  E.d_block a b h x q

/-- **The adapted basis** of `Cⁿ_R` (tex 5398–5403: "adapted bases"): the image under
`blockEquiv` of the product of a basis of `Cⁿ_P` and a basis of `Qⁿ`. Kind: definition. -/
def adaptedBasis (n : ℤ) {ιP ιQ : Type} (bP : Basis ιP S (CP.X n)) (bQ : Basis ιQ S (E.Qc n)) :
    Basis (ιP ⊕ ιQ) S (CR.X n) :=
  (bP.prod bQ).map (E.blockEquiv n)

/-- Coordinates in the adapted basis of a block vector.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem adaptedBasis_repr_blockEquiv (n : ℤ) {ιP ιQ : Type} (bP : Basis ιP S (CP.X n))
    (bQ : Basis ιQ S (E.Qc n)) (y : CP.X n × E.Qc n) :
    (E.adaptedBasis n bP bQ).repr (E.blockEquiv n y) = (bP.prod bQ).repr y := by
  simp [adaptedBasis, Basis.map_repr]

/-- The adapted basis vectors from `C_P`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem adaptedBasis_inl (n : ℤ) {ιP ιQ : Type} (bP : Basis ιP S (CP.X n))
    (bQ : Basis ιQ S (E.Qc n)) (k : ιP) :
    E.adaptedBasis n bP bQ (Sum.inl k) = E.blockEquiv n (bP k, 0) := by
  simp [adaptedBasis]

/-- The adapted basis vectors from `Q`.
Locator: tex 5398–5403. Kind: PROVED. -/
theorem adaptedBasis_inr (n : ℤ) {ιP ιQ : Type} (bP : Basis ιP S (CP.X n))
    (bQ : Basis ιQ S (E.Qc n)) (k : ιQ) :
    E.adaptedBasis n bP bQ (Sum.inr k) = E.blockEquiv n (0, bQ k) := by
  simp [adaptedBasis]

/-- **The matrix of the differential in adapted bases is upper triangular** (tex 5398–5403):
`[d_R] = [[d_P, *], [0, d_Q]]` as a block matrix `fromBlocks`. Kind: PROVED. -/
theorem toMatrix_d_adapted (a b : ℤ) (h : a + 1 = b) {ιPa ιQa ιPb ιQb : Type} [Fintype ιPa]
    [DecidableEq ιPa] [Fintype ιQa] [DecidableEq ιQa] [Fintype ιPb] [Fintype ιQb]
    (bPa : Basis ιPa S (CP.X a)) (bQa : Basis ιQa S (E.Qc a)) (bPb : Basis ιPb S (CP.X b))
    (bQb : Basis ιQb S (E.Qc b)) :
    LinearMap.toMatrix (E.adaptedBasis a bPa bQa) (E.adaptedBasis b bPb bQb) (CR.d a b h) =
      Matrix.fromBlocks (LinearMap.toMatrix bPa bPb (CP.d a b h))
        (LinearMap.toMatrix bQa bPb (E.offDiag a b h)) 0
        (LinearMap.toMatrix bQa bQb (E.dQ a b h)) := by
  ext (j | j) (k | k) <;>
    simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, adaptedBasis_inl, adaptedBasis_inr,
      d_blockEquiv, adaptedBasis_repr_blockEquiv, Basis.prod_repr_inl, Basis.prod_repr_inr,
      map_zero, add_zero, zero_add, Finsupp.zero_apply, Matrix.zero_apply]

end SplitInclusion

end Split

/-! ### Part 3: the full-condition pre-cancellation complex of a triangular extension -/

section FullPre

open ZInQ.Contrib.CloudB3RC53.ClearingComplex Matrix

variable {S : Type} [CommRing S]

/-- **The full-condition pre-cancellation complex of an upper triangular extension**
(tex 5398–5424): the old block complex `D` (`d⁰ = c⁰`, `d¹ = P`, `d² = U`) extended by new
summands `N` in degrees one and two with the triangular differential: `Y = 0`, `T = 0`
(tex 5420–5424: `T₀ = 0`), the new singular block `B : N → N`, and off-diagonal blocks
`Q : N → D²`, `V : N → C³`. The only remaining square-zero condition is `U Q + V B = 0`.
Kind: definition. -/
def fullPreOfTriangular (D : BlockComplex S) (N : Type) [Fintype N] [DecidableEq N]
    (Q : Matrix (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) N S) (V : Matrix (Fin D.m2) N S)
    (B : Matrix N N S) (h : D.d2 * Q + V * B = 0) : FullPreComplex S where
  m0 := D.m0
  m1 := D.m1
  m2 := D.m2
  N := N
  c0 := D.d0
  Y := 0
  P := D.d1
  Q := Q
  T := 0
  B := B
  U := D.d2
  V := V
  c1_c0 := by
    rw [fromBlocks_mul_fromRows, D.d1_d0, Matrix.mul_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, add_zero, fromRows_zero]
  c2_c1 := by
    rw [fromCols_mul_fromBlocks, D.d2_d1, Matrix.mul_zero, add_zero, h, fromCols_zero]

/-- **Cancelling the new singular block returns the old complex** (tex 5424–5425, 5440–5454):
for a triangular extension with `B` invertible, the Schur differential `P − Q B⁻¹ T` is `P`
(since `T = 0`), so `cancel` gives back `D`. Kind: PROVED. -/
theorem cancel_fullPreOfTriangular (D : BlockComplex S) (N : Type) [Fintype N] [DecidableEq N]
    (Q : Matrix (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) N S) (V : Matrix (Fin D.m2) N S)
    (B : Matrix N N S) (h : D.d2 * Q + V * B = 0)
    (hB : IsUnit (fullPreOfTriangular D N Q V B h).B.det) :
    (fullPreOfTriangular D N Q V B h).cancel hB = D := by
  cases D
  simp only [FullPreComplex.cancel, fullPreOfTriangular]
  congr 1
  exact sub_eq_self.2 (Matrix.mul_zero _)

/-- The matrix of `M.mulVecLin` in the standard bases is `M`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem toMatrix_basisFun_mulVecLin {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix κ ι S) :
    LinearMap.toMatrix (Pi.basisFun S ι) (Pi.basisFun S κ) M.mulVecLin = M := by
  ext i j
  simp [LinearMap.toMatrix_apply]

/-- Coordinates through bases: `b'(f(b⁻¹ x)) = [f] x`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem equivFun_map_equivFun_symm {M M' ι κ : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Basis ι S M)
    (b' : Basis κ S M') (f : M →ₗ[S] M') (x : ι → S) :
    b'.equivFun (f (b.equivFun.symm x)) = LinearMap.toMatrix b b' f *ᵥ x := by
  have h1 : ⇑(b.repr (b.equivFun.symm x)) = x := b.equivFun.apply_symm_apply x
  rw [Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b' f, h1]

/-- Coordinates into a standard basis: `f(b⁻¹ x) = [f] x`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem apply_equivFun_symm_eq_toMatrix_mulVec {M ι κ : Type*} [AddCommGroup M] [Module S M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Basis ι S M) (f : M →ₗ[S] (κ → S))
    (x : ι → S) : f (b.equivFun.symm x) = LinearMap.toMatrix b (Pi.basisFun S κ) f *ᵥ x := by
  have := equivFun_map_equivFun_symm b (Pi.basisFun S κ) f x
  rwa [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at this

section Split

variable (D : BlockComplex S) {CR : GCx S} (E : SplitInclusion D.toGCx CR) {N : Type}
  [Fintype N] [DecidableEq N] (bQ1 : Basis N S (E.Qc 1)) (bQ2 : Basis N S (E.Qc 2))

/-- The standard basis of `D¹ = B₁ ⊕ H₁ ⊕ E₁`.
Locator: tex 5398–5424. Kind: definition. -/
abbrev basisD1 : Basis (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) S (D.toGCx.X 1) :=
  Pi.basisFun S (Fin D.m0 ⊕ Unit ⊕ Fin D.m1)

/-- The standard basis of `D² = B₂ ⊕ H₂ ⊕ E₂`.
Locator: tex 5398–5424. Kind: definition. -/
abbrev basisD2 : Basis (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) S (D.toGCx.X 2) :=
  Pi.basisFun S (Fin D.m1 ⊕ Unit ⊕ Fin D.m2)

/-- The standard basis of `D³ = B₃`.
Locator: tex 5398–5424. Kind: definition. -/
abbrev basisD3 : Basis (Fin D.m2) S (D.toGCx.X 3) :=
  Pi.basisFun S (Fin D.m2)

/-- The matrix of `d¹` of the block complex is `D.d1`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem toMatrix_blockD1 :
    LinearMap.toMatrix (basisD1 D) (basisD2 D) (D.toGCx.d 1 2 rfl) = D.d1 :=
  toMatrix_basisFun_mulVecLin D.d1

/-- The matrix of `d²` of the block complex is `D.d2`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem toMatrix_blockD2 :
    LinearMap.toMatrix (basisD2 D) (basisD3 D) (D.toGCx.d 2 3 rfl) = D.d2 :=
  toMatrix_basisFun_mulVecLin D.d2

/-- The off-diagonal block `Q : N → D²` of a split extension, in the given basis of `Q¹`
(tex 5420–5424). Kind: definition. -/
def splitQ : Matrix (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) N S :=
  LinearMap.toMatrix bQ1 (basisD2 D) (E.offDiag 1 2 rfl)

/-- The new singular block `B : N → N`, the matrix of `d_Q : Q¹ → Q²` (tex 5420–5424:
`B₀ = A = diag(A_q)`). Kind: definition. -/
def splitB : Matrix N N S :=
  LinearMap.toMatrix bQ1 bQ2 (E.dQ 1 2 rfl)

/-- The off-diagonal block `V : N → D³` of a split extension, in the given basis of `Q²`.
Locator: tex 5398–5424. Kind: definition. -/
def splitV : Matrix (Fin D.m2) N S :=
  LinearMap.toMatrix bQ2 (basisD3 D) (E.offDiag 2 3 rfl)

/-- **The remaining square-zero identity holds for a split extension** (tex 5398–5424):
`U Q + V B = 0`, the matrix form of `d_P ∘ * + * ∘ d_Q = 0` from degree one to degree three.
Kind: PROVED. -/
theorem split_sq : D.d2 * splitQ D E bQ1 + splitV D E bQ2 * splitB D E bQ1 bQ2 = 0 := by
  have hlin : D.toGCx.d 2 3 rfl ∘ₗ E.offDiag 1 2 rfl + E.offDiag 2 3 rfl ∘ₗ E.dQ 1 2 rfl = 0 :=
    LinearMap.ext fun q => E.d_offDiag_add_offDiag_dQ 1 2 3 rfl rfl q
  have h := congrArg (LinearMap.toMatrix bQ1 (basisD3 D)) hlin
  rw [map_add, LinearMap.toMatrix_comp bQ1 (basisD2 D) (basisD3 D),
    LinearMap.toMatrix_comp bQ1 bQ2 (basisD3 D), map_zero, toMatrix_blockD2] at h
  exact h

/-- **The full-condition pre-cancellation complex of a split extension** (tex 5398–5424): for a
degreewise split inclusion `D → C_R` of the old block complex, with bases of the complements
`Q¹, Q²` indexed by `N`, the pre-cancellation complex with `c⁰ = d⁰`, `Y = 0`, `P = d¹`, `T = 0`,
`U = d²` and the blocks `Q, B, V` read off from the splitting. Kind: definition. -/
def fullPreOfSplit : FullPreComplex S :=
  fullPreOfTriangular D N (splitQ D E bQ1) (splitV D E bQ2) (splitB D E bQ1 bQ2)
    (split_sq D E bQ1 bQ2)

/-- **The differential out of degree one in adapted bases is `(P Q; T B)`** (tex 5398–5424):
the matrix of `d¹_R` in the adapted bases built from the standard bases of `D¹, D²` and the
bases of `Q¹, Q²` is `fromBlocks P Q T B` of `fullPreOfSplit`. Kind: PROVED. -/
theorem toMatrix_d_one_fullPreOfSplit :
    LinearMap.toMatrix (E.adaptedBasis 1 (basisD1 D) bQ1) (E.adaptedBasis 2 (basisD2 D) bQ2)
        (CR.d 1 2 rfl) =
      Matrix.fromBlocks (fullPreOfSplit D E bQ1 bQ2).P (fullPreOfSplit D E bQ1 bQ2).Q
        (fullPreOfSplit D E bQ1 bQ2).T (fullPreOfSplit D E bQ1 bQ2).B := by
  rw [E.toMatrix_d_adapted 1 2 rfl, toMatrix_blockD1]
  rfl

/-- The degree-one block coordinates `S^(D¹ ⊕ N) ≃ C¹_R`, `v ↦ i (v|D¹) + b₁ (v|N)`.
Locator: tex 5398–5424. Kind: definition. -/
def blockCoord1 : ((Fin D.m0 ⊕ Unit ⊕ Fin D.m1) ⊕ N → S) ≃ₗ[S] CR.X 1 :=
  LinearEquiv.sumArrowLequivProdArrow _ _ S S ≪≫ₗ
    LinearEquiv.prodCongr (LinearEquiv.refl S _) bQ1.equivFun.symm ≪≫ₗ E.blockEquiv 1

/-- The degree-two block coordinates `S^(D² ⊕ N) ≃ C²_R`, `v ↦ i (v|D²) + b₂ (v|N)`.
Locator: tex 5398–5424. Kind: definition. -/
def blockCoord2 : ((Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N → S) ≃ₗ[S] CR.X 2 :=
  LinearEquiv.sumArrowLequivProdArrow _ _ S S ≪≫ₗ
    LinearEquiv.prodCongr (LinearEquiv.refl S _) bQ2.equivFun.symm ≪≫ₗ E.blockEquiv 2

omit [DecidableEq N] in
/-- `blockCoord1 v = i (v|D¹) + b₁ (v|N)`.
Locator: tex 5398–5424. Kind: PROVED (definitional). -/
theorem blockCoord1_apply (v : (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) ⊕ N → S) :
    blockCoord1 D E bQ1 v =
      E.i.f 1 1 rfl (v ∘ (Sum.inl : (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) → _ ⊕ N)) +
        (bQ1.equivFun.symm (v ∘ Sum.inr) : CR.X 1) :=
  rfl

omit [DecidableEq N] in
/-- `blockCoord2 v = i (v|D²) + b₂ (v|N)`.
Locator: tex 5398–5424. Kind: PROVED (definitional). -/
theorem blockCoord2_apply (v : (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N → S) :
    blockCoord2 D E bQ2 v =
      E.i.f 2 2 rfl (v ∘ (Sum.inl : (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) → _ ⊕ N)) +
        (bQ2.equivFun.symm (v ∘ Sum.inr) : CR.X 2) :=
  rfl

/-- The components of the comparison `fullPreOfSplit → C_R`: `i` in degrees zero and three,
the block coordinates in degrees one and two.
Locator: tex 5398–5424. Kind: definition. -/
def splitCoordL : (n : ℤ) → ((fullPreOfSplit D E bQ1 bQ2).idx n → S) →ₗ[S] CR.X n
  | 0 => E.i.f 0 0 rfl
  | 1 => (blockCoord1 D E bQ1).toLinearMap
  | 2 => (blockCoord2 D E bQ2).toLinearMap
  | 3 => E.i.f 3 3 rfl
  | _ => 0

omit [DecidableEq N] in
/-- The comparison commutes with the differentials from degree zero.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem splitComm0 (y : Fin D.m0 → S) :
    blockCoord1 D E bQ1 (fromRows D.d0 (0 : Matrix N (Fin D.m0) S) *ᵥ y) =
      CR.d 0 1 rfl (E.i.f 0 0 rfl y) := by
  have h1 : (fromRows D.d0 (0 : Matrix N (Fin D.m0) S) *ᵥ y) ∘ Sum.inl = D.d0 *ᵥ y := by
    rw [fromRows_mulVec]
    rfl
  have h2 : (fromRows D.d0 (0 : Matrix N (Fin D.m0) S) *ᵥ y) ∘ Sum.inr = 0 := by
    rw [fromRows_mulVec, Sum.elim_comp_inr, Matrix.zero_mulVec]
  rw [blockCoord1_apply]
  refine (congrArg₂ (fun a c => E.i.f 1 1 rfl a + (bQ1.equivFun.symm c : CR.X 1)) h1 h2).trans ?_
  simp only [map_zero, ZeroMemClass.coe_zero, add_zero]
  exact E.i_d 0 1 rfl y

/-- The comparison commutes with the differentials from degree one.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem splitComm1 (v : (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) ⊕ N → S) :
    blockCoord2 D E bQ2 (fromBlocks D.d1 (splitQ D E bQ1) 0 (splitB D E bQ1 bQ2) *ᵥ v) =
      CR.d 1 2 rfl (blockCoord1 D E bQ1 v) := by
  have hoff : E.offDiag 1 2 rfl (bQ1.equivFun.symm (v ∘ Sum.inr)) =
      splitQ D E bQ1 *ᵥ (v ∘ Sum.inr) :=
    apply_equivFun_symm_eq_toMatrix_mulVec (κ := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) bQ1
      (E.offDiag 1 2 rfl) (v ∘ Sum.inr)
  have hdQ : E.dQ 1 2 rfl (bQ1.equivFun.symm (v ∘ Sum.inr)) =
      bQ2.equivFun.symm (splitB D E bQ1 bQ2 *ᵥ (v ∘ Sum.inr)) := by
    rw [splitB, ← equivFun_map_equivFun_symm, LinearEquiv.symm_apply_apply]
  have k1 : (fromBlocks D.d1 (splitQ D E bQ1) 0 (splitB D E bQ1 bQ2) *ᵥ v) ∘ Sum.inl =
      D.d1 *ᵥ (v ∘ Sum.inl) + splitQ D E bQ1 *ᵥ (v ∘ Sum.inr) := by
    rw [fromBlocks_mulVec]
    rfl
  have k2 : (fromBlocks D.d1 (splitQ D E bQ1) 0 (splitB D E bQ1 bQ2) *ᵥ v) ∘ Sum.inr =
      splitB D E bQ1 bQ2 *ᵥ (v ∘ Sum.inr) := by
    rw [fromBlocks_mulVec, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add]
  rw [blockCoord1_apply]
  refine Eq.trans ?_ (E.d_block 1 2 rfl (v ∘ Sum.inl) (bQ1.equivFun.symm (v ∘ Sum.inr))).symm
  rw [hoff, hdQ, blockCoord2_apply]
  exact congrArg₂ (fun a c => E.i.f 2 2 rfl a + (bQ2.equivFun.symm c : CR.X 2)) k1 k2

/-- The comparison commutes with the differentials from degree two, provided `Q³ = 0`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem splitComm2 (hQ3 : E.Qc 3 = ⊥) (v : (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N → S) :
    E.i.f 3 3 rfl (fromCols D.d2 (splitV D E bQ2) *ᵥ v) =
      CR.d 2 3 rfl (blockCoord2 D E bQ2 v) := by
  have hz : ∀ y, y ∈ E.Qc 3 → y = 0 := fun y hy => by
    rw [hQ3] at hy
    exact (Submodule.mem_bot S).1 hy
  have hoff : E.offDiag 2 3 rfl (bQ2.equivFun.symm (v ∘ Sum.inr)) =
      splitV D E bQ2 *ᵥ (v ∘ Sum.inr) :=
    apply_equivFun_symm_eq_toMatrix_mulVec (κ := Fin D.m2) bQ2 (E.offDiag 2 3 rfl)
      (v ∘ Sum.inr)
  rw [blockCoord2_apply]
  refine Eq.trans ?_ (E.d_block 2 3 rfl (v ∘ Sum.inl) (bQ2.equivFun.symm (v ∘ Sum.inr))).symm
  rw [hoff, hz _ (E.dQ 2 3 rfl (bQ2.equivFun.symm (v ∘ Sum.inr))).2, add_zero]
  exact congrArg (E.i.f 3 3 rfl) (fromCols_mulVec D.d2 (splitV D E bQ2) v)

omit [DecidableEq N] in
/-- The comparison commutes with the differentials from degree three.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem splitComm3 (y : Fin D.m2 → S) : (0 : CR.X 4) = CR.d 3 4 rfl (E.i.f 3 3 rfl y) := by
  refine Eq.trans ?_ (E.i_d 3 4 rfl y)
  exact (map_zero (E.i.f 4 4 rfl)).symm

/-- The comparison commutes with the differentials, provided `Q³ = 0`.
Locator: tex 5398–5424. Kind: PROVED. -/
theorem splitCoordL_comm (hQ3 : E.Qc 3 = ⊥) (i : ℤ) (x : (fullPreOfSplit D E bQ1 bQ2).idx i → S) :
    splitCoordL D E bQ1 bQ2 (i + 1) ((fullPreOfSplit D E bQ1 bQ2).ddL i x) =
      CR.d i (i + 1) rfl (splitCoordL D E bQ1 bQ2 i x) := by
  match i with
  | 0 => exact splitComm0 D E bQ1 x
  | 1 => exact splitComm1 D E bQ1 bQ2 x
  | 2 => exact splitComm2 D E bQ2 hQ3 x
  | 3 => exact splitComm3 D E x
  | Int.ofNat (n + 4) =>
    obtain rfl : x = 0 := Subsingleton.elim (α := Empty → S) _ _
    simp only [map_zero]
  | Int.negSucc n =>
    obtain rfl : x = 0 := Subsingleton.elim (α := Empty → S) _ _
    simp only [map_zero]

/-- **The comparison chain map** `fullPreOfSplit → C_R` (tex 5398–5424), for `Q³ = 0`.
Kind: definition. -/
def splitCoordHom (hQ3 : E.Qc 3 = ⊥) : GHom (fullPreOfSplit D E bQ1 bQ2).toGCx CR where
  f i j h := by subst h; exact splitCoordL D E bQ1 bQ2 i
  comm := by
    rintro i _ _ _ rfl rfl h rfl x
    exact splitCoordL_comm D E bQ1 bQ2 hQ3 i x

/-- **The comparison is a degreewise isomorphism** (tex 5398–5424: "the graded model of (5.6)
is `C_old ⊕ ⊕_q Q_q` with an upper triangular differential"): if the complements `Qⁿ` vanish
outside degrees one and two, `splitCoordL` is bijective in every degree, so `C_R` is
isomorphic to the pre-cancellation complex `fullPreOfSplit`. Kind: PROVED. -/
theorem splitCoordL_bijective (hQ : ∀ n, n ≠ 1 → n ≠ 2 → E.Qc n = ⊥) (n : ℤ) :
    Function.Bijective (splitCoordL D E bQ1 bQ2 n) := by
  match n with
  | 0 => exact E.i_bijective 0 (hQ 0 (by omega) (by omega))
  | 1 => exact (blockCoord1 D E bQ1).bijective
  | 2 => exact (blockCoord2 D E bQ2).bijective
  | 3 => exact E.i_bijective 3 (hQ 3 (by omega) (by omega))
  | Int.ofNat (n + 4) =>
    have hb := E.i_bijective _ (hQ (Int.ofNat (n + 4))
      (by intro h; injection h with h; omega) (by intro h; injection h with h; omega))
    refine ⟨fun x y _ => Subsingleton.elim (α := Empty → S) x y, fun y => ⟨0, ?_⟩⟩
    obtain ⟨x, rfl⟩ := hb.2 y
    obtain rfl : x = 0 := Subsingleton.elim (α := Empty → S) _ _
    rw [map_zero, map_zero]
  | Int.negSucc n =>
    have hb := E.i_bijective _ (hQ (Int.negSucc n) (by intro h; cases h) (by intro h; cases h))
    refine ⟨fun x y _ => Subsingleton.elim (α := Empty → S) x y, fun y => ⟨0, ?_⟩⟩
    obtain ⟨x, rfl⟩ := hb.2 y
    obtain rfl : x = 0 := Subsingleton.elim (α := Empty → S) _ _
    rw [map_zero, map_zero]

end Split

/-- **Finite free models of the inclusion with quotient over a field** (tex 5394–5454: "the
graded model of (5.6) is `C_old ⊕ ⊕_q Q_q` with an upper triangular differential"). Let `D` be
the old block complex over a field and `i : D → C_R` a degreewise injective chain map that is
surjective outside degrees one and two, whose cokernel in degrees one and two has dimension
`|N|`. Then there are a splitting and bases of the cokernel blocks such that the comparison
`fullPreOfSplit → C_R` is a degreewise isomorphism of complexes; the pre-cancellation complex
has `c⁰ = d⁰`, `Y = 0`, `P = d¹`, `T = 0`, `U = d²` (definitionally, `fullPreOfTriangular`),
and `d¹_R = (P Q; T B)` in the adapted bases (`toMatrix_d_one_fullPreOfSplit`).
Kind: PROVED. -/
theorem exists_fullPreModel {F : Type} [Field F] (D : BlockComplex F) {CR : GCx F}
    (i : GHom D.toGCx CR) (hi : ∀ n, Function.Injective (i.f n n rfl))
    (hsurj : ∀ n, n ≠ 1 → n ≠ 2 → Function.Surjective (i.f n n rfl))
    (N : Type) [Fintype N] [DecidableEq N]
    (hfin1 : Module.Finite F (CR.X 1 ⧸ LinearMap.range (i.f 1 1 rfl)))
    (hrk1 : Module.finrank F (CR.X 1 ⧸ LinearMap.range (i.f 1 1 rfl)) = Fintype.card N)
    (hfin2 : Module.Finite F (CR.X 2 ⧸ LinearMap.range (i.f 2 2 rfl)))
    (hrk2 : Module.finrank F (CR.X 2 ⧸ LinearMap.range (i.f 2 2 rfl)) = Fintype.card N) :
    ∃ (E : SplitInclusion D.toGCx CR) (bQ1 : Basis N F (E.Qc 1)) (bQ2 : Basis N F (E.Qc 2))
      (hQ3 : E.Qc 3 = ⊥), E.i = i ∧
        ∀ n, Function.Bijective ((splitCoordHom D E bQ1 bQ2 hQ3).f n n rfl) := by
  obtain ⟨E, rfl⟩ := exists_splitInclusion i hi
  have hQ : ∀ n, n ≠ 1 → n ≠ 2 → E.Qc n = ⊥ := fun n h1 h2 => by
    have hc := E.compl n
    rw [LinearMap.range_eq_top.2 (hsurj n h1 h2)] at hc
    simpa using hc.inf_eq_bot
  have e1 := Submodule.quotientEquivOfIsCompl _ _ (E.compl 1)
  have e2 := Submodule.quotientEquivOfIsCompl _ _ (E.compl 2)
  have : Module.Finite F (E.Qc 1) := Module.Finite.equiv e1
  have : Module.Finite F (E.Qc 2) := Module.Finite.equiv e2
  have hr1 : Module.finrank F (E.Qc 1) = Fintype.card N := e1.finrank_eq.symm.trans hrk1
  have hr2 : Module.finrank F (E.Qc 2) = Fintype.card N := e2.finrank_eq.symm.trans hrk2
  refine ⟨E, (Module.finBasisOfFinrankEq F (E.Qc 1) hr1).reindex (Fintype.equivFin N).symm,
    (Module.finBasisOfFinrankEq F (E.Qc 2) hr2).reindex (Fintype.equivFin N).symm,
    hQ 3 (by omega) (by omega), rfl, fun n => ?_⟩
  exact splitCoordL_bijective D E _ _ hQ n

end FullPre

end ZInQ.Manuscript.RC.Limits
