import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimTransfer
import ZInQKernel.Contrib.OneProof.RC.Limits.Lemmas

/-!
# Lane RC22 (glue sweep, limits): the contraction of the evaluation cone in degree zero

Manuscript tex 4686–4695, proof of Lemma `ex:limits-outer-evaluation`: "Its cone has no residual
cohomology in degrees at most zero. Cancel unit disks there so that the free cone starts in degree
one. [...] the same is true after every coefficient extension. The long exact sequence gives the
claimed injection."

Lane RC6 (`RC/Limits/Evaluation.lean`, `mem_range_of_cone_contraction`,
`mem_range_baseChange_of_cone_contraction`; `RC/Limits/Lemmas.lean`,
`ex_limits_outer_evaluation_base_change`) proves the injection from a contraction of the cone in
degree zero, given by its components `hrow₁`, `hrow₂`, and records the cancellation of unit disks
that produces this contraction as GLUE (tex 4692–4693). The cancellation is now available in the
tree: RC6's `MinimalModelsExist` is PROVED (`ResidualTransfer.minimalModelsExist_proof`), and a
minimal model of a complex whose residual cohomology vanishes in degree zero is zero in degree
zero. `degree_zero_contraction_lim` derives the contraction in degree zero for every bounded
finite free complex over a local ring with vanishing residual cohomology in degree zero.

RC6's consumers are stated on bare linear maps (the complexes `C₀ → C₁ → C₂` and `D₀ → D₁`, the
cone `C₀ → C₁ × D₀ → C₂ × D₁` written in components, and `hrow₁`, `hrow₂` the `C₁`-row of the
contraction). `evalCone` presents that cone, with RC6's signs, as a Mathlib cochain complex;
`exists_evalCone_rows_lim` extracts RC6's rows from the contraction, and
`ex_limits_outer_evaluation_base_change_lim` is RC6's `ex_limits_outer_evaluation_base_change`
with the rows replaced by the vanishing of the residual cohomology of the cone in degree zero.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open CategoryTheory CategoryTheory.Limits ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.ResidualTransfer

universe u

/-- **Cancelling unit disks: a contraction in degree zero** (tex 4691–4693). Let `K` be a bounded
complex of finite free modules over a local ring `S` whose cohomology after reduction to the
residue field vanishes in degree zero (`dim_k H⁰(k ⊗_S K) = 0`; the text has vanishing in all
degrees `≤ 0`). Then there are `h₀ : K⁰ → K⁻¹` and `h₁ : K¹ → K⁰` with `d⁻¹ h₀ + h₁ d⁰ = id` on
`K⁰` (written in diagrammatic order `h₀ ≫ d⁻¹ + d⁰ ≫ h₁ = 𝟙`). This is the contraction "the free
cone starts in degree one" provides, the input of RC6's `mem_range_of_cone_contraction`. PROVED,
from no remaining input beyond the data: the minimal model `L ≃ K` of `minimalModelsExist_proof`
has `rank L⁰ = dim_k H⁰(k ⊗ K) = 0`, so `L⁰ = 0`, and the homotopy `e.inv ∘ e.hom ≃ 𝟙` in degree
zero gives the identity.

Consumer: RC6's GLUE (tex 4692–4693) behind the hypotheses `hrow₁`, `hrow₂` of
`mem_range_of_cone_contraction`, `mem_range_baseChange_of_cone_contraction`,
`ex_limits_outer_evaluation_base_change` (rows extracted in `exists_evalCone_rows_lim`);
discharger: `ResidualTransfer.minimalModelsExist_proof`. -/
theorem degree_zero_contraction_lim {S : Type u} [CommRing S] [IsLocalRing S]
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, Module.Free S (K.X i)] [∀ i, Module.Finite S (K.X i)]
    (hres : Module.finrank (IsLocalRing.ResidueField S) (residualCohomology S K 0) = 0) :
    ∃ (h₀ : K.X 0 ⟶ K.X (-1)) (h₁ : K.X 1 ⟶ K.X 0),
      h₀ ≫ K.d (-1) 0 + K.d 0 1 ≫ h₁ = 𝟙 (K.X 0) := by
  have hbdd : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (K.X i) := by
    refine ⟨a, b, fun i hi => ?_⟩
    rcases hi with hi | hi
    · exact ModuleCat.subsingleton_of_isZero (K.isZero_of_isStrictlyGE a i hi)
    · exact ModuleCat.subsingleton_of_isZero (K.isZero_of_isStrictlyLE b i hi)
  obtain ⟨L, ⟨e⟩, hfree, -, -, hdim⟩ :=
    minimalModelsExist_proof S K (fun i => ⟨inferInstance, inferInstance⟩) hbdd
  have hL0 : IsZero (L.X 0) := by
    have : Module.Free S (L.X 0) := (hfree 0).1
    have : Module.Finite S (L.X 0) := (hfree 0).2
    have h0 : Module.finrank S (L.X 0) = 0 := (hdim 0).trans hres
    have := subsingleton_of_finrank_eq_zero h0
    exact ModuleCat.isZero_of_subsingleton _
  have hc := e.homotopyHomInvId.comm 0
  rw [dNext_eq e.homotopyHomInvId.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq e.homotopyHomInvId.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
    HomologicalComplex.comp_f, hL0.eq_zero_of_src (e.inv.f 0), Limits.comp_zero,
    HomologicalComplex.id_f] at hc
  refine ⟨-e.homotopyHomInvId.hom 0 (-1), -e.homotopyHomInvId.hom 1 0, ?_⟩
  rw [Preadditive.neg_comp, Preadditive.comp_neg]
  calc -(e.homotopyHomInvId.hom 0 (-1) ≫ K.d (-1) 0) + -(K.d 0 1 ≫ e.homotopyHomInvId.hom 1 0)
      = 0 - (K.d 0 1 ≫ e.homotopyHomInvId.hom 1 0) -
          e.homotopyHomInvId.hom 0 (-1) ≫ K.d (-1) 0 := by abel
    _ = 𝟙 (K.X 0) := by rw [hc]; abel

section EvalCone

variable {R : Type u} [CommRing R]
variable {C₀ C₁ C₂ D₀ D₁ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
  [AddCommGroup C₂] [Module R C₂] [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁]

/-- The terms of the cone of the comparison `(φ₀, φ₁)` from `C₀ → C₁ → C₂` to `D₀ → D₁`
(tex 4690–4693; RC6's `cone_H0_eq_zero`): `Cone⁻¹ = C₀`, `Cone⁰ = C₁ × D₀`, `Cone¹ = C₂ × D₁`, zero
elsewhere. -/
def evalConeX (C₀ C₁ C₂ D₀ D₁ : Type u) [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁]
    [Module R C₁] [AddCommGroup C₂] [Module R C₂] [AddCommGroup D₀] [Module R D₀]
    [AddCommGroup D₁] [Module R D₁] : ℤ → ModuleCat.{u} R
  | Int.negSucc 0 => ModuleCat.of R C₀
  | Int.ofNat 0 => ModuleCat.of R (C₁ × D₀)
  | Int.ofNat 1 => ModuleCat.of R (C₂ × D₁)
  | _ => ModuleCat.of R PUnit

example : evalConeX (R := R) C₀ C₁ C₂ D₀ D₁ (-1) = ModuleCat.of R C₀ := rfl
example : evalConeX (R := R) C₀ C₁ C₂ D₀ D₁ 0 = ModuleCat.of R (C₁ × D₀) := rfl
example : evalConeX (R := R) C₀ C₁ C₂ D₀ D₁ 1 = ModuleCat.of R (C₂ × D₁) := rfl

/-- RC6's cone differential `∂⁻¹ x = (-d₀ x, φ₀ x)` (`cone_Hneg1_eq_zero`). -/
def evalConeDm1 (d₀ : C₀ →ₗ[R] C₁) (φ₀ : C₀ →ₗ[R] D₀) : C₀ →ₗ[R] C₁ × D₀ :=
  (-d₀).prod φ₀

/-- RC6's cone differential `∂⁰ (c, y) = (-d₁ c, φ₁ c + δ₀ y)` (`cone_H0_eq_zero`). -/
def evalConeD0 (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₁ : C₁ →ₗ[R] D₁) :
    C₁ × D₀ →ₗ[R] C₂ × D₁ :=
  ((-d₁).comp (LinearMap.fst R C₁ D₀)).prod
    (φ₁.comp (LinearMap.fst R C₁ D₀) + δ₀.comp (LinearMap.snd R C₁ D₀))

/-- The cone differentials, degree by degree (zero outside degrees `-1`, `0`). -/
def evalConeD (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₀ : C₀ →ₗ[R] D₀)
    (φ₁ : C₁ →ₗ[R] D₁) : ∀ n : ℤ,
    evalConeX (R := R) C₀ C₁ C₂ D₀ D₁ n ⟶ evalConeX (R := R) C₀ C₁ C₂ D₀ D₁ (n + 1)
  | Int.negSucc 0 => ModuleCat.ofHom (evalConeDm1 d₀ φ₀)
  | Int.ofNat 0 => ModuleCat.ofHom (evalConeD0 d₁ δ₀ φ₁)
  | _ => 0

/-- `∂ ∘ ∂ = 0` for RC6's evaluation cone (tex 4690–4692), from `d₁ d₀ = 0` and `φ₁ d₀ = δ₀ φ₀`.
PROVED. -/
theorem evalConeD_sq (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁)
    (φ₀ : C₀ →ₗ[R] D₀) (φ₁ : C₁ →ₗ[R] D₁) (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀) :
    ∀ n : ℤ, evalConeD d₀ d₁ δ₀ φ₀ φ₁ n ≫ evalConeD d₀ d₁ δ₀ φ₀ φ₁ (n + 1) = 0
  | Int.negSucc 0 => by
      have k1 : ∀ x : C₀, -d₁ (-d₀ x) = 0 := fun x => by
        rw [map_neg, neg_neg]; exact LinearMap.congr_fun hd x
      have k2 : ∀ x : C₀, φ₁ (-d₀ x) + δ₀ (φ₀ x) = 0 := fun x => by
        rw [map_neg, ← LinearMap.comp_apply φ₁ d₀, hφ, LinearMap.comp_apply, neg_add_cancel]
      ext x
      exact Prod.ext (k1 x) (k2 x)
  | Int.ofNat 0 => by
      show ModuleCat.ofHom (evalConeD0 d₁ δ₀ φ₁) ≫ 0 = 0
      exact Limits.comp_zero
  | Int.ofNat (k + 1) => by
      show 0 ≫ _ = 0
      exact Limits.zero_comp
  | Int.negSucc (k + 1) => by
      show 0 ≫ _ = 0
      exact Limits.zero_comp

/-- RC6's evaluation cone `C₀ → C₁ × D₀ → C₂ × D₁` as a Mathlib cochain complex. -/
noncomputable def evalCone (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁)
    (φ₀ : C₀ →ₗ[R] D₀) (φ₁ : C₁ →ₗ[R] D₁) (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (evalConeX (R := R) C₀ C₁ C₂ D₀ D₁) (evalConeD d₀ d₁ δ₀ φ₀ φ₁)
    (evalConeD_sq d₀ d₁ δ₀ φ₀ φ₁ hd hφ)

variable (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₀ : C₀ →ₗ[R] D₀)
  (φ₁ : C₁ →ₗ[R] D₁) (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)

/-- The evaluation cone (tex 4690–4692) vanishes below degree `-1`. PROVED. -/
theorem evalCone_isStrictlyGE : (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).IsStrictlyGE (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rcases i with n | (_ | k)
  · exfalso; simp at hi; omega
  · exact absurd hi (by decide)
  · have : Subsingleton ((evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).X (Int.negSucc (k + 1))) :=
      inferInstanceAs (Subsingleton PUnit.{u+1})
    exact ModuleCat.isZero_of_subsingleton _

/-- The evaluation cone (tex 4690–4692) vanishes above degree `1`. PROVED. -/
theorem evalCone_isStrictlyLE : (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).IsStrictlyLE 1 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rcases i with (_ | _ | k) | n
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · have : Subsingleton ((evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).X (Int.ofNat (k + 2))) :=
      inferInstanceAs (Subsingleton PUnit.{u+1})
    exact ModuleCat.isZero_of_subsingleton _
  · have := Int.negSucc_lt_zero n
    omega

/-- The evaluation cone (tex 4690–4692) of free modules is free. PROVED. -/
theorem evalCone_free [Module.Free R C₀] [Module.Free R C₁] [Module.Free R C₂] [Module.Free R D₀]
    [Module.Free R D₁] (i : ℤ) : Module.Free R ((evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).X i) := by
  rcases i with (_ | _ | k) | (_ | k)
  · change Module.Free R (C₁ × D₀); infer_instance
  · change Module.Free R (C₂ × D₁); infer_instance
  · change Module.Free R PUnit.{u+1}; infer_instance
  · change Module.Free R C₀; infer_instance
  · change Module.Free R PUnit.{u+1}; infer_instance

/-- The evaluation cone (tex 4690–4692) of finite modules is finite. PROVED. -/
theorem evalCone_finite [Module.Finite R C₀] [Module.Finite R C₁] [Module.Finite R C₂]
    [Module.Finite R D₀] [Module.Finite R D₁] (i : ℤ) :
    Module.Finite R ((evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).X i) := by
  rcases i with (_ | _ | k) | (_ | k)
  · change Module.Finite R (C₁ × D₀); infer_instance
  · change Module.Finite R (C₂ × D₁); infer_instance
  · change Module.Finite R PUnit.{u+1}; infer_instance
  · change Module.Finite R C₀; infer_instance
  · change Module.Finite R PUnit.{u+1}; infer_instance

/-- The differential `Cone⁻¹ → Cone⁰` of the evaluation cone is RC6's `∂⁻¹` (tex 4690–4692,
`cone_Hneg1_eq_zero`). PROVED. -/
theorem evalCone_d_neg_one :
    (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).d (-1) 0 = ModuleCat.ofHom (evalConeDm1 d₀ φ₀) :=
  CochainComplex.of_d (evalConeX (R := R) C₀ C₁ C₂ D₀ D₁) (evalConeD d₀ d₁ δ₀ φ₀ φ₁) (-1)

/-- The differential `Cone⁰ → Cone¹` of the evaluation cone is RC6's `∂⁰` (tex 4690–4692,
`cone_H0_eq_zero`). PROVED. -/
theorem evalCone_d_zero :
    (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ).d 0 1 = ModuleCat.ofHom (evalConeD0 d₁ δ₀ φ₁) :=
  CochainComplex.of_d (evalConeX (R := R) C₀ C₁ C₂ D₀ D₁) (evalConeD d₀ d₁ δ₀ φ₀ φ₁) 0

end EvalCone

/-- **RC6's contraction rows from the cancellation of unit disks** (tex 4691–4693). Over a local
ring `R`, let `(φ₀, φ₁)` be a map from the finite free complex `C₀ → C₁ → C₂` to the finite free
complex `D₀ → D₁` whose cone `evalCone` has no residual cohomology in degree zero
(`dim_k H⁰(k ⊗_R Cone) = 0`). Then there are `h₁ : C₁ → C₀`, `h₂ : D₀ → C₀` and the `C₁`-row
`(a, b) : C₂ × D₁ → C₁` of a contraction of the cone in degree zero, with exactly RC6's identities
`-d₀ h₁ - a d₁ + b φ₁ = id` and `-d₀ h₂ + b δ₀ = 0`. PROVED, from no remaining input beyond the data
(through `degree_zero_contraction_lim` applied to `evalCone`).

Consumer: RC6's GLUE (tex 4692–4693) producing the hypotheses `hrow₁`, `hrow₂` of
`mem_range_of_cone_contraction`, `mem_range_baseChange_of_cone_contraction`,
`ex_limits_outer_evaluation_base_change`; discharger: `ResidualTransfer.minimalModelsExist_proof`
(through `degree_zero_contraction_lim`). -/
theorem exists_evalCone_rows_lim {R : Type u} [CommRing R] [IsLocalRing R]
    {C₀ C₁ C₂ D₀ D₁ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
    [AddCommGroup C₂] [Module R C₂] [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁]
    [Module R D₁] [Module.Free R C₀] [Module.Free R C₁] [Module.Free R C₂] [Module.Free R D₀]
    [Module.Free R D₁] [Module.Finite R C₀] [Module.Finite R C₁] [Module.Finite R C₂]
    [Module.Finite R D₀] [Module.Finite R D₁]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₀ : C₀ →ₗ[R] D₀)
    (φ₁ : C₁ →ₗ[R] D₁) (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)
    (hres : Module.finrank (IsLocalRing.ResidueField R)
      (residualCohomology R (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ) 0) = 0) :
    ∃ (h₁ : C₁ →ₗ[R] C₀) (h₂ : D₀ →ₗ[R] C₀) (a : C₂ →ₗ[R] C₁) (b : D₁ →ₗ[R] C₁),
      -(d₀ ∘ₗ h₁) - a ∘ₗ d₁ + b ∘ₗ φ₁ = LinearMap.id ∧ -(d₀ ∘ₗ h₂) + b ∘ₗ δ₀ = 0 := by
  have := evalCone_isStrictlyGE d₀ d₁ δ₀ φ₀ φ₁ hd hφ
  have := evalCone_isStrictlyLE d₀ d₁ δ₀ φ₀ φ₁ hd hφ
  have := evalCone_free d₀ d₁ δ₀ φ₀ φ₁ hd hφ
  have := evalCone_finite d₀ d₁ δ₀ φ₀ φ₁ hd hφ
  obtain ⟨g₀, g₁, hid⟩ := degree_zero_contraction_lim (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ) (-1) 1 hres
  rw [evalCone_d_neg_one, evalCone_d_zero] at hid
  let H0 : C₁ × D₀ →ₗ[R] C₀ := g₀.hom
  let H1 : C₂ × D₁ →ₗ[R] C₁ × D₀ := g₁.hom
  have key : ∀ v : C₁ × D₀, evalConeDm1 d₀ φ₀ (H0 v) + H1 (evalConeD0 d₁ δ₀ φ₁ v) = v := by
    intro v
    have := congrArg (fun f => ModuleCat.Hom.hom f v) hid
    exact this
  have hfst : ∀ (c : C₁) (y : D₀), -d₀ (H0 (c, y)) + (H1 (-d₁ c, φ₁ c + δ₀ y)).1 = c :=
    fun c y => congrArg Prod.fst (key (c, y))
  have hsplit : ∀ (x : C₂) (y : D₁), H1 (x, y) = H1 (x, 0) + H1 (0, y) := fun x y => by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hneg : ∀ x : C₂, H1 (-x, 0) = -H1 (x, 0) := fun x => by
    rw [← map_neg H1 (x, 0), Prod.neg_mk, neg_zero]
  refine ⟨H0 ∘ₗ LinearMap.inl R C₁ D₀, H0 ∘ₗ LinearMap.inr R C₁ D₀,
    LinearMap.fst R C₁ D₀ ∘ₗ H1 ∘ₗ LinearMap.inl R C₂ D₁,
    LinearMap.fst R C₁ D₀ ∘ₗ H1 ∘ₗ LinearMap.inr R C₂ D₁, ?_, ?_⟩
  · refine LinearMap.ext fun c => ?_
    have h := hfst c 0
    rw [map_zero, add_zero, hsplit, Prod.fst_add, hneg, Prod.fst_neg] at h
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.fst_apply,
      LinearMap.id_apply]
    refine Eq.trans ?_ h
    abel
  · refine LinearMap.ext fun y => ?_
    have h := hfst 0 y
    rw [map_zero, neg_zero, map_zero, zero_add] at h
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.zero_apply]
    exact h


/-- **Injectivity persists after every coefficient extension, without the contraction hypothesis**
(tex 4656–4657, 4691–4695). RC6's `ex_limits_outer_evaluation_base_change` with its hypotheses
`h₁`, `h₂`, `a`, `b`, `hrow₁`, `hrow₂` (the contraction produced by the GLUE cancellation of unit
disks) replaced by: `R` local, the five modules finite free, and the cone without residual
cohomology in degree zero ("Its cone has no residual cohomology in degrees at most zero", tex
4691–4692). PROVED, from these inputs: after any base change `S`, a cycle of the source whose image
is a boundary in the target is a boundary.

Consumer: RC6's `ex_limits_outer_evaluation_base_change` (= `mem_range_baseChange_of_cone_contraction`);
discharger: `exists_evalCone_rows_lim`. -/
theorem ex_limits_outer_evaluation_base_change_lim {R : Type u} [CommRing R] [IsLocalRing R]
    {C₀ C₁ C₂ D₀ D₁ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
    [AddCommGroup C₂] [Module R C₂] [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁]
    [Module R D₁] [Module.Free R C₀] [Module.Free R C₁] [Module.Free R C₂] [Module.Free R D₀]
    [Module.Free R D₁] [Module.Finite R C₀] [Module.Finite R C₁] [Module.Finite R C₂]
    [Module.Finite R D₀] [Module.Finite R D₁]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₀ : C₀ →ₗ[R] D₀)
    (φ₁ : C₁ →ₗ[R] D₁) (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)
    (hres : Module.finrank (IsLocalRing.ResidueField R)
      (residualCohomology R (evalCone d₀ d₁ δ₀ φ₀ φ₁ hd hφ) 0) = 0)
    (S : Type*) [CommRing S] [Algebra R S] {z : TensorProduct R S C₁}
    (hz : d₁.baseChange S z = 0)
    (hφz : φ₁.baseChange S z ∈ LinearMap.range (δ₀.baseChange S)) :
    z ∈ LinearMap.range (d₀.baseChange S) := by
  obtain ⟨h₁, h₂, a, b, hrow₁, hrow₂⟩ := exists_evalCone_rows_lim d₀ d₁ δ₀ φ₀ φ₁ hd hφ hres
  exact ex_limits_outer_evaluation_base_change S d₀ d₁ δ₀ φ₁ h₁ h₂ a b hrow₁ hrow₂ hz hφz

end ZInQ.Manuscript.RC.GlueSweep.Lim
