import ZInQKernel.Contrib.OneProof.RC.Local.TwoPlaceCaveat

/-!
# Lane RC31, round 7: surjectivity of the tame comparison map

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306.

For a topological group `G` whose points are separated by clopen sets (`TotallySeparatedSpace`,
which holds for profinite groups such as absolute Galois groups) and elements `φ σ : G` with
`φ ≠ σ`, `φ ≠ 1`, `σ ≠ φ⁻¹` (as for a Frobenius lift `φ` outside inertia and `σ` in inertia), the
comparison `tameCochainMap` from the continuous cochains to the tame free model is surjective
in every degree (`tameCochainMap_surjective`):

* degree `0`: constant cochains (`evalZero_surjective`);
* degree `1`: `c = a·1_U + b·1_{Uᶜ}` with `U` clopen, `φ ∈ U`, `σ ∉ U` (`tameOne_surjective`);
* degree `2`: `w = (φ⁻¹ • m)·1_V` with `V = U₁ × (U₂ ∩ U₃)` clopen, containing `(σ, φ⁻¹)` and
  avoiding `(1, 1)`, `(φ, φ⁻¹)`, `(φ, σφ⁻¹)` and `(σ^i, σ)`; then `tameE w = Φ (φ⁻¹ • m) = m`
  (`tameE_surjective`);
* other degrees: the target is trivial.

Hence the surjectivity hypothesis of `exists_retract_tameModel_field` is automatic
(`exists_retract_tameModel_field'`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.Limits

/-- A function taking two constant values on a clopen set and its complement is continuous
(tex 3470–3480). Kind: PROVED. -/
theorem continuous_ite_of_isClopen {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {p : α → Prop} {dp : DecidablePred p} (hp : IsClopen {x | p x}) (a b : β) :
    Continuous fun x => @ite β (p x) (dp x) a b := by
  let _ := dp
  refine Continuous.if (fun x hx => ?_) continuous_const continuous_const
  rw [hp.frontier_eq] at hx
  exact absurd hx (Set.notMem_empty x)

section Surjective

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

variable (R) in
/-- The continuous one-cochain `x ↦ c x` of a continuous function `c : G → M`
(tex 3298–3306). Kind: definition. -/
def cochainOneOf (c : G → M) (hc : Continuous c) : (contCochains R G M).X 1 :=
  ⟨(fun v : Fin 1 → G => c (v 0) : (groupCohomology.inhomogeneousCochains (rep R G M)).X 1),
    mem_contCochain.mpr (hc.comp (continuous_apply 0))⟩

/-- The values of `cochainOneOf` (tex 3298–3306). Kind: PROVED. -/
theorem evalOne_cochainOneOf (c : G → M) (hc : Continuous c) (x : G) :
    evalOne R M x (cochainOneOf R c hc) = c x := rfl

variable (R) in
/-- The continuous two-cochain `(x, y) ↦ w x y` of a jointly continuous `w`
(tex 3470–3480). Kind: definition. -/
def cochainTwoOf (w : G → G → M) (hw : Continuous fun v : Fin 2 → G => w (v 0) (v 1)) :
    (contCochains R G M).X 2 :=
  ⟨(fun v : Fin 2 → G => w (v 0) (v 1) :
    (groupCohomology.inhomogeneousCochains (rep R G M)).X 2), mem_contCochain.mpr hw⟩

/-- The values of `cochainTwoOf` (tex 3470–3480). Kind: PROVED. -/
theorem evalTwo_cochainTwoOf (w : G → G → M)
    (hw : Continuous fun v : Fin 2 → G => w (v 0) (v 1)) (x y : G) :
    evalTwo R M x y (cochainTwoOf R w hw) = w x y := rfl

/-- **Degree one**: the tame coordinates `c ↦ (c(φ), c(σ))` are surjective on continuous
one-cochains when `φ ≠ σ` and points of `G` are separated by clopen sets (tex 3298–3306).
Kind: PROVED. -/
theorem tameOne_surjective [TotallySeparatedSpace G] {φ σ : G} (hφσ : φ ≠ σ) :
    Function.Surjective (tameOne (R := R) (M := M) φ σ) := by
  classical
  rintro ⟨a, b⟩
  obtain ⟨U, hU, hφU, hσU⟩ := exists_isClopen_of_totally_separated hφσ
  have hσU' : σ ∉ U := hσU
  refine ⟨cochainOneOf R (fun x => if x ∈ U then a else b)
    (continuous_ite_of_isClopen (p := (· ∈ U)) hU a b), ?_⟩
  change ((if φ ∈ U then a else b), (if σ ∈ U then a else b)) = (a, b)
  simp [hφU, hσU']

/-- **Degree two**: `tameE` is surjective when `φ ≠ σ`, `φ ≠ 1`, `σ ≠ φ⁻¹`, `Φ = (φ • ·)` and
points of `G` are separated by clopen sets: `w = (φ⁻¹ • m)·1_V` vanishes at `(1, 1)`,
`(φ, φ⁻¹)`, `(φ, σφ⁻¹)`, `(σ^i, σ)` and takes the value `φ⁻¹ • m` at `(σ, φ⁻¹)`
(tex 3470–3480). Kind: PROVED. -/
theorem tameE_surjective [TotallySeparatedSpace G] (Φ g : M →ₗ[R] M) {φ σ : G} (q : ℕ)
    (hΦ : ∀ m, Φ m = φ • m) (hφσ : φ ≠ σ) (hφ1 : φ ≠ 1) (hσφ : σ ≠ φ⁻¹) :
    Function.Surjective (tameE Φ g φ σ q) := by
  classical
  intro m
  obtain ⟨U₁, hU₁, hσU₁, hφU₁⟩ := exists_isClopen_of_totally_separated hφσ.symm
  obtain ⟨U₂, hU₂, hφU₂, h1U₂⟩ := exists_isClopen_of_totally_separated (inv_ne_one.mpr hφ1)
  obtain ⟨U₃, hU₃, hφU₃, hσU₃⟩ := exists_isClopen_of_totally_separated hσφ.symm
  have hφU₁' : φ ∉ U₁ := hφU₁
  have h1U₂' : (1 : G) ∉ U₂ := h1U₂
  have hσU₃' : σ ∉ U₃ := hσU₃
  let w : G → G → M := fun x y => if x ∈ U₁ ∧ y ∈ U₂ ∩ U₃ then φ⁻¹ • m else 0
  have hV : IsClopen {v : Fin 2 → G | v 0 ∈ U₁ ∧ v 1 ∈ U₂ ∩ U₃} :=
    (hU₁.preimage (continuous_apply 0)).inter ((hU₂.inter hU₃).preimage (continuous_apply 1))
  have hw : Continuous fun v : Fin 2 → G => w (v 0) (v 1) :=
    continuous_ite_of_isClopen (p := fun v : Fin 2 → G => v 0 ∈ U₁ ∧ v 1 ∈ U₂ ∩ U₃) hV _ _
  refine ⟨cochainTwoOf R w hw, ?_⟩
  rw [tameE_apply]
  simp only [evalTwo_cochainTwoOf]
  have e1 : w 1 1 = 0 := by simp [w, h1U₂']
  have e2 : w φ φ⁻¹ = 0 := by simp [w, hφU₁']
  have e3 : w σ φ⁻¹ = φ⁻¹ • m := by simp [w, hσU₁, hφU₂, hφU₃]
  have e4 : w φ (σ * φ⁻¹) = 0 := by simp [w, hφU₁']
  have e5 : ∀ i, w (σ ^ i) σ = 0 := fun i => by simp [w, hσU₃']
  simp only [e1, e2, e3, e4, e5, map_zero, neg_zero, sub_zero, zero_add, add_zero,
    Finset.sum_const_zero, hΦ, smul_inv_smul]

/-- **Surjectivity of the tame comparison map in every degree** (tex 3470–3480): for `φ ≠ σ`,
`φ ≠ 1`, `σ ≠ φ⁻¹` and points of `G` separated by clopen sets, every component of
`tameCochainMap` is surjective (degrees `0, 1, 2` above; other degrees have trivial target).
Kind: PROVED. -/
theorem tameCochainMap_surjective [TotallySeparatedSpace G] (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ)
    (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m)
    (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hφσ : φ ≠ σ) (hφ1 : φ ≠ 1) (hσφ : σ ≠ φ⁻¹) (n : ℤ) :
    Function.Surjective ((tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel).f n n rfl) := by
  rcases n with ((_ | _ | _ | n) | n)
  · exact evalZero_surjective (R := R) (G := G) (M := M)
  · exact tameOne_surjective hφσ
  · exact tameE_surjective Φ g q hΦ hφσ hφ1 hσφ
  · exact fun _ => ⟨0, rfl⟩
  · exact fun _ => ⟨0, rfl⟩

end Surjective

section Normalize

open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- **A retract of the genuine local complex onto the tame model, over a field, without a
surjectivity hypothesis** (tex 3470–3480, 4423–4437): for `φ ≠ σ`, `φ ≠ 1`, `σ ≠ φ⁻¹` and points
of `G` separated by clopen sets, if the comparison `tameCochainMap` (at `g = 1`) is a
quasi-isomorphism, the genuine local complex retracts onto the tame free model with projection
the comparison itself. Kind: PROVED. -/
theorem exists_retract_tameModel_field' [TotallySeparatedSpace G] (Φ : M →ₗ[k] M) (φ σ : G)
    (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hφσ : φ ≠ σ) (hφ1 : φ ≠ 1) (hσφ : σ ≠ φ⁻¹)
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ id_invol
      (comm_id Φ) hrel))) :
    ∃ R : GRetract (natCx (contCochains k G M)) (tameFreeModel1 Φ q hq),
      ∀ n x, R.p.f n n rfl x =
        (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ id_invol (comm_id Φ) hrel).f n n rfl x :=
  exists_retract_tameModel_field Φ φ σ q hq hΦ hgσ hrel hQ
    (tameCochainMap_surjective Φ LinearMap.id φ σ q hq hΦ hgσ id_invol (comm_id Φ) hrel
      hφσ hφ1 hσφ)

end Normalize

end ZInQ.Manuscript.RC.Local
