import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchAdjunction
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual

/-!
# Genuine instantiations, part 14: the cohomology of the dual complex

Over a field `k`, the dual complex `Hom_k(A, k)[−m]` (`SelmerDuality.dualCx`) has
`Hⁿ(Hom_k(A, k)[−m]) ≅ H^{m−n}(A)^∨`; in particular
**`finrank_homology_dualCx`**: `dim Hⁿ(Hom(A, k)[−m]) = dim H^{m−n}(A)` when the latter is
finite-dimensional. No finiteness of the terms of `A` is needed (continuous cochains are
infinite-dimensional): the proof is

* `finrank_dual_homology` (linear algebra): for `U --f--> V --g--> W` with `g ∘ f = 0`, the homology
  of the dual sequence `W^∨ → V^∨ → U^∨` at `V^∨` is `(ker f^∨)/(range g^∨) ≅ (ker g / range f)^∨`
  (restriction to `ker g`; surjective by extension of linear forms, kernel `(ker g)^⊥ = range g^∨`);
* `homologyEquivQuot`: `Hⁱ(A) ≅ ker dⁱ / range d^{i−1}` (the class map `clsAt` is surjective with
  kernel the boundaries);
* the differentials of `dualCx` are `±` the dual maps.

Used for `dim H²(C_str) = dim H¹(C_rel)` through the Selmer duality quasi-isomorphism
`C_str ≃ Hom(C_rel, k)[−3]` (`ConeDuality.lean`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open Module CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k]

section LinearAlgebra

variable {U V W : Type} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The boundaries `range f` inside the cycles `ker g`. -/
abbrev bdrySub (f : U →ₗ[k] V) (g : V →ₗ[k] W) : Submodule k (LinearMap.ker g) :=
  (LinearMap.range f).comap (LinearMap.ker g).subtype

variable {Y Y₁ Y₃ : Type} [AddCommGroup Y] [Module k Y] [AddCommGroup Y₁] [Module k Y₁]
  [AddCommGroup Y₃] [Module k Y₃]

/-- The restriction map `ker b → (ker g / range f)^∨` for a dual sequence `Y₃ --a--> Y --b--> Y₁`
of `U --f--> V --g--> W` (`Y ≃ V^∨` by `e`, `b φ = 0 ↔ e φ ∘ f = 0`). -/
def dualRestrict (f : U →ₗ[k] V) (g : V →ₗ[k] W) (b : Y →ₗ[k] Y₁) (e : Y ≃ₗ[k] Dual k V)
    (hb : ∀ φ, b φ = 0 ↔ ∀ u, e φ (f u) = 0) :
    LinearMap.ker b →ₗ[k] Dual k (LinearMap.ker g ⧸ bdrySub f g) where
  toFun φ := (bdrySub f g).liftQ ((e φ.1).comp (LinearMap.ker g).subtype) (by
    rintro x ⟨u, hu⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    change e φ.1 (x : V) = 0
    rw [show (x : V) = f u from hu.symm]
    exact (hb φ.1).mp (LinearMap.mem_ker.mp φ.2) u)
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by ext x; simp

theorem dualRestrict_apply (f : U →ₗ[k] V) (g : V →ₗ[k] W) (b : Y →ₗ[k] Y₁)
    (e : Y ≃ₗ[k] Dual k V) (hb : ∀ φ, b φ = 0 ↔ ∀ u, e φ (f u) = 0) (φ : LinearMap.ker b)
    (x : LinearMap.ker g) :
    dualRestrict f g b e hb φ (Submodule.Quotient.mk x) = e φ.1 x :=
  rfl

theorem dualRestrict_surjective (f : U →ₗ[k] V) (g : V →ₗ[k] W) (hgf : ∀ u, g (f u) = 0)
    (b : Y →ₗ[k] Y₁) (e : Y ≃ₗ[k] Dual k V) (hb : ∀ φ, b φ = 0 ↔ ∀ u, e φ (f u) = 0) :
    Function.Surjective (dualRestrict f g b e hb) := by
  intro ψ
  obtain ⟨e', he⟩ := LinearMap.exists_extend (ψ.comp (bdrySub f g).mkQ)
  have hfu : ∀ u, e' (f u) = 0 := fun u => by
    have h1 := LinearMap.congr_fun he ⟨f u, LinearMap.mem_ker.mpr (hgf u)⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero (bdrySub f g)
        (x := ⟨f u, LinearMap.mem_ker.mpr (hgf u)⟩)).mpr ⟨u, rfl⟩, map_zero]
  refine ⟨⟨e.symm e', LinearMap.mem_ker.mpr ((hb _).mpr fun u => by
    rw [LinearEquiv.apply_symm_apply]; exact hfu u)⟩, ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, dualRestrict_apply, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun he x

theorem ker_dualRestrict (f : U →ₗ[k] V) (g : V →ₗ[k] W) (b : Y →ₗ[k] Y₁) (a : Y₃ →ₗ[k] Y)
    (e : Y ≃ₗ[k] Dual k V) (hb : ∀ φ, b φ = 0 ↔ ∀ u, e φ (f u) = 0)
    (ha : ∀ φ, φ ∈ LinearMap.range a ↔ ∀ x ∈ LinearMap.ker g, e φ x = 0) :
    LinearMap.ker (dualRestrict f g b e hb) = bdrySub a b := by
  ext φ
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ha]
  constructor
  · intro h x hx
    have := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨x, hx⟩)
    rwa [dualRestrict_apply] at this
  · intro h
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, dualRestrict_apply]
    exact h x.1 x.2

/-- **The homology of a dual sequence is the dual of the homology** (dimension form): for
`U --f--> V --g--> W` with `g ∘ f = 0` and a sequence `Y₃ --a--> Y --b--> Y₁` with `Y ≃ V^∨`,
`ker b = (range f)^⊥` and `range a = (ker g)^⊥`, `dim (ker b / range a) = dim (ker g / range f)`
when the latter is finite. PROVED. -/
theorem finrank_dual_homology (f : U →ₗ[k] V) (g : V →ₗ[k] W) (hgf : ∀ u, g (f u) = 0)
    (b : Y →ₗ[k] Y₁) (a : Y₃ →ₗ[k] Y) (e : Y ≃ₗ[k] Dual k V)
    (hb : ∀ φ, b φ = 0 ↔ ∀ u, e φ (f u) = 0)
    (ha : ∀ φ, φ ∈ LinearMap.range a ↔ ∀ x ∈ LinearMap.ker g, e φ x = 0)
    [FiniteDimensional k (LinearMap.ker g ⧸ bdrySub f g)] :
    finrank k (LinearMap.ker b ⧸ bdrySub a b) = finrank k (LinearMap.ker g ⧸ bdrySub f g) := by
  have eq := ((Submodule.quotEquivOfEq _ _ (ker_dualRestrict f g b a e hb ha)).symm.trans
    ((dualRestrict f g b e hb).quotKerEquivOfSurjective (dualRestrict_surjective f g hgf b e hb)))
  rw [eq.finrank_eq, Subspace.dual_finrank_eq]

end LinearAlgebra

/-! ### Homology of a relation-indexed complex as cycles modulo boundaries -/

/-- `Hⁱ(A) ≅ ker dⁱ / range d^{i−1}`. -/
def homologyEquivQuot (A : GCx k) (i' i j : ℤ) (hi : i' + 1 = i) (h : i + 1 = j) :
    (LinearMap.ker (A.d i j h) ⧸ bdrySub (A.d i' i hi) (A.d i j h)) ≃ₗ[k] A.toCC.homology i := by
  refine (Submodule.quotEquivOfEq _ _ ?_).trans
    ((clsAt A i j h).quotKerEquivOfSurjective (clsAt_surjective A i j h))
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    have hx : x = ⟨A.d i' i hi y, LinearMap.mem_ker.2 (A.d_d i' i j hi h y)⟩ :=
      Subtype.ext hy.symm
    rw [hx]
    exact clsAt_boundary A i' i j hi h y
  · intro hx
    exact clsAt_eq_zero A i' i j hi h x hx

/-! ### The dual complex -/

theorem ker_smul_eq {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {c : ℤ} (hc : c * c = 1) (L : M →ₗ[k] N) : LinearMap.ker (c • L) = LinearMap.ker L := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.smul_apply]
  constructor
  · intro h
    have := congrArg (c • ·) h
    simpa [smul_smul, hc] using this
  · intro h; rw [h, smul_zero]

theorem range_smul_eq {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {c : ℤ} (hc : c * c = 1) (L : M →ₗ[k] N) : LinearMap.range (c • L) = LinearMap.range L := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.smul_apply]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨c • x, by rw [map_zsmul]⟩
  · rintro ⟨x, rfl⟩; exact ⟨c • x, by rw [map_zsmul, smul_smul, hc, one_smul]⟩

theorem neg_sgn_mul_self (i : ℤ) : (-(sgn i)) * (-(sgn i)) = 1 := by
  rw [neg_mul_neg, sgn_mul_self]

theorem zsmul_eq_zero_iff_of_mul_self {M : Type} [AddCommGroup M] {c : ℤ} (hc : c * c = 1)
    (x : M) : c • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (c • ·) h
    simpa [smul_smul, hc] using this
  · intro h; rw [h, smul_zero]

/-- **`dim Hⁿ(Hom(A, k)[−m]) = dim H^{m−n}(A)`** over a field, when the latter is
finite-dimensional. PROVED. -/
theorem finrank_homology_dualCx (A : GCx k) (m n : ℤ)
    [FiniteDimensional k (A.toCC.homology (m - n))] :
    finrank k ((dualCx A m).toCC.homology n) = finrank k (A.toCC.homology (m - n)) := by
  have hA := homologyEquivQuot A (m - (n + 1)) (m - n) (m - (n - 1)) (by omega) (by omega)
  have : FiniteDimensional k (LinearMap.ker (A.d (m - n) (m - (n - 1)) _) ⧸
      bdrySub (A.d (m - (n + 1)) (m - n) _) (A.d (m - n) (m - (n - 1)) _)) :=
    LinearEquiv.finiteDimensional hA.symm
  rw [← (homologyEquivQuot (dualCx A m) (n - 1) n (n + 1) (by omega) rfl).finrank_eq,
    ← hA.finrank_eq]
  refine finrank_dual_homology (A.d (m - (n + 1)) (m - n) _)
    (A.d (m - n) (m - (n - 1)) _) (fun u => A.d_d _ _ _ _ _ u)
    ((dualCx A m).d n (n + 1) rfl) ((dualCx A m).d (n - 1) n (by omega))
    (LinearEquiv.refl k (Module.Dual k (A.X (m - n)))) (fun φ => ?_) (fun φ => ?_)
  · constructor
    · intro h u
      have h1 := congrArg (fun ψ => asDual ψ u) h
      simp only [dualCx_d_apply] at h1
      exact (zsmul_eq_zero_iff_of_mul_self (neg_sgn_mul_self n) _).mp h1
    · intro h
      refine dualCx_ext fun u => ?_
      rw [dualCx_d_apply]
      change (-(sgn n)) • asDual φ (A.d (m - (n + 1)) (m - n) _ u) = 0
      rw [show asDual φ (A.d (m - (n + 1)) (m - n) _ u) = 0 from h u, smul_zero]
  · change φ ∈ LinearMap.range ((-(sgn (n - 1))) •
        (A.d (m - n) (m - (n - 1)) (by omega)).dualMap) ↔ _
    rw [range_smul_eq (neg_sgn_mul_self _), LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact Submodule.mem_dualAnnihilator _

end ZInQ.Contrib.CloudB3RC53.GenuineInst
