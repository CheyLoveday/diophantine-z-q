import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHPK
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35Pad
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel

/-!
**Theorem 5.3: two-term models of the switching fibres over a field**

Lemma `ex:limits-inner-limit` (tex 4391–4451: "a bounded finite free model with actual inclusion,
projection and contraction homotopy"), in the shape used by the height-one switching argument
(Proposition `ex:limits-uniform-lower-bound`, tex 4976–4996: the two-term model
`[R^{n+1} --D--> R^{n+1}]` of a configuration, with fibre `[k^{n+1} --D̄--> k^{n+1}]`).

The field `model c : HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))` of
`HomologySwitchDataPK` (`GenuineSwitchHPK.lean`) asks for a homotopy equivalence of the
configuration's fibre complex with the fibre of the stage's two-term model. Over the field `k` this
file proves the linear algebra:

* `tmodCx D`: the square two-term complex `[k^m --D--> k^m]` (degrees one and two, `0` in degree
  zero); `twoTermFiberComplex ρ S = tmodCx (S.D.map ρ)` by definition (`twoTermFiberComplex_eq`).
* `tmodHomotopyEquiv₂`: a homotopy equivalence of two-term complexes from maps in degrees one and
  two (different in the two degrees), retractions and one homotopy.
* **The normal form** `tmodNormal D : tmodCx 0_s ≃ tmodCx D`, `s = dim ker D` (choose complements
  `ker D ⊕ K'` and `im D ⊕ C`; `D : K' ≅ im D`; the homotopy is `−(D|_{K'})⁻¹` on `im D`). Hence two
  square two-term complexes are homotopy equivalent as soon as their kernels have the same
  dimension (`tmodEquiv_of_finrank`), and the fibres of two stages with the same fibre dimension are
  homotopy equivalent (`twoTermFiberComplex_equiv`).
* `tmodMatEquiv`: lane RC31's matrix complex `matCx r 0` with zero differentials and ranks
  concentrated in degrees one and two, of equal rank `s`, is homotopy equivalent to `tmodCx 0_s`.

What a two-term model needs (`tmod_square_of_equiv`): a complex homotopy equivalent to a square
two-term complex has cohomology concentrated in degrees one and two with `dim H¹ = dim H²`
(finite). Conversely (with lane RC29's field splitting of a complex into its cohomology,
`FieldSplitting.lean`) every complex of `k`-vector spaces with finite-dimensional cohomology
concentrated in degrees one and two and `dim H¹ = dim H²` is homotopy equivalent to `tmodCx 0_s`
and to the fibre of every stage of fibre dimension `s` (`GenuineSwitchHModelAssembly.lean`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory CategoryTheory.Limits Module Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

/-! ### Two-term complexes and homotopy equivalences with two maps -/

section TwoMaps

variable {S : Type} [CommRing S] {N₁ N₂ : Type} [AddCommGroup N₁] [Module S N₁]
  [AddCommGroup N₂] [Module S N₂]

/-- The components of a map of two-term complexes `[N₁ → N₁] → [N₂ → N₂]` given by `φ₁` in
degree one and `φ₂` in degree two (degree zero and the others `0`). Kind: definition. -/
def tmodF₂ (φ₁ φ₂ : N₁ →ₗ[S] N₂) :
    ∀ i : ℤ, threeTermX S PUnit N₁ N₁ i ⟶ threeTermX S PUnit N₂ N₂ i
  | .ofNat 1 => ModuleCat.ofHom φ₁
  | .ofNat 2 => ModuleCat.ofHom φ₂
  | _ => 0

/-- **A map of two-term complexes** `[N₁ --d₁--> N₁] → [N₂ --d₂--> N₂]` with components `φ₁`
(degree one) and `φ₂` (degree two), for `φ₂ d₁ = d₂ φ₁`. Kind: definition (PROVED). -/
def tmodHom₂ (d₁ : N₁ →ₗ[S] N₁) (d₂ : N₂ →ₗ[S] N₂) (φ₁ φ₂ : N₁ →ₗ[S] N₂)
    (hφ : φ₂ ∘ₗ d₁ = d₂ ∘ₗ φ₁) :
    threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _) ⟶
      threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _) where
  f := tmodF₂ φ₁ φ₂
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    by_cases h0 : i = 0
    · subst h0
      have e1 : (threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _)).d 0 (0 + 1) =
          0 := (threeTermComplex_d_zero_one _ _ _).trans ModuleCat.ofHom_zero
      have e0 : tmodF₂ φ₁ φ₂ 0 = 0 := rfl
      rw [e0, e1]
      exact zero_comp.trans zero_comp.symm
    by_cases h1 : i = 1
    · subst h1
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change d₂ (φ₁ x) = φ₂ (d₁ x)
      exact (LinearMap.congr_fun hφ x).symm
    · have e₁ : (threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _)).d i (i + 1) =
          0 := threeTermD_eq_zero _ _ _ _ (fun h => h0 h.1) (fun h => h1 h.1)
      have e₂ : (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)).d i (i + 1) =
          0 := threeTermD_eq_zero _ _ _ _ (fun h => h0 h.1) (fun h => h1 h.1)
      rw [e₁, e₂]
      exact comp_zero.trans zero_comp.symm

/-- **A homotopy equivalence of two-term complexes with two maps** `[N₁ --d₁--> N₁] ≃
[N₂ --d₂--> N₂]`: maps of complexes `(φ₁, φ₂)`, `(ψ₁, ψ₂)` with `ψᵢ φᵢ = 1` and one homotopy
`s : N₂ → N₂` (degree two to one) with `φ₁ ψ₁ = s d₂ + 1` and `φ₂ ψ₂ = d₂ s + 1`. Kind: definition
(PROVED). -/
def tmodHomotopyEquiv₂ (d₁ : N₁ →ₗ[S] N₁) (d₂ : N₂ →ₗ[S] N₂) (φ₁ φ₂ : N₁ →ₗ[S] N₂)
    (ψ₁ ψ₂ : N₂ →ₗ[S] N₁) (s : N₂ →ₗ[S] N₂) (hφ : φ₂ ∘ₗ d₁ = d₂ ∘ₗ φ₁)
    (hψ : ψ₂ ∘ₗ d₂ = d₁ ∘ₗ ψ₁) (h₁ : ψ₁ ∘ₗ φ₁ = LinearMap.id) (h₂ : ψ₂ ∘ₗ φ₂ = LinearMap.id)
    (hs1 : φ₁ ∘ₗ ψ₁ = s ∘ₗ d₂ + LinearMap.id) (hs2 : φ₂ ∘ₗ ψ₂ = d₂ ∘ₗ s + LinearMap.id) :
    HomotopyEquiv (threeTermComplex (0 : PUnit →ₗ[S] N₁) d₁ (LinearMap.comp_zero _))
      (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)) where
  hom := tmodHom₂ d₁ d₂ φ₁ φ₂ hφ
  inv := tmodHom₂ d₂ d₁ ψ₁ ψ₂ hψ
  homotopyHomInvId := Homotopy.ofEq (by
    ext i : 1
    rcases i with (_ | _ | _ | n) | n
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change ψ₁ (φ₁ x) = x
      exact LinearMap.congr_fun h₁ x
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change ψ₂ (φ₂ x) = x
      exact LinearMap.congr_fun h₂ x
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _)
  homotopyInvHomId :=
    { hom := fun i j =>
          (show (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)).X i ⟶
            (threeTermComplex (0 : PUnit →ₗ[S] N₂) d₂ (LinearMap.comp_zero _)).X j from
            threeTermH (0 : N₂ →ₗ[S] PUnit) s i j)
      zero := fun i j hij => by
        simp only [ComplexShape.up_Rel] at hij
        apply threeTermH_eq_zero
        · rintro ⟨rfl, rfl⟩; exact hij rfl
        · rintro ⟨rfl, rfl⟩; exact hij rfl
      comm := fun i => by
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from by simp)]
        rcases i with (_ | _ | _ | n) | n
        · ext x
          exact Subsingleton.elim (α := PUnit) _ _
        · refine ModuleCat.hom_ext (LinearMap.ext fun (x : N₂) => ?_)
          change φ₁ (ψ₁ x) = s (d₂ x) + (0 : PUnit →ₗ[S] N₂) ((0 : N₂ →ₗ[S] PUnit) x) + x
          have := LinearMap.congr_fun hs1 x
          simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at this
          simp [this]
        · refine ModuleCat.hom_ext (LinearMap.ext fun (x : N₂) => ?_)
          change φ₂ (ψ₂ x) = (0 : N₂) + d₂ (s x) + x
          have := LinearMap.congr_fun hs2 x
          simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at this
          simp [this]
        · ext x
          exact Subsingleton.elim (α := PUnit) _ _
        · ext x
          exact Subsingleton.elim (α := PUnit) _ _ }

end TwoMaps

/-! ### The square two-term complex and its normal form over a field -/

section NormalForm

variable {k : Type} [Field k]

/-- **The square two-term complex** `[k^m --D--> k^m]` in degrees one and two (`0` in degree zero,
the shape of `twoTermFiberComplex`). Kind: definition. -/
abbrev tmodCx {m : ℕ} (D : Matrix (Fin m) (Fin m) k) : CochainComplex (ModuleCat.{0} k) ℤ :=
  threeTermComplex (0 : PUnit.{1} →ₗ[k] (Fin m → k)) D.mulVecLin (LinearMap.comp_zero _)

/-- The fibre of a stage's two-term model is the square two-term complex of the reduced matrix.
Kind: PROVED (definitional). -/
theorem twoTermFiberComplex_eq {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (S : TwoTermStage ι) : twoTermFiberComplex ρ S = tmodCx (S.D.map ρ) :=
  rfl

variable {m : ℕ} (D : Matrix (Fin m) (Fin m) k)

/-- The kernel `ker D`. Kind: definition. -/
abbrev tmodK : Submodule k (Fin m → k) := LinearMap.ker D.mulVecLin

/-- The image `im D`. Kind: definition. -/
abbrev tmodR : Submodule k (Fin m → k) := LinearMap.range D.mulVecLin

/-- A complement `K'` of `ker D`. Kind: definition. -/
def tmodK' : Submodule k (Fin m → k) := (Submodule.exists_isCompl (tmodK D)).choose

theorem tmodK'_isCompl : IsCompl (tmodK D) (tmodK' D) :=
  (Submodule.exists_isCompl (tmodK D)).choose_spec

/-- A complement `C` of `im D`. Kind: definition. -/
def tmodC : Submodule k (Fin m → k) := (Submodule.exists_isCompl (tmodR D)).choose

theorem tmodC_isCompl : IsCompl (tmodR D) (tmodC D) :=
  (Submodule.exists_isCompl (tmodR D)).choose_spec

/-- The fibre dimension `s = dim ker D`. Kind: definition. -/
abbrev tmodS : ℕ := finrank k (tmodK D)

/-- PROVED. `dim C = dim ker D` (rank–nullity). -/
theorem tmod_finrank_C : finrank k (tmodC D) = tmodS D := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (tmodC_isCompl D)
  have h2 := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have h3 : finrank k (tmodR D) = finrank k (LinearMap.range D.mulVecLin) := rfl
  have h4 : tmodS D = finrank k (LinearMap.ker D.mulVecLin) := rfl
  omega

/-- `ker D ≃ k^s`. Kind: definition. -/
def tmodEK : tmodK D ≃ₗ[k] (Fin (tmodS D) → k) :=
  LinearEquiv.ofFinrankEq _ _ (by simp)

/-- `C ≃ k^s`. Kind: definition. -/
def tmodEC : tmodC D ≃ₗ[k] (Fin (tmodS D) → k) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [tmod_finrank_C]; simp)

/-- `D` restricted to `K'`, into `im D`. Kind: definition. -/
def tmodDK : tmodK' D →ₗ[k] tmodR D :=
  LinearMap.codRestrict (tmodR D) (D.mulVecLin ∘ₗ (tmodK' D).subtype)
    (fun _ => LinearMap.mem_range_self _ _)

/-- PROVED. `D` kills the `ker D`-component: `D x = D (π_{K'} x)`. -/
theorem tmod_D_proj (x : Fin m → k) :
    D.mulVecLin x = D.mulVecLin ((tmodK' D).projection (tmodK D) (tmodK'_isCompl D).symm x) := by
  have h := Submodule.projection_add_projection_eq_self (tmodK'_isCompl D) x
  have hK : D.mulVecLin ((tmodK D).projection (tmodK' D) (tmodK'_isCompl D) x) = 0 :=
    (Submodule.projectionOnto (tmodK D) (tmodK' D) (tmodK'_isCompl D) x).2
  conv_lhs => rw [← h]
  rw [map_add, hK, zero_add]

/-- PROVED. `D : K' → im D` is bijective. -/
theorem tmodDK_bijective : Function.Bijective (tmodDK D) := by
  constructor
  · intro x y hxy
    have h1 : D.mulVecLin ((x : Fin m → k) - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (congrArg Subtype.val hxy)
    have hK : ((x : Fin m → k) - y) ∈ tmodK D := h1
    have hK' : ((x : Fin m → k) - y) ∈ tmodK' D := Submodule.sub_mem _ x.2 y.2
    have h0 : ((x : Fin m → k) - y) = 0 := by
      have := (tmodK'_isCompl D).inf_eq_bot
      rw [Submodule.eq_bot_iff] at this
      exact this _ ⟨hK, hK'⟩
    exact Subtype.ext (sub_eq_zero.1 h0)
  · rintro ⟨y, z, rfl⟩
    refine ⟨⟨(tmodK' D).projection (tmodK D) (tmodK'_isCompl D).symm z,
      (Submodule.projectionOnto (tmodK' D) (tmodK D) (tmodK'_isCompl D).symm z).2⟩, ?_⟩
    · apply Subtype.ext
      change D.mulVecLin _ = D.mulVecLin z
      exact (tmod_D_proj D z).symm

/-- `D : K' ≃ im D`. Kind: definition. -/
def tmodDKe : tmodK' D ≃ₗ[k] tmodR D := LinearEquiv.ofBijective (tmodDK D) (tmodDK_bijective D)

/-- PROVED. `(D|_{K'})⁻¹ (D x) = π_{K'} x`. -/
theorem tmodDKe_symm_D (x : Fin m → k) :
    ((tmodDKe D).symm ⟨D.mulVecLin x, LinearMap.mem_range_self _ _⟩ : Fin m → k) =
      (tmodK' D).projection (tmodK D) (tmodK'_isCompl D).symm x := by
  have hmem : (tmodK' D).projection (tmodK D) (tmodK'_isCompl D).symm x ∈ tmodK' D :=
    (Submodule.projectionOnto (tmodK' D) (tmodK D) (tmodK'_isCompl D).symm x).2
  have : (tmodDKe D) ⟨_, hmem⟩ = ⟨D.mulVecLin x, LinearMap.mem_range_self _ _⟩ := by
    apply Subtype.ext
    change D.mulVecLin _ = D.mulVecLin x
    exact (tmod_D_proj D x).symm
  rw [← this, LinearEquiv.symm_apply_apply]

/-- PROVED. `D ((D|_{K'})⁻¹ y) = y` for `y ∈ im D`. -/
theorem tmod_D_DKe_symm (y : tmodR D) :
    D.mulVecLin ((tmodDKe D).symm y : Fin m → k) = y := by
  have := congrArg Subtype.val ((tmodDKe D).apply_symm_apply y)
  exact this

/-- `φ₁ : k^s ≅ ker D ⊆ k^m`. Kind: definition. -/
def tmodφ₁ : (Fin (tmodS D) → k) →ₗ[k] (Fin m → k) :=
  (tmodK D).subtype ∘ₗ (tmodEK D).symm.toLinearMap

/-- `φ₂ : k^s ≅ C ⊆ k^m`. Kind: definition. -/
def tmodφ₂ : (Fin (tmodS D) → k) →ₗ[k] (Fin m → k) :=
  (tmodC D).subtype ∘ₗ (tmodEC D).symm.toLinearMap

/-- `ψ₁ : k^m → k^s`, the projection onto `ker D` along `K'`. Kind: definition. -/
def tmodψ₁ : (Fin m → k) →ₗ[k] (Fin (tmodS D) → k) :=
  (tmodEK D).toLinearMap ∘ₗ Submodule.projectionOnto (tmodK D) (tmodK' D) (tmodK'_isCompl D)

/-- `ψ₂ : k^m → k^s`, the projection onto `C` along `im D`. Kind: definition. -/
def tmodψ₂ : (Fin m → k) →ₗ[k] (Fin (tmodS D) → k) :=
  (tmodEC D).toLinearMap ∘ₗ
    Submodule.projectionOnto (tmodC D) (tmodR D) (tmodC_isCompl D).symm

/-- The homotopy `s = −(D|_{K'})⁻¹ ∘ π_{im D}` (degree two to one). Kind: definition. -/
def tmodσ : (Fin m → k) →ₗ[k] (Fin m → k) :=
  -((tmodK' D).subtype ∘ₗ (tmodDKe D).symm.toLinearMap ∘ₗ
    Submodule.projectionOnto (tmodR D) (tmodC D) (tmodC_isCompl D))

/-- **The normal form of a square two-term complex over a field** (tex 4416–4418: "split the
residual complex into cohomology and disks"): `[k^s --0--> k^s] ≃ [k^m --D--> k^m]` with
`s = dim ker D`. Kind: definition (PROVED). -/
def tmodNormal : HomotopyEquiv (tmodCx (0 : Matrix (Fin (tmodS D)) (Fin (tmodS D)) k)) (tmodCx D) :=
  tmodHomotopyEquiv₂ (0 : Matrix (Fin (tmodS D)) (Fin (tmodS D)) k).mulVecLin D.mulVecLin
    (tmodφ₁ D) (tmodφ₂ D) (tmodψ₁ D) (tmodψ₂ D) (tmodσ D)
    (LinearMap.ext fun y => by
      have hy : D.mulVecLin (tmodφ₁ D y) = 0 := ((tmodEK D).symm y).2
      change tmodφ₂ D ((0 : Matrix (Fin (tmodS D)) (Fin (tmodS D)) k) *ᵥ y) = D.mulVecLin _
      rw [hy, Matrix.zero_mulVec, map_zero])
    (LinearMap.ext fun x => by
      change tmodψ₂ D (D.mulVecLin x) = (0 : Matrix (Fin (tmodS D)) (Fin (tmodS D)) k) *ᵥ _
      rw [Matrix.zero_mulVec]
      change (tmodEC D) (Submodule.projectionOnto (tmodC D) (tmodR D) (tmodC_isCompl D).symm
        (D.mulVecLin x)) = 0
      rw [Submodule.projectionOnto_apply_of_mem_right _ (LinearMap.mem_range_self _ _), map_zero])
    (LinearMap.ext fun y => by
      change (tmodEK D) (Submodule.projectionOnto (tmodK D) (tmodK' D) (tmodK'_isCompl D)
        ((tmodEK D).symm y : Fin m → k)) = y
      rw [Submodule.projectionOnto_apply_left, LinearEquiv.apply_symm_apply])
    (LinearMap.ext fun y => by
      change (tmodEC D) (Submodule.projectionOnto (tmodC D) (tmodR D) (tmodC_isCompl D).symm
        ((tmodEC D).symm y : Fin m → k)) = y
      rw [Submodule.projectionOnto_apply_left, LinearEquiv.apply_symm_apply])
    (LinearMap.ext fun x => by
      have hproj := Submodule.projection_add_projection_eq_self (tmodK'_isCompl D) x
      have hR : Submodule.projectionOnto (tmodR D) (tmodC D) (tmodC_isCompl D) (D.mulVecLin x) =
          ⟨D.mulVecLin x, LinearMap.mem_range_self _ _⟩ :=
        Submodule.projectionOnto_apply_of_mem_left _ _
      change ((tmodEK D).symm ((tmodEK D) (Submodule.projectionOnto (tmodK D) (tmodK' D)
        (tmodK'_isCompl D) x)) : Fin m → k) =
          -((tmodDKe D).symm (Submodule.projectionOnto (tmodR D) (tmodC D) (tmodC_isCompl D)
            (D.mulVecLin x)) : Fin m → k) + x
      rw [LinearEquiv.symm_apply_apply, hR, tmodDKe_symm_D, neg_add_eq_sub, eq_sub_iff_add_eq]
      exact hproj)
    (LinearMap.ext fun y => by
      have hproj := Submodule.projection_add_projection_eq_self (tmodC_isCompl D) y
      change ((tmodEC D).symm ((tmodEC D) (Submodule.projectionOnto (tmodC D) (tmodR D)
        (tmodC_isCompl D).symm y)) : Fin m → k) =
          D.mulVecLin (-((tmodDKe D).symm (Submodule.projectionOnto (tmodR D) (tmodC D)
            (tmodC_isCompl D) y) : Fin m → k)) + y
      rw [LinearEquiv.symm_apply_apply, map_neg, tmod_D_DKe_symm, neg_add_eq_sub,
        eq_sub_iff_add_eq, add_comm]
      exact hproj)

omit [Field k] in
/-- `tmodCx 0_a ≃ tmodCx 0_b` for `a = b`. Kind: definition. -/
def tmodZeroCast {k : Type} [Field k] : ∀ {a b : ℕ}, a = b →
    HomotopyEquiv (tmodCx (0 : Matrix (Fin a) (Fin a) k)) (tmodCx (0 : Matrix (Fin b) (Fin b) k))
  | _, _, rfl => HomotopyEquiv.refl _

/-- **Two square two-term complexes with kernels of the same dimension are homotopy equivalent**
(over a field). Kind: definition (PROVED). -/
def tmodEquiv_of_finrank {m' : ℕ} (D' : Matrix (Fin m') (Fin m') k)
    (h : finrank k (LinearMap.ker D.mulVecLin) = finrank k (LinearMap.ker D'.mulVecLin)) :
    HomotopyEquiv (tmodCx D) (tmodCx D') :=
  ((tmodNormal D).symm.trans (tmodZeroCast h)).trans (tmodNormal D')

/-- **The fibres of two stages with the same fibre dimension are homotopy equivalent** (tex
4976–4996: the fibre `[k^{n+1} --D̄--> k^{n+1}]` is determined up to homotopy by `s = dim ker D̄`).
Kind: definition (PROVED). -/
def twoTermFiberComplex_equiv {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (S S' : TwoTermStage ι) (h : S.fiberDim ρ = S'.fiberDim ρ) :
    HomotopyEquiv (twoTermFiberComplex ρ S) (twoTermFiberComplex ρ S') :=
  tmodEquiv_of_finrank (S.D.map ρ) (S'.D.map ρ) h

end NormalForm

/-! ### Lane RC31's matrix complex with zero differential as a two-term complex -/

section MatCx

open ZInQ.Manuscript.RC.Limits (matCx)

variable {k : Type} [Field k]

omit [Field k] in
/-- PROVED. A function space on `Fin 0` is a subsingleton. -/
theorem tmod_subsingleton_fin {n : ℕ} (h : n = 0) : Subsingleton (Fin n → k) := by
  subst h
  infer_instance

/-- PROVED. The differentials of `matCx r 0` vanish. -/
theorem tmod_matCx_d (r : ℤ → ℕ)
    (hsq : ∀ a b c (_ : a + 1 = b) (_ : b + 1 = c),
      (0 : Matrix (Fin (r c)) (Fin (r b)) k) * (0 : Matrix (Fin (r b)) (Fin (r a)) k) = 0)
    (i j : ℤ) : (matCx r (fun a b _ => (0 : Matrix (Fin (r b)) (Fin (r a)) k)) hsq).toCC.d i j = 0 := by
  change (if h : i + 1 = j then ModuleCat.ofHom (Matrix.toLin' (0 : Matrix (Fin (r j)) (Fin (r i)) k))
    else 0) = 0
  split_ifs
  · rw [map_zero]
    rfl
  · rfl

/-- PROVED. The differentials of `tmodCx 0` vanish. -/
theorem tmod_zero_d (s : ℕ) (i j : ℤ) : (tmodCx (0 : Matrix (Fin s) (Fin s) k)).d i j = 0 := by
  by_cases h01 : i = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h01
    exact (threeTermComplex_d_zero_one _ _ _).trans ModuleCat.ofHom_zero
  by_cases h12 : i = 1 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h12
    refine (threeTermComplex_d_one_two _ _ _).trans ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (0 : Matrix (Fin s) (Fin s) k) *ᵥ x = 0
    exact Matrix.zero_mulVec x
  · exact threeTermD_eq_zero _ _ _ _ h01 h12

/-- The identification `k^a ≅ k^b` for `a = b`. Kind: definition. -/
def tmodCastLin {a b : ℕ} (h : a = b) : (Fin a → k) →ₗ[k] (Fin b → k) where
  toFun x j := x (Fin.cast h.symm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- PROVED. The two identifications are inverse. -/
theorem tmodCastLin_cast {a b : ℕ} (h : a = b) (x : Fin a → k) :
    tmodCastLin h.symm (tmodCastLin h x) = x :=
  funext fun _ => congrArg x (Fin.ext rfl)

/-- The components `matCx r 0 → tmodCx 0_s` (the identifications `k^{r 1} ≅ k^s ≅ k^{r 2}` in
degrees one and two, `0` elsewhere). Kind: definition. -/
def tmodMatF (r : ℤ → ℕ) {s : ℕ} (h1 : r 1 = s) (h2 : r 2 = s) :
    ∀ n : ℤ, ModuleCat.of k (Fin (r n) → k) ⟶ threeTermX k PUnit (Fin s → k) (Fin s → k) n
  | .ofNat 1 => ModuleCat.ofHom (tmodCastLin h1)
  | .ofNat 2 => ModuleCat.ofHom (tmodCastLin h2)
  | _ => 0

/-- The components `tmodCx 0_s → matCx r 0`. Kind: definition. -/
def tmodMatG (r : ℤ → ℕ) {s : ℕ} (h1 : r 1 = s) (h2 : r 2 = s) :
    ∀ n : ℤ, threeTermX k PUnit (Fin s → k) (Fin s → k) n ⟶ ModuleCat.of k (Fin (r n) → k)
  | .ofNat 1 => ModuleCat.ofHom (tmodCastLin h1.symm)
  | .ofNat 2 => ModuleCat.ofHom (tmodCastLin h2.symm)
  | _ => 0

/-- **Lane RC31's matrix complex with zero differential and ranks concentrated in degrees one and
two, of equal rank `s`, is homotopy equivalent to `[k^s --0--> k^s]`.** Kind: definition
(PROVED). -/
def tmodMatEquiv (r : ℤ → ℕ)
    (hsq : ∀ a b c (_ : a + 1 = b) (_ : b + 1 = c),
      (0 : Matrix (Fin (r c)) (Fin (r b)) k) * (0 : Matrix (Fin (r b)) (Fin (r a)) k) = 0)
    {s : ℕ} (h0 : ∀ n, n ≠ 1 → n ≠ 2 → r n = 0) (h1 : r 1 = s) (h2 : r 2 = s) :
    HomotopyEquiv (matCx r (fun a b _ => (0 : Matrix (Fin (r b)) (Fin (r a)) k)) hsq).toCC
      (tmodCx (0 : Matrix (Fin s) (Fin s) k)) where
  hom :=
    { f := tmodMatF r h1 h2
      comm' := fun i j _ => by
        rw [tmod_matCx_d, tmod_zero_d]
        exact (Limits.comp_zero).trans (Limits.zero_comp).symm }
  inv :=
    { f := tmodMatG r h1 h2
      comm' := fun i j _ => by
        rw [tmod_matCx_d, tmod_zero_d]
        exact (Limits.comp_zero).trans (Limits.zero_comp).symm }
  homotopyHomInvId := Homotopy.ofEq (by
    ext i : 1
    rcases i with (_ | _ | _ | n) | n
    · have := tmod_subsingleton_fin (k := k) (h0 (Int.ofNat 0) (by decide) (by decide))
      ext x
      exact Subsingleton.elim (α := Fin (r (Int.ofNat 0)) → k) _ _
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact tmodCastLin_cast h1 x
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact tmodCastLin_cast h2 x
    · have := tmod_subsingleton_fin (k := k)
        (h0 (Int.ofNat (n + 3)) (by rw [Int.ofNat_eq_natCast]; omega) (by rw [Int.ofNat_eq_natCast]; omega))
      ext x
      exact Subsingleton.elim (α := Fin (r (Int.ofNat (n + 3))) → k) _ _
    · have := tmod_subsingleton_fin (k := k)
        (h0 (Int.negSucc n) (by rw [Int.negSucc_eq]; omega) (by rw [Int.negSucc_eq]; omega))
      ext x
      exact Subsingleton.elim (α := Fin (r (Int.negSucc n)) → k) _ _)
  homotopyInvHomId := Homotopy.ofEq (by
    ext i : 1
    rcases i with (_ | _ | _ | n) | n
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact tmodCastLin_cast h1.symm x
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact tmodCastLin_cast h2.symm x
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _)

end MatCx

end ZInQ.Manuscript.RC.Wiring
