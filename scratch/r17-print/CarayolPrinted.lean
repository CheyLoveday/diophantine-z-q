import ZInQKernel.Contrib.OneProof.NewformDict
import ZInQKernel.Contrib.OneProof.CarayolLevel
import ZInQKernel.Contrib.OneProof.DSCoeffExt

noncomputable section

namespace CarayolPrinted

open PkgI4 LadicCond

/-! ## §1. The conductor exponent does not change under extension of scalars -/

section ScalarExt

variable {k k' : Type*} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}

/-- `GL_n(k) → GL_n(k')` along `φ`. -/
def mapGL : GL (Fin n) k →* GL (Fin n) k' :=
  Units.map (φ.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k').toMonoidHom

theorem coe_mapGL (g : GL (Fin n) k) :
    ((mapGL φ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') = (g : Matrix (Fin n) (Fin n) k).map φ :=
  rfl

theorem mapGL_eq_one_iff (g : GL (Fin n) k) : mapGL φ g = 1 ↔ g = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun x : GL (Fin n) k' => (x : Matrix (Fin n) (Fin n) k')) h
    simp only [coe_mapGL, Units.val_one] at h1
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.map_injective φ.injective
    show (g : Matrix (Fin n) (Fin n) k).map φ = (1 : Matrix (Fin n) (Fin n) k).map φ
    rw [h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  · rintro rfl
    exact map_one _

/-- The common zero set of the linear forms `v ↦ r ⬝ v`, `r ∈ T`. -/
def ann {K : Type*} [Field K] (T : Set (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ r ∈ T, r ⬝ᵥ v = 0}
  zero_mem' := by intro r _; simp
  add_mem' := by
    intro v w hv hw r hr
    rw [dotProduct_add, hv r hr, hw r hr, add_zero]
  smul_mem' := by
    intro c v hv r hr
    rw [dotProduct_smul, hv r hr, smul_zero]

theorem mem_ann {K : Type*} [Field K] {T : Set (Fin n → K)} {v : Fin n → K} :
    v ∈ ann T ↔ ∀ r ∈ T, r ⬝ᵥ v = 0 := Iff.rfl

/-- `r ↦ r ⬝ v`. -/
def dotL {K : Type*} [Field K] (v : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun r := r ⬝ᵥ v
  map_add' a b := add_dotProduct a b v
  map_smul' c a := smul_dotProduct c a v

theorem ann_le_of_subset_span {K : Type*} [Field K] {T T' : Set (Fin n → K)}
    (h : T ⊆ Submodule.span K T') : ann T' ≤ ann T := by
  intro v hv r hr
  have hle : Submodule.span K T' ≤ LinearMap.ker (dotL v) :=
    Submodule.span_le.2 (fun r' hr' => LinearMap.mem_ker.2 (hv r' hr'))
  exact LinearMap.mem_ker.1 (hle (h hr))

theorem ann_range_eq_ker {K : Type*} [Field K] {ι : Type*} [Fintype ι] (w : ι → Fin n → K) :
    ann (Set.range w) = LinearMap.ker (Matrix.of w).mulVecLin := by
  ext v
  rw [mem_ann, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    funext i
    exact h _ ⟨i, rfl⟩
  · rintro h r ⟨i, rfl⟩
    exact congrFun h i

theorem finrank_ker_mulVecLin {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (A : Matrix ι (Fin n) K) :
    Module.finrank K (LinearMap.ker A.mulVecLin) = n - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at h
  unfold Matrix.rank
  omega

/-- `φ ∘ t ∈ span_{k'} (φ ∘ b)` for `t ∈ span_k b`. -/
theorem map_mem_span {b : Set (Fin n → k)} {t : Fin n → k} (ht : t ∈ Submodule.span k b) :
    (φ ∘ t) ∈ Submodule.span k' ((fun r => φ ∘ r) '' b) := by
  induction ht using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (φ ∘ (0 : Fin n → k)) = 0 := by funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (φ ∘ (x + y)) = φ ∘ x + φ ∘ y := by funext i; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : (φ ∘ (c • x)) = φ c • (φ ∘ x) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

/-- **Dimension of a common zero set is unchanged by extension of scalars.** -/
theorem finrank_ann_map (T : Set (Fin n → k)) :
    Module.finrank k' (ann ((fun r => φ ∘ r) '' T)) = Module.finrank k (ann T) := by
  classical
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent k T
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let w : b → Fin n → k := fun i => i
  let w' : b → Fin n → k' := fun i => φ ∘ (i : Fin n → k)
  have h1 : ann T = LinearMap.ker (Matrix.of w).mulVecLin := by
    rw [← ann_range_eq_ker]
    have hr : Set.range w = b := Subtype.range_coe
    rw [hr]
    apply le_antisymm
    · exact ann_le_of_subset_span (fun x hx => Submodule.subset_span (hbT hx))
    · exact ann_le_of_subset_span (fun x hx => hspan ▸ Submodule.subset_span hx)
  have h2 : ann ((fun r => φ ∘ r) '' T) = LinearMap.ker (Matrix.of w').mulVecLin := by
    rw [← ann_range_eq_ker]
    apply le_antisymm
    · apply ann_le_of_subset_span
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, hbT i.2, rfl⟩
    · apply ann_le_of_subset_span
      rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ Submodule.span k b := hspan ▸ Submodule.subset_span ht
      have := map_mem_span φ ht'
      have hr : (fun r => φ ∘ r) '' b = Set.range w' := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
        · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩
      rwa [hr] at this
  have hli' : LinearIndependent k (Matrix.of w).row := hli
  let _ := φ.toAlgebra
  have : FaithfulSMul k k' := (faithfulSMul_iff_algebraMap_injective k k').2 φ.injective
  have hli2 : LinearIndependent k' (Matrix.of w').row := by
    have := (linearIndependent_algebraMap_comp_iff (R := k) (S := k') (v := w)).2 hli
    exact this
  rw [h1, h2, finrank_ker_mulVecLin, finrank_ker_mulVecLin, hli'.rank_matrix, hli2.rank_matrix]

variable {p : ℕ} [Fact p.Prime]

/-- The rows of `ρ(σ) − 1`, `σ ∈ S`. -/
def rowsSet {K : Type*} [Field K] (ρ : GQp p →* GL (Fin n) K) (S : Set (GQp p)) :
    Set (Fin n → K) :=
  {r | ∃ σ ∈ S, ∃ i, r = fun j => ((ρ σ : Matrix (Fin n) (Fin n) K) - 1) i j}

theorem invariants_eq_ann {K : Type*} [Field K] (ρ : GQp p →* GL (Fin n) K) (S : Set (GQp p)) :
    invariants ρ S = ann (rowsSet ρ S) := by
  ext v
  rw [mem_ann]
  constructor
  · rintro h r ⟨σ, hσ, i, rfl⟩
    have h' : (ρ σ : Matrix (Fin n) (Fin n) K).mulVec v = v := h σ hσ
    have h2 : ((ρ σ : Matrix (Fin n) (Fin n) K) - 1).mulVec v = 0 := by
      rw [Matrix.sub_mulVec, h', Matrix.one_mulVec, sub_self]
    exact congrFun h2 i
  · intro h σ hσ
    have h2 : ((ρ σ : Matrix (Fin n) (Fin n) K) - 1).mulVec v = 0 :=
      funext fun i => h _ ⟨σ, hσ, i, rfl⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
    exact h2

theorem rowsSet_map (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) :
    rowsSet ((mapGL φ).comp ρ) S = (fun r => φ ∘ r) '' rowsSet ρ S := by
  have hM : ∀ M : Matrix (Fin n) (Fin n) k, ∀ i,
      (fun j => (M.map φ - 1) i j) = φ ∘ (fun j => (M - 1) i j) := by
    intro M i
    funext j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, Function.comp_apply, map_sub]
    split_ifs <;> simp
  ext r
  constructor
  · rintro ⟨σ, hσ, i, rfl⟩
    refine ⟨_, ⟨σ, hσ, i, rfl⟩, ?_⟩
    rw [MonoidHom.comp_apply, coe_mapGL, hM]
  · rintro ⟨_, ⟨σ, hσ, i, rfl⟩, rfl⟩
    refine ⟨σ, hσ, i, ?_⟩
    rw [MonoidHom.comp_apply, coe_mapGL, hM]

theorem codimInv_map (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) :
    codimInv ((mapGL φ).comp ρ) S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_eq_ann, invariants_eq_ann, rowsSet_map, finrank_ann_map]

theorem isAdapted_map_iff (ρ : GQp p →* GL (Fin n) k) (L : Fld p) :
    IsAdapted L ((mapGL φ).comp ρ) ↔ IsAdapted L ρ := by
  unfold IsAdapted
  simp only [MonoidHom.comp_apply, mapGL_eq_one_iff]

/-- **The Serre–Tate conductor exponent is unchanged by extension of scalars** along a field
homomorphism (same invariant dimensions, same adapted levels, so `swan` chooses the same level). -/
theorem condExp_map (ρ : GQp p →* GL (Fin n) k) :
    condExp ((mapGL φ).comp ρ) = condExp ρ := by
  have hswan : swan ((mapGL φ).comp ρ) = swan ρ := by
    unfold swan
    by_cases h : ∃ L : Fld p, IsAdapted L ρ
    · have h' : ∃ L : Fld p, IsAdapted L ((mapGL φ).comp ρ) := by
        obtain ⟨L, hL⟩ := h
        exact ⟨L, (isAdapted_map_iff φ ρ L).2 hL⟩
      rw [dite_eq_left h, dite_eq_left h']
      have hc : h'.choose = h.choose :=
        CarayolLevel.choose_congr (funext fun L => propext (isAdapted_map_iff φ ρ L)) h' h
      rw [hc]
      unfold swanAt
      exact finsum_congr fun i => by rw [codimInv_map]
    · have h' : ¬ ∃ L : Fld p, IsAdapted L ((mapGL φ).comp ρ) := by
        rintro ⟨L, hL⟩
        exact h ⟨L, (isAdapted_map_iff φ ρ L).1 hL⟩
      rw [dite_eq_right h, dite_eq_right h']
  unfold condExp
  rw [codimInv_map, hswan]

end ScalarExt

/-! ## §2. Absolute irreducibility (Burnside form) survives extension of scalars and gives
semisimplicity -/

section Burnside

variable {k k' : Type*} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}

theorem adjoin_map_eq_top {ι : Type*} (M : ι → Matrix (Fin n) (Fin n) k)
    (h : Algebra.adjoin k (Set.range M) = ⊤) :
    Algebra.adjoin k' (Set.range fun i => (M i).map φ) = ⊤ := by
  set A' := Algebra.adjoin k' (Set.range fun i => (M i).map φ)
  have key : ∀ X ∈ Algebra.adjoin k (Set.range M),
      (φ.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k') X ∈ A' := by
    intro X hX
    induction hX using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap c =>
      have : (φ.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k')
          (algebraMap k (Matrix (Fin n) (Fin n) k) c) =
          algebraMap k' (Matrix (Fin n) (Fin n) k') (φ c) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
        split_ifs <;> simp
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  rw [eq_top_iff]
  intro Y _
  rw [Matrix.matrix_eq_sum_single Y]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
  have hE := key (Matrix.single i j (1 : k)) (h ▸ Algebra.mem_top)
  have : Matrix.single i j (Y i j) = Y i j •
      (φ.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k')
        (Matrix.single i j (1 : k)) := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply,
      smul_eq_mul]
    split_ifs <;> simp
  rw [this]
  exact Subalgebra.smul_mem _ hE _

/-- A family of matrices whose span is all matrices (Burnside's form of absolute irreducibility)
has no invariant subspace other than `0` and the whole space. -/
theorem eq_bot_or_top_of_adjoin {K : Type*} [Field K] {ι : Type*}
    (M : ι → Matrix (Fin n) (Fin n) K) (h : Algebra.adjoin K (Set.range M) = ⊤)
    (W : Submodule K (Fin n → K)) (hW : ∀ i, ∀ w ∈ W, (M i).mulVec w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hall : ∀ X : Matrix (Fin n) (Fin n) K, ∀ w ∈ W, X.mulVec w ∈ W := by
    intro X
    have hX : X ∈ Algebra.adjoin K (Set.range M) := h ▸ Algebra.mem_top
    induction hX using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hW i
    | algebraMap c =>
      intro w hw
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem c hw
    | add x y _ _ hx hy =>
      intro w hw
      rw [Matrix.add_mulVec]
      exact W.add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy =>
      intro w hw
      rw [← Matrix.mulVec_mulVec]
      exact hx _ (hy w hw)
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw0 (funext hc)
    rw [eq_top_iff]
    intro u _
    have hX : (Matrix.of fun a b => if b = j then u a / w j else 0).mulVec w = u := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact div_mul_cancel₀ _ hj
    rw [← hX]
    exact hall _ w hw

theorem isSemisimple_of_adjoin {ℓ : ℕ} [Fact ℓ.Prime] (ρ : GaloisRep ℓ n)
    (h : Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) = ⊤) : ρ.IsSemisimple := by
  intro W hW
  have hW' : ∀ σ, ∀ w ∈ W, (ρ.mat σ).mulVec w ∈ W := by
    intro σ w hw
    have := hW σ (Submodule.mem_map_of_mem (f := Matrix.toLin' (ρ.mat σ)) hw)
    simpa [Matrix.toLin'_apply] using this
  rcases eq_bot_or_top_of_adjoin ρ.mat h W hW' with hb | ht
  · subst hb
    exact ⟨⊤, isCompl_bot_top, fun σ => le_top⟩
  · subst ht
    exact ⟨⊥, isCompl_top_bot, fun σ => by rw [Submodule.map_bot]⟩

end Burnside

end CarayolPrinted
