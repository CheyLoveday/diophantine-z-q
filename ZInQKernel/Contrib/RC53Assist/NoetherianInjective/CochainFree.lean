import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageFlat

/-!
# Continuous cochains with finite free discrete coefficients are free

Let `G` be a profinite (compact, Hausdorff, totally disconnected) topological group, `R` any
commutative ring and `M` a finite free `R`-module with the discrete topology and a continuous
`G`-action. Then every term `C^n_cont(G, M)` (`n : ℕ`) of the complex of continuous
inhomogeneous cochains is a free `R`-module, and so is every term of its extension by zero to
`ℤ`. Nothing is assumed of `R` beyond commutativity: `R` need not be local, Noetherian or a
field, and no topology on `R` is used.

Proof. Continuous cochains with discrete coefficients are the locally constant functions
`G^n → M` (`contCochainLCEquiv`), and `G^n` is profinite. For a profinite `S`, Nöbeling's
theorem (`LocallyConstant.freeOfProfinite`) gives a `ℤ`-basis `b` of `LocallyConstant S ℤ`; its
image in `LocallyConstant S R` is an `R`-basis (`basisLocallyConstant`). It spans because a
locally constant function is a finite combination of the indicators of its fibres. It is
linearly independent because finitely many `b j` are constant on the blocks of one finite clopen
partition of `S`, on which the coordinate functional of `b` is a finite integer combination of
evaluations at points. Finally `LocallyConstant S M ≃ (LocallyConstant S R) ^ r` for a basis of
`M` with `r` elements.

These free modules are in general of infinite rank: they are not finitely generated, and for a
finite `M` and an infinite `G` the positive degree terms are infinite sets.

## Main declarations

* `castLC`, `linearIndependent_castLC`, `span_castLC`, `basisLocallyConstant`: the `R`-basis of
  `LocallyConstant S R` induced by a `ℤ`-basis of `LocallyConstant S ℤ`.
* `free_locallyConstant_ring`, `free_locallyConstant_profinite`: `LocallyConstant S R` and
  `LocallyConstant S M` are free for a profinite `S`.
* `free_contCochains_profinite`: the continuous cochain modules `C^n_cont(G, M)` are free.
* `free_globalCx_profinite`, `free_localCx_profinite`: the terms of the `ℤ`-indexed global and
  local complexes are free in every degree (zero in negative degrees).
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NoetherianInjective

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-! ### Locally constant functions on a profinite space -/

section LocallyConstant

universe u v w

variable {S : Type u} [TopologicalSpace S] (R : Type v) [Ring R]

/-- Evaluation of a finite sum of locally constant functions. -/
theorem lcSum_apply {Y : Type w} [AddCommMonoid Y] {ι : Type*} (t : Finset ι)
    (g : ι → LocallyConstant S Y) (x : S) : (∑ i ∈ t, g i) x = ∑ i ∈ t, g i x :=
  map_sum (LocallyConstant.evalAddMonoidHom x) g t

/-- Reading an integer-valued locally constant function as an `R`-valued one. -/
def castLC : LocallyConstant S ℤ →+ LocallyConstant S R :=
  LocallyConstant.mapAddMonoidHom (Int.castAddHom R)

@[simp]
theorem castLC_apply (f : LocallyConstant S ℤ) (x : S) : castLC R f x = (f x : R) :=
  rfl

/-- The images of the integer-valued functions lie in the `R`-span of the image of a
`ℤ`-basis. -/
theorem castLC_mem_span {ι : Type w} (b : Module.Basis ι ℤ (LocallyConstant S ℤ))
    (f : LocallyConstant S ℤ) :
    castLC R f ∈ Submodule.span R (Set.range fun i => castLC R (b i)) := by
  rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul R]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable [CompactSpace S]

/-- **The image of a `ℤ`-basis spans**: a locally constant `f : S → R` is the finite
`R`-combination `∑ q, f q • 1_q` of the integer-valued indicators of its fibres. -/
theorem span_castLC {ι : Type w} (b : Module.Basis ι ℤ (LocallyConstant S ℤ)) :
    Submodule.span R (Set.range fun i => castLC R (b i)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro f -
  have : Fintype f.discreteQuotient := Fintype.ofFinite _
  have hf : f = ∑ q : f.discreteQuotient, f.lift q •
      castLC R (blockFunctionsMap ℤ ℤ f.discreteQuotient (Pi.single q 1)) := by
    ext x
    rw [lcSum_apply]
    simp only [LocallyConstant.smul_apply, castLC_apply, blockFunctionsMap_apply, Pi.single_apply,
      Int.cast_ite, Int.cast_one, Int.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  rw [hf]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (castLC_mem_span R b _)

/-- **The image of a `ℤ`-basis is linearly independent over `R`.** For a finite set `s` of
indices, all `b j`, `j ∈ s`, are constant on the blocks `q` of one finite clopen partition `Q`;
with points `rep q` in the blocks and `β q` the `i₀`-th coordinate of the indicator of `q`, one
has `∑ q, b j (rep q) * β q = δ_{j i₀}` for `j ∈ s`, so evaluating an `R`-linear relation at the
points `rep q` recovers its `i₀`-th coefficient. -/
theorem linearIndependent_castLC {ι : Type w} (b : Module.Basis ι ℤ (LocallyConstant S ℤ)) :
    LinearIndependent R fun i => castLC R (b i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i₀ hi₀
  set Q : DiscreteQuotient S := s.inf fun j => (b j).discreteQuotient
  have : Fintype Q := Fintype.ofFinite Q
  have hconst : ∀ j ∈ s, ∀ x y, Q.proj x = Q.proj y → b j x = b j y := by
    intro j hj x y hxy
    have hle : Q ≤ (b j).discreteQuotient := Finset.inf_le hj
    have h1 : ∀ z, b j z = (b j).lift (DiscreteQuotient.ofLE hle (Q.proj z)) := fun z => by
      rw [DiscreteQuotient.ofLE_proj]
      rfl
    rw [h1 x, h1 y, hxy]
  choose rep hrep using Q.proj_surjective
  have hT : ∀ j ∈ s, b j = ∑ q, b j (rep q) • blockFunctionsMap ℤ ℤ Q (Pi.single q 1) := by
    intro j hj
    ext x
    rw [lcSum_apply]
    simp only [LocallyConstant.smul_apply, blockFunctionsMap_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hconst j hj _ _ (hrep _).symm
  set β : Q → ℤ := fun q => b.repr (blockFunctionsMap ℤ ℤ Q (Pi.single q 1)) i₀
  have hkey : ∀ j ∈ s, ∑ q, b j (rep q) * β q = if j = i₀ then 1 else 0 := by
    intro j hj
    have h := congrArg (fun f => b.repr f i₀) (hT j hj)
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] at h
    exact h.symm
  have hev : ∀ q, ∑ j ∈ s, g j * (b j (rep q) : R) = 0 := by
    intro q
    have h := congrArg (fun f : LocallyConstant S R => f (rep q)) hg
    simpa only [lcSum_apply, LocallyConstant.smul_apply, castLC_apply, smul_eq_mul,
      LocallyConstant.coe_zero, Pi.zero_apply] using h
  calc g i₀ = ∑ j ∈ s, g j * ((if j = i₀ then 1 else 0 : ℤ) : R) := by
        simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', hi₀, ite_true]
    _ = ∑ j ∈ s, g j * ((∑ q, b j (rep q) * β q : ℤ) : R) :=
        Finset.sum_congr rfl fun j hj => by rw [hkey j hj]
    _ = ∑ q, (∑ j ∈ s, g j * (b j (rep q) : R)) * (β q : R) := by
        simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp only [hev, zero_mul, Finset.sum_const_zero]

/-- **The `R`-basis of `LocallyConstant S R`** induced by a `ℤ`-basis of
`LocallyConstant S ℤ`, for a compact `S`. -/
def basisLocallyConstant {ι : Type w} (b : Module.Basis ι ℤ (LocallyConstant S ℤ)) :
    Module.Basis ι R (LocallyConstant S R) :=
  Module.Basis.mk (linearIndependent_castLC R b) (span_castLC R b).ge

@[simp]
theorem coe_basisLocallyConstant {ι : Type w} (b : Module.Basis ι ℤ (LocallyConstant S ℤ)) :
    ⇑(basisLocallyConstant R b) = fun i => castLC R (b i) :=
  Module.Basis.coe_mk _ _

variable [T2Space S] [TotallyDisconnectedSpace S]

/-- **`LocallyConstant S R` is a free `R`-module for a profinite `S` and any ring `R`**, by
Nöbeling's theorem and `basisLocallyConstant`. -/
theorem free_locallyConstant_ring : Module.Free R (LocallyConstant S R) :=
  have : Module.Free ℤ (LocallyConstant S ℤ) := LocallyConstant.freeOfProfinite (Profinite.of S)
  Module.Free.of_basis (basisLocallyConstant R (Module.Free.chooseBasis ℤ _))

/-- Locally constant functions into a finite power `ι → R` are `ι`-tuples of locally constant
functions. -/
def lcPiEquiv (ι : Type w) [Finite ι] :
    LocallyConstant S (ι → R) ≃ₗ[R] (ι → LocallyConstant S R) where
  toFun := LocallyConstant.flip
  invFun := LocallyConstant.unflip
  left_inv := LocallyConstant.unflip_flip
  right_inv := LocallyConstant.flip_unflip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`LocallyConstant S M` is free for a profinite `S` and a finite free `R`-module `M`**: with
a basis of `M` indexed by a finite type `ι` it is `(LocallyConstant S R) ^ ι`. -/
theorem free_locallyConstant_profinite (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] : Module.Free R (LocallyConstant S M) :=
  have := free_locallyConstant_ring R (S := S)
  Module.Free.of_equiv ((LocallyConstant.congrRightₗ R
    (Module.Free.chooseBasis R M).equivFun).trans (lcPiEquiv R _)).symm

end LocallyConstant

/-! ### The continuous cochain modules -/

section Cochains

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The actual continuous cochain modules `C^n_cont(G, M)` are free** for a profinite group
`G` and a finite free discrete coefficient module `M`, over any commutative ring `R`. -/
theorem free_contCochains_profinite [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Module.Free R M] [Module.Finite R M] (n : ℕ) : Module.Free R ((contCochains R G M).X n) :=
  have := free_locallyConstant_profinite R (S := Fin n → G) M
  Module.Free.of_equiv (contCochainLCEquiv R G M n).symm

end Cochains

/-! ### The `ℤ`-indexed global and local complexes -/

section Complexes

variable (k : Type) [CommRing k] (GS : Type) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul GS M] [Module.Free k M]
  [Module.Finite k M]

/-- The terms of the global complex `C^•_cont(G_S, M)`, extended by zero to `ℤ`, are free for a
profinite `G_S`. -/
theorem free_globalCx_profinite [CompactSpace GS] [T2Space GS] [TotallyDisconnectedSpace GS]
    (m : ℤ) : Module.Free k ((globalCx k GS M).X m) :=
  free_natX _ (fun n => free_contCochains_profinite n) m

omit [IsTopologicalGroup GS] in
/-- The terms of the local complex `C^•_cont(G_v, M)`, `G_v` acting through `loc_v` and extended
by zero to `ℤ`, are free for a profinite `G_v`. -/
theorem free_localCx_profinite (v : ι) [CompactSpace (Gv v)] [T2Space (Gv v)]
    [TotallyDisconnectedSpace (Gv v)] (m : ℤ) : Module.Free k ((localCx k GS Gv loc M v).X m) := by
  have : Module.Free k (ResMod (loc v) M) := inferInstanceAs (Module.Free k M)
  have : Module.Finite k (ResMod (loc v) M) := inferInstanceAs (Module.Finite k M)
  exact free_natX _ (fun n => free_contCochains_profinite (R := k) (G := Gv v)
    (M := ResMod (loc v) M) n) m

end Complexes

end ZInQ.Contrib.RC53Assist.NoetherianInjective
