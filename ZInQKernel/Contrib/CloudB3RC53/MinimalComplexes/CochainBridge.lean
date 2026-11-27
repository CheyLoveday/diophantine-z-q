import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.MinimalModel
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.DegreewiseInvertible

/-!
# RC53 MinimalComplexes: graded matrices as Mathlib cochain complexes

`MinimalModel.lean` writes a bounded complex of finite free modules with chosen bases as one graded
matrix `d : Matrix I I R` (`deg : I → ℤ`, `IsGradedDiff`, `d * d = 0`; `DEPARTURE`, form only). This
file attaches to such data a genuine `CochainComplex (ModuleCat R) ℤ` and transports the results of
`MinimalModel.lean` to Mathlib's complexes, so that they meet `DegreewiseInvertible.lean`
(tex L5357–5359, L5404–5411: "cancelling unit entries at its maximal ideal", "Decompose `D` over `Λ`
into a minimal complex `D_min` and unit disks `E`", "A homotopy equivalence between minimal bounded
free complexes over a local ring is degreewise invertible").

Nodes (PROVED):
* `GradedComplexBoundedFree`: `gradedComplex deg d` (degree `n` term `R^{deg⁻¹(n)}`, differential the
  degree-`n` block of `d`) is a cochain complex, strictly supported in `[a, b]` when `a ≤ deg ≤ b`,
  and finite free in every degree.
* `GradedIsoOfDegPreserving`: a degree-preserving inverse pair `P, Q` gives an isomorphism of cochain
  complexes `gradedComplex d ≅ gradedComplex (P d Q)`.
* `SplitFormHomotopyEquiv`: in split form, the complex is homotopy equivalent to its minimal part
  (the kind-`0` subcomplex), whose differential has image in `𝔪`; the unit disks are contractible.
* `MinimalModelCochain`: over a local ring every bounded finite free graded complex is homotopy
  equivalent to a minimal bounded finite free Mathlib cochain complex (differential into `𝔪`).
* `MinimalModelsDegreewiseIso`: two minimal models of homotopy-equivalent graded complexes are
  isomorphic in every degree (with `MinimalHomotopyEquivDegreewise`).
-/

namespace ZInQ.Contrib.CloudB3RC53.MinimalComplexes

open CategoryTheory Matrix

universe u

section Blocks

variable {R : Type u} [CommRing R]

/-- The `(j, i)` degree block of a matrix between graded index types. -/
def blk {α β : Type u} (dα : α → ℤ) (dβ : β → ℤ) (M : Matrix α β R) (j i : ℤ) :
    Matrix {a // dα a = j} {b // dβ b = i} R :=
  M.submatrix Subtype.val Subtype.val

theorem blk_add {α β : Type u} (dα : α → ℤ) (dβ : β → ℤ) (M N : Matrix α β R) (j i : ℤ) :
    blk dα dβ (M + N) j i = blk dα dβ M j i + blk dα dβ N j i := rfl

theorem blk_one {α : Type u} [DecidableEq α] (dα : α → ℤ) (i : ℤ) :
    blk dα dα (1 : Matrix α α R) i i = 1 := by
  ext x y
  simp only [blk, submatrix_apply, one_apply, Subtype.ext_iff]

theorem blk_zero {α β : Type u} (dα : α → ℤ) (dβ : β → ℤ) (j i : ℤ) :
    blk dα dβ (0 : Matrix α β R) j i = 0 := rfl

theorem sum_subtype_of_zero {γ : Type u} [Fintype γ] (p : γ → Prop) [DecidablePred p] (f : γ → R)
    (hf : ∀ x, ¬ p x → f x = 0) : ∑ x, f x = ∑ x : Subtype p, f x := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · rfl
  · exact hf x h

/-- Block multiplication through the unique intermediate degree `m` (hypothesis on the right
factor). -/
theorem blk_mul {α β γ : Type u} [Fintype β] (dα : α → ℤ) (dβ : β → ℤ) (dγ : γ → ℤ)
    (A : Matrix α β R) (B : Matrix β γ R) (j m i : ℤ)
    (hB : ∀ b c, dγ c = i → B b c ≠ 0 → dβ b = m) :
    blk dα dγ (A * B) j i = blk dα dβ A j m * blk dβ dγ B m i := by
  ext x y
  simp only [blk, submatrix_apply, mul_apply]
  rw [sum_subtype_of_zero (fun b => dβ b = m)]
  intro b hb
  have : B b y.1 = 0 := by
    by_contra h
    exact hb (hB b y.1 y.2 h)
  simp [this]

/-- Block multiplication through the unique intermediate degree `m` (hypothesis on the left
factor). -/
theorem blk_mul' {α β γ : Type u} [Fintype β] (dα : α → ℤ) (dβ : β → ℤ) (dγ : γ → ℤ)
    (A : Matrix α β R) (B : Matrix β γ R) (j m i : ℤ)
    (hA : ∀ a b, dα a = j → A a b ≠ 0 → dβ b = m) :
    blk dα dγ (A * B) j i = blk dα dβ A j m * blk dβ dγ B m i := by
  ext x y
  simp only [blk, submatrix_apply, mul_apply]
  rw [sum_subtype_of_zero (fun b => dβ b = m)]
  intro b hb
  have : A x.1 b = 0 := by
    by_contra h
    exact hb (hA x.1 b x.2 h)
  simp [this]

variable (R) in
/-- The degree-`n` term `R^{deg⁻¹(n)}`. -/
abbrev gX {α : Type u} (dα : α → ℤ) (n : ℤ) : ModuleCat.{u} R :=
  ModuleCat.of R ({a // dα a = n} → R)

/-- The morphism of a block matrix. -/
noncomputable def mat {α β : Type u} [Fintype β] [DecidableEq β] {dα : α → ℤ} {dβ : β → ℤ}
    {j i : ℤ} (M : Matrix {a // dα a = j} {b // dβ b = i} R) : gX R dβ i ⟶ gX R dα j :=
  ModuleCat.ofHom (Matrix.toLin' M)

theorem mat_comp {α β γ : Type u} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {dα : α → ℤ} {dβ : β → ℤ} {dγ : γ → ℤ} {k j i : ℤ}
    (M : Matrix {a // dα a = k} {b // dβ b = j} R) (N : Matrix {b // dβ b = j} {c // dγ c = i} R) :
    mat N ≫ mat M = mat (M * N) := by
  rw [mat, mat, mat, Matrix.toLin'_mul, ModuleCat.ofHom_comp]

theorem mat_zero {α β : Type u} [Fintype β] [DecidableEq β] {dα : α → ℤ} {dβ : β → ℤ} {j i : ℤ} :
    (mat (0 : Matrix {a // dα a = j} {b // dβ b = i} R)) = 0 := by
  rw [mat, map_zero]; rfl

theorem mat_add {α β : Type u} [Fintype β] [DecidableEq β] {dα : α → ℤ} {dβ : β → ℤ} {j i : ℤ}
    (M N : Matrix {a // dα a = j} {b // dβ b = i} R) : mat (M + N) = mat M + mat N := by
  rw [mat, mat, mat, map_add]; rfl

theorem mat_one {α : Type u} [Fintype α] [DecidableEq α] {dα : α → ℤ} {i : ℤ} :
    (mat (1 : Matrix {a // dα a = i} {a // dα a = i} R)) = 𝟙 _ := by
  rw [mat, Matrix.toLin'_one]; rfl

end Blocks

section Complex

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]

/-- The block of a graded differential vanishes unless the degree rises by one. -/
theorem blk_graded_zero {deg : I → ℤ} {d : Matrix I I R} (hg : IsGradedDiff deg d) {i j : ℤ}
    (hij : i + 1 ≠ j) : blk deg deg d j i = 0 := by
  ext x y
  simp only [blk, submatrix_apply, Matrix.zero_apply]
  by_contra h
  exact hij (by have := hg _ _ h; rw [x.2, y.2] at this; omega)

/-- **The cochain complex of a graded matrix**: degree `n` term `R^{deg⁻¹(n)}`, differential the
degree block of `d`. -/
noncomputable def gradedComplex (deg : I → ℤ) (d : Matrix I I R) (hg : IsGradedDiff deg d)
    (hd : d * d = 0) : CochainComplex (ModuleCat.{u} R) ℤ where
  X n := gX R deg n
  d i j := mat (blk deg deg d j i)
  shape i j hij := by
    rw [blk_graded_zero hg (by simpa using hij), mat_zero]
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    rw [mat_comp, ← blk_mul deg deg deg d d k j i (fun b c hc h => by
      have := hg b c h; omega), hd, blk_zero, mat_zero]

theorem gradedComplex_d (deg : I → ℤ) (d : Matrix I I R) (hg : IsGradedDiff deg d)
    (hd : d * d = 0) (i j : ℤ) : (gradedComplex deg d hg hd).d i j = mat (blk deg deg d j i) := rfl

/-- **The graded complex is bounded and finite free** (the "bounded free models" of tex
L5357–5359, L5404–5411). If `a ≤ deg x ≤ b` for all `x`, `gradedComplex deg d` is strictly supported
in `[a, b]`; every term is a finite free `R`-module. Classification: PROVED. -/
def GradedComplexBoundedFree : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (deg : I → ℤ)
    (d : Matrix I I R) (hg : IsGradedDiff deg d) (hd : d * d = 0) (a b : ℤ),
    (∀ x, a ≤ deg x) → (∀ x, deg x ≤ b) →
      (gradedComplex deg d hg hd).IsStrictlyGE a ∧ (gradedComplex deg d hg hd).IsStrictlyLE b ∧
      (∀ n, Module.Free R ((gradedComplex deg d hg hd).X n)) ∧
      (∀ n, Module.Finite R ((gradedComplex deg d hg hd).X n))

theorem isZero_gX_of_empty {α : Type u} (dα : α → ℤ) (n : ℤ) (h : ∀ x, dα x ≠ n) :
    Limits.IsZero (gX R dα n) := by
  rw [ModuleCat.isZero_of_iff_subsingleton]
  have : IsEmpty {a // dα a = n} := ⟨fun x => h x.1 x.2⟩
  infer_instance

theorem gradedComplexBoundedFree_proof : GradedComplexBoundedFree.{u} := by
  intro R _ I _ _ deg d hg hd a b ha hb
  refine ⟨?_, ?_, fun n => ?_, fun n => ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact isZero_gX_of_empty deg i (fun x hx => by have := ha x; omega)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact isZero_gX_of_empty deg i (fun x hx => by have := hb x; omega)
  · exact inferInstanceAs (Module.Free R ({x // deg x = n} → R))
  · exact inferInstanceAs (Module.Finite R ({x // deg x = n} → R))

/-- The degree-`n` isomorphism given by a degree-preserving inverse pair. -/
noncomputable def degIso (deg : I → ℤ) {P Q : Matrix I I R} (hP : IsDegPreserving deg P)
    (hQ : IsDegPreserving deg Q) (hPQ : P * Q = 1) (hQP : Q * P = 1) (n : ℤ) :
    gX R deg n ≅ gX R deg n where
  hom := mat (blk deg deg P n n)
  inv := mat (blk deg deg Q n n)
  hom_inv_id := by
    rw [mat_comp, ← blk_mul deg deg deg Q P n n n (fun b c hc h => (hP b c h).trans hc), hQP,
      blk_one, mat_one]
  inv_hom_id := by
    rw [mat_comp, ← blk_mul deg deg deg P Q n n n (fun b c hc h => (hQ b c h).trans hc), hPQ,
      blk_one, mat_one]

/-- **A degree-preserving change of bases is an isomorphism of cochain complexes**: for a
degree-preserving inverse pair `P, Q`, the components `P` (in each degree) form an isomorphism
`gradedComplex d ≅ gradedComplex (P d Q)`. Classification: PROVED. -/
def GradedIsoOfDegPreserving : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (deg : I → ℤ)
    (d P Q : Matrix I I R) (hg : IsGradedDiff deg d) (hd : d * d = 0)
    (hP : IsDegPreserving deg P) (hQ : IsDegPreserving deg Q) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      ∃ e : gradedComplex deg d hg hd ≅
          gradedComplex deg (P * d * Q) (IsGradedDiff.conj hP hg hQ) (conj_sq_zero hQP hd),
        ∀ n, (e.hom.f n) = mat (blk deg deg P n n)

/-- The isomorphism of `GradedIsoOfDegPreserving`. -/
noncomputable def gradedIso (deg : I → ℤ) (d P Q : Matrix I I R) (hg : IsGradedDiff deg d)
    (hd : d * d = 0) (hP : IsDegPreserving deg P) (hQ : IsDegPreserving deg Q) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) :
    gradedComplex deg d hg hd ≅
      gradedComplex deg (P * d * Q) (IsGradedDiff.conj hP hg hQ) (conj_sq_zero hQP hd) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => degIso deg hP hQ hPQ hQP n) (by
    intro i j _
    change mat (blk deg deg P i i) ≫ mat (blk deg deg (P * d * Q) j i) =
      mat (blk deg deg d j i) ≫ mat (blk deg deg P j j)
    rw [mat_comp, mat_comp,
      ← blk_mul deg deg deg (P * d * Q) P j i i (fun b c hc h => (hP b c h).trans hc),
      ← blk_mul' deg deg deg P d j j i (fun a b ha h => ((hP a b h).symm).trans ha)]
    congr 2
    rw [Matrix.mul_assoc, hQP, Matrix.mul_one])

theorem gradedIsoOfDegPreserving_proof : GradedIsoOfDegPreserving.{u} := by
  intro R _ I _ _ deg d P Q hg hd hP hQ hPQ hQP
  exact ⟨gradedIso deg d P Q hg hd hP hQ hPQ hQP, fun n => rfl⟩

end Complex

section Split

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {deg : I → ℤ} {D : Matrix I I R} {kind : I → Fin 3} {partner : I → I}

/-- The minimal part: the kind-`0` basis vectors. -/
abbrev MinIdx (kind : I → Fin 3) : Type u := {x : I // kind x = 0}

/-- The minimal differential. -/
def dmin (D : Matrix I I R) (kind : I → Fin 3) : Matrix (MinIdx kind) (MinIdx kind) R :=
  D.submatrix Subtype.val Subtype.val

variable (R) in
/-- The inclusion of the minimal part. -/
def iotaM (kind : I → Fin 3) : Matrix I (MinIdx kind) R :=
  Matrix.of fun x a => if x = a.1 then 1 else 0

variable (R) in
/-- The projection onto the minimal part. -/
def piM (kind : I → Fin 3) : Matrix (MinIdx kind) I R :=
  Matrix.of fun a x => if a.1 = x then 1 else 0

variable (R) in
/-- The contracting homotopy of the disks: `e_y ↦ e_{partner y}` for disk targets `y`. -/
def hM (kind : I → Fin 3) (partner : I → I) : Matrix I I R :=
  Matrix.of fun x y => if kind y = 2 ∧ x = partner y then 1 else 0

theorem split_col_zero (hS : SplitForm D kind partner) {x y : I} (hx : kind x = 0)
    (h : D y x ≠ 0) : kind y = 0 := by
  rcases hS.2.2.1 x y h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · rw [hx] at h1; exact absurd h1 (by decide)

theorem split_row_zero (hS : SplitForm D kind partner) {x y : I} (hy : kind y = 0)
    (h : D y x ≠ 0) : kind x = 0 := by
  rcases hS.2.2.1 x y h with ⟨h1, -⟩ | ⟨h1, rfl⟩
  · exact h1
  · rw [(hS.1 x h1).1] at hy; exact absurd hy (by decide)

theorem dmin_graded (hg : IsGradedDiff deg D) :
    IsGradedDiff (fun a : MinIdx kind => deg a.1) (dmin D kind) := fun a b h => hg a.1 b.1 h

theorem dmin_sq (hS : SplitForm D kind partner) (hd : D * D = 0) :
    dmin D kind * dmin D kind = 0 := by
  refine Matrix.ext fun a c => ?_
  have h := congrFun (congrFun hd a.1) c.1
  rw [mul_apply, sum_subtype_of_zero (fun b => kind b = 0)] at h
  · simpa [dmin, mul_apply] using h
  · intro b hb
    have : D b c.1 = 0 := by
      by_contra h0
      exact hb (split_col_zero hS c.2 h0)
    simp [this]

theorem G1 (hS : SplitForm D kind partner) :
    (D * iotaM R kind : Matrix I (MinIdx kind) R) = iotaM R kind * dmin D kind := by
  refine Matrix.ext fun x a => ?_
  have lhs : (D * iotaM R kind : Matrix I (MinIdx kind) R) x a = D x a.1 := by
    rw [mul_apply, Finset.sum_eq_single a.1]
    · simp [iotaM]
    · intro z _ hz; simp [iotaM, hz]
    · intro h; exact absurd (Finset.mem_univ _) h
  have rhs : (iotaM R kind * dmin D kind : Matrix I (MinIdx kind) R) x a =
      if kind x = 0 then D x a.1 else 0 := by
    rw [mul_apply]
    by_cases hx : kind x = 0
    · rw [if_pos hx, Finset.sum_eq_single ⟨x, hx⟩]
      · simp [iotaM, dmin]
      · intro b _ hb
        have : x ≠ b.1 := fun h => hb (Subtype.ext h.symm)
        simp [iotaM, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      apply Finset.sum_eq_zero
      intro b _
      have : x ≠ b.1 := fun h => hx (h ▸ b.2)
      simp [iotaM, this]
  rw [lhs, rhs]
  split_ifs with hx
  · rfl
  · by_contra h
    exact hx (split_col_zero hS a.2 h)

theorem G2 (hS : SplitForm D kind partner) :
    (piM R kind * D : Matrix (MinIdx kind) I R) = dmin D kind * piM R kind := by
  refine Matrix.ext fun a y => ?_
  have lhs : (piM R kind * D : Matrix (MinIdx kind) I R) a y = D a.1 y := by
    rw [mul_apply, Finset.sum_eq_single a.1]
    · simp [piM]
    · intro z _ hz
      have : a.1 ≠ z := fun h => hz h.symm
      simp [piM, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have rhs : (dmin D kind * piM R kind : Matrix (MinIdx kind) I R) a y =
      if kind y = 0 then D a.1 y else 0 := by
    rw [mul_apply]
    by_cases hy : kind y = 0
    · rw [if_pos hy, Finset.sum_eq_single ⟨y, hy⟩]
      · simp [piM, dmin]
      · intro b _ hb
        have : b.1 ≠ y := fun h => hb (Subtype.ext h)
        simp [piM, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hy]
      apply Finset.sum_eq_zero
      intro b _
      have : b.1 ≠ y := fun h => hy (h ▸ b.2)
      simp [piM, this]
  rw [lhs, rhs]
  split_ifs with hy
  · rfl
  · by_contra h
    exact hy (split_row_zero hS a.2 h)

theorem G3 :
    (piM R kind * iotaM R kind : Matrix (MinIdx kind) (MinIdx kind) R) = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [mul_apply, Finset.sum_eq_single a.1]
  · by_cases hab : a = b
    · subst hab; simp [piM, iotaM]
    · have : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simp [piM, iotaM, this, one_apply_ne hab]
  · intro z _ hz
    have : a.1 ≠ z := fun h => hz h.symm
    simp [piM, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem HD_apply (hS : SplitForm D kind partner) (x y : I) :
    (hM R kind partner * D : Matrix I I R) x y = if kind x = 1 ∧ x = y then 1 else 0 := by
  obtain ⟨s1, s2, s3, -⟩ := hS
  rw [mul_apply]
  by_cases hx : kind x = 1
  · rw [Finset.sum_eq_single (partner x)]
    · have hk := s1 x hx
      simp only [hM, of_apply, hk.1, hk.2.1, and_self, if_true, one_mul]
      by_cases hxy : x = y
      · subst hxy; simp [hx, hk.2.2]
      · rw [if_neg (fun h => hxy h.2)]
        by_contra h0
        rcases s3 y (partner x) h0 with ⟨-, h2⟩ | ⟨hy1, h2⟩
        · rw [hk.1] at h2; exact absurd h2 (by decide)
        · apply hxy
          rw [← hk.2.1, h2, (s1 y hy1).2.1]
    · intro z _ hz
      simp only [hM, of_apply]
      rw [if_neg]
      · simp
      · rintro ⟨hz2, rfl⟩
        exact hz (s2 z hz2).2.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hx h.1)]
    apply Finset.sum_eq_zero
    intro z _
    simp only [hM, of_apply]
    rw [if_neg]
    · simp
    · rintro ⟨hz2, rfl⟩
      exact hx (s2 z hz2).1

theorem DH_apply (hS : SplitForm D kind partner) (x y : I) :
    (D * hM R kind partner : Matrix I I R) x y = if kind y = 2 ∧ x = y then 1 else 0 := by
  obtain ⟨s1, s2, s3, -⟩ := hS
  rw [mul_apply]
  by_cases hy : kind y = 2
  · rw [Finset.sum_eq_single (partner y)]
    · have hk := s2 y hy
      simp only [hM, of_apply, hy, true_and, if_true, mul_one]
      have hD1 : D y (partner y) = 1 := by
        have := (s1 (partner y) hk.1).2.2
        rwa [hk.2] at this
      by_cases hxy : x = y
      · subst hxy; simp [hD1]
      · rw [if_neg (by intro h; first | exact hxy h | exact hxy h.2)]
        by_contra h0
        rcases s3 (partner y) x h0 with ⟨h2, -⟩ | ⟨-, h2⟩
        · rw [hk.1] at h2; exact absurd h2 (by decide)
        · exact hxy (h2.trans hk.2)
    · intro z _ hz
      simp only [hM, of_apply]
      rw [if_neg]
      · simp
      · rintro ⟨-, rfl⟩
        exact hz rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hy h.1)]
    apply Finset.sum_eq_zero
    intro z _
    simp only [hM, of_apply]
    rw [if_neg]
    · simp
    · rintro ⟨hz2, -⟩
      exact hy hz2

theorem G4 (hS : SplitForm D kind partner) :
    (iotaM R kind * piM R kind : Matrix I I R) =
      (-hM R kind partner * D + D * -hM R kind partner + 1 : Matrix I I R) := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply,
    Matrix.neg_apply, HD_apply hS, DH_apply hS, one_apply]
  have hIP : (iotaM R kind * piM R kind : Matrix I I R) x y = if x = y ∧ kind x = 0 then 1 else 0 := by
    rw [mul_apply]
    by_cases hx : kind x = 0
    · rw [Finset.sum_eq_single ⟨x, hx⟩]
      · by_cases hxy : x = y
        · subst hxy; simp [iotaM, piM, hx]
        · simp [iotaM, piM, hxy]
      · intro b _ hb
        have : x ≠ b.1 := fun h => hb (Subtype.ext h.symm)
        simp [iotaM, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg (fun h => hx h.2)]
      apply Finset.sum_eq_zero
      intro b _
      have : x ≠ b.1 := fun h => hx (h ▸ b.2)
      simp [iotaM, this]
  rw [hIP]
  by_cases hxy : x = y
  · subst hxy
    have : kind x = 0 ∨ kind x = 1 ∨ kind x = 2 := by
      rcases kind x with ⟨k, hk⟩
      interval_cases k <;> simp
    rcases this with h | h | h <;> simp [h]
  · simp [hxy]

theorem hM_deg (hg : IsGradedDiff deg D) (hS : SplitForm D kind partner) (x y : I)
    (h : hM R kind partner x y ≠ 0) : deg x + 1 = deg y := by
  simp only [hM, of_apply] at h
  split_ifs at h with hc
  · obtain ⟨hy, rfl⟩ := hc
    have hk := hS.2.1 y hy
    have hD1 : D y (partner y) = 1 := by
      have := (hS.1 (partner y) hk.1).2.2
      rwa [hk.2] at this
    exact (hg y (partner y) (by rw [hD1]; exact one_ne_zero)).symm
  · exact absurd rfl h

/-- The inclusion of the minimal part as a chain map. -/
noncomputable def iotaHom (hg : IsGradedDiff deg D) (hd : D * D = 0)
    (hS : SplitForm D kind partner) :
    gradedComplex (fun a : MinIdx kind => deg a.1) (dmin D kind) (dmin_graded hg) (dmin_sq hS hd) ⟶
      gradedComplex deg D hg hd where
  f n := mat (blk deg (fun a : MinIdx kind => deg a.1) (iotaM R kind) n n)
  comm' i j _ := by
    change mat (blk deg (fun a : MinIdx kind => deg a.1) (iotaM R kind) i i) ≫
        mat (blk deg deg D j i) =
      mat (blk (fun a : MinIdx kind => deg a.1) (fun a : MinIdx kind => deg a.1) (dmin D kind) j i) ≫
        mat (blk deg (fun a : MinIdx kind => deg a.1) (iotaM R kind) j j)
    rw [mat_comp, mat_comp, ← blk_mul _ _ _ D (iotaM R kind) j i i (fun b c hc h => by
        simp only [iotaM, of_apply] at h; split_ifs at h with hb
        · rw [hb]; exact hc
        · exact absurd rfl h),
      ← blk_mul' _ _ _ (iotaM R kind) (dmin D kind) j j i (fun a b ha h => by
        simp only [iotaM, of_apply] at h; split_ifs at h with hb
        · rw [← hb]; exact ha
        · exact absurd rfl h), G1 hS]

/-- The projection onto the minimal part as a chain map. -/
noncomputable def piHom (hg : IsGradedDiff deg D) (hd : D * D = 0)
    (hS : SplitForm D kind partner) :
    gradedComplex deg D hg hd ⟶
      gradedComplex (fun a : MinIdx kind => deg a.1) (dmin D kind) (dmin_graded hg)
        (dmin_sq hS hd) where
  f n := mat (blk (fun a : MinIdx kind => deg a.1) deg (piM R kind) n n)
  comm' i j _ := by
    change mat (blk (fun a : MinIdx kind => deg a.1) deg (piM R kind) i i) ≫
        mat (blk (fun a : MinIdx kind => deg a.1) (fun a : MinIdx kind => deg a.1) (dmin D kind) j i) =
      mat (blk deg deg D j i) ≫ mat (blk (fun a : MinIdx kind => deg a.1) deg (piM R kind) j j)
    rw [mat_comp, mat_comp, ← blk_mul _ _ _ (dmin D kind) (piM R kind) j i i (fun b c hc h => by
        simp only [piM, of_apply] at h; split_ifs at h with hb
        · rw [hb]; exact hc
        · exact absurd rfl h),
      ← blk_mul' _ _ _ (piM R kind) D j j i (fun a b ha h => by
        simp only [piM, of_apply] at h; split_ifs at h with hb
        · rw [← hb]; exact ha
        · exact absurd rfl h), G2 hS]

/-- The contracting homotopy of the unit disks, `-H` in each degree. -/
noncomputable def diskHtpy (hg : IsGradedDiff deg D) (hd : D * D = 0) :
    ∀ i j, (gradedComplex deg D hg hd).X i ⟶ (gradedComplex deg D hg hd).X j :=
  fun i j => mat (blk deg deg (-hM R kind partner) j i)

/-- The homotopy equivalence between a complex in split form and its minimal part. -/
noncomputable def splitHomotopyEquiv (hg : IsGradedDiff deg D) (hd : D * D = 0)
    (hS : SplitForm D kind partner) :
    HomotopyEquiv
      (gradedComplex (fun a : MinIdx kind => deg a.1) (dmin D kind) (dmin_graded hg)
        (dmin_sq hS hd))
      (gradedComplex deg D hg hd) where
  hom := iotaHom hg hd hS
  inv := piHom hg hd hS
  homotopyHomInvId := Homotopy.ofEq (by
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    change mat (blk deg (fun a : MinIdx kind => deg a.1) (iotaM R kind) n n) ≫
      mat (blk (fun a : MinIdx kind => deg a.1) deg (piM R kind) n n) = 𝟙 _
    rw [mat_comp, ← blk_mul _ _ _ (piM R kind) (iotaM R kind) n n n (fun b c hc h => by
        simp only [iotaM, of_apply] at h; split_ifs at h with hb
        · rw [hb]; exact hc
        · exact absurd rfl h), G3, blk_one, mat_one])
  homotopyInvHomId :=
    { hom := diskHtpy hg hd
      zero := fun i j hij => by
        show mat (blk deg deg (-hM R kind partner) j i) = 0
        have : blk deg deg (-hM R kind partner : Matrix I I R) j i = 0 := by
          ext x y
          simp only [blk, submatrix_apply, Matrix.zero_apply, Matrix.neg_apply, neg_eq_zero]
          by_contra h
          have := hM_deg hg hS _ _ h
          rw [x.2, y.2] at this
          exact hij (by simp only [ComplexShape.up_Rel]; omega)
        rw [this, mat_zero]
      comm := fun i => by
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
        rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
        change mat (blk (fun a : MinIdx kind => deg a.1) deg (piM R kind) i i) ≫
            mat (blk deg (fun a : MinIdx kind => deg a.1) (iotaM R kind) i i) =
          mat (blk deg deg D (i + 1) i) ≫ mat (blk deg deg (-hM R kind partner) i (i + 1)) +
            mat (blk deg deg (-hM R kind partner) (i - 1) i) ≫ mat (blk deg deg D i (i - 1)) +
              𝟙 (gX R deg i)
        rw [mat_comp, mat_comp, mat_comp, ← mat_one, ← blk_one deg i,
          ← blk_mul _ _ _ (iotaM R kind) (piM R kind) i i i (fun b c hc h => by
            simp only [piM, of_apply] at h; split_ifs at h with hb
            · rw [← hb] at hc; exact hc
            · exact absurd rfl h),
          ← blk_mul _ _ _ (-hM R kind partner) D i (i + 1) i (fun b c hc h => by
            have := hg b c h; omega),
          ← blk_mul _ _ _ D (-hM R kind partner) i (i - 1) i (fun b c hc h => by
            have := hM_deg hg hS b c (by simpa using h); omega),
          ← mat_add, ← mat_add, ← blk_add, ← blk_add, G4 hS] }

/-- **Split form: the complex is homotopy equivalent to its minimal part** (tex L5404–5409:
"Decompose `D` over `Λ` into a minimal complex `D_min` and unit disks `E`"). If the graded
square-zero `D` is in split form over a local ring, its cochain complex is homotopy equivalent to the
cochain complex of the kind-`0` part, whose differential has image in `𝔪` (the minimality hypothesis
of `MinimalHomotopyEquivDegreewise`). Classification: PROVED. -/
def SplitFormHomotopyEquiv : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (D : Matrix I I R) (kind : I → Fin 3) (partner : I → I)
    (hg : IsGradedDiff deg D) (hd : D * D = 0) (hS : SplitForm D kind partner),
      Nonempty (HomotopyEquiv
        (gradedComplex (fun a : MinIdx kind => deg a.1) (dmin D kind) (dmin_graded hg)
          (dmin_sq hS hd))
        (gradedComplex deg D hg hd)) ∧
      ∀ i j x, ((gradedComplex (fun a : MinIdx kind => deg a.1) (dmin D kind) (dmin_graded hg)
        (dmin_sq hS hd)).d i j).hom x ∈
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (gX R (fun a : MinIdx kind => deg a.1) j))

/-- A vector all of whose coordinates lie in an ideal `𝔞` lies in `𝔞 • ⊤`. -/
theorem mem_smul_top_of_forall {ι : Type u} [Fintype ι] [DecidableEq ι] (𝔞 : Ideal R)
    (v : ι → R) (hv : ∀ b, v b ∈ 𝔞) : v ∈ 𝔞 • (⊤ : Submodule R (ι → R)) := by
  rw [pi_eq_sum_univ v]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem_smul (hv b) Submodule.mem_top

theorem splitFormHomotopyEquiv_proof : SplitFormHomotopyEquiv.{u} := by
  intro R _ _ I _ _ deg D kind partner hg hd hS
  refine ⟨⟨splitHomotopyEquiv hg hd hS⟩, fun i j x => ?_⟩
  rw [gradedComplex_d]
  apply mem_smul_top_of_forall
  intro b
  change (blk _ _ (dmin D kind) j i *ᵥ x) b ∈ _
  simp only [mulVec, dotProduct]
  exact Submodule.sum_mem _ fun a _ =>
    Ideal.mul_mem_right _ _ (hS.2.2.2 a.1.1 b.1.1 a.1.2 b.1.2)

end Split

/-- **Every bounded finite free complex over a local ring has a minimal model, as a Mathlib cochain
complex** (tex L5357–5359, L5404–5409). For a graded square-zero `d` over a local ring there are a
finite index type `J` with degrees and a graded square-zero `m` on `J` such that the cochain complex
of `d` is homotopy equivalent to that of `m`, the complex of `m` is minimal (differential into `𝔪`),
bounded by the same bounds, and finite free. Classification: PROVED. -/
def MinimalModelCochain : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d : Matrix I I R) (hg : IsGradedDiff deg d) (hd : d * d = 0),
      ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J) (degJ : J → ℤ) (m : Matrix J J R)
        (hgm : IsGradedDiff degJ m) (hm : m * m = 0),
        Nonempty (HomotopyEquiv (gradedComplex degJ m hgm hm) (gradedComplex deg d hg hd)) ∧
        (∀ a b, (∀ x, a ≤ deg x) → (∀ x, deg x ≤ b) → ∀ y, a ≤ degJ y ∧ degJ y ≤ b) ∧
        ∀ i j x, ((gradedComplex degJ m hgm hm).d i j).hom x ∈
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (gX R degJ j))

theorem minimalModelCochain_proof : MinimalModelCochain.{u} := by
  intro R _ _ I _ _ deg d hg hd
  obtain ⟨P, Q, kind, partner, hPQ, hQP, hP, hQ, hS⟩ := minimalModelSplit_proof R I deg d hg hd
  have hgD := IsGradedDiff.conj hP hg hQ
  have hdD := conj_sq_zero hQP hd
  obtain ⟨⟨e⟩, hmin⟩ := splitFormHomotopyEquiv_proof R I deg (P * d * Q) kind partner hgD hdD hS
  refine ⟨MinIdx kind, inferInstance, inferInstance, fun a => deg a.1, dmin (P * d * Q) kind,
    dmin_graded hgD, dmin_sq hS hdD,
    ⟨e.trans (HomotopyEquiv.ofIso (gradedIso deg d P Q hg hd hP hQ hPQ hQP).symm)⟩,
    fun a b ha hb y => ⟨ha y.1, hb y.1⟩, hmin⟩

/-- **Two minimal models of homotopy-equivalent complexes are degreewise isomorphic** (tex
L5409–5411): if the graded complexes of `d` and `d'` over a local ring are homotopy equivalent, and
`m`, `m'` are minimal graded complexes homotopy equivalent to them (as provided by
`MinimalModelCochain`), then every homotopy equivalence between the complexes of `m` and `m'` is
bijective in every degree, and one exists. Classification: PROVED (with
`MinimalHomotopyEquivDegreewise`). -/
def MinimalModelsDegreewiseIso : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (J J' : Type u) [Fintype J] [DecidableEq J]
    [Fintype J'] [DecidableEq J'] (degJ : J → ℤ) (degJ' : J' → ℤ) (m : Matrix J J R)
    (m' : Matrix J' J' R) (hgm : IsGradedDiff degJ m) (hm : m * m = 0)
    (hgm' : IsGradedDiff degJ' m') (hm' : m' * m' = 0) (a b : ℤ),
    (∀ y, a ≤ degJ y ∧ degJ y ≤ b) → (∀ y, a ≤ degJ' y ∧ degJ' y ≤ b) →
    (∀ i j x, ((gradedComplex degJ m hgm hm).d i j).hom x ∈
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (gX R degJ j))) →
    (∀ i j x, ((gradedComplex degJ' m' hgm' hm').d i j).hom x ∈
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (gX R degJ' j))) →
    ∀ (e : HomotopyEquiv (gradedComplex degJ m hgm hm) (gradedComplex degJ' m' hgm' hm')) (n : ℤ),
      Function.Bijective (e.hom.f n).hom

theorem minimalModelsDegreewiseIso_proof : MinimalModelsDegreewiseIso.{u} := by
  intro R _ _ J J' _ _ _ _ degJ degJ' m m' hgm hm hgm' hm' a b hJ hJ' hmin hmin' e n
  obtain ⟨h1, h2, h3, h4⟩ := gradedComplexBoundedFree_proof R J degJ m hgm hm a b
    (fun y => (hJ y).1) (fun y => (hJ y).2)
  obtain ⟨h1', h2', h3', h4'⟩ := gradedComplexBoundedFree_proof R J' degJ' m' hgm' hm' a b
    (fun y => (hJ' y).1) (fun y => (hJ' y).2)
  exact minimalHomotopyEquivDegreewise_proof R _ _ a b hmin hmin' e n

end ZInQ.Contrib.CloudB3RC53.MinimalComplexes
