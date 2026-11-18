import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Homogeneous

/-!
# Lane RC26 (round 3): the prism homotopy for homogeneous continuous cochains

Let `U` be a group acting on topological spaces `X` and `Y`, and let `φ ψ : X → Y` be continuous
`U`-equivariant maps. The pullbacks `φ^*, ψ^* : C^•_hom(U; Y, M) → C^•_hom(U; X, M)` of homogeneous
continuous cochains (`homMap`) are chain homotopic, via the classical **prism operator**
```text
(HΘ)(x₀, …, x_n) = Σ_{i=0}^{n} (−1)^i Θ(φx₀, …, φx_i, ψx_i, …, ψx_n)      (n + 2 arguments),
```
which satisfies `dH + Hd = ψ^* − φ^*`. In particular `φ^*` and `ψ^*` induce the same map on
cohomology. (Compare the standard argument that the homogeneous cochain complex computes
cohomology independently of the chosen resolution: Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, I §2; Nekovář, *Selmer complexes*, Astérisque 310, 8.1.)

* `prismVec φ ψ i x`: the vector `(φx₀, …, φx_i, ψx_i, …, ψx_n)`;
* `prism_sum_aux`: the purely combinatorial telescoping identity behind `dH + Hd = ψ^* − φ^*`;
* `prism_identity_zero`, `prism_identity_succ`: the prism identity for arbitrary functions
  `Θ : Y^{n+1} → M`;
* `homPrismLin`, `homPrismHom`: the prism operator on homogeneous continuous cochains;
* `homPrism`: the homotopy `ψ^* ≃ φ^*` (a Mathlib `Homotopy`), with `homPrism_hom_apply`;
* `homMap_homologyMap_eq`: `ψ^*` and `φ^*` agree on cohomology.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory Finset

universe u

/-! ### The combinatorial telescoping identity -/

section Combinatorics

/-- **The prism telescoping identity.** Let `a b : ℕ → ℕ → M` and `c : ℕ → M` satisfy the face
relations of the prism decomposition in degree `m`:
`a i j = b (i − 1) j` for `j < i ≤ m`, `a i i = c i` and `a i (i + 1) = c (i + 1)` for `i ≤ m`, and
`a i j = b i (j − 1)` for `i + 1 < j ≤ m + 1`. Then
`Σ_{i ≤ m} Σ_{j ≤ m+1} (−1)^{i+j} a i j + Σ_{j ≤ m} Σ_{i < m} (−1)^{i+j} b i j = c 0 − c (m + 1)`:
the off-junction terms cancel in pairs and the junction terms telescope. -/
theorem prism_sum_aux {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (a b : ℕ → ℕ → M) (c : ℕ → M) (m : ℕ)
    (h1 : ∀ i j, j < i → i ≤ m → a i j = b (i - 1) j)
    (h2 : ∀ i, i ≤ m → a i i = c i)
    (h3 : ∀ i, i ≤ m → a i (i + 1) = c (i + 1))
    (h4 : ∀ i j, i + 1 < j → j ≤ m + 1 → a i j = b i (j - 1)) :
    ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 2), (-1 : R) ^ (i + j) • a i j +
      ∑ j ∈ range (m + 1), ∑ i ∈ range m, (-1 : R) ^ (i + j) • b i j =
      c 0 - c (m + 1) := by
  have sgn : ∀ p : ℕ, (-1 : R) ^ (p + 1) = -(-1 : R) ^ p := fun p => by
    rw [pow_succ, mul_neg_one]
  induction m with
  | zero =>
    rw [sum_range_one, sum_range_one, range_zero, sum_empty, add_zero, sum_range_succ,
      sum_range_one, h2 0 le_rfl, h3 0 le_rfl, sgn, zero_add, pow_zero, one_smul, neg_smul,
      one_smul, sub_eq_add_neg]
  | succ m ih =>
    have ih' := ih (fun i j hji hi => h1 i j hji (by omega)) (fun i hi => h2 i (by omega))
      (fun i hi => h3 i (by omega)) (fun i j hij hj => h4 i j hij (by omega))
    have e1 : ∑ i ∈ range (m + 1 + 1), ∑ j ∈ range (m + 1 + 2), (-1 : R) ^ (i + j) • a i j =
        (∑ i ∈ range (m + 1), ∑ j ∈ range (m + 2), (-1 : R) ^ (i + j) • a i j) +
          ∑ i ∈ range (m + 1), (-1 : R) ^ (i + (m + 2)) • a i (m + 2) +
          (∑ j ∈ range (m + 1), (-1 : R) ^ (m + 1 + j) • a (m + 1) j +
            (-1 : R) ^ (m + 1 + (m + 1)) • a (m + 1) (m + 1) +
            (-1 : R) ^ (m + 1 + (m + 2)) • a (m + 1) (m + 2)) := by
      rw [sum_range_succ _ (m + 1)]
      conv_rhs => rw [← sum_add_distrib]
      congr 1
      · exact sum_congr rfl fun i _ => sum_range_succ _ _
      · rw [show m + 1 + 2 = m + 2 + 1 from rfl, sum_range_succ _ (m + 2),
          sum_range_succ _ (m + 1)]
    have e2 : ∑ j ∈ range (m + 1 + 1), ∑ i ∈ range (m + 1), (-1 : R) ^ (i + j) • b i j =
        (∑ j ∈ range (m + 1), ∑ i ∈ range m, (-1 : R) ^ (i + j) • b i j) +
          ∑ j ∈ range (m + 1), (-1 : R) ^ (m + j) • b m j +
          ∑ i ∈ range (m + 1), (-1 : R) ^ (i + (m + 1)) • b i (m + 1) := by
      rw [sum_range_succ _ (m + 1)]
      conv_rhs => rw [← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun j _ => sum_range_succ _ _
    have hA : ∑ i ∈ range (m + 1), (-1 : R) ^ (i + (m + 2)) • a i (m + 2) +
        ∑ i ∈ range (m + 1), (-1 : R) ^ (i + (m + 1)) • b i (m + 1) = 0 := by
      rw [← sum_add_distrib]
      refine sum_eq_zero fun i hi => ?_
      rw [mem_range] at hi
      rw [h4 i (m + 2) (by omega) le_rfl, show m + 2 - 1 = m + 1 by omega,
        show i + (m + 2) = i + (m + 1) + 1 by omega, sgn, neg_smul, neg_add_cancel]
    have hB : ∑ j ∈ range (m + 1), (-1 : R) ^ (m + 1 + j) • a (m + 1) j +
        ∑ j ∈ range (m + 1), (-1 : R) ^ (m + j) • b m j = 0 := by
      rw [← sum_add_distrib]
      refine sum_eq_zero fun j hj => ?_
      rw [mem_range] at hj
      rw [h1 (m + 1) j (by omega) le_rfl, show m + 1 - 1 = m by omega,
        show m + 1 + j = m + j + 1 by omega, sgn, neg_smul, neg_add_cancel]
    have hC : (-1 : R) ^ (m + 1 + (m + 1)) • a (m + 1) (m + 1) +
        (-1 : R) ^ (m + 1 + (m + 2)) • a (m + 1) (m + 2) = c (m + 1) - c (m + 1 + 1) := by
      rw [h2 (m + 1) le_rfl, h3 (m + 1) le_rfl,
        show m + 1 + (m + 2) = m + 1 + (m + 1) + 1 by omega, sgn, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_smul, neg_smul, one_smul, sub_eq_add_neg]
    rw [e1, e2]
    have key := congrArg₂ (· + ·) (congrArg₂ (· + ·) ih' hA) (congrArg₂ (· + ·) hB hC)
    simp only [add_zero, zero_add] at key
    rw [show c 0 - c (m + 1 + 1) = c 0 - c (m + 1) + (c (m + 1) - c (m + 1 + 1)) by abel, ← key]
    abel

/-- The face map `δ_p = Fin.succAbove p : [n − 1] → [n]` on underlying natural numbers:
`δ_p(i) = i` for `i < p` and `δ_p(i) = i + 1` otherwise. -/
theorem prism_val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < p then (i : ℕ) else i + 1 := by
  unfold Fin.succAbove
  by_cases h : (i : ℕ) < p
  · rw [ite_eq_left (show Fin.castSucc i < p from h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (show ¬ Fin.castSucc i < p from h), ite_eq_right h]
    rfl

/-- The degeneracy map `σ_p = Fin.predAbove p : [n] → [n − 1]` on underlying natural numbers:
`σ_p(i) = i − 1` for `p < i` and `σ_p(i) = i` otherwise. -/
theorem prism_val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    ((p.predAbove i : Fin n) : ℕ) = if (p : ℕ) < i then (i : ℕ) - 1 else i := by
  unfold Fin.predAbove
  by_cases h : (p : ℕ) < i
  · rw [dite_eq_left (show Fin.castSucc p < i from h), ite_eq_left h]
    rfl
  · rw [dite_eq_right (show ¬ Fin.castSucc p < i from h), ite_eq_right h]
    rfl

end Combinatorics

/-! ### Prism vectors and their faces -/

section PrismVectors

variable {X Y : Type u}

/-- **The prism vectors.** For `x = (x₀, …, x_n)` and `0 ≤ i ≤ n`,
`prismVec φ ψ i x = (φx₀, …, φx_i, ψx_i, …, ψx_n) ∈ Y^{n+2}`; its `j`-th entry is
`φ(x_{σ_i j})` for `j ≤ i` and `ψ(x_{σ_i j})` for `j > i`, where `σ_i = Fin.predAbove i`. -/
def prismVec (φ ψ : X → Y) {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → X) : Fin (n + 2) → Y :=
  fun j => if (j : ℕ) ≤ i then φ (x (i.predAbove j)) else ψ (x (i.predAbove j))

/-- **The junction vectors.** `juncVec φ ψ t x = (φx₀, …, φx_{t−1}, ψx_t, …, ψx_{n−1})`: the first
`t` entries are taken through `φ`, the remaining ones through `ψ`. -/
def juncVec (φ ψ : X → Y) {n : ℕ} (t : ℕ) (x : Fin n → X) : Fin n → Y :=
  fun l => if (l : ℕ) < t then φ (x l) else ψ (x l)

/-- **Face of a prism vector before the junction.** For `j < i`, deleting the `j`-th entry of
`prismVec φ ψ i x` gives the prism vector `prismVec φ ψ (i − 1)` of the face `x ∘ δ_j`. -/
theorem prismVec_comp_succAbove_of_lt (φ ψ : X → Y) {n : ℕ} (x : Fin (n + 2) → X)
    (i : Fin (n + 2)) (j : Fin (n + 3)) (i' : Fin (n + 1)) (j' : Fin (n + 2))
    (hji : (j : ℕ) < i) (hi : (i' : ℕ) + 1 = i) (hj : (j' : ℕ) = j) :
    prismVec φ ψ i x ∘ Fin.succAbove j = prismVec φ ψ i' (x ∘ Fin.succAbove j') := by
  funext l
  simp only [Function.comp_apply, prismVec]
  have hidx : i.predAbove (j.succAbove l) = j'.succAbove (i'.predAbove l) := by
    ext
    simp only [prism_val_succAbove, prism_val_predAbove]
    split_ifs <;> omega
  have hcond : ((j.succAbove l : ℕ) ≤ i) ↔ ((l : ℕ) ≤ i') := by
    simp only [prism_val_succAbove]
    split_ifs <;> omega
  rw [hidx]
  by_cases hc : (l : ℕ) ≤ i'
  · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc]
  · rw [ite_eq_right (mt hcond.mp hc), ite_eq_right hc]

/-- **Face of a prism vector after the junction.** For `i + 1 < j`, deleting the `j`-th entry of
`prismVec φ ψ i x` gives the prism vector `prismVec φ ψ i` of the face `x ∘ δ_{j−1}`. -/
theorem prismVec_comp_succAbove_of_gt (φ ψ : X → Y) {n : ℕ} (x : Fin (n + 2) → X)
    (i : Fin (n + 2)) (j : Fin (n + 3)) (i' : Fin (n + 1)) (j' : Fin (n + 2))
    (hij : (i : ℕ) + 1 < j) (hi : (i' : ℕ) = i) (hj : (j' : ℕ) + 1 = j) :
    prismVec φ ψ i x ∘ Fin.succAbove j = prismVec φ ψ i' (x ∘ Fin.succAbove j') := by
  funext l
  simp only [Function.comp_apply, prismVec]
  have hidx : i.predAbove (j.succAbove l) = j'.succAbove (i'.predAbove l) := by
    ext
    simp only [prism_val_succAbove, prism_val_predAbove]
    split_ifs <;> omega
  have hcond : ((j.succAbove l : ℕ) ≤ i) ↔ ((l : ℕ) ≤ i') := by
    simp only [prism_val_succAbove]
    split_ifs <;> omega
  rw [hidx]
  by_cases hc : (l : ℕ) ≤ i'
  · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc]
  · rw [ite_eq_right (mt hcond.mp hc), ite_eq_right hc]

/-- **The junction faces of a prism vector.** Deleting the entry `φx_i` (position `j = i`) or the
entry `ψx_i` (position `j = i + 1`) of `prismVec φ ψ i x` gives the junction vector
`juncVec φ ψ j x`. -/
theorem prismVec_comp_succAbove_junc (φ ψ : X → Y) {m : ℕ} (x : Fin (m + 1) → X)
    (i : Fin (m + 1)) (j : Fin (m + 2)) (h : (j : ℕ) = i ∨ (j : ℕ) = i + 1) :
    prismVec φ ψ i x ∘ Fin.succAbove j = juncVec φ ψ (j : ℕ) x := by
  funext l
  simp only [Function.comp_apply, prismVec, juncVec]
  have hidx : i.predAbove (j.succAbove l) = l := by
    ext
    simp only [prism_val_succAbove, prism_val_predAbove]
    split_ifs <;> omega
  have hcond : ((j.succAbove l : ℕ) ≤ i) ↔ ((l : ℕ) < j) := by
    simp only [prism_val_succAbove]
    split_ifs <;> omega
  rw [hidx]
  by_cases hc : (l : ℕ) < j
  · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc]
  · rw [ite_eq_right (mt hcond.mp hc), ite_eq_right hc]

/-- The junction vector with junction at `0` is `ψ ∘ x`. -/
theorem juncVec_zero (φ ψ : X → Y) {n : ℕ} (x : Fin n → X) : juncVec φ ψ 0 x = ψ ∘ x := by
  funext l
  simp [juncVec]

/-- The junction vector with junction at the end is `φ ∘ x`. -/
theorem juncVec_top (φ ψ : X → Y) {n : ℕ} (x : Fin n → X) : juncVec φ ψ n x = φ ∘ x := by
  funext l
  simp [juncVec, l.isLt]

variable {k : Type u} [CommRing k] {M : Type u} [AddCommGroup M] [Module k M]

/-- The values `Θ(prismVec φ ψ i x ∘ δ_j)` (faces of the prism vectors of `x ∈ X^{m+1}`),
indexed by natural numbers `i, j` and extended by zero outside `i ≤ m`, `j ≤ m + 1`. -/
def prismFaceA (φ ψ : X → Y) {m : ℕ} (Θ : (Fin (m + 1) → Y) → M) (x : Fin (m + 1) → X)
    (i j : ℕ) : M :=
  if h : i < m + 1 ∧ j < m + 2 then Θ (prismVec φ ψ ⟨i, h.1⟩ x ∘ Fin.succAbove ⟨j, h.2⟩) else 0

/-- The values `Θ(prismVec φ ψ i (x ∘ δ_j))` (prism vectors of the faces of `x ∈ X^{n+2}`),
indexed by natural numbers `i, j` and extended by zero outside `i ≤ n`, `j ≤ n + 1`. -/
def prismFaceB (φ ψ : X → Y) {n : ℕ} (Θ : (Fin (n + 2) → Y) → M) (x : Fin (n + 2) → X)
    (i j : ℕ) : M :=
  if h : i < n + 1 ∧ j < n + 2 then Θ (prismVec φ ψ ⟨i, h.1⟩ (x ∘ Fin.succAbove ⟨j, h.2⟩)) else 0

/-- **The prism identity in positive degree**, for an arbitrary function `Θ : Y^{n+2} → M`:
`H(dΘ)(x) + d(HΘ)(x) + Θ(φ ∘ x) = Θ(ψ ∘ x)` for `x ∈ X^{n+2}`, where
`(HΘ)(x) = Σ_i (−1)^i Θ(prismVec φ ψ i x)` and `(dΘ)(y) = Σ_j (−1)^j Θ(y ∘ δ_j)`. -/
theorem prism_identity_succ (φ ψ : X → Y) {n : ℕ} (Θ : (Fin (n + 2) → Y) → M)
    (x : Fin (n + 2) → X) :
    (∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) •
        ∑ j : Fin (n + 3), (-1 : k) ^ (j : ℕ) • Θ (prismVec φ ψ i x ∘ Fin.succAbove j)) +
      (∑ j : Fin (n + 2), (-1 : k) ^ (j : ℕ) •
        ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) • Θ (prismVec φ ψ i (x ∘ Fin.succAbove j))) +
      Θ (φ ∘ x) = Θ (ψ ∘ x) := by
  have h1 : ∀ i j, j < i → i ≤ n + 1 →
      prismFaceA φ ψ Θ x i j = prismFaceB φ ψ Θ x (i - 1) j := by
    intro i j hji hi
    rw [prismFaceA, prismFaceB,
      dite_eq_left (And.intro (show i < n + 1 + 1 by omega) (show j < n + 1 + 2 by omega)),
      dite_eq_left (And.intro (show i - 1 < n + 1 by omega) (show j < n + 2 by omega))]
    exact congrArg Θ (prismVec_comp_succAbove_of_lt φ ψ x _ _ _ _ hji
      (show i - 1 + 1 = i by omega) rfl)
  have h2 : ∀ i, i ≤ n + 1 → prismFaceA φ ψ Θ x i i = Θ (juncVec φ ψ i x) := by
    intro i hi
    rw [prismFaceA,
      dite_eq_left (And.intro (show i < n + 1 + 1 by omega) (show i < n + 1 + 2 by omega))]
    exact congrArg Θ (prismVec_comp_succAbove_junc φ ψ x _ _ (Or.inl rfl))
  have h3 : ∀ i, i ≤ n + 1 → prismFaceA φ ψ Θ x i (i + 1) = Θ (juncVec φ ψ (i + 1) x) := by
    intro i hi
    rw [prismFaceA,
      dite_eq_left (And.intro (show i < n + 1 + 1 by omega) (show i + 1 < n + 1 + 2 by omega))]
    exact congrArg Θ (prismVec_comp_succAbove_junc φ ψ x _ _ (Or.inr rfl))
  have h4 : ∀ i j, i + 1 < j → j ≤ n + 1 + 1 →
      prismFaceA φ ψ Θ x i j = prismFaceB φ ψ Θ x i (j - 1) := by
    intro i j hij hj
    rw [prismFaceA, prismFaceB,
      dite_eq_left (And.intro (show i < n + 1 + 1 by omega) (show j < n + 1 + 2 by omega)),
      dite_eq_left (And.intro (show i < n + 1 by omega) (show j - 1 < n + 2 by omega))]
    exact congrArg Θ (prismVec_comp_succAbove_of_gt φ ψ x _ _ _ _ hij rfl
      (show j - 1 + 1 = j by omega))
  have key := prism_sum_aux (R := k) (prismFaceA φ ψ Θ x) (prismFaceB φ ψ Θ x)
    (fun t => Θ (juncVec φ ψ t x)) (n + 1) h1 h2 h3 h4
  have eA : ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) •
      ∑ j : Fin (n + 3), (-1 : k) ^ (j : ℕ) • Θ (prismVec φ ψ i x ∘ Fin.succAbove j) =
      ∑ i ∈ range (n + 1 + 1), ∑ j ∈ range (n + 1 + 2),
        (-1 : k) ^ (i + j) • prismFaceA φ ψ Θ x i j := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ range (n + 1 + 2), (-1 : k) ^ (i + j) • prismFaceA φ ψ Θ x i j)]
    refine sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (-1 : k) ^ ((i : ℕ) + j) • prismFaceA φ ψ Θ x i j), smul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← pow_add, prismFaceA, dite_eq_left (And.intro i.isLt j.isLt)]
  have eB : ∑ j : Fin (n + 2), (-1 : k) ^ (j : ℕ) •
      ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) • Θ (prismVec φ ψ i (x ∘ Fin.succAbove j)) =
      ∑ j ∈ range (n + 1 + 1), ∑ i ∈ range (n + 1),
        (-1 : k) ^ (i + j) • prismFaceB φ ψ Θ x i j := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => ∑ i ∈ range (n + 1), (-1 : k) ^ (i + j) • prismFaceB φ ψ Θ x i j)]
    refine sum_congr rfl fun j _ => ?_
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => (-1 : k) ^ (i + (j : ℕ)) • prismFaceB φ ψ Θ x i j), smul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← pow_add, add_comm (j : ℕ), prismFaceB,
      dite_eq_left (And.intro i.isLt j.isLt)]
  rw [eA, eB, key, juncVec_zero, juncVec_top, sub_add_cancel]

/-- **The prism identity in degree zero**, for an arbitrary function `Θ : Y → M` (on `Y^1`):
`H(dΘ)(x₀) + Θ(φx₀) = Θ(ψx₀)`, i.e. `(dΘ)(φx₀, ψx₀) = Θ(ψx₀) − Θ(φx₀)`. -/
theorem prism_identity_zero (φ ψ : X → Y) (Θ : (Fin 1 → Y) → M) (x : Fin 1 → X) :
    (∑ i : Fin 1, (-1 : k) ^ (i : ℕ) •
        ∑ j : Fin 2, (-1 : k) ^ (j : ℕ) • Θ (prismVec φ ψ i x ∘ Fin.succAbove j)) +
      Θ (φ ∘ x) = Θ (ψ ∘ x) := by
  rw [Fin.sum_univ_one, Fin.sum_univ_two,
    prismVec_comp_succAbove_junc φ ψ x 0 0 (Or.inl rfl),
    prismVec_comp_succAbove_junc φ ψ x 0 1 (Or.inr rfl)]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [juncVec_zero, juncVec_top]
  abel

end PrismVectors

/-! ### The prism homotopy on homogeneous continuous cochains -/

section Homotopy

variable {k : Type u} [CommRing k] {U : Type u} [Group U] {X Y : Type u} [MulAction U X]
  [TopologicalSpace X] [MulAction U Y] [TopologicalSpace Y] {M : Type u} [AddCommGroup M]
  [Module k M] [DistribMulAction U M] [SMulCommClass U k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M]

/-- The prism vectors `x ↦ prismVec φ ψ i x` depend continuously on `x` when `φ, ψ` are
continuous. -/
theorem continuous_prismVec (φ ψ : X → Y) (hφ : Continuous φ) (hψ : Continuous ψ) {n : ℕ}
    (i : Fin (n + 1)) : Continuous (prismVec φ ψ i) :=
  continuous_pi fun _ => continuous_if_const _ (fun _ => hφ.comp (continuous_apply _))
    (fun _ => hψ.comp (continuous_apply _))

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The prism vectors are `U`-equivariant when `φ, ψ` are:
`prismVec φ ψ i (u • x) = u • prismVec φ ψ i x`. -/
theorem prismVec_smul (φ ψ : X → Y) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) {n : ℕ} (i : Fin (n + 1)) (u : U)
    (x : Fin (n + 1) → X) : prismVec φ ψ i (u • x) = u • prismVec φ ψ i x := by
  funext j
  simp only [prismVec, Pi.smul_apply]
  split_ifs
  · exact hφe u _
  · exact hψe u _

/-- **The prism operator** `H : C^{n+1}_hom(U; Y, M) → C^n_hom(U; X, M)`,
`(HΘ)(x₀, …, x_n) = Σ_{i=0}^{n} (−1)^i Θ(φx₀, …, φx_i, ψx_i, …, ψx_n)`; `HΘ` is again continuous
and `U`-equivariant. -/
def homPrismLin (φ ψ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x)
    (hψ : Continuous ψ) (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) :
    homCochain k U Y M (n + 1) →ₗ[k] homCochain k U X M n where
  toFun Θ := ⟨fun x => ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) • Θ.1 (prismVec φ ψ i x),
    continuous_finsetSum _ fun i _ =>
      (Θ.2.1.comp (continuous_prismVec φ ψ hφ hψ i)).const_smul _,
    fun u x => by
      simp only [prismVec_smul φ ψ hφe hψe, Θ.2.2, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (smul_comm u _ _).symm⟩
  map_add' Θ Θ' := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c Θ := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_comm c]

/-- The prism operator as a morphism `(C^•_hom(U; Y, M))^{n+1} ⟶ (C^•_hom(U; X, M))^n` of
`k`-modules. -/
def homPrismHom (φ ψ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x)
    (hψ : Continuous ψ) (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) :
    (homCx k U Y M).X (n + 1) ⟶ (homCx k U X M).X n :=
  ModuleCat.ofHom (homPrismLin φ ψ hφ hφe hψ hψe n)

/-- The explicit formula for the prism operator:
`(HΘ)(x) = Σ_i (−1)^i Θ(prismVec φ ψ i x)`. -/
theorem homPrismHom_apply (φ ψ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (hψ : Continuous ψ)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) (Θ : (homCx k U Y M).X (n + 1))
    (x : Fin (n + 1) → X) :
    (homEl k U X M ((homPrismHom φ ψ hφ hφe hψ hψe n).hom Θ)).1 x =
      ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) • (homEl k U Y M Θ).1 (prismVec φ ψ i x) :=
  rfl

/-- Two elements of `(C^•_hom(U; X, M))^n` agree if they agree pointwise on `X^{n+1}`. -/
theorem homCx_ext_of_apply {n : ℕ} {Θ Θ' : (homCx k U X M).X n}
    (h : ∀ x, (homEl k U X M Θ).1 x = (homEl k U X M Θ').1 x) : Θ = Θ' :=
  Subtype.ext (funext h)

/-- Sums in `(C^•_hom(U; X, M))^n` are computed pointwise. -/
theorem homEl_add_apply {n : ℕ} (Θ Θ' : (homCx k U X M).X n) (x : Fin (n + 1) → X) :
    (homEl k U X M (Θ + Θ')).1 x = (homEl k U X M Θ).1 x + (homEl k U X M Θ').1 x :=
  rfl

/-- The zero cochain vanishes pointwise. -/
theorem homEl_zero_apply {n : ℕ} (x : Fin (n + 1) → X) :
    (homEl k U X M (0 : (homCx k U X M).X n)).1 x = 0 :=
  rfl

/-- The components `h^{i,j} : (C^•_hom(U; Y, M))^i ⟶ (C^•_hom(U; X, M))^j` of the prism
homotopy: the prism operator when `i = j + 1`, and zero otherwise. -/
def homPrismFamily (φ ψ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (hψ : Continuous ψ)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (i j : ℕ) :
    (homCx k U Y M).X i ⟶ (homCx k U X M).X j :=
  if h : j + 1 = i then ((homCx k U Y M).XIsoOfEq h.symm).hom ≫ homPrismHom φ ψ hφ hφe hψ hψe j
  else 0

/-- The component `h^{n+1,n}` of the prism homotopy is the prism operator. -/
theorem homPrismFamily_succ (φ ψ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (hψ : Continuous ψ)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) :
    homPrismFamily (k := k) (M := M) φ ψ hφ hφe hψ hψe (n + 1) n =
      homPrismHom φ ψ hφ hφe hψ hψe n := by
  rw [homPrismFamily, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.id_comp]

/-- **The prism homotopy.** For continuous `U`-equivariant maps `φ ψ : X → Y`, the prism
operators form a homotopy between the pullbacks `ψ^*` and `φ^*` on homogeneous continuous
cochains: `ψ^* = dH + Hd + φ^*`. -/
def homPrism (φ ψ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x)
    (hψ : Continuous ψ) (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) :
    Homotopy (homMap (k := k) (M := M) ψ hψ hψe) (homMap φ hφ hφe) where
  hom := homPrismFamily φ ψ hφ hφe hψ hψe
  zero i j h := by
    rw [homPrismFamily, dite_eq_right (show ¬(j + 1 = i) from h)]
  comm i := by
    rcases i with _ | n
    · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
        homPrismFamily_succ]
      refine ModuleCat.hom_ext (LinearMap.ext fun Θ => homCx_ext_of_apply fun x => ?_)
      simp only [add_zero, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
        LinearMap.comp_apply, homEl_add_apply, homMap_f_apply, homPrismHom_apply, homCx_d_apply']
      exact (prism_identity_zero φ ψ (homEl k U Y M Θ).1 x).symm
    · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
        homPrismFamily_succ, homPrismFamily_succ]
      refine ModuleCat.hom_ext (LinearMap.ext fun Θ => homCx_ext_of_apply fun x => ?_)
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
        LinearMap.comp_apply, homEl_add_apply, homMap_f_apply, homPrismHom_apply,
        homCx_d_apply']
      exact (prism_identity_succ φ ψ (homEl k U Y M Θ).1 x).symm

/-- The component `h^{n+1,n}` of the prism homotopy is the prism operator `homPrismHom`. -/
theorem homPrism_hom_succ (φ ψ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (hψ : Continuous ψ)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) :
    (homPrism (k := k) (M := M) φ ψ hφ hφe hψ hψe).hom (n + 1) n =
      homPrismHom φ ψ hφ hφe hψ hψe n :=
  homPrismFamily_succ φ ψ hφ hφe hψ hψe n

/-- The degree-`n` component of the prism homotopy, explicitly:
`(HΘ)(x₀, …, x_n) = Σ_{i=0}^{n} (−1)^i Θ(φx₀, …, φx_i, ψx_i, …, ψx_n)`. -/
theorem homPrism_hom_apply (φ ψ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (hψ : Continuous ψ)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) (Θ : (homCx k U Y M).X (n + 1))
    (x : Fin (n + 1) → X) :
    (homEl k U X M (((homPrism φ ψ hφ hφe hψ hψe).hom (n + 1) n).hom Θ)).1 x =
      ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) • (homEl k U Y M Θ).1 (prismVec φ ψ i x) := by
  rw [homPrism_hom_succ, homPrismHom_apply]

/-- **Homotopic pullbacks agree on cohomology**: for continuous `U`-equivariant `φ ψ : X → Y`,
`ψ^* = φ^* : H^n(C^•_hom(U; Y, M)) → H^n(C^•_hom(U; X, M))`. -/
theorem homMap_homologyMap_eq (φ ψ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (hψ : Continuous ψ)
    (hψe : ∀ (u : U) (x : X), ψ (u • x) = u • ψ x) (n : ℕ) :
    HomologicalComplex.homologyMap (homMap (k := k) (M := M) ψ hψ hψe) n =
      HomologicalComplex.homologyMap (homMap φ hφ hφe) n :=
  (homPrism φ ψ hφ hφe hψ hψe).homologyMap_eq n

end Homotopy

end ZInQ.Manuscript.RC.SelmerComplex
