import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Points
import Mathlib.GroupTheory.Coset.Card
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Two elementary counting lemmas for `|E(𝔽_{q²})|`

* `natCard_ker_sq_sub_one`: for an endomorphism `σ` of an abelian group with `σ − 1` surjective,
  `|ker(σ² − 1)| = |ker(σ − 1)| · |ker(σ + 1)|`. (`σ − 1` maps `ker(σ² − 1)` onto `ker(σ + 1)`:
  if `P − σP = Q` with `σQ = −Q`, then `σ²P = σP − σQ = P − Q + Q = P`; the kernel is `ker(σ − 1)`.)
* `natCard_quadratic_fix_add_anti`: over an algebraically closed field `K ⊇ F` with `F` finite of
  `q` elements, for `b, c ∈ F` the equation `y² + b y = c` has, counted together, exactly two
  solutions with `y^q = y` or `y^q = −y − b`: the roots are `y₀` and `−b − y₀`, and `y₀^q` is a
  root again.

Classification: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

section Group

variable {G : Type*} [AddCommGroup G]

/-- **`|ker(σ² − 1)| = |ker(σ − 1)| · |ker(σ + 1)|`** when `σ − 1` is surjective. PROVED. -/
theorem natCard_ker_sq_sub_one (σ : G →+ G) (hs : Function.Surjective (σ - AddMonoidHom.id G)) :
    Nat.card (σ.comp σ - AddMonoidHom.id G).ker =
      Nat.card (σ - AddMonoidHom.id G).ker * Nat.card (σ + AddMonoidHom.id G).ker := by
  set S := (σ.comp σ - AddMonoidHom.id G).ker
  let φ : S →+ G := (σ - AddMonoidHom.id G).comp S.subtype
  have hrange : ∀ Q : G, Q ∈ φ.range ↔ Q ∈ (σ + AddMonoidHom.id G).ker := by
    intro Q
    simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, AddMonoidHom.add_apply,
      AddMonoidHom.id_apply]
    constructor
    · rintro ⟨⟨P, hP⟩, rfl⟩
      simp only [S, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, sub_eq_zero] at hP
      simp only [φ, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, AddMonoidHom.sub_apply,
        AddMonoidHom.id_apply, map_sub, hP]
      abel
    · intro hQ
      obtain ⟨P, hP⟩ := hs Q
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply] at hP
      refine ⟨⟨P, ?_⟩, hP⟩
      simp only [S, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply]
      have h1 : σ P = Q + P := by rw [← hP]; abel
      rw [h1, map_add, eq_neg_of_add_eq_zero_left hQ, h1]
      abel
  have hker : ∀ P : S, P ∈ φ.ker ↔ (P : G) ∈ (σ - AddMonoidHom.id G).ker := fun P => Iff.rfl
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  congr 1
  · refine Nat.card_congr
      ((Equiv.subtypeEquivRight hker).trans ?_)
    refine
      { toFun := fun P => ⟨P.1.1, P.2⟩
        invFun := fun P => ⟨⟨P.1, ?_⟩, P.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have h := P.2
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      sub_eq_zero] at h
    simp only [S, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, h, sub_self]
  · exact Nat.card_congr (Equiv.subtypeEquivRight hrange)

end Group

section Quadratic

variable {F : Type*} [Field F] [Fintype F] {K : Type*} [Field K] (f : F →+* K)

/-- The roots of `y² + b y = c` are `y₀` and `−b − y₀`, for any root `y₀`. PROVED. -/
theorem quadratic_iff {b c y₀ : K} (h₀ : y₀ ^ 2 + b * y₀ = c) (y : K) :
    y ^ 2 + b * y = c ↔ y = y₀ ∨ y = -b - y₀ := by
  have e : y ^ 2 + b * y - c = (y - y₀) * (y - (-b - y₀)) := by rw [← h₀]; ring
  rw [← sub_eq_zero, e, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- **Two solutions in total.** PROVED. -/
theorem natCard_quadratic_fix_add_anti [IsAlgClosed K] {b c : K} (hb : powHom f b = b)
    (hc : powHom f c = c) :
    Nat.card {y : K // y ^ 2 + b * y = c ∧ powHom f y = y} +
      Nat.card {y : K // y ^ 2 + b * y = c ∧ powHom f y = -y - b} = 2 := by
  classical
  obtain ⟨y₀, h₀⟩ : ∃ y₀ : K, y₀ ^ 2 + b * y₀ = c := by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
      (Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C (-c))
      (by rw [Polynomial.degree_quadratic one_ne_zero]; norm_num)
    refine ⟨y, ?_⟩
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hy
    linear_combination hy
  set y₁ := -b - y₀ with hy₁
  have hz : powHom f y₀ = y₀ ∨ powHom f y₀ = y₁ := by
    rw [← quadratic_iff h₀]
    have := congrArg (powHom f) h₀
    rwa [map_add, map_mul, map_pow, hb, hc] at this
  have hz1 : powHom f y₁ = -b - powHom f y₀ := by rw [hy₁, map_sub, map_neg, hb]
  have key : ∀ Q : K → Prop, Nat.card {y : K // y ^ 2 + b * y = c ∧ Q y} =
      (({y₀, y₁} : Finset K).filter Q).card := by
    intro Q
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [quadratic_iff h₀, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  rw [key, key]
  by_cases he : y₀ = y₁
  · have hz' : powHom f y₀ = y₀ := by rcases hz with h | h <;> [exact h; rw [h, ← he]]
    rw [← he, Finset.pair_eq_singleton, Finset.filter_singleton, Finset.filter_singleton,
      ite_eq_left hz', ite_eq_left (by rw [hz']; linear_combination he)]
    rfl
  · rcases hz with h | h
    · rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
        Finset.filter_singleton, ite_eq_left h, ite_eq_left (by rw [hz1, h]),
        ite_eq_right (by rw [h]; intro h'; exact he (by linear_combination h')),
        ite_eq_right (by rw [hz1, h]; intro h'; exact he (by linear_combination -h'))]
      simp [Finset.card_insert_of_notMem, he]
    · rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
        Finset.filter_singleton, ite_eq_right (by rw [h]; exact Ne.symm he),
        ite_eq_right (by rw [hz1, h]; intro h'; exact he (by linear_combination h')),
        ite_eq_left (by rw [h, hy₁]; ring), ite_eq_left (by rw [hz1, h, hy₁]; ring)]
      simp [Finset.card_insert_of_notMem, he]

/-- The solutions of `y² + b y = c` satisfying any condition form a finite set. PROVED. -/
theorem finite_quadratic (b c : K) (Q : K → Prop) : Finite {y : K // y ^ 2 + b * y = c ∧ Q y} := by
  classical
  set p := Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C (-c)
  have hp : p ≠ 0 := by
    intro h
    have := Polynomial.degree_quadratic (one_ne_zero (α := K)) (b := b) (c := -c)
    change p.degree = 2 at this
    rw [h, Polynomial.degree_zero] at this
    exact absurd this (by decide)
  refine Finite.of_injective (β := p.roots.toFinset)
    (fun y => ⟨y.1, ?_⟩) (fun y y' h => Subtype.ext (congrArg Subtype.val h :))
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  linear_combination y.2.1

end Quadratic

end ZInQ.Contrib.CloudB3RC53.Frobenius
