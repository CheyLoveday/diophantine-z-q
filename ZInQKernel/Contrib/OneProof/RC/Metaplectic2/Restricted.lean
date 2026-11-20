import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Spherical
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Comparison
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-! Algebraic restricted tensor action on the finite factors of tex
8996–9007. The tensor presentation and evaluation are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Filter Set OldStageLaw
open scoped Classical

/-- A pure family has the standard reference factor at almost all primes. -/
abbrev Elementary := RestrictedProduct (fun p => ↥(SchwartzBruhat p)) (fun p => {spherical p}) cofinite

def replace (f : Elementary) (p : Place) (v : SchwartzBruhat p) : Elementary :=
  ⟨Function.update f.1 p v, by
    filter_upwards [f.2, (finite_singleton p).compl_mem_cofinite] with q hq hne
    rwa [Function.update_of_ne (show q ≠ p from hne)]⟩

private abbrev FreeTensor := Elementary →₀ ℂ

private def symbol (f : Elementary) : FreeTensor := Finsupp.single f 1

private def relations : Set FreeTensor :=
  {u | ∃ (f : Elementary) (p : Place) (v w : SchwartzBruhat p),
    u = symbol (replace f p (v + w)) - symbol (replace f p v) - symbol (replace f p w)} ∪
  {u | ∃ (f : Elementary) (p : Place) (c : ℂ) (v : SchwartzBruhat p),
    u = symbol (replace f p (c • v)) - c • symbol (replace f p v)}

/-- The algebraic restricted tensor product: pure families modulo
linearity in each place, with the spherical vector as the tail. -/
def RestrictedTensor := FreeTensor ⧸ Submodule.span ℂ relations

instance : AddCommGroup RestrictedTensor := inferInstanceAs (AddCommGroup (FreeTensor ⧸ Submodule.span ℂ relations))
instance : Module ℂ RestrictedTensor := inferInstanceAs (Module ℂ (FreeTensor ⧸ Submodule.span ℂ relations))

def pure (f : Elementary) : RestrictedTensor := Submodule.Quotient.mk (symbol f)

theorem pure_add (f : Elementary) (p : Place) (v w : SchwartzBruhat p) :
    pure (replace f p (v + w)) = pure (replace f p v) + pure (replace f p w) := by
  apply sub_eq_zero.mp
  rw [← sub_sub]
  change (Submodule.span ℂ relations).mkQ
      (symbol (replace f p (v + w)) - symbol (replace f p v) - symbol (replace f p w)) = 0
  apply (Submodule.Quotient.mk_eq_zero (p := Submodule.span ℂ relations)).2
  exact
    (Submodule.subset_span (Or.inl ⟨f, p, v, w, rfl⟩))

theorem pure_smul (f : Elementary) (p : Place) (c : ℂ) (v : SchwartzBruhat p) :
    pure (replace f p (c • v)) = c • pure (replace f p v) := by
  apply sub_eq_zero.mp
  change (Submodule.span ℂ relations).mkQ
    (symbol (replace f p (c • v)) - c • symbol (replace f p v)) = 0
  apply (Submodule.Quotient.mk_eq_zero (p := Submodule.span ℂ relations)).2
  exact
    (Submodule.subset_span (Or.inr ⟨f, p, c, v, rfl⟩))

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Coordinate linearity is the universal property needed to descend a map. -/
def tensorLift (g : Elementary → V)
    (ha : ∀ f p v w, g (replace f p (v + w)) = g (replace f p v) + g (replace f p w))
    (hs : ∀ f p (c : ℂ) v, g (replace f p (c • v)) = c • g (replace f p v)) :
    RestrictedTensor →ₗ[ℂ] V :=
  (Submodule.span ℂ relations).liftQ (Finsupp.linearCombination ℂ g) (by
    apply Submodule.span_le.mpr
    rintro u (⟨f, p, v, w, rfl⟩ | ⟨f, p, c, v, rfl⟩)
    · simp [symbol, Finsupp.linearCombination_single, ha, add_sub_cancel_left]
    · simp [symbol, Finsupp.linearCombination_single, hs])

theorem tensorLift_pure (g : Elementary → V) (ha hs) (f : Elementary) :
    tensorLift g ha hs (pure f) = g f := by
  change Finsupp.linearCombination ℂ g (symbol f) = _
  simp [symbol, Finsupp.linearCombination_single]

theorem tensor_ext {A B : RestrictedTensor →ₗ[ℂ] V}
    (h : ∀ f, A (pure f) = B (pure f)) : A = B := by
  have he : A.comp (Submodule.span ℂ relations).mkQ = B.comp (Submodule.span ℂ relations).mkQ := by
    apply Finsupp.lhom_ext
    intro f c
    rw [← Finsupp.smul_single_one f c, map_smul, map_smul]
    exact congrArg (c • ·) (h f)
  exact (Submodule.span ℂ relations).quot_hom_ext A B (LinearMap.congr_fun he)

def stabilizes (p : Place) : Submonoid (Module.End ℂ (SchwartzBruhat p)) where
  carrier := {T | T (spherical p) = spherical p}
  one_mem' := rfl
  mul_mem' {T U} hT hU := by
    change T (spherical p) = _ at hT
    change U (spherical p) = _ at hU
    change T (U (spherical p)) = _
    rw [hU, hT]

/-- Tuples of local operators fixing the reference at almost every place. -/
abbrev RestrictedOperators :=
  RestrictedProduct (fun p => Module.End ℂ (SchwartzBruhat p)) (fun p => (stabilizes p : Set _)) cofinite

def actFamily (T : RestrictedOperators) (f : Elementary) : Elementary :=
  ⟨fun p => T p (f p), by
    filter_upwards [T.2, f.2] with p hT hf
    change f p = spherical p at hf
    change T p (f p) = spherical p
    rw [hf]
    exact hT⟩

private theorem actFamily_replace (T : RestrictedOperators) (f : Elementary) (p : Place)
    (v : SchwartzBruhat p) :
    actFamily T (replace f p v) = replace (actFamily T f) p (T p v) := by
  apply RestrictedProduct.ext
  intro q
  change T q (Function.update f p v q) = Function.update (fun i => T i (f i)) p (T p v) q
  by_cases h : q = p
  · subst q
    simp
  · simp [Function.update_of_ne h]

def act (T : RestrictedOperators) : Module.End ℂ RestrictedTensor :=
  tensorLift (fun f => pure (actFamily T f))
    (by intros; simp only [actFamily_replace, map_add, pure_add])
    (by intros; simp only [actFamily_replace, map_smul, pure_smul])

theorem act_pure (T : RestrictedOperators) (f : Elementary) :
    act T (pure f) = pure (actFamily T f) := tensorLift_pure _ _ _ _

/-- Multiplicative action, so group actions map here by composition. -/
def restrictedAction : RestrictedOperators →* Module.End ℂ RestrictedTensor where
  toFun := act
  map_one' := by
    apply tensor_ext
    intro f
    rw [act_pure]
    congr 1
  map_mul' T U := by
    apply tensor_ext
    intro f
    change act (T * U) (pure f) = act T (act U (pure f))
    simp only [act_pure]
    congr 1

private theorem integral_tail (x : FiniteVectors) :
    ∀ᶠ p in cofinite, atPlace p x ∈ localLattice p :=
  (Filter.eventually_all.mpr fun i : Fin 3 => (x i).2).mono
    fun _ hp i _ => hp i

def evaluateFamily (f : Elementary) (x : FiniteVectors) : ℂ :=
  ∏ᶠ p, (f p).1 (atPlace p x)

private theorem evaluation_finite (f : Elementary) (x : FiniteVectors) :
    (fun p => (f p).1 (atPlace p x)).HasFiniteMulSupport := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [f.2, integral_tail x] with p h hp
  change f p = spherical p at h
  rw [h, spherical_apply, ite_eq_left hp]

private theorem evaluate_replace (f : Elementary) (p : Place) (v : SchwartzBruhat p)
    (x : FiniteVectors) :
    evaluateFamily (replace f p v) x = v.1 (atPlace p x) *
      ∏ᶠ q ∈ {q | q ≠ p}, (f q).1 (atPlace q x) := by
  unfold evaluateFamily
  rw [← mul_finprod_cond_ne p (evaluation_finite (replace f p v) x)]
  change ((Function.update (⇑f) p v p).1 (atPlace p x)) * _ = _
  rw [Function.update_self]
  congr 1
  apply finprod_mem_congr rfl
  intro q hq
  change (Function.update (⇑f) p v q).1 (atPlace q x) = _
  rw [Function.update_of_ne (show q ≠ p from hq)]

/-- Evaluation on adèlic vectors extends the finite products on pure tensors. -/
def evaluate : RestrictedTensor →ₗ[ℂ] (FiniteVectors → ℂ) :=
  tensorLift evaluateFamily
    (fun f p v w => funext fun x => by
      simp only [evaluate_replace, Pi.add_apply]
      change (v.1 (atPlace p x) + w.1 (atPlace p x)) * _ = _
      rw [add_mul])
    (fun f p c v => funext fun x => by
      simp only [evaluate_replace, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_assoc])

theorem evaluate_pure (f : Elementary) (x : FiniteVectors) :
    evaluate (pure f) x = ∏ᶠ p, (f p).1 (atPlace p x) := by
  rw [evaluate, tensorLift_pure]
  rfl

theorem evaluate_act (T : RestrictedOperators) (f : Elementary) (x : FiniteVectors) :
    evaluate (restrictedAction T (pure f)) x = ∏ᶠ p, (T p (f p)).1 (atPlace p x) := by
  change evaluate (act T (pure f)) x = _
  rw [act_pure, evaluate_pure]
  rfl

variable (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]

def upperTuple (n : ℤ) : RestrictedOperators :=
  ⟨fun p => upperUnipotent a p (-(n : ℚ_[p.val])),
    .of_forall fun p => upper_spherical a p (neg_mem (intCast_mem _ _))⟩

def weylTuple : RestrictedOperators :=
  ⟨fun p => Metaplectic.weyl a p, by
    filter_upwards [((badPlaces (determinant a)).finite_toSet.union
      (Set.finite_singleton dyadicPlace)).compl_mem_cofinite] with p hp
    change p ∉ (↑(badPlaces (determinant a)) : Set Place) ∪ {dyadicPlace} at hp
    exact weyl_spherical a p (fun h => hp (Or.inr h)) (fun h => hp (Or.inl h))⟩

variable {a}

/-- The elementary cosets at an adèlic center have the prescribed tail. -/
def elementaryFamily (c : FiniteVectors) : Elementary :=
  ⟨fun p => elementaryCoset p (atPlace p c), by
    filter_upwards [integral_tail c] with p hp
    change elementaryCoset p (atPlace p c) = spherical p
    apply Subtype.ext
    funext x
    have hm : x - atPlace p c ∈ localLattice p ↔ x ∈ localLattice p := by
      rw [show localLattice p = (rectangle p 1 : Set (LocalVectors p)) by
        ext y
        simp [localLattice, mem_rectangle]]
      have hc : atPlace p c ∈ rectangle p 1 := by
        simpa [localLattice, mem_rectangle] using hp
      constructor
      · intro hx
        change x ∈ rectangle p 1
        simpa only [sub_add_cancel] using (rectangle p 1).add_mem hx hc
      · intro hx
        exact (rectangle p 1).sub_mem hx hc
    change localCoset p (atPlace p c) x = localCoset p 0 x
    simp [localCoset, Set.indicator_apply, hm]⟩

omit [∀ i, NeZero (2 * a i)] in
theorem elementary_grid (r : Grid a) (x : FiniteVectors) :
    evaluate (pure (elementaryFamily (center r))) x = cosetIndicator r x := by
  rw [evaluate_pure, cosetIndicator_tensor]
  rfl

omit [∀ i, NeZero (2 * a i)] in
/-- The first literal evaluation required by GeneratorTensorAction. -/
theorem restricted_upper (n : ℤ) (r : Grid a) (x : FiniteVectors) :
    evaluate (restrictedAction (upperTuple a n) (pure (elementaryFamily (center r)))) x =
      ∏ᶠ p, localUpper a p n (localCoset p (atPlace p (center r))) (atPlace p x) := by
  rw [evaluate_act]
  exact finprod_congr (fun p => upper_elementary a p n _ _)

/-- The second literal evaluation required by GeneratorTensorAction. -/
theorem restricted_weyl (r : Grid a) (y : FiniteVectors) :
    evaluate (restrictedAction (weylTuple a) (pure (elementaryFamily (center r)))) y =
      ∏ᶠ p, (gaussIndex a p : ℂ) *
        localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y) := by
  rw [evaluate_act]
  exact finprod_congr (fun p => weyl_elementary a p _ _)

#print axioms pure_add
#print axioms pure_smul
#print axioms tensorLift_pure
#print axioms tensor_ext
#print axioms actFamily_replace
#print axioms act_pure
#print axioms integral_tail
#print axioms evaluation_finite
#print axioms evaluate_replace
#print axioms evaluate_pure
#print axioms evaluate_act
#print axioms elementary_grid
#print axioms restricted_upper
#print axioms restricted_weyl

end ZInQ.Manuscript.RC.Metaplectic2
