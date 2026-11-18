/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Lie.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.Prod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Algebra.Valued.WithVal
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.DifferentialLine
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.IsogenyScalar
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.ConstantField
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Different.Basic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Different.Complementary
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Different.Divisor
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Different.Tame
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Differential.Cotrace
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Differential.Dimension
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Differential.Kaehler
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Differential.LocalComponent
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Differential.LocalOrder
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.GeometricDegree
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Approximation
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Basic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Degree
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Existence
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Tower
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Filtration
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import ZInQKernel.Contrib.TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import ZInQKernel.Contrib.TauCeti.FieldTheory.RatFunc.Transcendental
import ZInQKernel.Contrib.TauCeti.RingTheory.Algebraic.Basic
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.Different.Basic
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.Different.Derivative
import ZInQKernel.Contrib.TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Residue comparison for rational function fields of one variable

The differential comparison and residue proofs are ported from the public Tau Ceti
source at revision `5a01f5fe3621`, Apache-2.0. Each section records its original module
and source digest. Imported statements are reused. Module boundaries and documentation
are adapted; the monogenic lemma is renamed to avoid duplicating an existing source.
Namespace and minor API adaptations for the pinned Mathlib revision are recorded in
the proof receipt. No literature assertion is substituted for a proof.

Upstream Mathlib: `ccbef15ebdb41c2addfac682131f83c75904c3c1`.
The proofs are checked against the repository's pinned Mathlib revision.
-/

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
open scoped _root_.IntermediateField


/-! ## Source 1: `TauCeti.Algebra.BigOperators.Finset.Pairs`
Original source SHA256: `0f499393f81a24c8f23ba39bc5387d11e034a03758f0350d12a71b617b7f91a7`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Sums and products over pairs

A sum of `F : l × l → M` over all ordered pairs, for `l` a finite linear order, can be folded onto
the increasing pairs by adding each term to its transpose. When `F` vanishes on the diagonal the
diagonal contributes nothing and the fold is exact, which is
`TauCeti.sum_univ_prod_eq_sum_lt_add_swap`.

This is the shape a sum indexed by unordered pairs takes once the linear order is used to name each
pair by its increasing representative. It is what lets an antisymmetric summand, for which the two
terms of a transposed pair combine, be summed over pairs rather than over ordered pairs.

For a symmetric summand the increasing representative carries no information beyond the unordered
pair, so a product `∏_{i<j} f i j` over the increasing pairs is unchanged when the indices are
permuted, which is `TauCeti.prod_prod_Ioi_comp_perm`. This is the symmetric counterpart of
Mathlib's `Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod`, where an antisymmetric summand picks up the
sign of the permutation.

## Main results

* `TauCeti.sum_univ_prod_eq_sum_lt_add_swap`: a sum over all ordered pairs of a function vanishing
  on the diagonal, as a sum over the increasing pairs of the term plus its transpose.
* `TauCeti.prod_prod_Ioi_comp_perm`: a product of a symmetric function over the increasing pairs is
  invariant under permuting the indices.
* `TauCeti.prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag`: a product over weakly increasing
  pairs separates into the strictly increasing pairs and the diagonal.
* `TauCeti.prod_prod_Ioi_eq_of_two`: separates the first pair and its cross terms from a product
  over the increasing pairs of a finite ordinal.
* `TauCeti.prod_prod_Ioi_three` and `TauCeti.prod_prod_Ioi_four`: the products over the increasing
  pairs of `Fin 3` and of `Fin 4`, written out.
* `TauCeti.prod_prod_Ioi_snoc`: splits the pair product of a tuple with a final entry.
* `TauCeti.prod_prod_Ioi_append`: the pair product of appended tuples splits into the pair
  products of each tuple and their cross terms.
* `TauCeti.prod_prod_Ioi_append_of_mul`: the cross term for a bimultiplicative pairing
  is the pairing of the products.
* `TauCeti.sum_sum_Ioi_append_of_mul`: the same for a pairing turning products into sums.
* `TauCeti.prod_prod_Ioi_scale`: scaling all entries of a pair product for a symmetric
  bimultiplicative pairing.
-/

section
namespace TauCeti

open Finset

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:64` (proof source at `5a01f5fe3621`).
 A sum over bounded pairs of indices of total degree less than the bound equals the
antidiagonal sum, provided the summands agree under the natural-index coercions. -/
theorem sum_fin_product_eq_sum_antidiagonal {M : Type*} [AddCommMonoid M] {n d : ℕ}
    (hd : d < n) (f : Fin n × Fin n → M) (g : ℕ × ℕ → M)
    (hfg : ∀ l, (l.1 : ℕ) + (l.2 : ℕ) = d → f l = g (l.1, l.2)) :
    (∑ l : Fin n × Fin n with (l.1 : ℕ) + (l.2 : ℕ) = d, f l) =
      ∑ l ∈ antidiagonal d, g l := by
  classical
  refine Finset.sum_bij (fun l _ ↦ ((l.1 : ℕ), (l.2 : ℕ))) ?_ ?_ ?_ ?_
  · intro l hl
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hl).2
  · intro l _ m _ hlm
    exact Prod.ext (Fin.ext (Prod.mk.inj hlm).1) (Fin.ext (Prod.mk.inj hlm).2)
  · intro l hl
    have hl' := Finset.HasAntidiagonal.mem_antidiagonal.mp hl
    refine ⟨(⟨l.1, by omega⟩, ⟨l.2, by omega⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hl'
  · intro l hl
    exact hfg l (Finset.mem_filter.mp hl).2

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:85` (proof source at `5a01f5fe3621`).
 A product over weakly increasing pairs splits into the strictly increasing pairs and the
diagonal. -/
theorem prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag
    {ι M : Type*} [PartialOrder ι] [Fintype ι]
    [LocallyFiniteOrderTop ι] [CommMonoid M] (f : ι → ι → M) :
    (∏ i, ∏ j ∈ Ici i, f i j) = (∏ i, ∏ j ∈ Ioi i, f i j) * ∏ i, f i i := by
  calc
    (∏ i, ∏ j ∈ Ici i, f i j) = ∏ i, (f i i * ∏ j ∈ Ioi i, f i j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (mul_prod_Ioi_eq_prod_Ici (f := f i) i).symm
    _ = _ := by rw [prod_mul_distrib, mul_comm]

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:97` (proof source at `5a01f5fe3621`).
 Peel the first two indices off a product over the increasing pairs of `Fin (m + 2)`. -/
theorem prod_prod_Ioi_eq_of_two {M : Type*} [CommMonoid M] {m : ℕ}
    (f : Fin (m + 2) → Fin (m + 2) → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j =
      f 0 1 * ((∏ k : Fin m, f 0 k.succ.succ) * ∏ k : Fin m, f 1 k.succ.succ) *
        ∏ i : Fin m, ∏ j ∈ Ioi i, f i.succ.succ j.succ.succ := by
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Fin.succ_zero_eq_one]
  ac_rfl

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:106` (proof source at `5a01f5fe3621`).
 The product over the three increasing pairs of `Fin 3`. -/
theorem prod_prod_Ioi_three {M : Type*} [CommMonoid M] (f : Fin 3 → Fin 3 → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j = f 0 1 * f 0 2 * f 1 2 := by
  simp [Fin.prod_univ_succ, Fin.prod_Ioi_succ, mul_assoc]

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:111` (proof source at `5a01f5fe3621`).
 The product over the six increasing pairs of `Fin 4`. -/
theorem prod_prod_Ioi_four {M : Type*} [CommMonoid M] (f : Fin 4 → Fin 4 → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j = f 0 1 * f 0 2 * f 0 3 * f 1 2 * f 1 3 * f 2 3 := by
  simp [Fin.prod_univ_succ, Fin.prod_Ioi_succ, mul_assoc]

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:117` (proof source at `5a01f5fe3621`).
 A pair product on a tuple extended by a final entry splits into the old pairs and the
pairings with that entry. -/
theorem prod_prod_Ioi_snoc {A M : Type*} [CommMonoid M] {n : ℕ}
    (f : A → A → M) (w : Fin n → A) (a : A) :
    (∏ i : Fin (n + 1), ∏ j ∈ (Ioi i : Finset (Fin (n + 1))),
      f (Fin.snoc (α := fun _ => A) w a i) (Fin.snoc (α := fun _ => A) w a j)) =
      (∏ i : Fin n, ∏ j ∈ Ioi i, f (w i) (w j)) *
        (∏ i : Fin n, f (w i) a) := by
  have hIoi (i : Fin n) :
      (Ioi i.castSucc : Finset (Fin (n + 1))) =
        insert (Fin.last n) ((Ioi i).map Fin.castSuccEmb) := by
    ext j
    rcases j.eq_castSucc_or_eq_last with ⟨k, rfl⟩ | rfl
    · simp [Fin.le_last]
    · simp
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [hIoi]
  have hlast (i : Fin n) : Fin.last n ∉ (Ioi i).map Fin.castSuccEmb := by simp
  simp_rw [Finset.prod_insert (hlast _), Finset.prod_map]
  simp [Fin.snoc_castSucc, Fin.top_eq_last, Fin.snoc_last,
    Finset.prod_mul_distrib, mul_comm]

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:140` (proof source at `5a01f5fe3621`).
 The pair product of concatenated tuples is the product over pairs in each tuple and over
all pairs with one entry in each tuple. -/
theorem prod_prod_Ioi_append {A M : Type*} [CommMonoid M] {n m : ℕ}
    (f : A → A → M) (w : Fin n → A) (v : Fin m → A) :
    (∏ i : Fin (n + m), ∏ j ∈ Ioi i, f (Fin.append w v i) (Fin.append w v j)) =
      (∏ i : Fin n, ∏ j ∈ Ioi i, f (w i) (w j)) *
      (∏ i : Fin m, ∏ j ∈ Ioi i, f (v i) (v j)) *
      (∏ i : Fin n, ∏ j : Fin m, f (w i) (v j)) := by
  induction m with
  | zero =>
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst v
    simp
  | succ m ih =>
    let v₀ := Fin.init v
    let b := v (Fin.last m)
    have hv : v = Fin.snoc v₀ b := (Fin.snoc_init_self v).symm
    rw [hv, Fin.append_snoc]
    -- `Nat.add_succ` makes `n + (m + 1)` and `(n + m) + 1` definitionally equal here.
    -- The remaining `change` exposes the `Fin.snoc` expression used by the snoc lemma.
    change (∏ i : Fin ((n + m) + 1), ∏ j ∈ Ioi i,
      f (Fin.snoc (α := fun _ => A) (Fin.append w v₀) b i)
        (Fin.snoc (α := fun _ => A) (Fin.append w v₀) b j)) = _
    rw [prod_prod_Ioi_snoc f (Fin.append w v₀) b]
    rw [prod_prod_Ioi_snoc f v₀ b, ih v₀]
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have hcross : (∏ i : Fin (n + m), f (Fin.append w v₀ i) b) =
        (∏ i : Fin n, f (w i) b) * ∏ i : Fin m, f (v₀ i) b := by
      rw [Fin.prod_univ_add]
      simp
    rw [hcross]
    simp only [Finset.prod_mul_distrib]
    ac_rfl

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:173` (proof source at `5a01f5fe3621`).
 The pairwise product of a concatenation for a bimultiplicative pairing. -/
theorem prod_prod_Ioi_append_of_mul {A M : Type*} [CommMonoid A] [CommMonoid M] (F : A → A → M)
    (hone_left : ∀ b, F 1 b = 1) (hone_right : ∀ a, F a 1 = 1)
    (hmul_left : ∀ a b c, F (a * b) c = F a c * F b c)
    (hmul_right : ∀ a b c, F a (b * c) = F a b * F a c)
    {m n : ℕ} (p : Fin m → A) (q : Fin n → A) :
    (∏ i, ∏ j ∈ Ioi i, F (Fin.append p q i) (Fin.append p q j)) =
      (∏ i, ∏ j ∈ Ioi i, F (p i) (p j)) *
        (∏ i, ∏ j ∈ Ioi i, F (q i) (q j)) *
        F (∏ i, p i) (∏ j, q j) := by
  let h₁ (a : A) : A →* M := {
    toFun := F a
    map_one' := hone_right a
    map_mul' := hmul_right a }
  let h₂ (b : A) : A →* M := {
    toFun := fun a => F a b
    map_one' := hone_left b
    map_mul' := fun a c => hmul_left a c b }
  rw [prod_prod_Ioi_append]
  congr 1
  calc
    (∏ i, ∏ j, F (p i) (q j)) = ∏ i, F (p i) (∏ j, q j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (map_prod (h₁ (p i)) q Finset.univ).symm
    _ = F (∏ i, p i) (∏ j, q j) :=
      (map_prod (h₂ (∏ j, q j)) p Finset.univ).symm

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:202` (proof source at `5a01f5fe3621`).
 The pairwise sum of a concatenation for a pairing that turns products in either argument into
sums. -/
theorem sum_sum_Ioi_append_of_mul {A M : Type*} [CommMonoid A] [AddCommMonoid M] (F : A → A → M)
    (hone_left : ∀ b, F 1 b = 0) (hone_right : ∀ a, F a 1 = 0)
    (hmul_left : ∀ a b c, F (a * b) c = F a c + F b c)
    (hmul_right : ∀ a b c, F a (b * c) = F a b + F a c)
    {m n : ℕ} (p : Fin m → A) (q : Fin n → A) :
    (∑ i, ∑ j ∈ Ioi i, F (Fin.append p q i) (Fin.append p q j)) =
      (∑ i, ∑ j ∈ Ioi i, F (p i) (p j)) +
        (∑ i, ∑ j ∈ Ioi i, F (q i) (q j)) +
        F (∏ i, p i) (∏ j, q j) := by
  apply Multiplicative.ofAdd.injective
  simpa only [ofAdd_add, ofAdd_sum] using prod_prod_Ioi_append_of_mul
    (fun a b => Multiplicative.ofAdd (F a b))
    (fun b => by rw [hone_left, ofAdd_zero]) (fun a => by rw [hone_right, ofAdd_zero])
    (fun a b c => by rw [hmul_left, ofAdd_add]) (fun a b c => by rw [hmul_right, ofAdd_add]) p q

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:219` (proof source at `5a01f5fe3621`).
 Scaling every coefficient in a pairwise product for a symmetric bimultiplicative
pairing. The self-pairing law supplies the correction for each coefficient pair. -/
theorem prod_prod_Ioi_scale {A M : Type*} [CommMonoid A] [CommMonoid M] (F : A → A → M)
    {s : A}
    (hmul_right : ∀ a b c, F a (b * c) = F a b * F a c)
    (hcomm : ∀ a b, F a b = F b a) (a : A) (hself : F a a = F a s)
    {n : ℕ} (w : Fin n → A) :
    (∏ i, ∏ j ∈ Ioi i, F (a * w i) (a * w j)) =
      (∏ i, ∏ j ∈ Ioi i, F (w i) (w j)) *
        F a s ^ n.choose 2 * F a (∏ i, w i) ^ (n - 1) := by
  have hmul_left (x y z : A) : F (x * y) z = F x z * F y z := by
    rw [hcomm (x * y) z, hmul_right, hcomm z x, hcomm z y]
  have hmulmul (b c : A) :
      F (a * b) (a * c) = F b c * F a s * F a b * F a c := by
    rw [hmul_left, hmul_right, hmul_right, hself, hcomm b a]
    ac_rfl
  have hprod_nonempty {k : ℕ} (v : Fin (k + 1) → A) :
      (∏ i, F a (v i)) = F a (∏ i, v i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (∏ i, F a (v i)) = F a (v 0) * ∏ i : Fin (k + 1), F a (v i.succ) :=
          Fin.prod_univ_succ _
        _ = F a (v 0) * F a (∏ i : Fin (k + 1), v i.succ) :=
          congrArg (F a (v 0) * ·) (ih (fun i => v i.succ))
        _ = F a (∏ i, v i) := by rw [Fin.prod_univ_succ v, hmul_right]
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      let w₀ := Fin.init w
      let b := w (Fin.last (n + 1))
      have hw : w = Fin.snoc w₀ b := (Fin.snoc_init_self w).symm
      rw [hw]
      have hs (i : Fin ((n + 1) + 1)) :
          a * Fin.snoc (α := fun _ => A) w₀ b i =
            Fin.snoc (α := fun _ => A) (fun j => a * w₀ j) (a * b) i := by
        rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl <;> simp
      simp_rw [hs]
      have hprod : (∏ i, F a (w₀ i)) = F a (∏ i, w₀ i) :=
        hprod_nonempty w₀
      have hchoose : ((n + 1) + 1).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      rw [prod_prod_Ioi_snoc F (fun j => a * w₀ j) (a * b),
        prod_prod_Ioi_snoc F w₀ b, ih w₀, Fin.prod_snoc, Nat.add_sub_cancel]
      simp_rw [hmulmul]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        hprod, hmul_right, mul_pow, hchoose, pow_add]
      rw [Nat.add_sub_cancel, pow_succ (F a (∏ i, w₀ i)) n,
        pow_succ (F a b) n]
      simp only [pow_one]
      ac_nf

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:276` (proof source at `5a01f5fe3621`).
 **A sum over all ordered pairs, folded onto the increasing ones.** A function vanishing on the
diagonal sums over `l × l` to the sum over the increasing pairs of its value together with its
value at the transposed pair. -/
theorem sum_univ_prod_eq_sum_lt_add_swap {l : Type*} [Fintype l] [LinearOrder l] {M : Type*}
    [AddCommMonoid M] (F : l × l → M) (hdiag : ∀ a, F (a, a) = 0) :
    ∑ ij : l × l, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, (F ij + F ij.swap) := by
  classical
  have hswap : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, F ij.swap :=
    Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) (by simp) (by simp) (by simp) (by simp)
      (by simp)
  have hnot : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ¬ ij.1 < ij.2}, F ij := by
    refine Finset.sum_subset ?_ ?_
    · intro ij hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hij ⊢
      exact hij.le
    · rintro ⟨a, b⟩ hmem hnotmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem hnotmem
      exact hdiag a ▸ congrArg (fun c => F (a, c)) (le_antisymm hnotmem hmem).symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ij : l × l => ij.1 < ij.2) F,
    ← hnot, hswap, Finset.sum_add_distrib]

/-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:302` (proof source at `5a01f5fe3621`).
 **A product over the increasing pairs of a symmetric function is permutation invariant:**
for symmetric `f`, `∏_{i<j} f (σ i) (σ j) = ∏_{i<j} f i j` for every permutation `σ`. -/
@[to_additive /-- Kind: THEOREM. Locator: `TauCeti/Algebra/BigOperators/Finset/Pairs.lean:299`.
 **A sum over the increasing pairs of a symmetric function is permutation
invariant:** for symmetric `f`, `∑_{i<j} f (σ i) (σ j) = ∑_{i<j} f i j` for every permutation
`σ`. -/]
theorem prod_prod_Ioi_comp_perm {ι M : Type*} [LinearOrder ι] [Fintype ι]
    [LocallyFiniteOrderTop ι] [CommMonoid M] (f : ι → ι → M) (σ : Equiv.Perm ι)
    (hf : ∀ i j, f i j = f j i) :
    ∏ i, ∏ j ∈ Ioi i, f (σ i) (σ j) = ∏ i, ∏ j ∈ Ioi i, f i j := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun x ↦ ⟨min (σ x.1) (σ x.2), max (σ x.1) (σ x.2)⟩)
    (fun y ↦ ⟨min (σ.symm y.1) (σ.symm y.2), max (σ.symm y.1) (σ.symm y.2)⟩) ?_ ?_ ?_ ?_ ?_
  all_goals
    rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and] at h ⊢
  · rcases lt_or_gt_of_ne (σ.injective.ne h.ne) with hab | hab
    · simpa [hab.le] using hab
    · simpa [hab.le] using hab
  · rcases lt_or_gt_of_ne (σ.symm.injective.ne h.ne) with hab | hab
    · simpa [hab.le] using hab
    · simpa [hab.le] using hab
  · rcases le_total (σ a) (σ b) with hab | hab <;> simp [hab, h.le]
  · rcases le_total (σ.symm a) (σ.symm b) with hab | hab <;> simp [hab, h.le]
  · rcases le_total (σ a) (σ b) with hab | hab
    · simp [hab]
    · simp [hab, hf]

end TauCeti
end

end

/-! ## Source 2: `TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Basic`
Original source SHA256: `809e226688d6d7ce020a587a1b7090f0e2fa1d5954f2e41f1edeca5467151c78`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The canonical Weil differential of the rational function field

The space of Weil differentials of the rational function field `k(x)` is one-dimensional over
`k(x)`, so it has no canonical element until a normalization is chosen.  Stichtenoth pins one down
by prescribing its divisor and one value of one local component: there is exactly one Weil
differential `η` of `k(x) / k` with

`(η) = -2 · P_∞` and `η_{P_∞} (x⁻¹) = -1`,

and it is the differential written `dx` in the classical language, whose local components are the
residues `η_P (z) = res_P (z dx)`.  This is Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., Proposition 1.7.4.  The identification with
residues at the rational places is in
`TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Residue`.

## The construction

The genus of `k(x)` is zero, so `-2 · P_∞` has degree `2g - 2` and lies in the canonical class
(`TauCeti.divisorClass_neg_two_zsmul_ofPoint_infty`); every divisor of that class is the divisor
of a nonzero Weil differential, which produces a differential `ω` with `(ω) = -2 · P_∞`.  Since
`P_∞` is rational with uniformizer `x⁻¹`, the local-order characterization of
`TauCeti.repartitionDualComponent_uniformizer_zpow_ne_zero` says that `ω_{P_∞}` does not kill
`(x⁻¹) ^ (2 - 1) = x⁻¹`, so scaling `ω` by the constant `-(ω_{P_∞} (x⁻¹))⁻¹` — which does not
move the divisor — normalizes that value to `-1`.  Uniqueness is one-dimensionality: a second such
differential is `c · η`, the divisor condition forces `div c = 0`, hence `c ∈ k` by exactness of
the constant field, and the normalization forces `c = 1`.

## The local components

The values of `η` on the powers of `x` are the residues of `xⁿ dx`, that is `-1` for `n = -1` and
`0` otherwise.  Three separate mechanisms produce them: for `n ≤ -2` the bound `(η) = -2 · P_∞`
kills `xⁿ` at `P_∞`; for `n = -1` it is the normalization; and for `n ≥ 0` it is the abstract
residue theorem `∑_P η_P (z) = 0`, whose other summands vanish because `xⁿ` is then a polynomial,
hence regular at every finite place.

## Main definitions

* `TauCeti.ratFuncWeilDifferential`: the Weil differential `η` of Stichtenoth,
  Proposition 1.7.4.

## Main results

* `TauCeti.divisorClass_neg_two_zsmul_ofPoint_infty`: `-2 · P_∞` represents the canonical class
  of `k(x)`.
* `TauCeti.weilDifferentialDivisor_ratFuncWeilDifferential` and
  `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_inv_X`: the two normalizing
  properties `(η) = -2 · P_∞` and `η_{P_∞} (x⁻¹) = -1`.
* `TauCeti.eq_ratFuncWeilDifferential`: **uniqueness** — they determine `η`.
* `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty`,
  `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_algebraMap` and
  `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_zpow`: the local components of `η`
  vanish on the functions regular at a finite place and on the polynomials at infinity, and
  `η_{P_∞} (xⁿ) = -1` for `n = -1` and `0` otherwise.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.4.
-/

section
open Polynomial

namespace TauCeti

open _root_.TauCeti.AlgebraicGeometry

variable {k : Type*} [Field k]

/-! ### The canonical class of the rational function field -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:86` (proof source at `5a01f5fe3621`).
 **`-2 · P_∞` represents the canonical class of `k(x)`**: it has degree `-2 = 2g - 2` for the
genus `g = 0` of the rational function field, and `ℓ(-2 · P_∞) ≥ 0 = g` is vacuous. -/
theorem divisorClass_neg_two_zsmul_ofPoint_infty (k : Type*) [Field k] :
    (Place.orderSystem (IsFunctionField.ratFunc k)).divisorClass
        ((-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k)) =
      canonicalClass (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc := by
  rw [divisorClass_eq_canonicalClass_iff, genus_ratFunc]
  refine ⟨?_, Nat.zero_le _⟩
  rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infty]
  norm_num

/-! ### The differential `η` -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:100` (proof source at `5a01f5fe3621`).
 The normalized Weil differential of `k(x)` exists: this is the existence half of Stichtenoth,
Proposition 1.7.4, in the proof-argument-free `IsGreatest` form that
`TauCeti.ratFuncWeilDifferential` is defined from. -/
private theorem exists_isGreatest_ratFuncWeilDifferential (k : Type*) [Field k] :
    ∃ ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)),
      ω ∈ weilDifferentialSpace k (RatFunc k) ∧
      IsGreatest {D : Divisor k (RatFunc k) | ω ∈ weilDifferentialFiltration D}
        ((-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k)) ∧
      repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1 := by
  obtain ⟨ω, hmem, hω0, hgreat⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass
    (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
    (divisorClass_neg_two_zsmul_ofPoint_infty k)
  -- The order of `ω` at `P_∞` is `-2`, so `ω_{P_∞}` does not kill the uniformizer `x⁻¹`.
  have hord : weilDifferentialOrder (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
      hmem hω0 (Place.infty k) = -2 := by
    rw [← coeff_weilDifferentialDivisor,
      (isGreatest_weilDifferentialDivisor _ _ hmem hω0).unique hgreat,
      _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self, mul_one]
  have hne := repartitionDualComponent_uniformizer_zpow_ne_zero (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc hmem hω0 (Place.degree_infty k) Place.isUniformizer_infty
  rw [hord] at hne
  norm_num only [zpow_one] at hne
  -- Scale by the constant that normalizes that value to `-1`.
  set v := repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ with hv
  refine ⟨repartitionDualMul (IsFunctionField.ratFunc k) (algebraMap k (RatFunc k) (-v⁻¹)) ω,
    repartitionDualMul_mem_weilDifferentialSpace _ _ hmem, ?_, ?_⟩
  · have hc0 : algebraMap k (RatFunc k) (-v⁻¹) ≠ 0 := by
      simpa using inv_ne_zero hne
    obtain ⟨z, hz⟩ : ∃ z : (RatFunc k)ˣ, (z : RatFunc k) = algebraMap k (RatFunc k) (-v⁻¹) :=
      ⟨Units.mk0 _ hc0, rfl⟩
    have hprincipal : Divisor.principal (IsFunctionField.ratFunc k) z = 0 :=
      Divisor.principal_eq_zero_of_isAlgebraic _ (hz ▸ isAlgebraic_algebraMap _)
    have hgreat' := isGreatest_weilDifferentialDivisor (IsFunctionField.ratFunc k)
      isIntegrallyClosedIn_ratFunc
      (repartitionDualMul_mem_weilDifferentialSpace (IsFunctionField.ratFunc k) (z : RatFunc k)
        hmem)
      (repartitionDualMul_ne_zero (IsFunctionField.ratFunc k) (Units.ne_zero z) hω0)
    rw [weilDifferentialDivisor_repartitionDualMul _ _ hmem hω0 z, hprincipal, zero_add,
      (isGreatest_weilDifferentialDivisor _ _ hmem hω0).unique hgreat, hz] at hgreat'
    exact hgreat'
  · rw [repartitionDualComponent_repartitionDualMul_algebraMap, ← hv, smul_eq_mul, neg_mul,
      inv_mul_cancel₀ hne]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:147` (proof source at `5a01f5fe3621`).
 **The canonical Weil differential of the rational function field** (Stichtenoth,
Proposition 1.7.4): the unique Weil differential `η` of `k(x) / k` with divisor `-2 · P_∞` whose
local component at `P_∞` sends the uniformizer `x⁻¹` to `-1`.

Classically it is the differential `dx`, and its local components are the residues
`η_P (z) = res_P (z dx)`; `TauCeti.eq_ratFuncWeilDifferential` is the uniqueness that makes the
normalization meaningful. -/
noncomputable def ratFuncWeilDifferential (k : Type*) [Field k] :
    Module.Dual k ↥(repartitionSpace k (RatFunc k)) :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:152` (proof source at `5a01f5fe3621`).
 `η` is a Weil differential of `k(x) / k`. -/
theorem ratFuncWeilDifferential_mem (k : Type*) [Field k] :
    ratFuncWeilDifferential k ∈ weilDifferentialSpace k (RatFunc k) :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose_spec.1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:158` (proof source at `5a01f5fe3621`).
 **`(η) = -2 · P_∞`**, in the form saying that `-2 · P_∞` is the greatest divisor bounding `η`
(Stichtenoth, Proposition 1.7.4). -/
theorem isGreatest_ratFuncWeilDifferential (k : Type*) [Field k] :
    IsGreatest {D : Divisor k (RatFunc k) |
        ratFuncWeilDifferential k ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k)) :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose_spec.2.1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:168` (proof source at `5a01f5fe3621`).
 **The normalization `η_{P_∞} (x⁻¹) = -1`** (Stichtenoth, Proposition 1.7.4).

This is deliberately not `@[simp]`: `TauCeti.repartitionDualComponent_apply` already unfolds the
left-hand side to `η (ι_{P_∞} x⁻¹)`, so tagging it would violate simp-normal form. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_inv_X (k : Type*) [Field k] :
    repartitionDualComponent (ratFuncWeilDifferential k) (Place.infty k)
      (RatFunc.X : RatFunc k)⁻¹ = -1 :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose_spec.2.2

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:174` (proof source at `5a01f5fe3621`).
 `η` is nonzero: its local component at `P_∞` takes the value `-1`. -/
theorem ratFuncWeilDifferential_ne_zero (k : Type*) [Field k] :
    ratFuncWeilDifferential k ≠ 0 := by
  intro h
  have := repartitionDualComponent_ratFuncWeilDifferential_inv_X k
  rw [h, repartitionDualComponent_apply, LinearMap.zero_apply, eq_comm, neg_eq_zero] at this
  exact one_ne_zero this

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:183` (proof source at `5a01f5fe3621`).
 **The divisor of the canonical Weil differential of `k(x)` is `-2 · P_∞`** (Stichtenoth,
Proposition 1.7.4). -/
theorem weilDifferentialDivisor_ratFuncWeilDifferential (k : Type*) [Field k] :
    weilDifferentialDivisor (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
        (ratFuncWeilDifferential_mem k) (ratFuncWeilDifferential_ne_zero k) =
      (-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k) :=
  (isGreatest_weilDifferentialDivisor _ _ (ratFuncWeilDifferential_mem k)
    (ratFuncWeilDifferential_ne_zero k)).unique (isGreatest_ratFuncWeilDifferential k)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:195` (proof source at `5a01f5fe3621`).
 **Uniqueness in Stichtenoth, Proposition 1.7.4**: a Weil differential of `k(x)` with divisor
`-2 · P_∞` whose local component at `P_∞` sends `x⁻¹` to `-1` is `η`.

This is what makes the normalization meaningful: the two conditions of
`TauCeti.ratFuncWeilDifferential` pin down a single differential. -/
theorem eq_ratFuncWeilDifferential {ω : Module.Dual k ↥(repartitionSpace k (RatFunc k))}
    (hmem : ω ∈ weilDifferentialSpace k (RatFunc k))
    (hgreat : IsGreatest {D : Divisor k (RatFunc k) | ω ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k)))
    (hnorm : repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1) :
    ω = ratFuncWeilDifferential k := by
  -- Any such differential is a function multiple `c · η`; the two divisors agree, so `div c = 0`
  -- and `c` is a constant because `k` is the exact constant field of `k(x)`; the normalization
  -- then makes that constant `1`.
  obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc (ratFuncWeilDifferential_mem k)
    (ratFuncWeilDifferential_ne_zero k) hmem
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, repartitionDualComponent_apply, LinearMap.zero_apply, eq_comm, neg_eq_zero] at hnorm
    exact one_ne_zero hnorm
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hω0 (by rw [← hc, map_zero, LinearMap.zero_apply])
  obtain ⟨z, hz⟩ : ∃ z : (RatFunc k)ˣ, (z : RatFunc k) = c := ⟨Units.mk0 c hc0, rfl⟩
  -- Translating the filtration by `div z` compares the two greatest elements.
  have htrans : ∀ D : Divisor k (RatFunc k),
      D + Divisor.principal (IsFunctionField.ratFunc k) z ≤
          (-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k) ↔
        D ≤ (-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k) := by
    intro D
    rw [← mem_weilDifferentialFiltration_iff_le_of_isGreatest hgreat,
      ← mem_weilDifferentialFiltration_iff_le_of_isGreatest (isGreatest_ratFuncWeilDifferential k),
      ← hc, ← hz]
    exact repartitionDualMul_mem_weilDifferentialFiltration_iff (IsFunctionField.ratFunc k) z
  have hprincipal : Divisor.principal (IsFunctionField.ratFunc k) z = 0 := by
    have hle := (htrans _).mpr (le_refl ((-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k)))
    have hge := (htrans ((-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k) -
      Divisor.principal (IsFunctionField.ratFunc k) z)).mp (by rw [sub_add_cancel])
    refine le_antisymm (by simpa using hle) (by simpa using hge)
  obtain ⟨a, ha⟩ := (Divisor.principal_eq_zero_iff (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc z).mp hprincipal
  -- The normalization pins the constant to `1`.
  rw [hz] at ha
  rw [← hc, ← ha, repartitionDualComponent_repartitionDualMul_algebraMap,
    repartitionDualComponent_ratFuncWeilDifferential_inv_X, smul_eq_mul, mul_neg, mul_one,
    neg_inj] at hnorm
  rw [← hc, ← ha, hnorm]
  simp

/-! ### The local components of `η` -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:246` (proof source at `5a01f5fe3621`).
 **The local components of `η` away from infinity kill every regular function**: the divisor of
`η` is supported at `P_∞` alone, so `η_P` vanishes on the valuation ring of every other place
(Stichtenoth, Proposition 1.7.4).  Classically this says that `z dx` has no residue at a finite
place at which `z` is regular. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty {P : Place k (RatFunc k)}
    (hP : P ≠ Place.infty k) {z : RatFunc k} (hz : z ∈ P.integers) :
    repartitionDualComponent (ratFuncWeilDifferential k) P z = 0 := by
  refine repartitionDualComponent_apply_eq_zero_of_le (isGreatest_ratFuncWeilDifferential k).1 P ?_
  rw [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hP, mul_zero, WithZero.exp_zero]
  exact P.mem_integers_iff.mp hz

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:257` (proof source at `5a01f5fe3621`).
 **A polynomial has no residue at infinity**: `η_{P_∞} (p) = 0` for every `p ∈ k[X]`.

Classically this says that `p dx` is a regular differential on the affine line, so its only
residue — the one at infinity — must vanish. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_algebraMap (p : k[X]) :
    repartitionDualComponent (ratFuncWeilDifferential k) (Place.infty k)
      (algebraMap k[X] (RatFunc k) p) = 0 := by
  -- The abstract residue theorem `∑_P η_P (p) = 0` of Stichtenoth, (1.45): a polynomial is
  -- regular at every finite place, so all the other summands vanish.
  have hzero : ∀ P : Place k (RatFunc k), P ≠ Place.infty k →
      repartitionDualComponent (ratFuncWeilDifferential k) P
        (algebraMap k[X] (RatFunc k) p) = 0 := fun P hP ↦
    repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hP (by
      by_contra hcon
      exact hP (Place.exists_algebraMap_notMem_integers_iff_eq_infty.mp ⟨p, hcon⟩))
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (ratFuncWeilDifferential_mem k) (algebraMap k[X] (RatFunc k) p)
  rwa [finsum_eq_single _ (Place.infty k) hzero] at hsum

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Basic.lean:274` (proof source at `5a01f5fe3621`).
 **The local components of `η` on the powers of `x`** (Stichtenoth, Proposition 1.7.4): at the
place at infinity, `η_{P_∞} (xⁿ) = -1` for `n = -1` and `0` otherwise — the residues of `xⁿ dx`. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_zpow (k : Type*) [Field k] (n : ℤ) :
    repartitionDualComponent (ratFuncWeilDifferential k) (Place.infty k)
      ((RatFunc.X : RatFunc k) ^ n) = if n = -1 then -1 else 0 := by
  -- For `n ≤ -2` the bound `(η) = -2 · P_∞` applies, for `n = -1` this is the normalization, and
  -- for `n ≥ 0` the power is a polynomial, which has no residue at infinity.
  split_ifs with hn
  · rw [hn, zpow_neg_one, repartitionDualComponent_ratFuncWeilDifferential_inv_X]
  rcases lt_or_ge n 0 with hneg | hnonneg
  · -- A pole of order at least two at `P_∞` is killed by the bound `(η) = -2 · P_∞`.
    refine repartitionDualComponent_apply_eq_zero_of_le
      (isGreatest_ratFuncWeilDifferential k).1 (Place.infty k) ?_
    rw [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self, mul_one,
      (Place.infty k).valuation_eq_exp_neg_ord (zpow_ne_zero _ RatFunc.X_ne_zero),
      WithZero.exp_le_exp, Place.ord_zpow, Place.ord_infty, RatFunc.intDegree_X]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
    rw [zpow_natCast, ← RatFunc.algebraMap_X, ← map_pow]
    exact repartitionDualComponent_ratFuncWeilDifferential_algebraMap _

end TauCeti
end

end

/-! ## Source 3: `TauCeti.FieldTheory.FunctionField.Differential.Comparison`
Original source SHA256: `8a78948ffedacdea503b1bdcbf57e16b9aed701e6b63e6c76f009450e0580c2f`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Comparing Kähler and Weil differentials

Let `F / k` be an algebraic function field and let `x ∈ F` be a separating element.  The
embedding `k(X) → F` which sends `X` to `x` carries the normalized Weil differential `dX` of
`k(X)` to a nonzero differential of `F` by cotrace.  This differential, written
`TauCeti.weilDifferentialOfSeparating`, is the Weil-theoretic `dx`.

Assume in addition that `k` is algebraically closed in `F` (`IsIntegrallyClosedIn k F`).  Both
the Kähler and Weil differential spaces are then one-dimensional over `F`.  Sending the Kähler
differential `D k F x` to this cotrace therefore determines an `F`-linear equivalence

`Ω[F⁄k] ≃ₗ[F] weilDifferentialSpace k F`.

For every `y ∈ F`, the equivalence sends `dy` to `(dy/dx) dx`.  This is the linear comparison in
Stichtenoth, Theorem 4.3.2.  The equivalence does not depend on the separating element, and at
rational places with a separating prime element the local components of the Weil differential
attached to `ω` are the residues of `ω`
(`TauCeti.FieldTheory.FunctionField.Differential.Independence`).

The divisor of `dx` is explicit: `(dx) = -2 (x)_∞ + Diff(F / k(x))` (Stichtenoth, Remark 4.3.7(c)).
It is the divisor of a cotrace, `Con (η) + Diff(F / k(x))`, where the normalized differential `η` of
`k(x)` has divisor `-2 P_∞`, and the conorm of `P_∞ = (X)_∞` is the pole divisor of `x`.  In
particular `-2 (x)_∞ + Diff(F / k(x))` is a canonical divisor of `F`.  At a place with separable
residue field where `x` is a prime element, the place is unramified and tame over `k(x)`, so `dx`
has order zero there.

## Main definitions

* `TauCeti.weilDifferentialOfSeparating`: the cotrace of the normalized differential of `k(X)`
  along the embedding `X ↦ x`.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating`: the comparison equivalence
  determined by a separating element.

## Main results

* `TauCeti.weilDifferentialOfSeparating_ne_zero`: `dx` is nonzero.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self`: the comparison sends
  `dx` to its Weil counterpart.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D`: the comparison sends `dy`
  to `(dy/dx) dx`.
* `TauCeti.weilDifferentialDivisor_weilDifferentialOfSeparating`:
  `(dx) = -2 (x)_∞ + Diff(F / k(x))`, and
  `TauCeti.weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential`, the same
  identity for any finite separable extension of `k(x)`.
* `TauCeti.divisorClass_neg_two_zsmul_poles_add_different_eq_canonicalClass`:
  `-2 (x)_∞ + Diff(F / k(x))` represents the canonical class.
* `TauCeti.weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero`: `dx` has order zero at a
  place with separable residue field at which `x` is a prime element.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.3, Definition 4.3.1, Theorem 4.3.2 and Remark 4.3.7.
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

open Module KaehlerDifferential

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable {x : F}

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:87` (proof source at `5a01f5fe3621`).
 The Weil differential `dx` attached to a separating element `x`: the cotrace to `F` of the
normalized differential `dX` on the rational function field, along the embedding `X ↦ x`.

The result belongs to the intrinsic Weil differential space, so the chosen rational-function
algebra structure used in its construction is not exposed in the type. -/
noncomputable def weilDifferentialOfSeparating (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ↥(weilDifferentialSpace k F) :=
  letI := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
    ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:99` (proof source at `5a01f5fe3621`).
 The Weil differential attached to `x` is the cotrace of the normalized differential on
`k(X)` under the rational-function algebra structure induced by `X ↦ x`. -/
theorem weilDifferentialOfSeparating_def (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
    let _ := isFunctionField_iff_functionField.mp hF
    let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
    weilDifferentialOfSeparating hF hx =
      weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ := by
  rw [weilDifferentialOfSeparating]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:111` (proof source at `5a01f5fe3621`).
 The Weil differential `dx` attached to a separating element is nonzero. -/
theorem weilDifferentialOfSeparating_ne_zero (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    weilDifferentialOfSeparating hF hx ≠ 0 := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  rw [weilDifferentialOfSeparating_def, ne_eq,
    weilDifferentialCotrace_eq_zero_iff, Submodule.mk_eq_zero]
  exact ratFuncWeilDifferential_ne_zero k

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:123` (proof source at `5a01f5fe3621`).
 The Weil differential of a separating element remains nonzero as a repartition dual. -/
theorem coe_weilDifferentialOfSeparating_ne_zero (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    (weilDifferentialOfSeparating hF hx : Module.Dual k (repartitionSpace k F)) ≠ 0 := by
  simpa only [ne_eq, Submodule.coe_eq_zero] using weilDifferentialOfSeparating_ne_zero hF hx

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:130` (proof source at `5a01f5fe3621`).
 The basis of the Weil differential space whose unique vector is the differential `dx`
attached to a separating element. -/
noncomputable def weilDifferentialBasisOfSeparating (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Basis Unit F ↥(weilDifferentialSpace k F) :=
  let _ := weilDifferentialSpaceModule hF
  FiniteDimensional.basisSingleton Unit (finrank_weilDifferentialSpace hF hex)
    (weilDifferentialOfSeparating hF hx) (weilDifferentialOfSeparating_ne_zero hF hx)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:140` (proof source at `5a01f5fe3621`).
-/
@[simp]
theorem weilDifferentialBasisOfSeparating_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (i : Unit) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialBasisOfSeparating hF hex hx i = weilDifferentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [weilDifferentialBasisOfSeparating]
  exact FiniteDimensional.basisSingleton_apply _ _ _ _ i

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:152` (proof source at `5a01f5fe3621`).
 **The Kähler–Weil differential comparison for a separating element** (Stichtenoth,
Theorem 4.3.2): the `F`-linear equivalence which sends the Kähler differential `dx` to the
cotrace of the normalized Weil differential `dX` along `k(X) → F`, `X ↦ x`. -/
noncomputable def kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Ω[F⁄k] ≃ₗ[F] ↥(weilDifferentialSpace k F) :=
  letI := weilDifferentialSpaceModule hF
  (kaehlerBasisOfSeparating hx).equiv (weilDifferentialBasisOfSeparating hF hex hx)
    (Equiv.refl Unit)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:164` (proof source at `5a01f5fe3621`).
 The Kähler–Weil comparison sends the differential of the chosen separating element to its
Weil counterpart. -/
@[simp]
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx (D k F x) =
      weilDifferentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [← kaehlerBasisOfSeparating_apply hx (),
    kaehlerDifferentialEquivWeilDifferentialOfSeparating, Basis.equiv_apply]
  exact weilDifferentialBasisOfSeparating_apply hF hex hx ()

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:178` (proof source at `5a01f5fe3621`).
 The inverse Kähler–Weil comparison sends the Weil differential attached to the chosen
separating element back to its Kähler differential. -/
@[simp]
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_symm_weilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm
        (weilDifferentialOfSeparating hF hx) = D k F x := by
  let _ := weilDifferentialSpaceModule hF
  apply (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).injective
  rw [LinearEquiv.apply_symm_apply,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:192` (proof source at `5a01f5fe3621`).
 Under the Kähler–Weil comparison determined by `x`, the differential `dy` is
`(dy/dx) dx`. -/
@[simp]
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_D
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (y : F) :
    letI := weilDifferentialSpaceModule hF
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx (D k F y) =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  rw [← derivativeOfSeparating_smul_D hx y, map_smul,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:204` (proof source at `5a01f5fe3621`).
 The Kähler–Weil comparison determined by `x` preserves coordinates: the coordinate in `dx` of
the Weil differential attached to `ω` is the coordinate of `ω` in `dx`. -/
theorem coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (ω : Ω[F⁄k]) :
    letI := weilDifferentialSpaceModule hF
    (weilDifferentialBasisOfSeparating hF hex hx).coord ()
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω) =
      (kaehlerBasisOfSeparating hx).coord () ω := by
  let := weilDifferentialSpaceModule hF
  simp [kaehlerDifferentialEquivWeilDifferentialOfSeparating, Basis.equiv]

/-! ### The divisor of `dx` -/

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:222` (proof source at `5a01f5fe3621`).
 The cotrace to `F` of the normalized differential of `k(x)` is nonzero. -/
theorem weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero (hF : IsFunctionField k F) :
    (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) ≠ 0 := by
  rw [ne_eq, ZeroMemClass.coe_eq_zero, weilDifferentialCotrace_eq_zero_iff,
    Submodule.mk_eq_zero]
  exact ratFuncWeilDifferential_ne_zero k

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:235` (proof source at `5a01f5fe3621`).
 **The divisor of `dx`** (Stichtenoth, Remark 4.3.7(c)): for a finite separable extension `F`
of `k(x)` with exact constant field `k`, the cotrace to `F` of the normalized differential `η` of
`k(x)` has divisor `-2 (x)_∞ + Diff(F / k(x))`, where `x` is the image in `F` of the variable of
`k(x)`. -/
@[simp]
theorem weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    weilDifferentialDivisor hF hex
        (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
          ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩).2
        (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF) =
      (-2 : ℤ) • Divisor.poles hF (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
          (Units.mk0 RatFunc.X RatFunc.X_ne_zero)) +
        Divisor.different k F (IsFunctionField.ratFunc k) := by
  -- `(Cotr η) = Con (η) + Diff(F / k(x))`, `(η) = -2 P_∞`, and `Con P_∞ = Con (x)_∞ = (x)_∞`.
  rw [weilDifferentialDivisor_weilDifferentialCotrace (IsFunctionField.ratFunc k) hF
    isIntegrallyClosedIn_ratFunc hex _ (by simpa using ratFuncWeilDifferential_ne_zero k),
    weilDifferentialDivisor_ratFuncWeilDifferential, map_zsmul, ← Divisor.poles_X,
    Divisor.conorm_poles k F (IsFunctionField.ratFunc k) hF]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:254` (proof source at `5a01f5fe3621`).
 **`-2 (x)_∞ + Diff(F / k(x))` is a canonical divisor** (Stichtenoth, Remark 4.3.7(c)): for a
finite separable extension `F` of `k(x)` with exact constant field `k`, this divisor represents the
canonical class of `F`. -/
@[simp]
theorem divisorClass_neg_two_zsmul_poles_add_different_eq_canonicalClass
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    -(2 • (Place.orderSystem hF).divisorClass
        (Divisor.poles hF (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
          (Units.mk0 RatFunc.X RatFunc.X_ne_zero)))) +
      (Place.orderSystem hF).divisorClass
        (Divisor.different k F (IsFunctionField.ratFunc k)) =
      canonicalClass hF hex := by
  calc
    _ = (Place.orderSystem hF).divisorClass
          ((-2 : ℤ) • Divisor.poles hF
            (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
              (Units.mk0 RatFunc.X RatFunc.X_ne_zero)) +
            Divisor.different k F (IsFunctionField.ratFunc k)) := by simp; rfl
    _ = canonicalClass hF hex := by
      rw [← weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential hF hex,
        divisorClass_weilDifferentialDivisor]

end RatFunc

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:278` (proof source at `5a01f5fe3621`).
 **The divisor of `dx`** (Stichtenoth, Remark 4.3.7(c)): for a separating element `x` of `F / k`
with exact constant field `k`, the Weil differential `dx` has divisor `-2 (x)_∞ + Diff(F / k(x))`,
the different being taken along the embedding `k(X) → F`, `X ↦ x`. -/
@[simp]
theorem weilDifferentialDivisor_weilDifferentialOfSeparating (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := isFunctionField_iff_functionField.mp hF
    letI := isSeparable_ratFuncAlgebraOfTranscendental hx
    weilDifferentialDivisor hF hex (weilDifferentialOfSeparating hF hx).2
        (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) =
      (-2 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero) +
        Divisor.different k F (IsFunctionField.ratFunc k) := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX : Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = Units.mk0 x hx.ne_zero :=
    Units.ext (algebraMap_ratFuncAlgebraOfTranscendental_X hx)
  simp_rw [weilDifferentialOfSeparating_def, ← hX]
  exact weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential hF hex

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Comparison.lean:302` (proof source at `5a01f5fe3621`).
 **The differential of a prime element has order zero**: if `t` is a separating element of
`F / k` with exact constant field and `t` is a prime element at a place `P` whose residue field is
separable over `k` (for instance a rational place, or any place over a perfect field), then the
Weil differential `dt` has order zero at `P`. -/
theorem weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable k⟮t⟯ F] {P : Place k F} [Algebra.IsSeparable k P.ResidueField]
    (htP : P.ord t = 1) :
    weilDifferentialOrder hF hex (weilDifferentialOfSeparating hF ht).2
      (by simpa using weilDifferentialOfSeparating_ne_zero hF ht) P = 0 := by
  let _ := ratFuncAlgebraOfTranscendental ht
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental ht
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental ht
  -- `P` is unramified over `k(t)`, since `t` is a prime element at `P` and at the place below.
  have he : Place.ramificationIdx (RatFunc k) P = 1 := by
    have h := Place.ord_algebraMap_restrict k (RatFunc k) P RatFunc.X
    rw [algebraMap_ratFuncAlgebraOfTranscendental_X, htP] at h
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h.symm
  -- `P` is tame over `k(t)`: its residue field is separable over `k`, hence over the residue
  -- field of the place below.
  have htame : Place.IsTame k (RatFunc k) P := by
    rw [Place.isTame_iff_isSeparable_residueField, he, Nat.cast_one]
    exact ⟨Algebra.isSeparable_tower_top_of_isSeparable k _ _, one_ne_zero⟩
  have hd := (Divisor.coeff_different_add_one_eq_ramificationIdx_iff
    (IsFunctionField.ratFunc k) P).mpr htame
  rw [he, Nat.cast_one, add_eq_right] at hd
  rw [← coeff_weilDifferentialDivisor, weilDifferentialDivisor_weilDifferentialOfSeparating,
    _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_add, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, hd,
    Divisor.coeff_poles]
  simp [htP]

end TauCeti
end

end

/-! ## Source 4: `TauCeti.RingTheory.DedekindDomain.Different.Monogenic`
Original source SHA256: `cd685f72f5b4857d25bc32050ab2c41dfcd03c0990881bd2a1fedfaa57cbc818`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The different of a monogenic extension

When the integral closure `B` of `A` in `L` is generated over `A` by a single element `x` — the
monogenic case — the different ideal is generated by `f'(x)`, where `f` is the minimal polynomial
of `x`:

`differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))}`.

This is the computational handle on the different. Without it the different is only accessible
through the trace dual, which is not something one evaluates at a specific extension.

## The conductor is what makes this work

Mathlib supplies the general identity

`conductor A x * differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))}`
(`conductor_mul_differentIdeal`),

which holds for any `x` generating `L` over `K`, monogenic or not. The order conductor measures
exactly the failure of `A[x]` to be all of `B`, so the monogenic hypothesis is precisely the
statement that it is the unit ideal (`conductor_eq_top_of_adjoin_eq_top`). This file records the
resulting closed form; it reproves neither half.

Only the *ring* generation hypothesis `Algebra.adjoin A {x} = ⊤` is needed. Mathlib's identity
also asks that `x` generate `L` over `K`, but in this setting that follows: `L` is the fraction
field of `B = A[x]`, so every element of `L` is a ratio of two polynomials in `x`
(`TauCeti.IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top`).

## Main results

* `TauCeti.residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly`: the closed form.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
* J-P. Serre, *Local Fields*, Chapter III, §6.
-/

section
open Polynomial

namespace TauCeti

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegralClosure B A L]
  [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K L in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/DedekindDomain/Different/Monogenic.lean:68` (proof source at `5a01f5fe3621`).
 **The different of a monogenic extension is generated by `f'(x)`.** The hypothesis is that `x`
generates `B` as an `A`-algebra; that it also generates `L` over `K` is a consequence, since `L`
is the fraction field of `B`. -/
theorem residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly (x : B)
    (hx : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  -- Ring generation upgrades to field generation: every element of `L` is a ratio in `A[x]`.
  have hK : Algebra.adjoin K {algebraMap B L x} = ⊤ := by
    rw [← IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun y _ => IsAlgebraic.of_finite K y)]
    exact TauCeti.IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top hx
  rw [← conductor_mul_differentIdeal A K L x hK, conductor_eq_top_of_adjoin_eq_top hx,
    Ideal.top_mul]

end TauCeti

end

end

/-! ## Source 5: `TauCeti.RingTheory.DedekindDomain.Different.Localization`
Original source SHA256: `15e1bae843b5033c8b8eae8a41b75158d5d759d8dd706c98559d39caea7cb6f8`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Localization of the different ideal

This file proves that trace duals and different ideals commute with localization, so localization
preserves the coefficient of the different ideal at every nonzero prime.  This is the
localization input needed to read the transitivity theorem for different ideals coefficientwise at
a tower of discrete valuations.

## References

- H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections III.4–III.5.
- A. Yang, [Mathlib's different-ideal formalization](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/DedekindDomain/Different.lean).
-/

section
open Module

open scoped nonZeroDivisors

namespace TauCeti

universe uR uRm uS uSm uK uL

variable {R : Type uR} {Rₘ : Type uRm} {S : Type uS} {Sₘ : Type uSm}
variable {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field K] [Field L]
variable {M : Submonoid R}
variable [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ]
variable [Algebra R Sₘ] [IsScalarTower R S Sₘ]
variable [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K]
variable [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L] [Algebra Sₘ L]
variable [IsScalarTower R K L] [IsScalarTower Rₘ K L]
variable [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L] [IsScalarTower S Sₘ L]
variable [IsScalarTower R Sₘ L]
variable [IsLocalization M Rₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable [Module.Finite R S]
variable [IsDomain R]
variable [IsFractionRing R K]

include M

omit [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Sₘ L]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [IsDomain R]
  [IsFractionRing R K] in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean:58` (proof source at `5a01f5fe3621`).
-/
private theorem exists_smul_mem_traceDual_of_mem_traceDual {x : L}
    (hx : x ∈ Submodule.traceDual Rₘ K (1 : Submodule Sₘ L)) :
    ∃ b : M, algebraMap R K b • x ∈ Submodule.traceDual R K (1 : Submodule S L) := by
  rw [Submodule.mem_traceDual] at hx
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  choose c hc using fun i : s ↦ hx (algebraMap S L i) (Submodule.mem_one.mpr
    ⟨algebraMap S Sₘ i, by rw [← IsScalarTower.algebraMap_apply S Sₘ L]⟩)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M c
  refine ⟨b, ?_⟩
  rw [Submodule.mem_traceDual]
  intro a ha
  rw [Submodule.mem_one] at ha
  obtain ⟨a, rfl⟩ := ha
  let f : S →ₗ[R] K := ((Algebra.traceForm K L) (algebraMap R K b • x)).restrictScalars R
    ∘ₗ (Algebra.linearMap S L).restrictScalars R
  let N : Submodule R S := Submodule.comap f (1 : Submodule R K)
  have hsN : (s : Set S) ⊆ N := by
    intro i hi
    let j : s := ⟨i, hi⟩
    obtain ⟨r, hr⟩ := hb j
    apply Submodule.mem_comap.mpr
    rw [Submodule.mem_one]
    refine ⟨r, ?_⟩
    calc
      algebraMap R K r = algebraMap Rₘ K (algebraMap R Rₘ r) := by
        rw [IsScalarTower.algebraMap_apply R Rₘ K]
      _ = algebraMap Rₘ K ((b : R) • c j) := congrArg (algebraMap Rₘ K) hr
      _ = algebraMap R K b * algebraMap Rₘ K (c j) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R Rₘ K]
      _ = algebraMap R K b * (Algebra.traceForm K L x) (algebraMap S L j) := by
        rw [hc j]
      _ = (Algebra.trace K L) (algebraMap R K b • (x * algebraMap S L j)) := by
        rw [(Algebra.trace K L).map_smul, Algebra.traceForm_apply, Algebra.smul_def]
        simp only [Algebra.algebraMap_self_apply]
      _ = (Algebra.trace K L) ((algebraMap R K b • x) * algebraMap S L i) := by
        congr 1
        simp only [Algebra.smul_def, j]
        ring
      _ = ((Algebra.traceForm K L) (algebraMap R K b • x)) (algebraMap S L i) := by
        rw [Algebra.traceForm_apply]
      _ = f i := by
        simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
          Algebra.linearMap_apply]
  have hN : N = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsN
  have haN : a ∈ N := hN.symm ▸ Submodule.mem_top
  exact Submodule.mem_one.mp (Submodule.mem_comap.mp haN)

omit [IsDomain R] [IsFractionRing R K] in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean:110` (proof source at `5a01f5fe3621`).
 The trace dual of a finite algebra commutes with localization. -/
theorem span_traceDual_one_eq_traceDual_one :
    Submodule.span Sₘ (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      Submodule.traceDual Rₘ K (1 : Submodule Sₘ L) := by
  let _ : Nontrivial R := (algebraMap R K).domain_nontrivial
  apply le_antisymm
  -- Extension of scalars sends an integral trace value to its localized image.
  · rw [Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe] at hx ⊢
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨⟨s, _, m, hm, rfl⟩, hsm⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid S M) a
    obtain ⟨r, hr⟩ := hx (algebraMap S L s) (Submodule.mem_one.mpr ⟨s, rfl⟩)
    have hsmL : algebraMap Sₘ L a * algebraMap R L m = algebraMap S L s := by
      simpa only [map_mul, IsScalarTower.algebraMap_apply R S Sₘ,
        IsScalarTower.algebraMap_apply R Sₘ L, IsScalarTower.algebraMap_apply S Sₘ L]
        using congrArg (algebraMap Sₘ L) hsm
    have htrace : (Algebra.traceForm K L x) (algebraMap Sₘ L a) * algebraMap R K m =
        algebraMap R K r := by
      calc
        _ = algebraMap R K m * (Algebra.trace K L) (x * algebraMap Sₘ L a) := mul_comm _ _
        _ = (Algebra.trace K L) (algebraMap R K m • (x * algebraMap Sₘ L a)) :=
          ((Algebra.trace K L).map_smul _ _).symm
        _ = (Algebra.trace K L) (x * algebraMap S L s) := by
          congr 1
          rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L]
          calc
            algebraMap R L m * (x * algebraMap Sₘ L a) =
                x * (algebraMap Sₘ L a * algebraMap R L m) := by ring
            _ = x * algebraMap S L s := by rw [hsmL]
        _ = _ := hr.symm
    refine ⟨IsLocalization.mk' Rₘ r ⟨m, hm⟩, ?_⟩
    apply mul_right_cancel₀ (b := algebraMap R K m)
    · rw [IsScalarTower.algebraMap_apply R Rₘ K]
      exact ((IsLocalization.map_units Rₘ ⟨m, hm⟩).map (algebraMap Rₘ K)).ne_zero
    rw [IsScalarTower.algebraMap_apply R Rₘ K, ← map_mul, IsLocalization.mk'_spec]
    simpa only [IsScalarTower.algebraMap_apply R Rₘ K] using htrace.symm
  -- Conversely, clear one denominator for trace values on a finite set of algebra generators.
  · intro x hx
    obtain ⟨b, hbx⟩ := exists_smul_mem_traceDual_of_mem_traceDual
      (R := R) (Rₘ := Rₘ) (S := S) (Sₘ := Sₘ) (K := K) (L := L) (M := M) hx
    let bm : Algebra.algebraMapSubmonoid S M := ⟨algebraMap R S b, ⟨b, b.2, rfl⟩⟩
    have hbx' := Submodule.smul_mem (Submodule.span Sₘ
      (Submodule.traceDual R K (1 : Submodule S L) : Set L)) (IsLocalization.mk' Sₘ 1 bm)
      (Submodule.subset_span hbx)
    suffices IsLocalization.mk' Sₘ 1 bm • (algebraMap R K b • x) = x by rwa [this] at hbx'
    rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply S Sₘ L,
      ← mul_assoc, ← map_mul, IsLocalization.mk'_spec]
    simp only [map_one, one_mul]

variable [IsFractionRing S L]
variable [IsIntegrallyClosed R]
variable [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ]

section

variable [IsDomain S]

omit [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ] in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean:176` (proof source at `5a01f5fe3621`).
 The trace-dual fractional ideal commutes with localization. -/
theorem extended_dual_one_eq_dual_one :
    let _ : Nontrivial Rₘ := (algebraMap Rₘ K).domain_nontrivial
    let hM : M ≤ R⁰ := fun m hm ↦ mem_nonZeroDivisors_iff_ne_zero.mpr fun hm0 ↦
      (IsLocalization.map_units Rₘ ⟨m, hm⟩).ne_zero (by simp [hm0])
    let _ : IsDomain Rₘ := IsLocalization.isDomain_of_le_nonZeroDivisors Rₘ hM
    let hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
      map_le_nonZeroDivisors_of_injective _
        (algebraMap_injective_of_field_isFractionRing R S K L) hM
    let _ : IsFractionRing Rₘ K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
    let _ : IsIntegrallyClosed Rₘ :=
      isIntegrallyClosed_of_isLocalization Rₘ M hM
    let _ : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors Sₘ hMS
    let _ : IsFractionRing Sₘ L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        (Algebra.algebraMapSubmonoid S M) Sₘ L
    FractionalIdeal.extended L
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (IsLocalization.injective Sₘ hMS))
        (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) =
      FractionalIdeal.dual Rₘ K (1 : FractionalIdeal Sₘ⁰ L) := by
  intro _ hM _ hMS _ _ _ _
  let h : S⁰ ≤ Submonoid.comap (algebraMap S Sₘ) Sₘ⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (IsLocalization.injective Sₘ hMS)
  -- `extended` takes the inclusion proof explicitly, so proof irrelevance identifies the
  -- canonical proof in the statement with the named proof `h` used throughout this proof.
  change FractionalIdeal.extended L h
      (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) = _
  apply FractionalIdeal.coeToSubmodule_injective
  refine (FractionalIdeal.coe_extended_eq_span L h _).trans ?_
  have hmap : IsLocalization.map L (algebraMap S Sₘ) h = RingHom.id L := by
    apply IsFractionRing.ringHom_ext (A := S)
    intro s
    rw [IsLocalization.map_eq, RingHom.id_apply, IsScalarTower.algebraMap_apply S Sₘ L]
  rw [hmap]
  simp only [RingHom.id_apply, Set.image_id']
  calc
    Submodule.span Sₘ
        ((↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) : Set L) =
        Submodule.span Sₘ (Submodule.traceDual R K (1 : Submodule S L) : Set L) :=
      congrArg (Submodule.span Sₘ)
        (congrArg (fun N : Submodule S L ↦ (N : Set L))
          FractionalIdeal.coe_dual_one_of_isDomain)
    _ = Submodule.traceDual Rₘ K (1 : Submodule Sₘ L) :=
      span_traceDual_one_eq_traceDual_one (M := M)
    _ = (↑(FractionalIdeal.dual Rₘ K (1 : FractionalIdeal Sₘ⁰ L)) : Submodule Sₘ L) :=
      (FractionalIdeal.coe_dual_one_of_isDomain (R := Rₘ) (S := Sₘ)).symm

end

variable [IsDedekindDomain S]

omit [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ] in
include K L in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean:232` (proof source at `5a01f5fe3621`).
 The different ideal commutes with localization. -/
theorem map_differentIdeal_eq_differentIdeal :
    let _ : Nontrivial Rₘ := (algebraMap Rₘ K).domain_nontrivial
    let hM : M ≤ R⁰ := fun m hm ↦ mem_nonZeroDivisors_iff_ne_zero.mpr fun hm0 ↦
      (IsLocalization.map_units Rₘ ⟨m, hm⟩).ne_zero (by simp [hm0])
    let _ : IsDomain Rₘ := IsLocalization.isDomain_of_le_nonZeroDivisors Rₘ hM
    let hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
      map_le_nonZeroDivisors_of_injective _
        (algebraMap_injective_of_field_isFractionRing R S K L) hM
    let _ : IsFractionRing Rₘ K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
    let _ : IsIntegrallyClosed Rₘ :=
      isIntegrallyClosed_of_isLocalization Rₘ M hM
    let _ : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors Sₘ hMS
    let _ : IsFractionRing Sₘ L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        (Algebra.algebraMapSubmonoid S M) Sₘ L
    let _ : IsDedekindDomain Sₘ := IsLocalization.isDedekindDomain S hMS Sₘ
    let _ : IsTorsionFree R L := .trans_faithfulSMul R K L
    let _ : IsTorsionFree Rₘ L := .trans_faithfulSMul Rₘ K L
    let _ : IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L
    let _ : IsTorsionFree Rₘ Sₘ := IsIntegralClosure.isTorsionFree Rₘ L
    (differentIdeal R S).map (algebraMap S Sₘ) = differentIdeal Rₘ Sₘ := by
  intro _ hM _ hMS _ _ _ _ _ _ _ _ _
  have hSSₘ : Function.Injective (algebraMap S Sₘ) := IsLocalization.injective Sₘ hMS
  let h : S⁰ ≤ Submonoid.comap (algebraMap S Sₘ) Sₘ⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hSSₘ
  rw [← FractionalIdeal.coeIdeal_inj (K := L),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) L h,
    ← FractionalIdeal.extendedHom'_apply]
  rw [coeIdeal_differentIdeal R K L S, coeIdeal_differentIdeal Rₘ K L Sₘ, map_inv₀,
    FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one (R := R) (Rₘ := Rₘ) (S := S)
      (Sₘ := Sₘ)
      (K := K) (L := L) (M := M)]

include K L in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean:270` (proof source at `5a01f5fe3621`).
 **Localization preserves the coefficients of the different ideal**: at a nonzero prime `P` of
`Sₘ`, the coefficient of `𝔇(Sₘ / Rₘ)` is the coefficient of `𝔇(S / R)` at `P ∩ S`. -/
theorem multiplicity_differentIdeal_eq_multiplicity_under [IsDomain Rₘ] [IsDedekindDomain Sₘ]
    {P : Ideal Sₘ} [P.IsPrime] (hP : P ≠ ⊥) :
    multiplicity P (differentIdeal Rₘ Sₘ) = multiplicity (P.under S) (differentIdeal R S) := by
  -- Extending `P ∩ S` to the localization gives back `P`, so its ramification index is one and
  -- extension preserves the coefficient; `map_differentIdeal_eq_differentIdeal` identifies the
  -- extended different with `𝔇(Sₘ / Rₘ)`.
  have hM : M ≤ R⁰ := fun m hm ↦ mem_nonZeroDivisors_iff_ne_zero.mpr fun hm0 ↦
    (IsLocalization.map_units Rₘ ⟨m, hm⟩).ne_zero (by simp [hm0])
  have hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective R S) hM
  let _ : FaithfulSMul S Sₘ :=
    (faithfulSMul_iff_algebraMap_injective S Sₘ).mpr (IsLocalization.injective Sₘ hMS)
  have hmap : (P.under S).map (algebraMap S Sₘ) = P :=
    IsLocalization.map_under (Algebra.algebraMapSubmonoid S M) Sₘ P
  have hunder : P.under S ≠ ⊥ := fun h ↦ hP (by rw [← hmap, h, Ideal.map_bot])
  have hD : differentIdeal R S ≠ ⊥ := by
    rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal R K L S]
    simp
  have hone : Ideal.ramificationIdx' (P.under S) P = 1 := by
    have h : Ideal.ramificationIdx' (P.under S) ((P.under S).map (algebraMap S Sₘ)) = 1 :=
      Ideal.ramificationIdx'_map_self_eq_one (by rw [hmap]; exact Ideal.IsPrime.ne_top ‹_›)
        (by rwa [hmap])
    rwa [hmap] at h
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hD
    (Ideal.prime_of_isPrime hunder (Ideal.IsPrime.under S P)).irreducible
    (Ideal.prime_of_isPrime hP ‹P.IsPrime›).irreducible hP
  rw [hone, Nat.cast_one, one_mul,
    (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP ‹P.IsPrime›)
      (Ideal.map_ne_bot_of_ne_bot hD)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hunder (Ideal.IsPrime.under S P))
      hD).emultiplicity_eq_multiplicity,
    map_differentIdeal_eq_differentIdeal (R := R) (Rₘ := Rₘ) (S := S) (Sₘ := Sₘ) (K := K)
      (L := L) (M := M)] at h
  exact_mod_cast h

end TauCeti

end

end

/-! ## Source 6: `TauCeti.RingTheory.Localization.Integral`
Original source SHA256: `1619cb903900c6935b55ab97460b80d4ffbedc81ad8d032f40f1c9d84e354628`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Integral closures of localizations

If `Rₘ` is a localization of `R` at a submonoid `M`, and `S`, `Sₘ` are integral closures of `R`,
`Rₘ` in the same commutative ring `L`, then `Sₘ` is the localization of `S` at the image of `M`.

Mathlib's `IsLocalization.integralClosure` states this for the literal subalgebra
`integralClosure R L`; the version here applies to arbitrary types satisfying
`IsIntegralClosure`.

## Main results

* `TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure`: an integral closure of a
  localization is the corresponding localization of an integral closure.
-/

section
namespace TauCeti

universe uR uRm uS uSm uL

variable {R : Type uR} {Rₘ : Type uRm} {S : Type uS} {Sₘ : Type uSm} {L : Type uL}
variable [CommRing R] [CommRing Rₘ] [CommSemiring S] [CommSemiring Sₘ] [CommRing L]
variable {M : Submonoid R}
variable [Algebra R Rₘ] [Algebra R S] [Algebra R L]
variable [Algebra Rₘ L] [Algebra S Sₘ] [Algebra S L] [Algebra Sₘ L]
variable [IsScalarTower R Rₘ L] [IsScalarTower R S L] [IsScalarTower S Sₘ L]
variable [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
variable [IsLocalization M Rₘ]

include Rₘ L M in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Localization/Integral.lean:49` (proof source at `5a01f5fe3621`).
 If `Rₘ` is a localization of `R`, then an integral closure of `Rₘ` in a commutative ring `L`
is the corresponding localization of an integral closure of `R` in `L`.
The maps `R → Rₘ → L`, `R → S → L`, and `S → Sₘ → L` must agree with the direct maps
to `L`.

Unlike `IsLocalization.integralClosure`, this applies when the original integral closure is an
arbitrary type satisfying `IsIntegralClosure`, rather than the literal `integralClosure R L`. -/
theorem isLocalization_algebraMapSubmonoid_of_isIntegralClosure :
    IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, m, hm, rfl⟩
    -- The inverse in `Rₘ` maps to an integral element of `L`, hence lifts to `Sₘ`.
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp (IsLocalization.map_units Rₘ ⟨m, hm⟩)
    obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (A := Sₘ) (R := Rₘ)).mp
      (isIntegral_algebraMap (A := L) (x := z))
    apply isUnit_iff_exists_inv.mpr
    refine ⟨s, IsIntegralClosure.algebraMap_injective Sₘ Rₘ L ?_⟩
    simpa only [map_mul, map_one, ← IsScalarTower.algebraMap_apply S Sₘ L,
      ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R Rₘ L, hs]
      using congrArg (algebraMap Rₘ L) hz
  · intro y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := R) (Rₘ := Rₘ) M (algebraMap Sₘ L y)
        ((IsIntegralClosure.isIntegral_iff (A := Sₘ) (R := Rₘ)).mpr ⟨y, rfl⟩)
    obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (A := S) (R := R)).mp hm
    refine ⟨⟨s, algebraMap R S m, m, m.2, rfl⟩, ?_⟩
    apply IsIntegralClosure.algebraMap_injective Sₘ Rₘ L
    rw [map_mul, ← IsScalarTower.algebraMap_apply S Sₘ L,
      ← IsScalarTower.algebraMap_apply S Sₘ L,
      ← IsScalarTower.algebraMap_apply R S L, hs,
      Submonoid.smul_def, Algebra.smul_def, mul_comm]
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul]
    apply IsIntegralClosure.algebraMap_injective S R L
    have h := congrArg (algebraMap Sₘ L) hxy
    simpa only [IsScalarTower.algebraMap_apply S Sₘ L] using h

end TauCeti

end

end

/-! ## Source 7: `TauCeti.FieldTheory.FunctionField.Different.Localization`
Original source SHA256: `42eb5bf9190e5a7dc8d8e150febd786545a38cba23258730853ab78a41abb5c0`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Reading the different exponent on an arbitrary affine model

The different exponent `d(P' ∣ P)` of a place `P'` of `F' / k'` is defined on the local model
`𝒪_P ⊆ 𝒪'_P` at `P = P'.restrict k F`.  This file shows that it may be read on *any* affine model
of `F` on which `P'` is finite: if `B` is such a model and `C` is its integral closure in `F'`,
then `d(P' ∣ P)` is the coefficient of `differentIdeal B C` at the centre of `P'` on `C`.

The local model is the localization of `B` at the centre of `P`, and `𝒪'_P` is the matching
localization of `C`, so this is the localization invariance of the coefficients of the different
ideal, `TauCeti.multiplicity_differentIdeal_eq_multiplicity_under`.

## Main results

* `TauCeti.Place.differentExponent_eq_multiplicity_center`: the different exponent is the
  coefficient of the different ideal of an affine model at the centre of the place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.4.
-/

section
open IsDedekindDomain Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra k F']
variable [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable {B : Type*} {C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F]
  [IsFractionRing B F] [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
  [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
  [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Localization.lean:65` (proof source at `5a01f5fe3621`).
 **The different exponent can be read on an affine model**: if `P'` is finite on the integral
closure `C` in `F'` of an affine model `B` of `F`, then `d(P' ∣ P)` is the coefficient of the
different ideal of `C` over `B` at the centre of `P'`. -/
theorem differentExponent_eq_multiplicity_center (P' : Place k' F')
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    differentExponent k F P' = multiplicity (P'.center hC).asIdeal (differentIdeal B C) := by
  -- After localizing at the centre of `P` (below),
  -- `TauCeti.multiplicity_differentIdeal_eq_multiplicity_under` compares the two coefficients.
  let P : Place k F := P'.restrict k F
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P.center hB
  -- Localize at `p`: `𝒪_P` is the localization of `B`, and its integral closure `Cₘ` in `F'`
  -- is the matching localization of `C`.  Mathlib's `IsLocalization.integralClosure` is stated
  -- for the literal `integralClosure B F'`, whereas `C` is an arbitrary integral closure, so
  -- `TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure` supplies the abstract
  -- version needed.
  let Bₘ := P.integers
  let Cₘ := integralClosure Bₘ F'
  let _ : Algebra B Bₘ := ((algebraMap B F).codRestrict Bₘ hB).toAlgebra
  let _ : IsScalarTower B Bₘ F := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[B] Bₘ :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring
          (P.valuationSubringAtPrime_eq_integers hB)))
      fun _ ↦ rfl
  let _ : IsLocalization p.asIdeal.primeCompl Bₘ :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eB
  let _ : IsScalarTower B Bₘ F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply B F F' x
  let _ : Algebra C Cₘ :=
    ((algebraMap C F').codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := Bₘ)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  let _ : IsScalarTower C Cₘ F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B C F' x
  let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B F F' x
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F') (M := p.asIdeal.primeCompl)
  -- The centre of `P'` on `Cₘ` contracts to the centre on `C`, so localization preserves the
  -- coefficient.
  have hunder : (centerIntegralClosure k F P').asIdeal.under C = (P'.center hC).asIdeal := by
    ext c
    rw [Ideal.mem_under]
    simp only [centerIntegralClosure_def, mem_center_asIdeal]
    rw [← IsScalarTower.algebraMap_apply C Cₘ F']
  rw [differentExponent_def, ← hunder]
  exact multiplicity_differentIdeal_eq_multiplicity_under (R := B) (Rₘ := Bₘ) (S := C)
    (Sₘ := Cₘ) (K := F) (L := F') (M := p.asIdeal.primeCompl)
    (centerIntegralClosure k F P').ne_bot

end Place

end TauCeti

end

end

/-! ## Source 8: `TauCeti.FieldTheory.FunctionField.Different.Derivative`
Original source SHA256: `913be6abcd0daefde2813ca3689d7cb87d46a04f55d0fb00a8b2096727dee819`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The different exponent and derivatives of generating equations

Let `F' / k'` be an extension of the field extension `F / k` with `F' / F` finite and separable,
let `P'` be a place of `F'` over the place `P` of `F`, and suppose `F' = F(y)`. If `y` is a root
of a monic polynomial `ψ` with coefficients in the valuation ring `𝒪_P`, then

`d(P' ∣ P) ≤ ord_{P'} (ψ'(y))`

provided `ψ'(y) ≠ 0` (Stichtenoth, Theorem 3.5.10(a), where `ψ` is the minimal polynomial of
`y`). This is the tool that computes different exponents from an explicit equation: a place at
which `ψ'(y)` is a unit is unramified, with `d(P' ∣ P) = 0`.

When an integral element generates the full local integral closure, the corresponding bound is
an equality for the derivative of its minimal polynomial (Stichtenoth, Theorem 3.5.10(b)). The
same holds for a generator of the integral closure `C` in `F'` of an affine model `B` of `F`, at
every place `P'` finite on `C`.

## Main results

* `TauCeti.Place.differentExponent_le_ord_aeval_derivative`: `d(P' ∣ P) ≤ ord_{P'} (ψ'(y))`.
* `TauCeti.Place.differentExponent_le_ord_two_mul_add`: the case of a quadratic equation
  `z² + u z - v = 0`, where `ψ'(z) = 2 z + u`.
* `TauCeti.Place.differentExponent_eq_ord_aeval_derivative_minpoly`: equality for a generator of
  the integral closure.
* `TauCeti.Place.differentExponent_eq_ord_aeval_derivative_minpoly_of_isIntegralClosure`: equality
  for a generator of the integral closure of an affine model.
* `TauCeti.Place.differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one`: if `ψ'(y)` is a
  unit at `P'`, then `d(P' ∣ P) = 0`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.10.
-/

section
open Polynomial

open scoped _root_.IntermediateField

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F) {P' : Place k' F'}

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Derivative.lean:76` (proof source at `5a01f5fe3621`).
 **The different exponent is bounded by the derivative of a generating equation**
(Stichtenoth, Theorem 3.5.10(a)): if `F' = F(y)` and `y` is a root of a monic `ψ ∈ F[X]` whose
coefficients are regular at the place `P` below `P'`, then `d(P' ∣ P) ≤ ord_{P'} (ψ'(y))`, as
long as `ψ'(y) ≠ 0`. Stichtenoth takes `ψ` to be the minimal polynomial of `y`; any monic multiple
of it with coefficients in `𝒪_P` works as well. -/
theorem differentExponent_le_ord_aeval_derivative {y : F'} (hgen : F⟮y⟯ = ⊤) {ψ : F[X]}
    (hψ : ψ.Monic) (hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers)
    (hy : aeval y ψ = 0) (hψ' : aeval y (derivative ψ) ≠ 0) :
    (differentExponent k F P' : ℤ) ≤ P'.ord (aeval y (derivative ψ)) := by
  set A := (P'.restrict k F).integers
  -- Lift `ψ` to a monic polynomial `q` over `𝒪_P`.
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := algebraMap A F) ψ).mpr fun i ↦ ⟨⟨_, hcoeff i⟩, rfl⟩) hψ
  have hqy : aeval y q = 0 := by rw [← aeval_map_algebraMap F, hq, hy]
  -- So `y` is integral over `𝒪_P`: it is an element `x` of the local model `𝒪'_P`.
  have hint : IsIntegral A y := ⟨q, hqm, by rwa [← aeval_def]⟩
  set x : integralClosure A F' := ⟨y, hint⟩
  have hx : algebraMap (integralClosure A F') F' x = y := rfl
  have hgen' : Algebra.adjoin F {algebraMap (integralClosure A F') F' x} = ⊤ := by
    rw [hx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic y), hgen, IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (algebraMap (integralClosure A F') F') :=
    FaithfulSMul.algebraMap_injective _ _
  have hqx : aeval x q = 0 := hinj (by rw [← aeval_algebraMap_apply, hx, hqy, map_zero])
  have hmem : aeval x (derivative q) ∈ differentIdeal A (integralClosure A F') :=
    aeval_derivative_mem_differentIdeal_of_aeval_eq_zero (K := F) (L := F') hgen' hqx
  have hval : algebraMap (integralClosure A F') F' (aeval x (derivative q)) =
      aeval y (derivative ψ) := by
    rw [← aeval_algebraMap_apply, hx, ← hq, derivative_map, aeval_map_algebraMap]
  have hne : aeval x (derivative q) ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hval
    exact hψ' hval.symm
  rw [← hval]
  exact differentExponent_le_ord_of_mem_differentIdeal k F P' hmem hne

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Derivative.lean:110` (proof source at `5a01f5fe3621`).
 **The different exponent of a quadratic equation**: if `F' = F(z)` with
`z² + u z - v = 0` and `u, v ∈ F` regular at `P'`, then `d(P' ∣ P) ≤ ord_{P'} (2 z + u)`, as long
as `2 z + u ≠ 0`. This is `differentExponent_le_ord_aeval_derivative` for `ψ = X² + u X - v`. -/
theorem differentExponent_le_ord_two_mul_add {u v : F} (hu : algebraMap F F' u ∈ P'.integers)
    (hv : algebraMap F F' v ∈ P'.integers) {z : F'} (hgen : F⟮z⟯ = ⊤)
    (hz : z ^ 2 + algebraMap F F' u * z - algebraMap F F' v = 0)
    (hne : 2 * z + algebraMap F F' u ≠ 0) :
    (differentExponent k F P' : ℤ) ≤ P'.ord (2 * z + algebraMap F F' u) := by
  have hψ : (X ^ 2 + C u * X - C v : F[X]).Monic := by monicity!
  have hderiv : aeval z (derivative (X ^ 2 + C u * X - C v : F[X])) =
      2 * z + algebraMap F F' u := by
    simp only [derivative_sub, derivative_X_pow, derivative_C_mul_X, derivative_C, sub_zero,
      map_add, map_mul, aeval_C, Nat.cast_ofNat, map_ofNat]
    norm_num
  rw [← hderiv]
  refine differentExponent_le_ord_aeval_derivative k F hgen hψ (fun i ↦ ?_)
    (by simpa using hz) (by rwa [hderiv])
  rw [mem_integers_restrict_iff]
  rcases i with _ | _ | _ | i <;>
    simp [coeff_X, coeff_C, coeff_X_pow, neg_mem_iff, hu, hv]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Derivative.lean:130` (proof source at `5a01f5fe3621`).
 For a generator of the integral closure over the valuation ring, the different exponent is
the order of the derivative of its field minimal polynomial. -/
theorem differentExponent_eq_ord_aeval_derivative_minpoly
    {x : integralClosure (P'.restrict k F).integers F'}
    (hx : Algebra.adjoin (P'.restrict k F).integers {x} = ⊤) :
    (differentExponent k F P' : ℤ) = P'.ord
      (aeval (algebraMap (integralClosure (P'.restrict k F).integers F') F' x)
        (derivative (minpoly F
          (algebraMap (integralClosure (P'.restrict k F).integers F') F' x)))) := by
  let A := (P'.restrict k F).integers
  let B := integralClosure A F'
  have hdifferent := residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly A F F' B x hx
  have hderiv0 : aeval x (derivative (minpoly A x)) ≠ 0 := by
    intro h
    exact differentIdeal_ne_bot (A := A) (B := B)
      (by rw [hdifferent, h, Ideal.span_singleton_eq_bot])
  have hmap : algebraMap B F' (aeval x (derivative (minpoly A x))) =
      aeval (algebraMap B F' x) (derivative (minpoly F (algebraMap B F' x))) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions F F'
        (integralClosure.isIntegral x), derivative_map, aeval_map_algebraMap,
      aeval_algebraMap_apply]
  rw [← hmap, differentExponent_def, hdifferent,
    P'.ord_algebraMap_eq_multiplicity_center
      (algebraMap_mem_integers_of_mem_integralClosure k F P') hderiv0,
    ← centerIntegralClosure_def]

section AffineModel

variable {B : Type*} {C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F]
  [IsFractionRing B F] [CommRing C] [Algebra C F'] [Algebra B C] [Algebra B F']
  [IsScalarTower B C F'] [IsScalarTower B F F'] [IsIntegralClosure C B F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Derivative.lean:164` (proof source at `5a01f5fe3621`).
 **The different exponent from a generator of an affine model**: if `y` generates the integral
closure `C` in `F'` of an affine model `B` of `F` as a `B`-algebra, then at every place `P'`
finite on `C` the different exponent is the order of the derivative of the minimal polynomial
of `y`. -/
theorem differentExponent_eq_ord_aeval_derivative_minpoly_of_isIntegralClosure (P' : Place k' F')
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) {y : C} (hy : Algebra.adjoin B {y} = ⊤) :
    (differentExponent k F P' : ℤ) =
      P'.ord (aeval (algebraMap C F' y) (derivative (minpoly F (algebraMap C F' y)))) := by
  have : IsDomain C := (IsIntegralClosure.algebraMap_injective C B F').isDomain
  have : Module.IsTorsionFree B F' := .trans_faithfulSMul B F F'
  have : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B F'
  have := IsIntegralClosure.isFractionRing_of_finite_extension B F F' C
  have := IsIntegralClosure.isDedekindDomain B F F' C
  have hmap : algebraMap C F' (aeval y (derivative (minpoly B y))) =
      aeval (algebraMap C F' y) (derivative (minpoly F (algebraMap C F' y))) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions F F'
        (IsIntegralClosure.isIntegral B F' y), derivative_map, aeval_map_algebraMap,
      aeval_algebraMap_apply]
  have hne : aeval y (derivative (minpoly B y)) ≠ 0 := fun h ↦
    (Algebra.IsSeparable.isSeparable F (algebraMap C F' y)).aeval_derivative_ne_zero
      (minpoly.aeval F _) (by rw [← hmap, h, map_zero])
  rw [differentExponent_eq_multiplicity_center (B := B) P' hC,
    residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly B F F' C y hy, ← hmap,
    P'.ord_algebraMap_eq_multiplicity_center hC hne]

end AffineModel

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Derivative.lean:191` (proof source at `5a01f5fe3621`).
 **A place at which the derivative of a generating equation is a unit is unramified**
(Stichtenoth, Theorem 3.5.10(a)): if `F' = F(y)`, `y` is a root of a monic `ψ ∈ F[X]` whose
coefficients are regular at the place `P` below `P'`, and `ψ'(y)` is a unit at `P'`, then
`d(P' ∣ P) = 0`. -/
theorem differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one {y : F'}
    (hgen : F⟮y⟯ = ⊤) {ψ : F[X]} (hψ : ψ.Monic)
    (hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers) (hy : aeval y ψ = 0)
    (hψ' : P'.valuation (aeval y (derivative ψ)) = 1) :
    differentExponent k F P' = 0 := by
  have hne : aeval y (derivative ψ) ≠ 0 := fun h0 ↦ by simp [h0] at hψ'
  have hord : P'.ord (aeval y (derivative ψ)) = 0 := by
    rw [P'.ord_eq_iff_valuation_eq_exp_neg hne, neg_zero, WithZero.exp_zero, hψ']
  have := differentExponent_le_ord_aeval_derivative k F hgen hψ hcoeff hy hne
  omega

end Place

end TauCeti
end

end

/-! ## Source 9: `TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.InvariantDifferential`
Original source SHA256: `48da8493f17c384050cedda36288fd9a7afc7988bea054917a0fd096431efc3c`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Proof-only: `F(x)⟮y⟯ = F(W)`, the generation hypothesis of the different bound.
-- Proof-only: the bound of the different exponent by the derivative of an equation.

/-!
# The divisor of the invariant differential

Let `W` be an elliptic Weierstrass curve over a field `F`, with function field `F(W)` and
coordinate functions `x` and `y`. Its invariant differential `ω = dx / (2y + a₁x + a₃)` lives in
the Kähler differentials `Ω[F(W)/F]`, and the Kähler–Weil comparison determined by the separating
element `x` carries it to a nonzero Weil differential of `F(W) / F`. This file proves that this
Weil differential has **divisor zero**: `ω` is regular and nonvanishing at every place of `F(W)`
(Silverman, Proposition III.1.5).

The divisor of `dx` is `-2 (x)_∞ + Diff(F(W) / F(x))`, so

`(ω) = -div (2y + a₁x + a₃) - 2 (x)_∞ + Diff(F(W) / F(x))`.

No different exponent has to be computed exactly. At a place `P` where `x` is regular, `y` is a
root of `Y² + (a₁x + a₃) Y - (x³ + a₂x² + a₄x + a₆)`, a monic equation over the valuation ring
below `P` whose derivative at `y` is `2y + a₁x + a₃`; at a pole of `x`, the function `y / x²` is a
root of the monic equation obtained by dividing by `x⁴`, whose coefficients are polynomials in
`1 / x`, and whose derivative at `y / x²` is `(2y + a₁x + a₃) / x²`. Bounding the different
exponent by the order of these derivatives shows that every coefficient of `(ω)` is at most zero.
Since `(ω)` has degree `2g - 2 = 0`, it is zero.

## Main results

All in the namespace `WeierstrassCurve.Affine`:

* `kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential`: the Kähler–Weil
  comparison sends `ω` to `(2y + a₁x + a₃)⁻¹ · dx`.
* `weilDifferentialDivisor_invariantDifferential`: **the invariant differential has divisor
  zero.**

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Proposition III.1.5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.10 and Remark 4.3.7.
-/

section
open Polynomial TauCeti _root_.AlgebraicGeometry

open scoped _root_.IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-! ### The local bound -/

section Local

/-- Kind: THEOREM. Locator: `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean:69` (proof source at `5a01f5fe3621`).
 The rational function field acts on `F(W)` through `x`, compatibly with `F[X]`. -/
private theorem isScalarTower_polynomial_ratFunc :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    IsScalarTower F[X] (RatFunc F) W.FunctionField := by
  let _ := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
  refine .of_algebraMap_eq fun p ↦ ?_
  rw [algebraMap_ratFuncAlgebraOfTranscendental_apply, RatFunc.algEquivOfTranscendental_algebraMap,
    algebraMap_eq_aeval_genericX]
  simp

/-- Kind: THEOREM. Locator: `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean:79` (proof source at `5a01f5fe3621`).
 The Weierstrass equation at the generic point, written out in `F(W)`. -/
private theorem genericY_sq_add_eq :
    genericY W ^ 2 + algebraMap F W.FunctionField W.a₁ * genericX W * genericY W +
        algebraMap F W.FunctionField W.a₃ * genericY W =
      genericX W ^ 3 + algebraMap F W.FunctionField W.a₂ * genericX W ^ 2 +
        algebraMap F W.FunctionField W.a₄ * genericX W + algebraMap F W.FunctionField W.a₆ := by
  have h := (equation_iff _ _).mp (equation_genericX_genericY W)
  simpa [WeierstrassCurve.baseChange] using h

variable [W.IsElliptic]

/-- Kind: THEOREM. Locator: `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean:91` (proof source at `5a01f5fe3621`).
 **The local bound behind `(ω) = 0`**: at every place `P` of `F(W)`, the different exponent of
`F(W) / F(x)` is at most `ord_P (2y + a₁x + a₃) + 2 max(-ord_P x, 0)`. -/
private theorem differentExponent_le (P : Place F W.FunctionField) :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isFunctionField_iff_functionField.mp W.isFunctionField
    letI := isSeparable_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    (Place.differentExponent F (RatFunc F) P : ℤ) ≤
      P.ord (invariantDifferentialDenom W) + 2 * (-P.ord (genericX W) ⊔ 0) := by
  let hx := transcendental_genericX W
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp W.isFunctionField
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_polynomial_ratFunc W
  have heq := genericY_sq_add_eq W
  set x := genericX W
  set y := genericY W
  have hX : algebraMap (RatFunc F) W.FunctionField RatFunc.X = x :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have hC (c : F) : algebraMap (RatFunc F) W.FunctionField (algebraMap F (RatFunc F) c) =
      algebraMap F W.FunctionField c :=
    (IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField c).symm
  have hc (c : F) : algebraMap F W.FunctionField c ∈ P.integers := P.algebraMap_mem_integers c
  have hden : invariantDifferentialDenom W =
      2 * y + algebraMap F W.FunctionField W.a₁ * x + algebraMap F W.FunctionField W.a₃ :=
    invariantDifferentialDenom_def W
  -- `omega` treats `genericX W` and its abbreviation `x` as distinct atoms.
  have hxx : P.ord (genericX W) = P.ord x := rfl
  rcases le_or_gt 0 (P.ord x) with hxP | hxP
  · -- `x` is regular at `P`: use the Weierstrass equation for `y` itself.
    have hxi : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr hxP
    have hu : 2 * y + algebraMap (RatFunc F) W.FunctionField
        (algebraMap F (RatFunc F) W.a₁ * RatFunc.X + algebraMap F (RatFunc F) W.a₃) =
        invariantDifferentialDenom W := by
      simp only [map_add, map_mul, hX, hC, hden]
      ring
    have h := Place.differentExponent_le_ord_two_mul_add F (RatFunc F) (P' := P)
      (u := algebraMap F (RatFunc F) W.a₁ * RatFunc.X + algebraMap F (RatFunc F) W.a₃)
      (v := RatFunc.X ^ 3 + algebraMap F (RatFunc F) W.a₂ * RatFunc.X ^ 2 +
        algebraMap F (RatFunc F) W.a₄ * RatFunc.X + algebraMap F (RatFunc F) W.a₆) (z := y)
      (by simp only [map_add, map_mul, hX, hC]; exact add_mem (mul_mem (hc _) hxi) (hc _))
      (by
        simp only [map_add, map_mul, map_pow, hX, hC]
        exact add_mem (add_mem (add_mem (pow_mem hxi _) (mul_mem (hc _) (pow_mem hxi _)))
          (mul_mem (hc _) hxi)) (hc _))
      (adjoin_genericY_eq_top W (RatFunc F))
      (by simp only [map_add, map_mul, map_pow, hX, hC]; linear_combination heq)
      (by rw [hu]; exact invariantDifferentialDenom_ne_zero W)
    rw [hu] at h
    omega
  · -- `x` has a pole at `P`: use the equation for `y / x²`, with coefficients in `F[1 / x]`.
    have hx0 : x ≠ 0 := hx.ne_zero
    have hti : x⁻¹ ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, P.ord_inv]
      omega
    have hgen : (RatFunc F)⟮y * x⁻¹ ^ 2⟯ = ⊤ := by
      refine top_le_iff.mp ((adjoin_genericY_eq_top W (RatFunc F)).symm.le.trans ?_)
      rw [IntermediateField.adjoin_simple_le_iff]
      have hy : y = algebraMap (RatFunc F) W.FunctionField (RatFunc.X ^ 2) * (y * x⁻¹ ^ 2) := by
        rw [map_pow, hX]
        field_simp
      have hmem := mul_mem
        (IntermediateField.algebraMap_mem (RatFunc F)⟮y * x⁻¹ ^ 2⟯ (RatFunc.X ^ 2))
        (IntermediateField.mem_adjoin_simple_self (RatFunc F) (y * x⁻¹ ^ 2))
      rwa [← hy] at hmem
    have hu : 2 * (y * x⁻¹ ^ 2) + algebraMap (RatFunc F) W.FunctionField
        (algebraMap F (RatFunc F) W.a₁ * RatFunc.X⁻¹ +
          algebraMap F (RatFunc F) W.a₃ * RatFunc.X⁻¹ ^ 2) =
        invariantDifferentialDenom W * (x ^ 2)⁻¹ := by
      simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC, hden]
      field_simp
      ring
    have hx2 : (x ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hx0)
    have h := Place.differentExponent_le_ord_two_mul_add F (RatFunc F) (P' := P)
      (u := algebraMap F (RatFunc F) W.a₁ * RatFunc.X⁻¹ +
        algebraMap F (RatFunc F) W.a₃ * RatFunc.X⁻¹ ^ 2)
      (v := RatFunc.X⁻¹ + algebraMap F (RatFunc F) W.a₂ * RatFunc.X⁻¹ ^ 2 +
        algebraMap F (RatFunc F) W.a₄ * RatFunc.X⁻¹ ^ 3 +
        algebraMap F (RatFunc F) W.a₆ * RatFunc.X⁻¹ ^ 4) (z := y * x⁻¹ ^ 2)
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        exact add_mem (mul_mem (hc _) hti) (mul_mem (hc _) (pow_mem hti _)))
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        exact add_mem (add_mem (add_mem hti (mul_mem (hc _) (pow_mem hti _)))
          (mul_mem (hc _) (pow_mem hti _))) (mul_mem (hc _) (pow_mem hti _)))
      hgen
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        field_simp
        linear_combination heq)
      (by rw [hu]; exact mul_ne_zero (invariantDifferentialDenom_ne_zero W) hx2)
    rw [hu, P.ord_mul (invariantDifferentialDenom_ne_zero W) hx2, P.ord_inv, P.ord_pow] at h
    push_cast at h
    omega

end Local

/-! ### The divisor of the invariant differential -/

section Divisor

variable [W.IsElliptic]

/-- Kind: THEOREM. Locator: `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean:196` (proof source at `5a01f5fe3621`).
 **The invariant differential as a Weil differential**: the Kähler–Weil comparison determined
by the separating element `x` sends `ω = dx / (2y + a₁x + a₃)` to `(2y + a₁x + a₃)⁻¹ · dx`. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential :
    letI := weilDifferentialSpaceModule W.isFunctionField
    kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
        (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
        (invariantDifferential W) =
      (invariantDifferentialDenom W)⁻¹ •
        weilDifferentialOfSeparating W.isFunctionField (transcendental_genericX W) := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [invariantDifferential_def, map_smul,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

/-- Kind: THEOREM. Locator: `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean:208` (proof source at `5a01f5fe3621`).
 The Weil differential attached to the invariant differential is nonzero. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero :
    letI := weilDifferentialSpaceModule W.isFunctionField
    ((kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
        (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
        (invariantDifferential W) : ↥(weilDifferentialSpace F W.FunctionField)) :
          Module.Dual F ↥(repartitionSpace F W.FunctionField)) ≠ 0 := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
  exact invariantDifferential_ne_zero W

/-- Kind: THEOREM. Locator: `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean:222` (proof source at `5a01f5fe3621`).
 **The invariant differential has divisor zero** (Silverman, Proposition III.1.5): under the
Kähler–Weil comparison determined by `x`, the invariant differential `ω = dx / (2y + a₁x + a₃)`
of an elliptic curve is a Weil differential of `F(W) / F` with neither zeros nor poles. -/
@[simp]
theorem weilDifferentialDivisor_invariantDifferential :
    letI := weilDifferentialSpaceModule W.isFunctionField
    weilDifferentialDivisor W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
          (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
          (invariantDifferential W)).2
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero W) =
      0 := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  let hF := W.isFunctionField
  let hex := isIntegrallyClosedIn_functionField W
  let hx := transcendental_genericX W
  -- `(ω) = -div (2y + a₁x + a₃) + (dx)`, by the transformation law of Weil divisors.
  let z : W.FunctionFieldˣ := Units.mk0 (invariantDifferentialDenom W)⁻¹
    (inv_ne_zero (invariantDifferentialDenom_ne_zero W))
  have hD := weilDifferentialDivisor_repartitionDualMul hF hex
    (weilDifferentialOfSeparating hF hx).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) z
  rw [weilDifferentialDivisor_weilDifferentialOfSeparating] at hD
  have hω : ((kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx
      (invariantDifferential W) : ↥(weilDifferentialSpace F W.FunctionField)) :
        Module.Dual F ↥(repartitionSpace F W.FunctionField)) =
      repartitionDualMul hF (z : W.FunctionField) (weilDifferentialOfSeparating hF hx) := by
    rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential,
      coe_weilDifferentialSpaceModule_smul, Units.val_mk0]
  -- `(ω)` has degree `2g - 2 = 0`, so it suffices to show that `(ω) ≤ 0`.
  refine Divisor.eq_of_le_of_degree_eq hF ?_ ?_
  · rw [(weilDifferentialDivisor_congr hF hex hω _ _ _ _).trans hD, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.le_iff]
    intro P
    have h := differentExponent_le W P
    simp only [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_add, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, Divisor.coeff_principal,
      Divisor.coeff_poles, Divisor.coeff_different, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zero, z, Units.val_mk0,
      P.ord_inv]
    omega
  · rw [degree_weilDifferentialDivisor, genus_functionField, map_zero]
    norm_num

end Divisor

end WeierstrassCurve.Affine
end

end

/-! ## Source 10: `TauCeti.FieldTheory.Frobenius.Range`
Original source SHA256: `3156c4e0b264c3a6839bce7584a0059ac246607e111e9452f66ee96f0c725a0c`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Frobenius power subfields over perfect constants

If `k` is perfect of exponential characteristic `p`, the `p^n`-th powers in an extension `F`
form an intermediate field of `F / k`. Iterated Frobenius identifies `F` with this field,
semilinearly over the corresponding Frobenius automorphism of `k`. The construction uses
Mathlib's `RingHom.fieldRange` and `RingHom.rangeRestrictFieldEquiv`.

This distinguishes an isomorphism of abstract fields preserving the constant subfield from a
`k`-algebra isomorphism: Frobenius need not fix each element of `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.10.
-/

section
namespace TauCeti

variable (k F : Type*) [Field k] [Field F] [Algebra k F]
variable (p : ℕ) [ExpChar k p] [PerfectRing k p] (n : ℕ)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:35` (proof source at `5a01f5fe3621`).
 The intermediate field `F^{p^n}` of iterated Frobenius powers. Perfectness ensures that
it contains every constant from `k`. -/
noncomputable def frobeniusPowers : IntermediateField k F := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  exact (iterateFrobenius F p n).fieldRange.toIntermediateField fun c ↦ by
    refine ⟨algebraMap k F ((iterateFrobeniusEquiv k p n).symm c), ?_⟩
    rw [← RingHom.map_iterateFrobenius, ← coe_iterateFrobeniusEquiv,
      RingEquiv.apply_symm_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:43` (proof source at `5a01f5fe3621`).
 The underlying subfield is Mathlib's field range of iterated Frobenius. -/
theorem frobeniusPowers_toSubfield :
    letI : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
    (frobeniusPowers k F p n).toSubfield = (iterateFrobenius F p n).fieldRange := by
  unfold frobeniusPowers
  exact Subfield.toIntermediateField_toSubfield _ _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:51` (proof source at `5a01f5fe3621`).
 Membership in the Frobenius power subfield means being a `p^n`-th power in `F`. -/
@[simp]
theorem mem_frobeniusPowers (z : F) :
    z ∈ frobeniusPowers k F p n ↔ ∃ x : F, x ^ p ^ n = z := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  rw [← IntermediateField.mem_toSubfield, frobeniusPowers_toSubfield, RingHom.mem_fieldRange]
  simp only [iterateFrobenius_def]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:59` (proof source at `5a01f5fe3621`).
 Iterated Frobenius as an isomorphism from `F` onto its power subfield. It is semilinear,
not generally linear, over `k`. -/
noncomputable def iterateFrobeniusEquivPowers : F ≃+* frobeniusPowers k F p n := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  -- Adding the proof that the range contains `k` does not change its underlying field.
  unfold frobeniusPowers
  exact (iterateFrobenius F p n).rangeRestrictFieldEquiv

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:67` (proof source at `5a01f5fe3621`).
 The field isomorphism onto the power subfield sends `x` to `x^{p^n}`. -/
@[simp]
theorem coe_iterateFrobeniusEquivPowers (x : F) :
    (iterateFrobeniusEquivPowers k F p n x : F) = x ^ p ^ n := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  exact (RingHom.rangeRestrictFieldEquiv_apply_coe (iterateFrobenius F p n) x).trans
    (iterateFrobenius_def p n x)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:75` (proof source at `5a01f5fe3621`).
 On constants, the power-subfield isomorphism acts by the Frobenius automorphism of `k`. -/
@[simp]
theorem iterateFrobeniusEquivPowers_algebraMap (c : k) :
    iterateFrobeniusEquivPowers k F p n (algebraMap k F c) =
      algebraMap k (frobeniusPowers k F p n) (iterateFrobeniusEquiv k p n c) := by
  apply Subtype.ext
  simp [iterateFrobenius_def]

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/Frobenius/Range.lean:82` (proof source at `5a01f5fe3621`).
 The ambient field is purely inseparable over its iterated Frobenius power subfield. -/
instance isPurelyInseparable_frobeniusPowers :
    IsPurelyInseparable (frobeniusPowers k F p n) F := by
  have : ExpChar (frobeniusPowers k F p n) p :=
    expChar_of_injective_algebraMap (algebraMap k _).injective p
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  exact ⟨n, ⟨x ^ p ^ n, (mem_frobeniusPowers k F p n _).mpr ⟨x, rfl⟩⟩, rfl⟩

end TauCeti
end

end

/-! ## Source 11: `TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic`
Original source SHA256: `bc27c7b04ffbabd828ab6ad33f64d961884b95d9af66855e0b47245b7285634a`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Finite extensions of the constant field

A finite extension of constants yields a finite compositum over the original field, and a
separable or purely inseparable extension of constants produces a compositum of the same kind.
Exactness of the original constant field is needed for none of these statements. The function-field
theorem for arbitrary algebraic extensions of constants is in `ConstantExtension.Algebraic`.

Under the hypotheses that make constant field extensions well behaved — the original constant
field `k` is exact in `F` and `k' / k` is separable — the compositum acquires no new separable
constants: no element of `F · k'` outside `k'` is separable over `k'`.  Comparing coordinates in
a basis of constants upgrades this to exactness of `k'` in `F · k'`
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top` in `ConstantExtension.Basis`).
Separability of `k' / k` cannot simply be dropped: over an imperfect `k` an inseparable constant
field extension can enlarge the field of constants beyond `k'`.  For instance,
`k = 𝔽_p(t, u)` is exact in `F = k(x, y)` with `y ^ p = t * x ^ p + u`, but for `k' = k(t ^ (1/p))`
the element `y - t ^ (1/p) * x` of `F · k'` is a `p`-th root of `u`, and `u ^ (1/p) ∉ k'`.

Finite extensions of constants with as many elements as desired always exist, realized as
composita inside an algebraic closure of `F`.  Over a finite constant field this is how arguments
that need many constants, such as choosing a vector outside finitely many proper subspaces, are
carried out after a finite constant field extension.

## Main results

* `TauCeti.finiteDimensional_of_constantCompositum_eq_top`: a compositum with finite constants
  is finite over the original field.
* `TauCeti.finiteDimensional_base_of_constantCompositum_eq_top`: conversely, for an exact `k` and
  separable `k' / k`, a compositum finite over the original field has finite constants.
* `TauCeti.isSeparable_of_constantCompositum_eq_top`: the compositum of a separable constant
  field extension is separable over the original field.
* `TauCeti.isPurelyInseparable_of_constantCompositum_eq_top`: the compositum of a purely
  inseparable constant field extension is purely inseparable over the original field.
* `TauCeti.separableClosure_eq_bot_of_constantCompositum_eq_top`: for a separable constant field
  extension of an exact constant field, `k'` is separably closed in `F · k'`.
* `TauCeti.adjoin_image_eq_top_of_constantCompositum_eq_top`: generators of `F` over `k` generate
  `F · k'` over `k'`.
* `TauCeti.isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top`: if `F` is separable over
  `k(x)`, then `F · k'` is separable over `k'(x)`.
* `TauCeti.exists_finiteDimensional_lt_card_constantCompositum_eq_top` and
  `TauCeti.exists_finiteDimensional_normal_splits_constantCompositum_eq_top`: finite constant field
  extensions `F · k'` with more than a given number of constants, or with `k'` normal and
  splitting a given polynomial.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Proposition 3.6.1.
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:78` (proof source at `5a01f5fe3621`).
 A compositum with finite constants is finite over the original field. The ambient field
`F'` is assumed to be precisely the compositum of `F` and `k'`. -/
theorem finiteDimensional_of_constantCompositum_eq_top [FiniteDimensional k k']
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional F F' := by
  let : Algebra.EssFiniteType k k' := inferInstance
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k k'
  have htop : IntermediateField.adjoin F ((algebraMap k' F') '' (S : Set k')) = ⊤ := by
    rw [← constantCompositum_eq_adjoin_of_adjoin_eq_top (F := F) (k' := k')
      (F' := F') S hS]
    exact h
  have hfinite : Finite ((algebraMap k' F') '' (S : Set k')) :=
    S.finite_toSet.image _
  let : Finite ((algebraMap k' F') '' (S : Set k')) := hfinite
  have hi : ∀ x ∈ (algebraMap k' F') '' (S : Set k'), IsIntegral F x := by
    rintro x ⟨c, _, rfl⟩
    exact (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  have := IntermediateField.finiteDimensional_adjoin hi
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:100` (proof source at `5a01f5fe3621`).
 **Finiteness of the compositum detects finiteness of the constants**: if `k` is exact in `F`,
`k' / k` is separable and the compositum `F · k'` is finite over `F`, then `k' / k` is finite.  This
is the converse of `TauCeti.finiteDimensional_of_constantCompositum_eq_top`, by the degree identity
`[F · k' : F] = [k' : k]` of linear disjointness. -/
theorem finiteDimensional_base_of_constantCompositum_eq_top [FiniteDimensional F F']
    [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional k k' := by
  have hrank := finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex
  rw [h, IntermediateField.finrank_top'] at hrank
  exact Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:109` (proof source at `5a01f5fe3621`).
 A separable extension of the constant field produces a separable compositum over the
original field. -/
theorem isSeparable_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) : Algebra.IsSeparable F F' := by
  rw [← IntermediateField.isSeparable_top]
  rw [← hcomp, constantCompositum_def,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  rintro y ⟨c, rfl⟩
  exact IsSeparable.tower_top F <|
    (Algebra.IsSeparable.isSeparable k c).map (IsScalarTower.toAlgHom k k' F')
      (algebraMap k' F').injective

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:121` (proof source at `5a01f5fe3621`).
 Adjoining purely inseparable constants produces a purely inseparable extension of the
original field, whether or not the constant extension is finite. -/
theorem isPurelyInseparable_of_constantCompositum_eq_top [IsPurelyInseparable k k']
    (h : constantCompositum F k' F' = ⊤) : IsPurelyInseparable F F' := by
  obtain ⟨q, _⟩ := ExpChar.exists k
  have := expChar_of_injective_algebraMap (algebraMap k F).injective q
  rw [isPurelyInseparable_iff_perfectClosure_eq_top]
  apply top_le_iff.mp
  rw [← h, constantCompositum_def]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q c
  exact (mem_perfectClosure_iff_pow_mem q).mpr ⟨n, algebraMap k F a, by
    rw [← map_pow, ← ha, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩

/-! ### The constant field of the compositum -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:142` (proof source at `5a01f5fe3621`).
 **The enlarged constant field is separably closed in the compositum**: if `k` is the exact
constant field of `F` and `k' / k` is separable algebraic, then every element of `F · k'` that is
separable over `k'` is already a constant of `k'`.

This is the separable half of Stichtenoth, Proposition 3.6.1(a);
`IsIntegrallyClosedIn.of_constantCompositum_eq_top` upgrades it to exactness of `k'`. -/
theorem separableClosure_eq_bot_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    separableClosure k' F' = ⊥ := by
  refine eq_bot_iff.2 fun z hz ↦ IntermediateField.mem_bot.2 ?_
  refine mem_range_algebraMap_of_mem_adjoin_of_isSeparable_of_isIntegrallyClosedIn hex ?_
    (mem_separableClosure_iff.1 hz)
  rw [← constantCompositum_def, h]
  exact IntermediateField.mem_top

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:154` (proof source at `5a01f5fe3621`).
 **Generators of `F` generate the compositum over `k'`**: if a set `S` generates `F` over `k`,
then its image generates the compositum `F' = F · k'` over `k'`.  For instance, if
`F = k(x, y)` then `F · k' = k'(x, y)`. -/
theorem adjoin_image_eq_top_of_constantCompositum_eq_top {S : Set F}
    (hS : IntermediateField.adjoin k S = ⊤) (h : constantCompositum F k' F' = ⊤) :
    IntermediateField.adjoin k' (algebraMap F F' '' S) = ⊤ := by
  set E := IntermediateField.adjoin k' (algebraMap F F' '' S)
  -- `E` contains the image of `F = k(S)`, so it is an intermediate field of `F' / F`.
  have hFE : ∀ f : F, algebraMap F F' f ∈ E := by
    have hle : IntermediateField.adjoin k S ≤
        (E.restrictScalars k).comap (IsScalarTower.toAlgHom k F F') :=
      IntermediateField.adjoin_le_iff.mpr fun z hz ↦
        IntermediateField.subset_adjoin k' _ ⟨z, hz, rfl⟩
    exact fun f ↦ hle (hS ▸ IntermediateField.mem_top)
  have hle := (constantCompositum_le_iff F k' F'
    (K := E.toSubfield.toIntermediateField hFE)).mpr fun c ↦ E.algebraMap_mem c
  rw [h] at hle
  exact top_le_iff.mp fun z _ ↦ hle IntermediateField.mem_top

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:173` (proof source at `5a01f5fe3621`).
 **A separating element stays separating in the compositum**: if `F` is separable over `k(x)`,
then the compositum `F' = F · k'` is separable over `k'(x)`. No hypothesis on `k' / k` is needed,
since the new constants lie in `k'(x)`. -/
theorem isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top
    (h : constantCompositum F k' F' = ⊤) {x : F} [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable k'⟮algebraMap F F' x⟯ F' := by
  set L := k'⟮algebraMap F F' x⟯
  -- `k(x)` maps into `k'(x)`.
  have hmem (a : k⟮x⟯) : algebraMap F F' a ∈ L := by
    have ha : algebraMap F F' a ∈ k⟮x⟯.map (IsScalarTower.toAlgHom k F F') := ⟨a, a.2, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at ha
    exact (IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.mem_adjoin_simple_self k' (algebraMap F F' x)) :
        k⟮IsScalarTower.toAlgHom k F F' x⟯ ≤ L.restrictScalars k) ha
  let ψ : k⟮x⟯ →+* L :=
    ((algebraMap F F').comp (algebraMap k⟮x⟯ F)).codRestrict L.toSubfield hmem
  have hψ : (algebraMap L F').comp ψ = (algebraMap F F').comp (algebraMap k⟮x⟯ F) :=
    RingHom.ext fun a ↦ RingHom.codRestrict_apply _ _ hmem a
  -- Each element of `F` stays separable: its minimal polynomial over `k(x)`, mapped to `k'(x)`,
  -- is separable and vanishes at it.
  have hsep (z : F) : IsSeparable L (algebraMap F F' z) := by
    have hroot : Polynomial.aeval (algebraMap F F' z) ((minpoly k⟮x⟯ z).map ψ) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hψ,
        ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hp : (minpoly k⟮x⟯ z).Separable := Algebra.IsSeparable.isSeparable k⟮x⟯ z
    exact (hp.map (f := ψ)).of_dvd (minpoly.dvd L _ hroot)
  -- The image of `F` generates `F'` over `k'`, hence over `k'(x)`.
  have htop : IntermediateField.adjoin L (Set.range (algebraMap F F')) = ⊤ := by
    have hk' := adjoin_image_eq_top_of_constantCompositum_eq_top
      (IntermediateField.adjoin_univ k F) h
    rw [Set.image_univ] at hk'
    refine eq_top_iff.mpr fun w _ ↦ ?_
    exact (IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin L _) :
      IntermediateField.adjoin k' _ ≤ (IntermediateField.adjoin L _).restrictScalars k')
        (hk' ▸ IntermediateField.mem_top)
  rw [← IntermediateField.isSeparable_top, ← htop]
  exact (IntermediateField.isSeparable_adjoin_iff_isSeparable L F').mpr fun _ ⟨z, hz⟩ ↦ hz ▸ hsep z

/-! ### Large finite extensions of constants -/

variable (k F) in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:215` (proof source at `5a01f5fe3621`).
 **Large finite constant field extensions exist**: for every `n`, there is a finite extension
`k' / k` with more than `n` elements together with a field `F'`, intermediate between `F` and its
algebraic closure, which is the compositum `F · k'`.  The elements of `k'` are chosen among the
infinitely many elements of the algebraic closure of `k` in that of `F`. -/
theorem exists_finiteDimensional_lt_card_constantCompositum_eq_top (n : ℕ) :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ (n : ℕ∞) < ENat.card k' ∧ constantCompositum F k' F' = ⊤ := by
  classical
  let Ω := AlgebraicClosure F
  let A := algebraicClosure k Ω
  have : IsAlgClosed A := IsAlgClosure.isAlgClosed k
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq A (n + 1)
  -- adjoin the `n + 1` chosen algebraic constants `T` to `F`, and then to `k` inside `F(T)`
  let T : Set Ω := Subtype.val '' (S : Set A)
  let F' := IntermediateField.adjoin F T
  let T' : Set F' := Subtype.val ⁻¹' T
  have hT'T : Subtype.val '' T' = T :=
    Set.image_preimage_eq_of_subset fun x hx ↦ by
      simpa using IntermediateField.subset_adjoin F T hx
  have : Finite T' := (S.finite_toSet.image _).preimage Subtype.val_injective.injOn
  have hint : ∀ x ∈ T', IsIntegral k x := by
    rintro x ⟨a, -, hax⟩
    have hx : IsIntegral k (x : Ω) := by
      rw [← hax]
      exact (mem_algebraicClosure_iff.mp a.2).isIntegral
    exact (isIntegral_algHom_iff (F'.val.restrictScalars k) Subtype.val_injective).mp hx
  refine ⟨F', IntermediateField.adjoin k T', IntermediateField.finiteDimensional_adjoin hint,
    ?_, ?_⟩
  · have hT' : T'.encard = n + 1 := by
      rw [← Subtype.val_injective.injOn.encard_image, hT'T,
        Subtype.val_injective.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard, hS]
      norm_cast
    have hle : T'.encard ≤ ENat.card (IntermediateField.adjoin k T') :=
      (Set.encard_le_encard (IntermediateField.subset_adjoin k T')).trans_eq
        (ENat.card_coe_set_eq _).symm
    rw [hT'] at hle
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle
  · have htop : IntermediateField.adjoin F T' = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, hT'T, IntermediateField.lift_top]
    rw [eq_top_iff, ← htop, constantCompositum_def]
    refine IntermediateField.adjoin.mono _ _ _ fun x hx ↦ ?_
    exact ⟨⟨x, IntermediateField.subset_adjoin k T' hx⟩, rfl⟩

variable (F) in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basic.lean:259` (proof source at `5a01f5fe3621`).
 **A finite normal constant field extension splitting a polynomial exists**: for every
`f ∈ k[X]`, the splitting field `k'` of `f` over `k`, formed inside the algebraic closure of `F`, is
a finite normal extension of `k`, and `F' = F(roots of f)` is the compositum `F · k'`. -/
theorem exists_finiteDimensional_normal_splits_constantCompositum_eq_top (f : Polynomial k) :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ Normal k k' ∧ (f.map (algebraMap k k')).Splits ∧
        Polynomial.IsSplittingField k k' f ∧ constantCompositum F k' F' = ⊤ := by
  let F' := IntermediateField.adjoin F ((f.map (algebraMap k F)).rootSet (AlgebraicClosure F))
  have : Polynomial.IsSplittingField F F' (f.map (algebraMap k F)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hsplit : (f.map (algebraMap k F')).Splits := by
    have := Polynomial.IsSplittingField.splits F' (f.map (algebraMap k F))
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  let k' : IntermediateField k F' := IntermediateField.adjoin k (f.rootSet F')
  have : Polynomial.IsSplittingField k k' f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  refine ⟨F', k', Polynomial.IsSplittingField.finiteDimensional k' f,
    Normal.of_isSplittingField f, Polynomial.IsSplittingField.splits k' f, this, ?_⟩
  -- Each root of `f` in the algebraic closure lies in `F'`, and there it lies in `k'`.
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hle : F' ≤ (constantCompositum F k' F').map F'.val := by
    refine IntermediateField.adjoin_le_iff.mpr fun r hr ↦ ?_
    have hrF' : r ∈ F' := IntermediateField.subset_adjoin _ _ hr
    have hroot : (⟨r, hrF'⟩ : F') ∈ f.rootSet F' := by
      rw [Polynomial.mem_rootSet] at hr ⊢
      refine ⟨fun hf ↦ hr.1 (by rw [hf, Polynomial.map_zero]), Subtype.ext ?_⟩
      rw [Polynomial.aeval_map_algebraMap] at hr
      have hval := Polynomial.aeval_algHom_apply (F'.val.restrictScalars k) (⟨r, hrF'⟩ : F') f
      simp only [AlgHom.coe_restrictScalars', IntermediateField.coe_val] at hval
      rw [← hval, ZeroMemClass.coe_zero]
      exact hr.2
    exact ⟨⟨r, hrF'⟩,
      algebraMap_mem_constantCompositum F k' F' ⟨_, IntermediateField.subset_adjoin k _ hroot⟩, rfl⟩
  -- The preimage `w` of `x` under the inclusion `F · k' → F'` is `x` itself.
  obtain ⟨w, hw, hwx⟩ := hle x.2
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

end TauCeti
end

end

/-! ## Source 12: `TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic`
Original source SHA256: `c7d34e3d185e27e105b5ac09eaa280122c906aa2828f8ac6699663cb15e45483`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Algebraic extensions of the constant field

Adjoining an arbitrary algebraic extension of constants to a function field produces an
algebraic extension of it, and a function field over the enlarged constants, even when the
extension is infinite.  An element of `F` transcendental over `k` stays transcendental over `k'`
in `F'`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Algebraic.lean:40` (proof source at `5a01f5fe3621`).
 The compositum with an algebraic algebra of constants is algebraic over the original field.
The constants need only form a commutative ring, and their map into the ambient field need not
be injective. -/
theorem isAlgebraic_constantCompositum
    {k' : Type u'} [CommRing k'] [Algebra k k'] [Algebra k' F']
    [IsScalarTower k k' F'] [Algebra.IsAlgebraic k k'] :
    Algebra.IsAlgebraic F (constantCompositum F k' F') := by
  rw [constantCompositum_def]
  apply IntermediateField.isAlgebraic_adjoin
  rintro x ⟨c, rfl⟩
  exact (IsIntegral.algebraMap
    ((Algebra.IsAlgebraic.isAlgebraic (R := k) c).isIntegral)).tower_top

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Algebraic.lean:52` (proof source at `5a01f5fe3621`).
 If `F'` is the compositum of `F` with an algebraic algebra of constants, then `F'` is
algebraic over `F`. -/
theorem isAlgebraic_of_constantCompositum_eq_top
    {k' : Type u'} [CommRing k'] [Algebra k k'] [Algebra k' F']
    [IsScalarTower k k' F'] [Algebra.IsAlgebraic k k'] (h : constantCompositum F k' F' = ⊤) :
    Algebra.IsAlgebraic F F' := by
  have halg := isAlgebraic_constantCompositum (k := k) (k' := k') (F := F) (F' := F')
  rw [h] at halg
  exact IntermediateField.topEquiv.isAlgebraic_iff.mp halg

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Algebraic.lean:62` (proof source at `5a01f5fe3621`).
 The compositum is finitely generated over the new constants. A finite field-generating
set for `F / k` also generates `F' / k'`, since the two fields generate the compositum. -/
theorem essFiniteType_of_constantCompositum_eq_top [Algebra.EssFiniteType k F]
    (h : constantCompositum F k' F' = ⊤) : Algebra.EssFiniteType k' F' := by
  classical
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k F
  let T : Set F' := (algebraMap F F') '' (S : Set F)
  let K : IntermediateField k' F' := IntermediateField.adjoin k' T
  have hmap : (IsScalarTower.toAlgHom k F F').fieldRange ≤ K.restrictScalars k := by
    rw [AlgHom.fieldRange_eq_map, ← hS, IntermediateField.adjoin_map]
    exact IntermediateField.adjoin_le_iff.mpr (fun x hx ↦
      IntermediateField.subset_adjoin k' T hx)
  have hmap' (f : F) : algebraMap F F' f ∈ K := by
    apply (IntermediateField.mem_restrictScalars k).1
    apply hmap
    exact (AlgHom.mem_fieldRange).2 ⟨f, rfl⟩
  have hle : (constantCompositum F k' F' : Set F') ⊆ (K : Set F') := by
    rw [constantCompositum_def]
    refine (IntermediateField.adjoin_subset_adjoin_iff F).2 ?_
    constructor
    · rintro x ⟨f, rfl⟩
      exact hmap' f
    · rintro x ⟨c, rfl⟩
      exact K.algebraMap_mem c
  have hK : K = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact hle (by simp [h])
  have hT : T.Finite := S.finite_toSet.image _
  have hfg : (⊤ : IntermediateField k' F').FG := by
    rw [← hK]
    exact IntermediateField.fg_adjoin_of_finite hT
  exact IntermediateField.fg_top_iff.mp hfg

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Algebraic.lean:97` (proof source at `5a01f5fe3621`).
 Adjoining an arbitrary algebraic extension of constants to a function field gives a
function field over the enlarged constants, provided the ambient field is their compositum.
No finite-degree or separability assumption on the constants is needed. -/
theorem IsFunctionField.of_constantCompositum_eq_top
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  let : Algebra.EssFiniteType k' F' := essFiniteType_of_constantCompositum_eq_top (k := k) h
  rw [isFunctionField_iff_trdeg_eq_one]
  have := isAlgebraic_of_constantCompositum_eq_top (k := k) h
  rw [trdeg_eq_of_isAlgebraic_base (R := k)]
  exact hF.trdeg_eq_one_of_isAlgebraic

end TauCeti
end

end

/-! ## Source 13: `TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis`
Original source SHA256: `fc400b8b22bf7128081528374ea1d66cfad49dbbd6f6357464617a2f19f34150`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Proof-only: a spanning family with as many elements as the dimension is independent.

/-!
# Bases of constants in a constant field extension

Let `F' = F · k'` be the compositum of a field `F` with a separable extension `k'` of a field `k`
that is relatively algebraically closed in `F`; the case of interest is a constant field extension
of an algebraic function field `F / k` with exact constant field `k`.  Linear disjointness of `F`
and `k'` over `k` makes `F'` behave like `F ⊗[k] k'`: the image in `F'` of a `k`-basis of `k'` is
an `F`-basis of `F'`, the coordinates of a constant in this basis are the images of its
coordinates over `k`, the trace from `F'` to `F` of a constant is the image of its trace from `k'`
to `k`, and the trace dual of a basis of constants is the basis of constants attached to the trace
dual over `k`.  Comparing coordinates before and after raising to a power of the characteristic
also shows that `k'` is the exact constant field of `F'`.

These are the linear-algebraic inputs to the local theory of constant field extensions: at every
place `P` of `F / k` a basis of constants is an integral basis, which is what identifies the
functions of `F' = F · k'` with bounded poles in terms of those of `F`.

Without separability or exactness, linear disjointness can fail, and its degree form
`[F · k' : F] = [k' : k]` is then the test: for finite `k' / k` it implies linear disjointness, and
for algebraic `k' / k` linear disjointness follows once the test passes for every finite
subextension.  This is how an inseparable constant field extension is compared with `F`.

## Main definitions and results

* `TauCeti.finrank_le_finrank_of_constantCompositum_eq_top`: `[F · k' : F] ≤ [k' : k]` for any
  finite `k' / k`, with no exactness or separability hypothesis.
* `TauCeti.linearDisjoint_fieldRange_of_finrank_constantCompositum_eq`: equality there makes `F`
  and `k'` linearly disjoint over `k`, again with no exactness or separability hypothesis, and
  `TauCeti.linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq` deduces linear
  disjointness for an algebraic `k' / k` from equality for its finite subextensions.
* `TauCeti.constantBasis`: the `F`-basis of `F' = F · k'` given by a `k`-basis of `k'`.
* `TauCeti.constantBasis_repr_algebraMap`: the coordinates of a constant in a basis of constants
  are the images of its coordinates over `k`.
* `IsIntegrallyClosedIn.of_constantCompositum_eq_top`: `k'` is the exact constant field
  of `F · k'` (Stichtenoth, Proposition 3.6.1(a)), with no perfectness hypothesis.
* `TauCeti.trace_algebraMap_of_constantCompositum_eq_top`: the trace of a constant is the image
  of its trace over `k`.  This is Mathlib's `Subalgebra.LinearDisjoint.trace_algebraMap` for the
  linearly disjoint pair `F`, `k'`, stated for the trace over the field `F` itself rather than
  over its image in `F'`.
* `TauCeti.traceDual_constantBasis`: the trace dual of a basis of constants.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Proposition 3.6.1.
-/

section
open Module

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:76` (proof source at `5a01f5fe3621`).
 The constants generate the compositum `F · k'` as an `F`-algebra: for an algebraic extension
of constants, the intermediate field they generate is already the subalgebra they generate. -/
theorem adjoin_range_algebraMap_of_constantCompositum_eq_top [Algebra.IsIntegral k k']
    (h : constantCompositum F k' F' = ⊤) :
    Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤ := by
  have halg : ∀ x ∈ Set.range (algebraMap k' F'), IsAlgebraic F x := by
    rintro _ ⟨c, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := k) c).map
      (IsScalarTower.toAlgHom k k' F')).tower_top.isAlgebraic
  have := congrArg IntermediateField.toSubalgebra h
  rwa [constantCompositum_def, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg,
    IntermediateField.top_toSubalgebra] at this

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:89` (proof source at `5a01f5fe3621`).
 The image of a `k`-basis of `k'` spans the compositum `F' = F · k'` over `F`, for an algebraic
extension of constants. -/
theorem span_range_algebraMap_comp_of_constantCompositum_eq_top [Algebra.IsIntegral k k']
    (h : constantCompositum F k' F' = ⊤) {ι : Type*} (b : Basis ι k k') :
    Submodule.span F (Set.range (algebraMap k' F' ∘ b)) = ⊤ := by
  let L : Subalgebra k F' := (IsScalarTower.toAlgHom k k' F').range
  let e : k' ≃ₐ[k] L := AlgEquiv.ofInjective _ (algebraMap k' F').injective
  have hspan := Subalgebra.adjoin_eq_span_basis F L (b.map e.toLinearEquiv)
  have hfun : (fun i ↦ ((b.map e.toLinearEquiv) i).1) = algebraMap k' F' ∘ b := by
    ext i
    exact AlgEquiv.ofInjective_apply _ (algebraMap k' F').injective (b i)
  rw [AlgHom.coe_range, IsScalarTower.coe_toAlgHom',
    adjoin_range_algebraMap_of_constantCompositum_eq_top (k := k) h, Algebra.top_toSubmodule, hfun]
    at hspan
  exact hspan.symm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:108` (proof source at `5a01f5fe3621`).
 **Adjoining finitely many constants costs at most their degree**: if `F' = F · k'` for a finite
extension `k' / k`, then `[F' : F] ≤ [k' : k]`, because the image of a `k`-basis of `k'` spans `F'`
over `F`.  Equality is the degree form of linear disjointness of `F` and `k'` over `k`
(`TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`); for an inseparable `k' / k` the
inequality can be strict. -/
theorem finrank_le_finrank_of_constantCompositum_eq_top [FiniteDimensional k k']
    (h : constantCompositum F k' F' = ⊤) : Module.finrank F F' ≤ Module.finrank k k' := by
  let b := Module.finBasis k k'
  have hle := finrank_range_le_card (R := F) (algebraMap k' F' ∘ b)
  rwa [Set.finrank, span_range_algebraMap_comp_of_constantCompositum_eq_top h b, finrank_top,
    Fintype.card_fin] at hle

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:123` (proof source at `5a01f5fe3621`).
 **The degree form of linear disjointness implies linear disjointness**: if `k' / k` is finite
and adjoining it to `F` costs exactly `[k' : k]`, that is `[F · k' : F] = [k' : k]`, then the
image of `k'` in `F'` and `F` are linearly disjoint over `k`.  The image of a `k`-basis of `k'`
spans `F · k'` over `F` and has `[F · k' : F]` elements, so it stays linearly independent over
`F`.

This is the converse of `TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`.  No
exactness or separability hypothesis is needed. -/
theorem linearDisjoint_fieldRange_of_finrank_constantCompositum_eq [FiniteDimensional k k']
    (h : finrank F (constantCompositum F k' F') = finrank k k') :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let C := constantCompositum F k' F'
  let := constantCompositumAlgebra F k' F'
  have := isScalarTower_constantCompositum F k' F'
  have := isScalarTower_base_constantCompositum k F k' F'
  have hC : constantCompositum F k' C = ⊤ := (constantCompositum_eq_top_iff F k' F' C).2 rfl
  let b := finBasis k k'
  have hc : LinearIndependent F (algebraMap k' C ∘ b) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank
      (span_range_algebraMap_comp_of_constantCompositum_eq_top hC b).ge
      (by rw [Fintype.card_fin, ← h])
  refine .of_basis_left (b.map (IsScalarTower.toAlgHom k k' F').equivFieldRange.toLinearEquiv) ?_
  convert hc.map' C.val.toLinearMap (LinearMap.ker_eq_bot.2 C.val.injective) using 1
  ext i
  simpa [AlgHom.equivFieldRange_apply_coe] using IsScalarTower.algebraMap_apply k' C F' (b i)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:147` (proof source at `5a01f5fe3621`).
 **Linear disjointness from the finite subextensions**: if `k' / k` is algebraic and every
finite subextension `M` of `k' / k` satisfies `[F · M : F] = [M : k]`, then the image of `k'` in
`F'` and `F` are linearly disjoint over `k`.  By
`TauCeti.linearDisjoint_fieldRange_of_forall_finiteDimensional` it suffices to treat each `M`,
where `TauCeti.linearDisjoint_fieldRange_of_finrank_constantCompositum_eq` applies.  The extension
`k' / k` may be infinite, for instance an algebraic closure of `k`. -/
theorem linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq
    [Algebra.IsAlgebraic k k']
    (h : ∀ M : IntermediateField k k', FiniteDimensional k M →
      finrank F (constantCompositum F M F') = finrank k M) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F :=
  linearDisjoint_fieldRange_of_forall_finiteDimensional fun M _ ↦
    linearDisjoint_fieldRange_of_finrank_constantCompositum_eq (h M ‹_›)

variable [Algebra.IsSeparable k k']
variable (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:162` (proof source at `5a01f5fe3621`).
 **A basis of constants**: the `F`-basis of the compositum `F' = F · k'` given by the image of
a `k`-basis of `k'`.  Linear independence is the linear disjointness of `F` and `k'` over `k`
(Stichtenoth, Proposition 3.6.1(b)), which needs `k` exact in `F` and `k' / k` separable; spanning
is the definition of the compositum. -/
noncomputable def constantBasis {ι : Type*} (b : Basis ι k k') : Basis ι F F' :=
  Basis.mk (linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn hex
    (fun i ↦ Algebra.IsSeparable.isSeparable k (b i)) b.linearIndependent)
    (span_range_algebraMap_comp_of_constantCompositum_eq_top h b).ge

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:168` (proof source at `5a01f5fe3621`).
-/
@[simp]
theorem constantBasis_apply {ι : Type*} (b : Basis ι k k') (i : ι) :
    constantBasis hex h b i = algebraMap k' F' (b i) :=
  Basis.mk_apply _ _ i

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:172` (proof source at `5a01f5fe3621`).
-/
theorem coe_constantBasis {ι : Type*} (b : Basis ι k k') :
    ⇑(constantBasis hex h b) = algebraMap k' F' ∘ b :=
  Basis.coe_mk _ _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:179` (proof source at `5a01f5fe3621`).
 The coordinates of a constant in a basis of constants are the images of its coordinates
over `k`. -/
@[simp]
theorem constantBasis_repr_algebraMap {ι : Type*} (b : Basis ι k k') (c : k') (i : ι) :
    (constantBasis hex h b).repr (algebraMap k' F' c) i = algebraMap k F (b.repr c i) := by
  have hc : algebraMap k' F' c = Finsupp.linearCombination F (constantBasis hex h b)
      ((b.repr c).mapRange (algebraMap k F) (map_zero _)) := by
    conv_lhs => rw [← b.linearCombination_repr c]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum,
      Finsupp.sum_mapRange_index]
    · refine Finsupp.sum_congr fun j _ ↦ ?_
      simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, constantBasis_apply]
    · intro
      simp
  rw [hc, Basis.repr_linearCombination, Finsupp.mapRange_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:195` (proof source at `5a01f5fe3621`).
 Raising to the power `q ^ n`, for `q` the exponential characteristic, raises the coordinates
in a basis of constants to the power `q ^ n`, read off in the basis of constants given by the
`q ^ n`-th powers of the original `k`-basis of `k'`. -/
private theorem constantBasis_mapPowExpCharPowOfIsSeparable_repr_pow (q n : ℕ) [ExpChar k q]
    [ExpChar F' q] {ι : Type*} (b : Basis ι k k') (z : F') (i : ι) :
    (constantBasis hex h (b.mapPowExpCharPowOfIsSeparable q n)).repr (z ^ q ^ n) i =
      (constantBasis hex h b).repr z i ^ q ^ n := by
  have hb (j : ι) : b.mapPowExpCharPowOfIsSeparable q n j = b j ^ q ^ n := Basis.mk_apply _ _ j
  have h0 : (0 : F) ^ q ^ n = 0 := zero_pow (expChar_pow_pos F' q n).ne'
  let B := constantBasis hex h b
  have hz : z ^ q ^ n = Finsupp.linearCombination F
      (constantBasis hex h (b.mapPowExpCharPowOfIsSeparable q n))
      ((B.repr z).mapRange (· ^ q ^ n) h0) := by
    conv_lhs => rw [← B.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), ← iterateFrobenius_def, map_finsuppSum]
    refine Finsupp.sum_congr fun j _ ↦ ?_
    rw [iterateFrobenius_def, smul_pow, constantBasis_apply, constantBasis_apply, hb, map_pow]
  rw [hz, Basis.repr_linearCombination, Finsupp.mapRange_apply]

include hex h in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:224` (proof source at `5a01f5fe3621`).
 **The constant field of a separable constant field extension** (Stichtenoth,
Proposition 3.6.1(a)): if `k` is the exact constant field of `F` and `k' / k` is separable
algebraic, then the compositum `F' = F · k'` has exact constant field `k'`.  Stichtenoth assumes
`k` perfect; separability of `k' / k` is all that is needed.  For an inseparable `k' / k` the
conclusion can fail: `k = 𝔽_p(t, u)` is exact in `F = k(x, y)` with `y ^ p = t * x ^ p + u`, but
`y - t ^ (1/p) * x` is a `p`-th root of `u` in `F · k(t ^ (1/p))`.

Together with `TauCeti.IsFunctionField.of_constantCompositum_eq_top`, this makes `F · k' / k'` a
function field with exact constant field for a separable algebraic `k' / k`, so that its genus,
its places and their degrees are the ones the theory of constant field extensions compares with
those of `F / k`. -/
theorem _root_.IsIntegrallyClosedIn.of_constantCompositum_eq_top : IsIntegrallyClosedIn k' F' := by
  -- An element `z` algebraic over `k'` has a power `z ^ q ^ n` that is a constant. Raising to the
  -- power `q ^ n` carries a `k`-basis of the separable extension `k'` to another one, so the
  -- coordinates of `z` in a basis of constants have `q ^ n`-th powers in `k`, hence lie in `k`.
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.2 fun z hz ↦ ?_
  let q := ringExpChar k
  have : ExpChar k' q := expChar_of_injective_algebraMap (algebraMap k k').injective q
  have : ExpChar F' q := expChar_of_injective_algebraMap (algebraMap k F').injective q
  -- Some power `z ^ q ^ n` is separable over `k'`, hence a constant.
  obtain ⟨g, hg, n, hgz⟩ := (minpoly.irreducible hz.isIntegral).hasSeparableContraction q
  have hsep : IsSeparable k' (z ^ q ^ n) := hg.of_dvd <| minpoly.dvd k' _ <| by
    simpa only [Polynomial.expand_aeval, minpoly.aeval] using congr(Polynomial.aeval z $hgz)
  obtain ⟨c, hc⟩ : ∃ c : k', algebraMap k' F' c = z ^ q ^ n := by
    refine IntermediateField.mem_bot.1 ?_
    rw [← separableClosure_eq_bot_of_constantCompositum_eq_top hex h]
    exact mem_separableClosure_iff.2 hsep
  -- Compare coordinates in the bases of constants given by `b` and by its `q ^ n`-th powers.
  let b := Basis.ofVectorSpace k k'
  let B := constantBasis hex h b
  have hcoord (i) : ∃ a : k, algebraMap k F a = B.repr z i := by
    have hi := constantBasis_mapPowExpCharPowOfIsSeparable_repr_pow hex h q n b z i
    rw [← hc, constantBasis_repr_algebraMap] at hi
    let _ := hex
    exact IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
      (pow_pos (expChar_pos k q) n) (hi ▸ isIntegral_algebraMap)
  choose a ha using hcoord
  -- So `z` is the image of a constant.
  refine ⟨∑ i ∈ (B.repr z).support, a i • b i, ?_⟩
  conv_rhs => rw [← B.linearCombination_repr z]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← ha, constantBasis_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

include hex h in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:264` (proof source at `5a01f5fe3621`).
 **The trace of a constant is a constant**: for a finite separable extension of constants, the
trace from `F' = F · k'` to `F` of a constant is the image of its trace from `k'` to `k`.

This is not a `simp` lemma: the base field `k` does not occur in the left-hand side, so `simp`
cannot infer it (the `simpNF` linter rejects the lemma); use `rw`. -/
theorem trace_algebraMap_of_constantCompositum_eq_top [FiniteDimensional k k'] (c : k') :
    Algebra.trace F F' (algebraMap k' F' c) = algebraMap k F (Algebra.trace k k' c) := by
  classical
  let b := Module.finBasis k k'
  rw [Algebra.trace_eq_matrix_trace (constantBasis hex h b), Algebra.trace_eq_matrix_trace b,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, constantBasis_apply, ← map_mul,
    constantBasis_repr_algebraMap]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Basis.lean:278` (proof source at `5a01f5fe3621`).
 The trace dual of a basis of constants is the basis of constants attached to the trace dual
over `k`: the trace form of `F' / F` restricts on constants to the trace form of `k' / k`. -/
@[simp]
theorem traceDual_constantBasis [FiniteDimensional k k'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι k k') :
    (constantBasis hex h b).traceDual = constantBasis hex h b.traceDual := by
  refine Basis.eq_of_apply_eq (congrFun (Basis.traceDual_eq_iff.2 fun i j ↦ ?_))
  rw [constantBasis_apply, constantBasis_apply, Algebra.traceForm_apply, ← map_mul,
    trace_algebraMap_of_constantCompositum_eq_top hex h, Basis.trace_traceDual_mul]
  split_ifs <;> simp

end TauCeti
end

end

/-! ## Source 14: `TauCeti.FieldTheory.FunctionField.ConstantExtension.FiniteDescent`
Original source SHA256: `2470478ed0bfb443e7a95e98f50912888ece6627a4fbd3d540272f1c48327b47`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Finite descent in an algebraic constant extension

An arbitrary extension of constants is the directed union of the extensions obtained by adjoining
finitely many constants.  When the constant extension is algebraic, each of these intermediate
constant fields is finite-dimensional over the original constants.  Consequently every element,
finite set, or finitely generated intermediate field in the full compositum already occurs over a
finite constant subextension.

This is the finite-descent step used to pass results proved for finite constant extensions to an
algebraic closure of the constant field.  In the function-field setting, it lets finite algebraic
data be placed in a finite constant extension before applying degree, genus, and Riemann--Roch
comparison theorems.

## Main results

* `TauCeti.constantCompositum_eq_iSup_adjoin_finset`: a constant compositum is the supremum of
  the composita obtained from finitely generated constant subfields.
* `TauCeti.exists_finset_of_mem_constantCompositum`: one element of a constant compositum is
  defined over finitely many constants.
* `TauCeti.exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum`: a
  finite set in an algebraic constant compositum is defined over one finite constant subextension.
* `TauCeti.exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum`: a finitely
  generated intermediate field in the compositum descends to one finite constant subextension.
* `TauCeti.exists_finiteDimensional_constantSubfield_of_finiteDimensional_le_constantCompositum`:
  a finite-dimensional intermediate field descends to one finite constant subextension.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:57` (proof source at `5a01f5fe3621`).
 Enlarging an intermediate field of constants enlarges its compositum with `F`. -/
theorem constantCompositum_mono {L M : IntermediateField k k'} (h : L ≤ M) :
    constantCompositum F L F' ≤ constantCompositum F M F' := by
  rw [constantCompositum_def, constantCompositum_def]
  apply IntermediateField.adjoin.mono
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c, h c.2⟩, rfl⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:67` (proof source at `5a01f5fe3621`).
 **A constant compositum is the directed union of its finitely generated constant
subextensions.**  No algebraicity hypothesis is needed for this lattice identity. -/
theorem constantCompositum_eq_iSup_adjoin_finset :
    constantCompositum F k' F' =
      ⨆ S : Finset k', constantCompositum F (IntermediateField.adjoin k (S : Set k')) F' := by
  apply le_antisymm
  · rw [constantCompositum_def]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨c, rfl⟩
    apply (le_iSup (fun S : Finset k' ↦
      constantCompositum F (IntermediateField.adjoin k (S : Set k')) F') {c})
    rw [constantCompositum_def]
    let d : IntermediateField.adjoin k (({c} : Finset k') : Set k') :=
      ⟨c, IntermediateField.subset_adjoin k (({c} : Finset k') : Set k') (by simp)⟩
    apply IntermediateField.subset_adjoin F _
    refine ⟨d, ?_⟩
    rw [IsScalarTower.algebraMap_apply
      (IntermediateField.adjoin k (({c} : Finset k') : Set k')) k' F' d,
      IntermediateField.algebraMap_apply]
  · refine iSup_le fun S ↦ ?_
    rw [constantCompositum_def, constantCompositum_def]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨c, rfl⟩
    exact ⟨c.1, by
      rw [IsScalarTower.algebraMap_apply
        (IntermediateField.adjoin k (S : Set k')) k' F' c,
        IntermediateField.algebraMap_apply]⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:96` (proof source at `5a01f5fe3621`).
 **An element of a constant compositum uses only finitely many constants.**  If `x` belongs to
`F · k'`, there is a finite set `S ⊆ k'` such that `x` already belongs to `F · k(S)`. -/
theorem exists_finset_of_mem_constantCompositum {x : F'}
    (hx : x ∈ constantCompositum F k' F') :
    ∃ S : Finset k',
      x ∈ constantCompositum F (IntermediateField.adjoin k (S : Set k')) F' := by
  classical
  rw [constantCompositum_def] at hx
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hx
  let C : Set k' := algebraMap k' F' ⁻¹' (T : Set F')
  have hC : C.Finite :=
    Set.Finite.preimage (algebraMap k' F').injective.injOn T.finite_toSet
  let S : Finset k' := hC.toFinset
  refine ⟨S, mem_of_le_of_mem ?_ hxT⟩
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := hT hy
  rw [constantCompositum_def]
  apply IntermediateField.subset_adjoin
  have hcC : c ∈ C := by
    simpa only [C, Set.mem_preimage] using hy
  have hcS : c ∈ S := by
    simpa only [S, Set.Finite.mem_toFinset] using hcC
  let d : IntermediateField.adjoin k (S : Set k') :=
    ⟨c, IntermediateField.subset_adjoin k (S : Set k') hcS⟩
  refine ⟨d, ?_⟩
  rw [IsScalarTower.algebraMap_apply
    (IntermediateField.adjoin k (S : Set k')) k' F' d,
    IntermediateField.algebraMap_apply]

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:127` (proof source at `5a01f5fe3621`).
 **One element in an algebraic constant compositum descends to a finite constant
subextension.** -/
theorem exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
    [Algebra.IsAlgebraic k k'] {x : F'} (hx : x ∈ constantCompositum F k' F') :
    ∃ L : IntermediateField k k',
      FiniteDimensional k L ∧ x ∈ constantCompositum F L F' := by
  obtain ⟨S, hxS⟩ := exists_finset_of_mem_constantCompositum
    (k := k) (k' := k') (F := F) (F' := F') hx
  let L := IntermediateField.adjoin k (S : Set k')
  let _ : Finite (S : Set k') := Set.toFinite _
  let _ : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun c _ ↦
      Algebra.IsIntegral.isIntegral c
  exact ⟨L, inferInstance, hxS⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:143` (proof source at `5a01f5fe3621`).
 **A finite set in an algebraic constant compositum descends simultaneously to one finite
constant subextension.** -/
theorem exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum
    [Algebra.IsAlgebraic k k'] (S : Finset F')
    (hS : ∀ x ∈ S, x ∈ constantCompositum F k' F') :
    ∃ L : IntermediateField k k', FiniteDimensional k L ∧
      ∀ x ∈ S, x ∈ constantCompositum F L F' := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨⊥, inferInstance, ?_⟩
      simp
  | @insert x S hx ih =>
      obtain ⟨L, hL, hxL⟩ :=
        exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
          (k := k) (k' := k') (F := F) (F' := F') (hS x (by simp))
      obtain ⟨M, hM, hSM⟩ := ih fun y hy ↦ hS y (by simp [hy])
      let _ : FiniteDimensional k L := hL
      let _ : FiniteDimensional k M := hM
      let N := L ⊔ M
      let _ : FiniteDimensional k N := IntermediateField.finiteDimensional_sup L M
      refine ⟨N, inferInstance, fun y hy ↦ ?_⟩
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact constantCompositum_mono (F := F) (F' := F') le_sup_left hxL
      · exact constantCompositum_mono (F := F) (F' := F') le_sup_right (hSM y hy)

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:173` (proof source at `5a01f5fe3621`).
 **A finitely generated field inside an algebraic constant compositum descends to a finite
constant subextension.**  This packages simultaneous finite descent in the form used for finite
algebraic data: if `E / F` is generated by finitely many elements and `E ⊆ F · k'`, then some
finite-dimensional `L / k` satisfies `E ⊆ F · L`. -/
theorem exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum
    [Algebra.IsAlgebraic k k'] {E : IntermediateField F F'} (hE : E.FG)
    (hle : E ≤ constantCompositum F k' F') :
    ∃ L : IntermediateField k k',
      FiniteDimensional k L ∧ E ≤ constantCompositum F L F' := by
  obtain ⟨S, hS⟩ := hE
  have hScomp : ∀ x ∈ S, x ∈ constantCompositum F k' F' := by
    intro x hx
    apply hle
    rw [← hS]
    exact IntermediateField.subset_adjoin F (S : Set F') hx
  obtain ⟨L, hL, hSL⟩ :=
    exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum
      (k := k) (k' := k') (F := F) (F' := F') S hScomp
  refine ⟨L, hL, ?_⟩
  rw [← hS, IntermediateField.adjoin_le_iff]
  exact hSL

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/FiniteDescent.lean:196` (proof source at `5a01f5fe3621`).
 **A finite-dimensional field inside an algebraic constant compositum descends to a finite
constant subextension.**  This is the direct interface for finite algebraic data: if `E / F` is
finite-dimensional and `E ⊆ F · k'`, then some finite-dimensional `L / k` satisfies
`E ⊆ F · L`. -/
theorem
    exists_finiteDimensional_constantSubfield_of_finiteDimensional_le_constantCompositum
    [Algebra.IsAlgebraic k k'] {E : IntermediateField F F'} [FiniteDimensional F E]
    (hle : E ≤ constantCompositum F k' F') :
    ∃ L : IntermediateField k k',
      FiniteDimensional k L ∧ E ≤ constantCompositum F L F' := by
  apply exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum
    (k := k) (k' := k') (F := F) (F' := F')
  · exact E.fg_of_fg_toSubalgebra
      (Subalgebra.fg_of_fg_toSubmodule Submodule.FG.of_finite)
  · exact hle

end TauCeti
end

end

/-! ## Source 15: `TauCeti.FieldTheory.FunctionField.ConstantExtension.IntegralBasis`
Original source SHA256: `b0833e16b8b44b2b03c7a317aa1ff25eb0468f36165a05f27f194e65e37d51ec`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Constants form integral bases in a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of a field `F` with exact
constant field `k`, and let `P` be a place of `F / k`.  A basis of constants — the `F`-basis of
`F'` given by a `k`-basis of `k'` — is an integral basis at `P`: its `𝒪_P`-span is the integral
closure of `𝒪_P` in `F'`.  Both the basis and its trace dual consist of constants, which are
integral over `𝒪_P`, and a basis whose trace dual is integral is an integral basis.

So the elements of `F'` integral over `𝒪_P` are exactly the `𝒪_P`-combinations of constants: the
local model of a constant field extension at `P` is `𝒪_P ⊗[k] k'`.  This is the local input to
the comparison of the Riemann–Roch spaces of `F / k` and `F' / k'`.

## Main result

* `TauCeti.Place.isIntegralBasis_constantBasis`: a basis of constants is an integral basis at
  every place of `F / k`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6, the proof of
Theorem 3.6.3.
-/

section
open Module

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/IntegralBasis.lean:57` (proof source at `5a01f5fe3621`).
 **A basis of constants is an integral basis at every place** (Stichtenoth, proof of
Theorem 3.6.3): for a finite separable extension of constants `k' / k` with `k` exact in `F` and
`F' = F · k'`, the `𝒪_P`-span of the image of a `k`-basis of `k'` is the integral closure of `𝒪_P`
in `F'`, for every place `P` of `F / k`. -/
theorem isIntegralBasis_constantBasis [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) {ι : Type*} [Finite ι] (b : Basis ι k k')
    (P : Place k F) : P.IsIntegralBasis F' (constantBasis hex h b) := by
  classical
  have := Module.Finite.of_basis b
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  have := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') h
  refine IsIntegralBasis.of_isIntegral_of_isIntegral_traceDual F' P _ (fun i ↦ ?_) fun i ↦ ?_
  · rw [constantBasis_apply]
    exact isIntegral_integers_algebraMap P _
  · rw [traceDual_constantBasis, constantBasis_apply]
    exact isIntegral_integers_algebraMap P _

end Place

end TauCeti
end

end

/-! ## Source 16: `TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc`
Original source SHA256: `55b59be6b6a1f96a1e0492b92f7d4270a07be409b2e8849da763dbe86f9c964f`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Constant field extensions of the rational function field

For a field extension `k' / k`, the rational function field `k'(X)` is the constant field
extension `k(X) · k'` of `k(X)`, for any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`.
When `k' / k` is finite, the place at infinity of `k'(X)` is the only place over the place at
infinity of `k(X)`.

## Main results

* `TauCeti.constantCompositum_ratFunc_eq_top`: `k'(X)` is the compositum of `k(X)` and `k'`.
* `TauCeti.Place.restrict_ratFunc_eq_infty_iff`: a place of `k'(X)` lies over the place at
  infinity of `k(X)` exactly when it is the place at infinity of `k'(X)`.
-/

section
namespace TauCeti

variable {k k' : Type*} [Field k] [Field k']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/RatFunc.lean:36` (proof source at `5a01f5fe3621`).
 **`k'(X)` is the compositum of `k(X)` with the constants `k'`**, for any `k(X)`-algebra
structure on `k'(X)` sending `X` to `X`. -/
theorem constantCompositum_ratFunc_eq_top [Algebra (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    constantCompositum (RatFunc k) k' (RatFunc k') = ⊤ := by
  set K := constantCompositum (RatFunc k) k' (RatFunc k')
  -- `K` contains the constants `k'`, so it is an intermediate field of `k'(X) / k'`; it contains
  -- `X`, which generates `k'(X)` over `k'`.
  let E : IntermediateField k' (RatFunc k') :=
    { K.toSubfield with
      algebraMap_mem' := algebraMap_mem_constantCompositum (RatFunc k) k' (RatFunc k') }
  have hXE : (RatFunc.X : RatFunc k') ∈ E := hX ▸ K.algebraMap_mem RatFunc.X
  have hE : E = ⊤ := eq_top_iff.mpr <|
    RatFunc.adjoin_X.symm.le.trans (IntermediateField.adjoin_simple_le_iff.mpr hXE)
  exact eq_top_iff.mpr fun f _ ↦ (hE ▸ IntermediateField.mem_top : f ∈ E)

namespace Place

variable [Algebra k k'] [FiniteDimensional k k']
variable [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/RatFunc.lean:58` (proof source at `5a01f5fe3621`).
 **The place at infinity of `k'(X)` is the only place over the place at infinity of `k(X)`**,
for a finite extension `k' / k` and any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`. -/
@[simp]
theorem restrict_ratFunc_eq_infty_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    (P' : Place k' (RatFunc k')) :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    P'.restrict k (RatFunc k) = infty k ↔ P' = infty k' := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k)
    (constantCompositum_ratFunc_eq_top hX)
  rw [← X_notMem_integers_iff_eq_infty, ← X_notMem_integers_iff_eq_infty,
    mem_integers_restrict_iff, hX]

end Place

end TauCeti
end

end

/-! ## Source 17: `TauCeti.FieldTheory.FunctionField.ConstantExtension.ResidueField`
Original source SHA256: `30e41ce16538ecc897f9e6377bbb575ca91c2ad29675bd313f29e65f5b35bfe6`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Residue fields in a constant field extension

Let `F' = F · k'` be a separable algebraic constant field extension of an algebraic function
field `F / k` with exact constant field `k`, finite or not (an algebraic closure of a perfect `k`,
for instance), and let `P'` be a place of `F' / k'` lying over the place `P` of `F / k`.  The
residue field of `P'` is the compositum of the residue field of `P` and the new constants:

`F'_{P'} = F_P · k'`.

In fact more is true: `F'_{P'}` is spanned as an `F_P`-vector space by the image of `k'`.  When
`k' / k` is finite, every residue class at `P'` is represented by a function regular at all the
places over `P`, hence integral over `𝒪_P`, and such a function is an `𝒪_P`-combination of a
`k`-basis of `k'` (`TauCeti.Place.isIntegralBasis_constantBasis`).  Reducing that combination at
`P'` writes the residue class as an `F_P`-combination of residues of constants.  In general, a
function representing a residue class at `P'` already lies in `F · L` for a finite subextension
`L` of `k' / k` (`TauCeti.exists_finiteDimensional_constantSubfield_of_mem_constantCompositum`).
The finite case writes its residue at the place below `P'` in `F · L` over the constants of `L`,
and the residue-field map into `F'_{P'}` carries that expression to one over `k'`.

Consequently a place becomes rational as soon as the constants are enlarged enough: if `k' / k`
is normal and the residue field `F_P` admits a `k`-embedding into `k'`, every place of `F'` over
`P` has degree one.  Each element of `F_P` is a root of its minimal polynomial over `k`, which
splits in `k'`, so its residue in `F'_{P'}` is already a constant.  For `k'` a separable closure
of `k`, this applies to every place whose residue field is separable over `k`, hence to every
place when `k` is perfect.

## Main results

* `TauCeti.Place.span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top`:
  `F'_{P'}` is spanned over `F_P` by the image of `k'`.
* `TauCeti.Place.adjoin_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top`:
  **`F'_{P'} = F_P · k'`** (Stichtenoth, Theorem 3.6.3(g)).
* `TauCeti.Place.degree_eq_one_of_constantCompositum_eq_top`: a place over `P` is rational when
  `k' / k` is normal and `F_P` embeds into `k'` over `k`.
* `TauCeti.Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one`: a place with
  separable residue field becomes rational after a finite separable extension of constants.

## Reference

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.6.3(g).
-/

section
open Module

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsSeparable k k']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/ResidueField.lean:77` (proof source at `5a01f5fe3621`).
 In a finite separable constant field extension, the residues of constants span the residue
field over the residue field of the restricted place. -/
private theorem span_range_algebraMap_residueField_eq_top_of_finiteDimensional
    [FiniteDimensional k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
    Submodule.span (P'.restrict k F).ResidueField (Set.range (algebraMap k' P'.ResidueField)) =
      ⊤ := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  set P := P'.restrict k F
  refine eq_top_iff.2 fun y _ ↦ ?_
  -- Represent `y` by a function regular at every place over `P`, hence integral over `𝒪_P`.
  classical
  obtain ⟨g, hg, hgy⟩ := exists_forall_residue_eq
    (P := fun Q : {Q : Place k' F' // Q.restrict k F = P} ↦ (Q : Place k' F'))
    Subtype.val_injective fun Q ↦ if hQ : (Q : Place k' F') = P' then hQ ▸ y else 0
  have hint : IsIntegral P.integers g :=
    (isIntegral_iff_forall_restrict_eq_mem_integers (hF.of_constantCompositum_eq_top h) P).2
      fun Q hQ ↦ hg ⟨Q, hQ⟩
  -- Expand `g` in a basis of constants, with coordinates in `𝒪_P`.
  let b := Module.finBasis k k'
  have hb := isIntegralBasis_constantBasis hex h b P
  have hrepr := hb.isIntegral_iff_repr_mem.1 hint
  set a : Fin (finrank k k') → P.integers := fun i ↦ ⟨(constantBasis hex h b).repr g i, hrepr i⟩
  have hgsum : (⟨g, hg ⟨P', rfl⟩⟩ : P'.integers) =
      ∑ i, algebraMap P.integers P'.integers (a i) * algebraMap k' P'.integers (b i) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_algebraMap_constants, a]
    conv_lhs => rw [← (constantBasis hex h b).sum_repr g]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coe_algebraMap_integers, constantBasis_apply, Algebra.smul_def]
  have hy : y = IsLocalRing.residue P'.integers ⟨g, hg ⟨P', rfl⟩⟩ := by
    simpa using (hgy ⟨P', rfl⟩).symm
  rw [hy, hgsum, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_mul, ← IsLocalRing.ResidueField.algebraMap_residue, ← algebraMap_residueField (R := k'),
    ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/ResidueField.lean:118` (proof source at `5a01f5fe3621`).
 **The residue field of a constant field extension is spanned by the constants**: for a
separable algebraic constant field extension `F' = F · k'` of `F / k` with exact constant field
`k`, finite or not, the residue field of a place `P'` of `F' / k'` is spanned over the residue
field of the place below by the image of `k'`. -/
theorem span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    Submodule.span (P'.restrict k F).ResidueField (Set.range (algebraMap k' P'.ResidueField)) =
      ⊤ := by
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  set P := P'.restrict k F
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective y
  -- The function `g` already lies in `E = F · L` for a finite subextension `L` of `k' / k`.
  obtain ⟨L, hL, hgL⟩ := exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
    (k := k) (F := F) (by rw [h]; exact IntermediateField.mem_top (x := (g : F')))
  let E := constantCompositum F L F'
  let : Algebra L E := constantCompositumAlgebra F L F'
  have : IsScalarTower L E F' := isScalarTower_constantCompositum F L F'
  have : IsScalarTower k L E := isScalarTower_base_constantCompositum k F L F'
  have hE : constantCompositum F L E = ⊤ := (constantCompositum_eq_top_iff F L F' E).mpr rfl
  let : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
  let : Algebra.IsAlgebraic E F' := Algebra.IsAlgebraic.tower_top (K := F) (L := E)
  let Q := P'.restrict L E
  -- At the place `Q` below `P'`, the finite case writes the residue of `g` over `L`.
  have hgQ : (⟨g, hgL⟩ : E) ∈ Q.integers := by
    rw [mem_integers_restrict_iff]
    exact g.2
  have hmem : IsLocalRing.residue Q.integers ⟨_, hgQ⟩ ∈
      Submodule.span (Q.restrict k F).ResidueField (Set.range (algebraMap L Q.ResidueField)) := by
    rw [span_range_algebraMap_residueField_eq_top_of_finiteDimensional hF hex hE Q]
    exact Submodule.mem_top
  -- The residue-field map `E_Q → F'_{P'}` carries that expression to one over `k'`.
  have hg : algebraMap Q.ResidueField P'.ResidueField (IsLocalRing.residue Q.integers ⟨_, hgQ⟩) =
      IsLocalRing.residue P'.integers g := by
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    exact congrArg _ (Subtype.ext (by simp [Q]))
  rw [← hg]
  generalize IsLocalRing.residue Q.integers ⟨_, hgQ⟩ = z at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    refine Submodule.subset_span ⟨c, ?_⟩
    rw [algebraMap_residueField (R := k'), algebraMap_residueField (R := L),
      IsLocalRing.ResidueField.algebraMap_residue]
    refine congrArg _ (Subtype.ext ?_)
    simpa [Q, coe_algebraMap_constants, coe_algebraMap_integers] using
      (IsScalarTower.algebraMap_apply L k' F' c).symm.trans
        (IsScalarTower.algebraMap_apply L E F' c)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx =>
    -- A coefficient from the residue field of `Q ∩ F` is a coefficient from `F_P`.
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have ha : (a : F) ∈ P.integers := by
      rw [mem_integers_restrict_iff, IsScalarTower.algebraMap_apply F E F', ←
        mem_integers_restrict_iff L E P', ← mem_integers_restrict_iff k F Q]
      exact a.2
    have hr : algebraMap Q.ResidueField P'.ResidueField
        (algebraMap (Q.restrict k F).ResidueField Q.ResidueField (IsLocalRing.residue _ a)) =
        algebraMap P.ResidueField P'.ResidueField (IsLocalRing.residue P.integers ⟨a, ha⟩) := by
      rw [IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.algebraMap_residue,
        IsLocalRing.ResidueField.algebraMap_residue]
      refine congrArg _ (Subtype.ext ?_)
      simp only [Q, P, coe_algebraMap_integers, IsScalarTower.algebraMap_apply F E F']
    rw [Algebra.smul_def, map_mul, hr, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/ResidueField.lean:188` (proof source at `5a01f5fe3621`).
 **The residue field of a constant field extension is a compositum** (Stichtenoth,
Theorem 3.6.3(g)): for a separable algebraic constant field extension `F' = F · k'` of `F / k`
with exact constant field `k`, finite or not, the residue field of a place `P'` of `F' / k'` is
generated over the residue field `F_P` of the place below by the constants:
`F'_{P'} = F_P · k'`. -/
theorem adjoin_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    IntermediateField.adjoin (P'.restrict k F).ResidueField
      (Set.range (algebraMap k' P'.ResidueField)) = ⊤ := by
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  -- The adjoined field contains the span, which is already everything.
  refine eq_top_iff.2 fun y _ ↦
    (Submodule.span_le (p := (IntermediateField.adjoin _ _).toSubalgebra.toSubmodule)).2
      (IntermediateField.subset_adjoin _ _) ?_
  rw [span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top hF hex h P']
  exact Submodule.mem_top

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/ResidueField.lean:206` (proof source at `5a01f5fe3621`).
 **A place becomes rational in a large enough normal constant field extension**: for a
separable normal algebraic constant field extension `F' = F · k'` of `F / k` with exact constant
field `k`, finite or not, a place `P'` of `F' / k'` has degree one as soon as the residue field of
the place below admits a `k`-embedding into `k'`. -/
theorem degree_eq_one_of_constantCompositum_eq_top [Normal k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    (φ : letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
      (P'.restrict k F).ResidueField →ₐ[k] k') :
    P'.degree = 1 := by
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  set P := P'.restrict k F
  let ι := algebraMap k' P'.ResidueField
  -- The two routes from `k` into `F'_{P'}`, through `F_P` and through `k'`, agree.
  have hcomp (c : k) : algebraMap P.ResidueField P'.ResidueField (algebraMap k P.ResidueField c) =
      ι (algebraMap k k' c) := by
    rw [algebraMap_residueField (R := k), IsLocalRing.ResidueField.algebraMap_residue,
      algebraMap_residueField (R := k')]
    congr 1
    apply Subtype.ext
    rw [coe_algebraMap_integers, coe_algebraMap_constants, coe_algebraMap_constants,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  -- Each element of `F_P` reduces to a constant, as a root of a polynomial splitting in `k'`.
  have hmem (α : P.ResidueField) : algebraMap P.ResidueField P'.ResidueField α ∈ ι.range := by
    have := P.finiteDimensional_residueField hF
    have hαint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
    have hsplit := Normal.splits (F := k) (K := k') inferInstance (φ α)
    rw [minpoly.algHom_eq φ φ.injective α] at hsplit
    refine hsplit.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hαint)) ?_
    have hroot : ((minpoly k α).map (algebraMap k P.ResidueField)).IsRoot α := by
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, minpoly.aeval]
    rw [Polynomial.map_map, show ι.comp (algebraMap k k') =
        (algebraMap P.ResidueField P'.ResidueField).comp (algebraMap k P.ResidueField) from
        RingHom.ext fun c ↦ (hcomp c).symm, ← Polynomial.map_map]
    exact hroot.map
  rw [degree_eq_one_iff_algebraMap_surjective]
  intro y
  have hy : y ∈ Submodule.span P.ResidueField (Set.range ι) := by
    rw [span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top hF hex h P']
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero ι⟩
  | add x y _ _ hx hy => exact ι.range.add_mem hx hy
  | smul r x _ hx => exact Algebra.smul_def r x ▸ ι.range.mul_mem (hmem r) hx

omit [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/ResidueField.lean:253` (proof source at `5a01f5fe3621`).
 **A place becomes rational after a finite separable extension of constants**: if the residue
field of a place `P` of `F / k`, with `k` exact, is separable over `k`, then some finite separable
constant field extension `F' = F · k'`, formed inside an algebraic closure of `F`, has only places
of degree one over `P`. -/
theorem exists_constantCompositum_eq_top_and_forall_degree_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) [Algebra.IsSeparable k P.ResidueField] :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ constantCompositum F k' F' = ⊤ ∧
        ∀ P' : Place k' F', P'.restrict k F = P → P'.degree = 1 := by
  classical
  have := P.finiteDimensional_residueField hF
  -- Adjoin to `F` the roots of the minimal polynomial `p` of a primitive element `γ` of `F_P`.
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element k P.ResidueField
  have hγint : IsIntegral k γ := Algebra.IsIntegral.isIntegral γ
  set p := minpoly k γ
  obtain ⟨F', k', _, _, hsplit, _, htop⟩ :=
    exists_finiteDimensional_normal_splits_constantCompositum_eq_top F p
  have : Algebra.IsSeparable k k' :=
    Algebra.isSeparable_of_separable_splitting_field (F := k) (E := k')
      (Algebra.IsSeparable.isSeparable k γ)
  -- `F_P = k(γ)` embeds into `k'`, where `p` has a root.
  obtain ⟨r, hr⟩ := hsplit.exists_eval_eq_zero (by
    rw [Polynomial.degree_map]; exact (minpoly.degree_pos hγint).ne')
  have hroot : r ∈ p.aroots k' := by
    rw [Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hγint, by rwa [Polynomial.eval_map_algebraMap] at hr⟩
  let φ : P.ResidueField →ₐ[k] k' := ((IntermediateField.algHomAdjoinIntegralEquiv k hγint).symm
    ⟨r, hroot⟩).comp ((IntermediateField.equivOfEq hγ).trans IntermediateField.topEquiv).symm
  refine ⟨F', k', inferInstance, inferInstance, htop, fun P' hP' ↦ ?_⟩
  exact degree_eq_one_of_constantCompositum_eq_top hF hex htop P' (hP' ▸ φ)


end Place

end TauCeti
end

end

/-! ## Source 18: `TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein`
Original source SHA256: `872adbc57a38a8ee35fb992f5f275678500153be36009dc715d4c6d431e4e908`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Totally ramified places, and the Eisenstein criterion

Let `F' / k'` be a finite extension of the field extension `F / k`. A place `P'` of `F' / k'` is
**totally ramified** over `F` when its ramification index is as large as the fundamental
inequality allows, `e(P' ∣ P) = [F' : F]`. The inequality then forces the rest of the picture:
the relative degree is `1` and `P'` is the *only* place of `F'` lying over `P`, which is
Stichtenoth's Definition 3.1.13 read at `P`.

The criterion that produces totally ramified places is Eisenstein's. Call `φ ∈ F[X]`
*Eisenstein at a place `P` of `F / k`* when its leading coefficient is a unit of `𝒪_P`, every
coefficient below the leading one vanishes at `P`, and the constant coefficient vanishes to
order exactly one — the three conditions of Mathlib's `Polynomial.IsEisensteinAt` at the maximal
ideal of `𝒪_P`, read off the order function so that a polynomial over `F` may be tested. If `y`
generates `F'` over `F` and its minimal polynomial is Eisenstein at `P`, then every place `P'`
of `F'` over `P` is totally ramified and `y` is a prime element at `P'`.

The proof is the Newton-polygon computation, run with the strict triangle inequality. Write
`n = deg φ`, `e = e(P' ∣ P)` and `m = ord_{P'} y`, and expand `0 = φ(y)` as the sum of its
`n + 1` terms. The term of index `i < n` has order at least `e + i·m` because its coefficient
vanishes at `P`, the term of index `0` has order exactly `e`, and the leading term has order
`n·m`. If any one of the terms had order strictly smaller than all the others, the strict
triangle inequality would make the sum nonzero; so neither the leading term nor the constant
term can dominate, and comparing the two possibilities gives `n·m = e` — first for `m ≤ 0`,
where the leading term would dominate, and then for the two ways `n·m` and `e` could differ.
Since `e ≤ [F' : F] = n` and `m ≥ 1`, this forces `e = n` and `m = 1`.

## Main definitions

* `TauCeti.Place.IsTotallyRamified`: `e(P' ∣ P) = [F' : F]` (Stichtenoth, Definition 3.1.13).
* `TauCeti.Place.IsEisensteinAt`: a polynomial over `F` is Eisenstein at a place of `F / k`.

## Main results

* `TauCeti.Place.relativeDegree_eq_one_of_isTotallyRamified` and
  `TauCeti.Place.eq_of_isTotallyRamified`: a totally ramified place has relative degree `1` and
  is the only place lying over the place below it, packaged as
  `TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified`.
* `TauCeti.Place.adjoin_eq_top_of_isTotallyRamified_of_ord_eq_one`: every uniformizer at a
  totally ramified place generates the field extension.
* `TauCeti.Place.IsEisensteinAt.natDegree_pos`: an Eisenstein polynomial has positive degree.
* `TauCeti.Place.natDegree_mul_ord_eq_ramificationIdx`: the order of a root of an Eisenstein
  polynomial, `n · ord_{P'} y = e(P' ∣ P)`.
* `TauCeti.Place.isTotallyRamified_of_isEisensteinAt` and
  `TauCeti.Place.ord_eq_one_of_isEisensteinAt`: **the Eisenstein criterion** (Stichtenoth,
  Proposition 3.1.15).
* `TauCeti.Place.isEisensteinAt_map`: a polynomial over `𝒪_P` that is Eisenstein at the maximal
  ideal of `𝒪_P` in the sense of Mathlib's `Polynomial.IsEisensteinAt` is Eisenstein at `P` in
  the sense used here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

section
open Polynomial
open scoped _root_.IntermediateField

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section TotallyRamified

variable (F)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:93` (proof source at `5a01f5fe3621`).
 A place `P'` of `F' / k'` is **totally ramified** over `F` when its ramification index is
the full degree `[F' : F]`. By the fundamental inequality this is the largest value the
ramification index can take, and it forces the relative degree to be `1`
(`TauCeti.Place.relativeDegree_eq_one_of_isTotallyRamified`) and `P'` to be the only place of
`F'` over the place of `F` below it (`TauCeti.Place.eq_of_isTotallyRamified`): the situation
Stichtenoth's Definition 3.1.13 calls total ramification of that place of `F`. -/
def IsTotallyRamified (P' : Place k' F') : Prop :=
  ramificationIdx F P' = Module.finrank F F'

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:98` (proof source at `5a01f5fe3621`).
 Total ramification unfolds to its defining equality of the ramification index with the
degree. -/
theorem isTotallyRamified_iff {P' : Place k' F'} :
    IsTotallyRamified F P' ↔ ramificationIdx F P' = Module.finrank F F' := Iff.rfl

variable (k) [FiniteDimensional F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:106` (proof source at `5a01f5fe3621`).
 **A totally ramified place has relative degree one**: the fundamental inequality has no room
left for a residue field extension. -/
@[simp]
theorem relativeDegree_eq_one_of_isTotallyRamified {P' : Place k' F'}
    (h : IsTotallyRamified F P') : relativeDegree k F P' = 1 := by
  have hle := ramificationIdx_mul_relativeDegree_le_finrank k F P'
  rw [h] at hle
  have hpos : 0 < Module.finrank F F' := Module.finrank_pos
  have h1 := one_le_relativeDegree k F P'
  nlinarith

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:116` (proof source at `5a01f5fe3621`).
 **A totally ramified place is the only place over the place below it**: a second place in
the fibre would contribute at least `1` more to the fundamental inequality. -/
theorem eq_of_isTotallyRamified {P' Q' : Place k' F'} (h : IsTotallyRamified F P')
    (hQ : Q'.restrict k F = P'.restrict k F) : Q' = P' := by
  classical
  by_contra hne
  have hle := sum_ramificationIdx_mul_relativeDegree_le_finrank k F (P'.restrict k F)
    {P', Q'} (by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · rfl
      · exact hQ)
  rw [Finset.sum_pair (Ne.symm hne), h] at hle
  have h1 := one_le_relativeDegree k F P'
  have h2 := ramificationIdx_pos F Q'
  have h3 := one_le_relativeDegree k F Q'
  nlinarith

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:136` (proof source at `5a01f5fe3621`).
 The fibre of `TauCeti.Place.restrict` over the place below a totally ramified place is a
single point. -/
@[simp]
theorem setOf_restrict_eq_eq_singleton_of_isTotallyRamified {P' : Place k' F'}
    (h : IsTotallyRamified F P') :
    {Q' : Place k' F' | Q'.restrict k F = P'.restrict k F} = {P'} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun _ hQ => eq_of_isTotallyRamified k F h hQ⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:143` (proof source at `5a01f5fe3621`).
 A uniformizer at a totally ramified place generates the field extension.  Its first
`e(P' | P) = [F' : F]` powers are linearly independent, hence form a basis. -/
theorem adjoin_eq_top_of_isTotallyRamified_of_ord_eq_one {P' : Place k' F'} {t : F'}
    (h : IsTotallyRamified F P') (ht : P'.ord t = 1) : F⟮t⟯ = ⊤ := by
  classical
  have hind := linearIndependent_pow_fin_ramificationIdx F P' ht
  let _ : Nonempty (Fin (ramificationIdx F P')) :=
    Fin.pos_iff_nonempty.mp (ramificationIdx_pos F P')
  have hcard : Fintype.card (Fin (ramificationIdx F P')) = Module.finrank F F' := by
    rw [Fintype.card_fin, ← isTotallyRamified_iff]
    exact h
  have hspan := hind.span_eq_top_of_card_eq_finrank hcard
  apply top_unique
  intro x _
  have hx : x ∈ Submodule.span F (Set.range fun j : Fin (ramificationIdx F P') ↦
      t ^ (j : ℕ)) := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ ↦ x ∈ F⟮t⟯) (fun y hy ↦ ?_) (by simp)
    (fun _ _ _ _ hx hy ↦ add_mem hx hy)
    (fun c _ _ hx ↦ ?_) hx
  · obtain ⟨j, rfl⟩ := hy
    exact pow_mem (IntermediateField.mem_adjoin_simple_self F t) _
  · simpa [Algebra.smul_def] using mul_mem (IntermediateField.algebraMap_mem F⟮t⟯ c) hx

end TotallyRamified

section Eisenstein

/-- Kind: STRUCTURE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:178` (proof source at `5a01f5fe3621`).
 A polynomial over `F` is **Eisenstein at a place `P` of `F / k`** when its leading
coefficient is a unit of `𝒪_P`, every coefficient below the leading one vanishes at `P`, and the
constant coefficient vanishes to order exactly one. For a polynomial with coefficients in `𝒪_P`
these are the three conditions of Mathlib's `Polynomial.IsEisensteinAt` at the maximal ideal of
`𝒪_P`; see `TauCeti.Place.isEisensteinAt_map`. The conditions are stated through the valuation
and the order function rather than through membership in the maximal ideal, so that a polynomial
over `F` — for instance a minimal polynomial — may be tested directly; the junk value
`ord_P 0 = 0` is avoided by using the valuation in the condition that admits zero coefficients. -/
structure IsEisensteinAt (P : Place k F) (φ : F[X]) : Prop where
  /-- Kind: FIELD. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:179`.
 The leading coefficient is a unit of `𝒪_P`; monic polynomials qualify. -/
  ord_leadingCoeff : P.ord φ.leadingCoeff = 0
  /-- Kind: FIELD. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:181`.
 Every coefficient below the leading one lies in the maximal ideal of `𝒪_P`. -/
  valuation_coeff_lt_one : ∀ i < φ.natDegree, P.valuation (φ.coeff i) < 1
  /-- Kind: FIELD. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:183`.
 The constant coefficient vanishes to order exactly one. -/
  ord_coeff_zero : P.ord (φ.coeff 0) = 1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:188` (proof source at `5a01f5fe3621`).
 An Eisenstein polynomial has positive degree: in degree zero the leading coefficient *is*
the constant coefficient, and the two order conditions contradict each other. -/
theorem IsEisensteinAt.natDegree_pos {P : Place k F} {φ : F[X]} (h : P.IsEisensteinAt φ) :
    0 < φ.natDegree := by
  rcases Nat.eq_zero_or_pos φ.natDegree with h0 | h0
  · have hl := h.ord_leadingCoeff
    rw [Polynomial.leadingCoeff, h0, h.ord_coeff_zero] at hl
    exact absurd hl (by decide)
  · exact h0

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:198` (proof source at `5a01f5fe3621`).
 An element of `𝒪_P` of order at least two lies in the square of the maximal ideal: a prime
element `t` for `P` factors it as `t · t · u` with `u ∈ 𝒪_P`. -/
private theorem mem_maximalIdeal_sq_of_two_le_ord (P : Place k F) {f : P.integers}
    (h : 2 ≤ P.ord (f : F)) : f ∈ IsLocalRing.maximalIdeal P.integers ^ 2 := by
  rcases eq_or_ne (f : F) 0 with hf0 | hf0
  · have hf : f = 0 := Subtype.ext hf0
    rw [hf]
    exact Submodule.zero_mem _
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [P.isUniformizer_iff_ord_eq_one] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [P.ord_zero] at ht
    exact absurd ht (by decide)
  have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hu : (f : F) / (t * t) ∈ P.integers := by
    refine P.mem_integers_iff_ord_nonneg.mpr ?_
    rw [P.ord_div hf0 (mul_ne_zero ht0 ht0), P.ord_mul ht0 ht0, ht]
    omega
  have hcoe : ((⟨t, htmem⟩ : P.integers) : F) = t := rfl
  have hmem : (⟨t, htmem⟩ : P.integers) ∈ IsLocalRing.maximalIdeal P.integers :=
    (P.mem_maximalIdeal_iff_ord_pos (by rw [hcoe]; exact ht0)).mpr (by rw [hcoe, ht]; omega)
  have hfeq : f = ⟨t, htmem⟩ * ⟨t, htmem⟩ * ⟨(f : F) / (t * t), hu⟩ := by
    refine Subtype.ext ?_
    push_cast
    field_simp
  rw [hfeq, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hmem hmem)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:231` (proof source at `5a01f5fe3621`).
 **Mathlib's Eisenstein condition is this one**: a polynomial over `𝒪_P` of positive degree
which is Eisenstein at the maximal ideal of `𝒪_P` in the sense of `Polynomial.IsEisensteinAt`
becomes, read in `F[X]`, a polynomial Eisenstein at `P`. No monicity is needed: the
`Polynomial.IsEisensteinAt.leading` field already puts the leading coefficient outside the
maximal ideal, hence makes it a unit of `𝒪_P`. The `Polynomial.IsEisensteinAt.notMem` field is
what pins the order of the constant coefficient down to exactly one. -/
theorem isEisensteinAt_map (P : Place k F) {ψ : Polynomial P.integers}
    (hdeg : 0 < ψ.natDegree) (h : ψ.IsEisensteinAt (IsLocalRing.maximalIdeal P.integers)) :
    P.IsEisensteinAt (ψ.map (algebraMap P.integers F)) := by
  have hinj : Function.Injective (algebraMap P.integers F) := fun a b hab =>
    Subtype.ext (by simpa [ValuationSubring.algebraMap_apply] using hab)
  have hnat : (ψ.map (algebraMap P.integers F)).natDegree = ψ.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj ψ
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · have hlc : (ψ.map (algebraMap P.integers F)).leadingCoeff = (ψ.leadingCoeff : F) := by
      rw [Polynomial.leadingCoeff_map_of_injective hinj, ValuationSubring.algebraMap_apply]
    have hlcne : ψ.leadingCoeff ≠ 0 := fun h0 =>
      h.leading (by rw [h0]; exact Submodule.zero_mem _)
    have hlc0 : (ψ.leadingCoeff : F) ≠ 0 := fun h0 => hlcne (Subtype.ext h0)
    have hnonneg : 0 ≤ P.ord (ψ.leadingCoeff : F) :=
      P.mem_integers_iff_ord_nonneg.mp ψ.leadingCoeff.2
    have hnotpos : ¬0 < P.ord (ψ.leadingCoeff : F) := fun hp =>
      h.leading ((P.mem_maximalIdeal_iff_ord_pos hlc0).mpr hp)
    rw [hlc]
    omega
  · rw [hnat] at hi
    rw [Polynomial.coeff_map, ValuationSubring.algebraMap_apply]
    exact P.mem_maximalIdeal_iff_valuation_lt_one.mp (h.mem hi)
  · have hne : ((ψ.coeff 0 : P.integers) : F) ≠ 0 := by
      intro h0
      have hz : ψ.coeff 0 = 0 := Subtype.ext h0
      exact h.notMem (by rw [hz]; exact Submodule.zero_mem _)
    have hpos : 0 < P.ord ((ψ.coeff 0 : P.integers) : F) :=
      (P.mem_maximalIdeal_iff_ord_pos hne).mp (h.mem hdeg)
    have hlt : ¬2 ≤ P.ord ((ψ.coeff 0 : P.integers) : F) := fun hh =>
      h.notMem (mem_maximalIdeal_sq_of_two_le_ord P hh)
    rw [Polynomial.coeff_map, ValuationSubring.algebraMap_apply]
    omega

variable {P' : Place k' F'}

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:268` (proof source at `5a01f5fe3621`).
 Comparison of valuations from a comparison of orders, with the junk value `ord_P 0 = 0`
guarded: the zero element has valuation `0`, below the valuation of any nonzero element. -/
private theorem valuation_lt_of_ord_lt {a b : F'} (hb : b ≠ 0)
    (h : a ≠ 0 → P'.ord b < P'.ord a) : P'.valuation a < P'.valuation b := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]
    exact zero_lt_iff.mpr (P'.valuation.ne_zero_iff.mpr hb)
  · rw [P'.valuation_eq_exp_neg_ord ha, P'.valuation_eq_exp_neg_ord hb, WithZero.exp_lt_exp]
    have := h ha
    omega

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:279` (proof source at `5a01f5fe3621`).
 **The strict triangle inequality for a finite sum**: a sum with a strictly dominant term is
nonzero. -/
private theorem sum_ne_zero_of_forall_valuation_lt (Q' : Place k' F') {ι : Type*} {s : Finset ι}
    {T : ι → F'} {j : ι} (hj : j ∈ s) (hTj : T j ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → Q'.valuation (T i) < Q'.valuation (T j)) :
    ∑ i ∈ s, T i ≠ 0 := by
  classical
  intro hsum
  have hval := Q'.valuation.map_sum_eq_of_lt hj fun i hi => by
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact hlt i hi.1 hi.2
  rw [hsum, map_zero] at hval
  exact (Q'.valuation.ne_zero_iff.mpr hTj) hval.symm

variable (k F) [Algebra.IsIntegral F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:297` (proof source at `5a01f5fe3621`).
 **The order of a root of an Eisenstein polynomial** (Stichtenoth, Proposition 3.1.15): if
`φ ∈ F[X]` of degree `n` is Eisenstein at the place of `F / k` below `P'`, then a root `y ∈ F'`
of `φ` satisfies `n · ord_{P'} y = e(P' ∣ P)`. In particular `n` divides the ramification index,
which is the whole content of the criterion. -/
theorem natDegree_mul_ord_eq_ramificationIdx {φ : F[X]}
    (hφ : (P'.restrict k F).IsEisensteinAt φ)
    {y : F'} (hy : aeval y φ = 0) :
    (φ.natDegree : ℤ) * P'.ord y = ramificationIdx F P' := by
  classical
  have hdeg : 0 < φ.natDegree := hφ.natDegree_pos
  set P := P'.restrict k F
  set n := φ.natDegree with hndef
  set e : ℤ := (ramificationIdx F P' : ℤ) with hedef
  have he0 : 0 < e := by
    rw [hedef]
    exact_mod_cast ramificationIdx_pos F P'
  have hord0 := hφ.ord_coeff_zero
  have hc0 : φ.coeff 0 ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hord0
    exact absurd hord0 (by decide)
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h : algebraMap F F' (φ.coeff 0) = 0 := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero] using hy
    exact hc0 ((map_eq_zero (algebraMap F F')).mp h)
  set m := P'.ord y
  set T : ℕ → F' := fun i => algebraMap F F' (φ.coeff i) * y ^ i with hTdef
  have hsum : ∑ i ∈ Finset.range (n + 1), T i = 0 := by
    rw [← hy, Polynomial.aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
  have hTne : ∀ i, φ.coeff i ≠ 0 → T i ≠ 0 := fun i hci =>
    mul_ne_zero (by simpa using hci) (pow_ne_zero i hy0)
  have hordT : ∀ i, φ.coeff i ≠ 0 → P'.ord (T i) = e * P.ord (φ.coeff i) + i * m := by
    intro i hci
    have h1 : algebraMap F F' (φ.coeff i) ≠ 0 := by simpa using hci
    rw [hTdef]
    simp only
    rw [P'.ord_mul h1 (pow_ne_zero i hy0), P'.ord_pow, ord_algebraMap_restrict k F P']
  have hφ0 : φ ≠ 0 := fun h => by simp [h, hndef] at hdeg
  have hcoeff_n : φ.coeff n = φ.leadingCoeff := by rw [hndef, Polynomial.coeff_natDegree]
  have hcn0 : φ.coeff n ≠ 0 := by
    rw [hcoeff_n]
    exact Polynomial.leadingCoeff_ne_zero.mpr hφ0
  have hTn0 : T n ≠ 0 := hTne n hcn0
  have hT00 : T 0 ≠ 0 := hTne 0 hc0
  have hordTn : P'.ord (T n) = n * m := by
    rw [hordT n hcn0, hcoeff_n, hφ.ord_leadingCoeff, mul_zero, zero_add]
  have hordT0 : P'.ord (T 0) = e := by
    rw [hordT 0 hc0, hord0, mul_one, Nat.cast_zero, zero_mul, add_zero]
  have hlow : ∀ i, i < n → φ.coeff i ≠ 0 → e + i * m ≤ P'.ord (T i) := by
    intro i hi hci
    have hpos : 0 < P.ord (φ.coeff i) :=
      (P.valuation_lt_one_iff_ord_pos hci).mp (hφ.valuation_coeff_lt_one i hi)
    have hge : e ≤ e * P.ord (φ.coeff i) := le_mul_of_one_le_right he0.le hpos
    rw [hordT i hci]
    linarith
  -- Step 1: the root has positive order, else the leading term dominates.
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hm0 : m ≤ 0 := by omega
    refine sum_ne_zero_of_forall_valuation_lt P' (Finset.self_mem_range_succ n) hTn0 ?_ hsum
    intro i hi hne
    refine valuation_lt_of_ord_lt hTn0 fun hi0 => ?_
    have hci : φ.coeff i ≠ 0 := fun h => hi0 (by rw [hTdef]; simp [h])
    have hilt : i < n := by
      rw [Finset.mem_range] at hi
      omega
    have hle : (n : ℤ) * m ≤ (i : ℤ) * m :=
      mul_le_mul_of_nonpos_right (by exact_mod_cast hilt.le) hm0
    have := hlow i hilt hci
    rw [hordTn]
    linarith
  -- Step 2: neither the leading term nor the constant term may dominate.
  have hkey : (n : ℤ) * m = e := by
    rcases lt_trichotomy ((n : ℤ) * m) e with hlt | heq | hgt
    · refine absurd hsum (sum_ne_zero_of_forall_valuation_lt P'
        (Finset.self_mem_range_succ n) hTn0 ?_)
      intro i hi hne
      refine valuation_lt_of_ord_lt hTn0 fun hi0 => ?_
      have hci : φ.coeff i ≠ 0 := fun h => hi0 (by rw [hTdef]; simp [h])
      have hilt : i < n := by
        rw [Finset.mem_range] at hi
        omega
      have hnn : (0 : ℤ) ≤ (i : ℤ) * m := mul_nonneg (Int.natCast_nonneg i) (by omega)
      have := hlow i hilt hci
      rw [hordTn]
      linarith
    · exact heq
    · refine absurd hsum (sum_ne_zero_of_forall_valuation_lt P'
        (Finset.mem_range.mpr (by omega)) hT00 ?_)
      intro i hi hne
      refine valuation_lt_of_ord_lt hT00 fun hi0 => ?_
      have hci : φ.coeff i ≠ 0 := fun h => hi0 (by rw [hTdef]; simp [h])
      rw [hordT0]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) with rfl | hilt
      · rw [hordTn]
        linarith
      · have hi1 : 1 ≤ (i : ℤ) := by
          have : 0 < i := Nat.pos_of_ne_zero hne
          exact_mod_cast this
        have hnn : (1 : ℤ) ≤ (i : ℤ) * m := one_le_mul_of_one_le_of_one_le hi1 hm1
        have := hlow i hilt hci
        linarith
  rw [hkey]

variable [FiniteDimensional F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:401` (proof source at `5a01f5fe3621`).
-/
private theorem ramificationIdx_eq_and_ord_eq_one {y : F'}
    (htop : IntermediateField.adjoin F {y} = ⊤)
    (hφ : (P'.restrict k F).IsEisensteinAt (minpoly F y)) :
    IsTotallyRamified F P' ∧ P'.ord y = 1 := by
  have hint : IsIntegral F y := IsIntegral.of_finite F y
  have hfr : Module.finrank F F' = (minpoly F y).natDegree := by
    rw [← IntermediateField.finrank_top' (F := F) (E := F'), ← htop,
      IntermediateField.adjoin.finrank hint]
  have hdeg : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have hkey := natDegree_mul_ord_eq_ramificationIdx k F hφ (minpoly.aeval F y)
  have hle : ramificationIdx F P' ≤ Module.finrank F F' := ramificationIdx_le_finrank F P'
  rw [hfr] at hle
  have hle' : (ramificationIdx F P' : ℤ) ≤ ((minpoly F y).natDegree : ℤ) := by
    exact_mod_cast hle
  have he0 : (0 : ℤ) < (ramificationIdx F P' : ℤ) := by exact_mod_cast ramificationIdx_pos F P'
  have hn0 : (0 : ℤ) < ((minpoly F y).natDegree : ℤ) := by exact_mod_cast hdeg
  have hm1 : 1 ≤ P'.ord y := by nlinarith
  have hm : P'.ord y = 1 := by nlinarith [hle', hn0]
  refine ⟨?_, hm⟩
  have : (ramificationIdx F P' : ℤ) = (Module.finrank F F' : ℤ) := by
    rw [hfr, ← hkey, hm, mul_one]
  exact_mod_cast this

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:430` (proof source at `5a01f5fe3621`).
 **The Eisenstein criterion** (Stichtenoth, Proposition 3.1.15): if `F' = F(y)` and the
minimal polynomial of `y` over `F` is Eisenstein at the place of `F / k` below `P'`, then `P'`
is totally ramified over `F`. Together with
`TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified` this says that the place
below `P'` is totally ramified in `F' / F`: it has exactly one extension, of ramification index
`[F' : F]` and relative degree `1`. -/
theorem isTotallyRamified_of_isEisensteinAt {y : F'}
    (htop : IntermediateField.adjoin F {y} = ⊤)
    (hφ : (P'.restrict k F).IsEisensteinAt (minpoly F y)) :
    IsTotallyRamified F P' :=
  (ramificationIdx_eq_and_ord_eq_one k F htop hφ).1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Eisenstein.lean:438` (proof source at `5a01f5fe3621`).
 **A generator with an Eisenstein minimal polynomial is a prime element** (Stichtenoth,
Proposition 3.1.15). -/
theorem ord_eq_one_of_isEisensteinAt {y : F'}
    (htop : IntermediateField.adjoin F {y} = ⊤)
    (hφ : (P'.restrict k F).IsEisensteinAt (minpoly F y)) :
    P'.ord y = 1 :=
  (ramificationIdx_eq_and_ord_eq_one k F htop hφ).2

end Eisenstein

end Place

end TauCeti
end

end

/-! ## Source 19: `TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified`
Original source SHA256: `b1a916dca6e6b529454948c2611f5af03b82f5f8a418104a35a34b4cb67aded3`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Unramified constant field extensions

Let `k' / k` be finite and separable and suppose that `F'` is the compositum `F k'`. Then
`F' / F` is separable and is unramified at every place. The ramification-index statement extends
to arbitrary separable algebraic extensions of constants, including algebraic closures over a
perfect base field: every place still has index one.

These are the local inputs to the comparison of the divisor theories of `F / k` and `F' / k'`.
Vanishing different exponents say that the different divisor of `F' / F` is zero, and
`e(P' | P) = 1` says that no place of `F` ramifies in `F'`, so the conorm of the point divisor of
a place of `F` is the sum of the point divisors of the places of `F'` above it with no
multiplicities, leaving the residue degrees as the only local data to track.  The genus,
divisor-degree and Riemann–Roch comparisons of Stichtenoth, Section III.6 consume these local
facts, but do not follow from them alone: they also need the constant field of `F'`, the
comparison of degrees normalised over `k` with those normalised over `k'`, and base change for
the Riemann–Roch spaces `L(D)`, none of which is proved here.

Separability is inherited by scalar extension, which is
`TauCeti.isSeparable_of_constantCompositum_eq_top`. For unramifiedness, choose a primitive element
`c` of `k' / k`. Its image generates `F' / F`, while the derivative of the minimal polynomial of
`c` evaluated at `c` is a nonzero element of `k'`, so its image in `F'` is a constant and hence a
unit at every place of `F'`. The derivative criterion for the different therefore makes every
different exponent vanish.

Read backwards, unramifiedness detects new constants.  If `k` is exact in `F`, a finite separable
extension with a totally ramified place has no new constants: any finite separable extension of
constants is unramified, and multiplicativity of ramification indices prevents it from occurring
inside a totally ramified extension.  This is how the exactness of the constants of Kummer covers
is established.

## Main results

* `TauCeti.Place.differentExponent_eq_zero_of_constantCompositum_eq_top`: every different
  exponent of the constant extension vanishes.
* `TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top`: each corresponding local model is
  unramified.
* `TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`: every place has
  ramification index one, even in an infinite separable algebraic constant extension.
* `TauCeti.isIntegrallyClosedIn_of_isTotallyRamified`: a finite separable extension with a
  totally ramified place acquires no new constants.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.6.3(a), and
the argument of Proposition 3.7.3(c).
-/

section
open Polynomial

open scoped _root_.IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

namespace Place

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Unramified.lean:84` (proof source at `5a01f5fe3621`).
 **Every different exponent of a finite separable constant extension vanishes** (Stichtenoth,
Proposition 3.6.3(a)): for a place `P'` of `F' / k'` lying over the place `P = P'.restrict k F` of
`F / k`, the different exponent `d(P' ∣ P)` is zero, so the different divisor of `F' / F` is the
zero divisor. -/
theorem differentExponent_eq_zero_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    letI := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    differentExponent k F P' = 0 := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  let := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  obtain ⟨c, hc⟩ := Field.exists_primitive_element k k'
  let y : F' := algebraMap k' F' c
  have hgen : F⟮y⟯ = ⊤ := by
    rw [← hcomp, constantCompositum_eq_adjoin_of_adjoin_eq_top F k' F' {c} hc]
    simp [y]
  have hpmonic : ((minpoly k c).map (algebraMap k F)).Monic :=
    (minpoly.monic (Algebra.IsSeparable.isIntegral k c)).map _
  have hpcoeff : ∀ i, ((minpoly k c).map (algebraMap k F)).coeff i ∈
      (P'.restrict k F).integers := by
    intro i
    rw [coeff_map]
    exact (P'.restrict k F).algebraMap_mem_integers _
  have hmap_aeval (q : k[X]) :
      aeval (algebraMap k' F' c) q = algebraMap k' F' (aeval c q) := by
    simpa only [IsScalarTower.toAlgHom_apply] using
      aeval_algHom_apply (IsScalarTower.toAlgHom k k' F') c q
  have hroot : aeval y ((minpoly k c).map (algebraMap k F)) = 0 := by
    dsimp [y]
    rw [aeval_map_algebraMap, hmap_aeval, minpoly.aeval, map_zero]
  have hderiv_ne : aeval c (derivative (minpoly k c)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable k c).aeval_derivative_ne_zero (minpoly.aeval k c)
  have hderiv : P'.valuation
      (aeval y (derivative ((minpoly k c).map (algebraMap k F)))) = 1 := by
    dsimp [y]
    rw [derivative_map, aeval_map_algebraMap, hmap_aeval]
    exact Valuation.IsTrivialOn.eq_one _ hderiv_ne
  exact differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one
    k F hgen hpmonic hpcoeff hroot hderiv

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Unramified.lean:126` (proof source at `5a01f5fe3621`).
 **A finite separable constant extension is unramified at every place** (Stichtenoth,
Proposition 3.6.3(a)), in Mathlib's local formulation: for a place `P'` of `F' / k'` over
`P = P'.restrict k F`, the local model of `F'` at `P` — the integral closure of the valuation ring
`𝒪_P` in `F'` — is unramified at the centre of `P'`, so `P'` is unramified over `P` with separable
residue extension. -/
theorem isUnramifiedAt_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    letI := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
      (centerIntegralClosure k F P').asIdeal := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  let := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  exact (differentExponent_eq_zero_iff k F P').mp
    (differentExponent_eq_zero_of_constantCompositum_eq_top hcomp P')

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Unramified.lean:140` (proof source at `5a01f5fe3621`).
 Every place in an arbitrary separable algebraic constant extension has ramification index
one. Neither finiteness of the constant extension nor exactness of the constants is required. -/
theorem ramificationIdx_eq_one_of_constantCompositum_eq_top
    [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    ramificationIdx F P' = 1 := by
  let : Algebra.IsSeparable F F' := isSeparable_of_constantCompositum_eq_top (k := k) hcomp
  -- A uniformizer already occurs over a finite extension of the constants.
  obtain ⟨t, ht⟩ := P'.exists_isUniformizer
  rw [isUniformizer_iff_ord_eq_one] at ht
  obtain ⟨L, hL, htL⟩ :=
    exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
      (k := k) (F := F) (by rw [hcomp]; exact IntermediateField.mem_top (x := t))
  let : FiniteDimensional k L := hL
  let E := constantCompositum F L F'
  let : Algebra L E := ((algebraMap L F').codRestrict E
    (algebraMap_mem_constantCompositum F L F')).toAlgebra
  have : IsScalarTower L E F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun c ↦
    Subtype.ext (IsScalarTower.algebraMap_apply k L F' c)
  have hE : constantCompositum F L E = ⊤ :=
    (constantCompositum_eq_top_iff F L F' E).mpr rfl
  let : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
  let : Algebra.IsSeparable F E := isSeparable_of_constantCompositum_eq_top (k := k) hE
  let : Algebra.IsAlgebraic E F' := Algebra.IsAlgebraic.tower_top (K := F) (L := E)
  let Q := P'.restrict L E
  -- The finite constant extension has index one by the local unramifiedness criterion.
  have hQ : Q.ramificationIdx F = 1 := by
    have := isUnramifiedAt_of_constantCompositum_eq_top (k := k) hE Q
    rw [ramificationIdx_eq_ramificationIdx_center (R := (Q.restrict k F).integers) k F Q
      (algebraMap_mem_integers_of_mem_integralClosure k F Q), ← centerIntegralClosure_def]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  -- Since `t` belongs to `E` and has order one upstairs, the remaining index is one too.
  have he : P'.ramificationIdx E = 1 := by
    have hord := ord_algebraMap_restrict L E P' (⟨t, htL⟩ : E)
    rw [IntermediateField.algebraMap_apply, ht] at hord
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) hord.symm
  rw [ramificationIdx_restrict_mul (k₁ := L) (F₀ := F) (F₁ := E), he, one_mul]
  exact hQ

end Place

/-! ### Ramification keeps the constant field exact -/

section Ramified

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/ConstantExtension/Unramified.lean:190` (proof source at `5a01f5fe3621`).
 **A finite separable extension with a totally ramified place acquires no new constants**:
if `k` is the exact constant field of `F` and some place of `F'` is totally ramified over `F`,
then `k` is also the exact constant field of `F'`.

This is the exact-constant-field criterion used for Kummer extensions
(Stichtenoth, Proposition 3.7.3(c)). -/
theorem isIntegrallyClosedIn_of_isTotallyRamified [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] (hex : IsIntegrallyClosedIn k F) {P' : Place k F'}
    (hP' : P'.IsTotallyRamified F) : IsIntegrallyClosedIn k F' := by
  -- Adjoining a constant `c : F'` algebraic over `k` gives a finite separable constant extension
  -- `E = F(c)` of `F`, so the restriction of the totally ramified place to `E` is unramified.
  -- Multiplicativity of ramification indices and degrees then forces `E = F`, after which
  -- exactness of `k` in `F` gives `c ∈ k`.
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.2 fun c hc ↦ ?_
  have hci : IsIntegral k c := hc.isIntegral
  let K := k⟮c⟯
  let E := constantCompositum F K F'
  let : FiniteDimensional k K := IntermediateField.adjoin.finiteDimensional hci
  let : Algebra.IsSeparable k K := by
    rw [IntermediateField.isSeparable_adjoin_simple_iff_isSeparable, IsSeparable,
      ← Polynomial.separable_map (algebraMap k F),
      minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hci]
    exact Algebra.IsSeparable.isSeparable F c
  let : Algebra K E := constantCompositumAlgebra F K F'
  let : Algebra k E := ((algebraMap k F').codRestrict E fun a ↦ by
    rw [IsScalarTower.algebraMap_apply k F F']
    exact IntermediateField.algebraMap_mem E (algebraMap k F a)).toAlgebra
  let : IsScalarTower k F E := .of_algebraMap_eq fun a ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply k F F' a
  let : IsScalarTower k K E := .of_algebraMap_eq fun a ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply k K F' a
  let : IsScalarTower k E F' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply k F E, ← IsScalarTower.algebraMap_apply F E F',
      ← IsScalarTower.algebraMap_apply k F F']
  have : IsScalarTower K E F' := isScalarTower_constantCompositum F K F'
  let Q : Place K E := Place.constantsEquiv k K E (P'.restrict k E)
  have hQ : Q.ramificationIdx F = 1 := Place.ramificationIdx_eq_one_of_constantCompositum_eq_top
    (k := k) ((constantCompositum_eq_top_iff F K F' E).2 rfl) Q
  have hQ' : (P'.restrict k E).ramificationIdx F = 1 := by
    simpa only [Q, Place.ramificationIdx_def, Place.valuation_constantsEquiv] using hQ
  have htower := Place.ramificationIdx_restrict_mul (k₁ := k) (F₀ := F)
    (F₁ := E) P'
  have hle : Module.finrank F F' ≤ Module.finrank E F' := by
    calc
      Module.finrank F F' = Place.ramificationIdx F P' :=
        ((Place.isTotallyRamified_iff F).mp hP').symm
      _ = Place.ramificationIdx E P' * (P'.restrict k E).ramificationIdx F := htower
      _ = Place.ramificationIdx E P' := by rw [hQ', mul_one]
      _ ≤ Module.finrank E F' := Place.ramificationIdx_le_finrank E P'
  have hEbot : E = ⊥ := (IntermediateField.eq_of_le_of_finrank_le' bot_le <| by
    rwa [IntermediateField.finrank_bot']).symm
  have hcmem : c ∈ E := algebraMap_mem_constantCompositum F K F'
    ⟨c, IntermediateField.mem_adjoin_simple_self k c⟩
  rw [hEbot, IntermediateField.mem_bot] at hcmem
  obtain ⟨a, rfl⟩ := hcmem
  obtain ⟨b, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    (isIntegral_algebraMap_iff.mp hci)
  exact ⟨b, IsScalarTower.algebraMap_apply k F F' b⟩

end Ramified

end TauCeti
end

end

/-! ## Source 20: `TauCeti.FieldTheory.FunctionField.Different.Separating`
Original source SHA256: `d36ba7fb6ec09bb3112206f8127a87c19b9e478e8cdc49aa14ea28c313b92a53`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Translates of a separating element are almost always prime elements

Let `F / k` be an algebraic function field and `x` a separating element, so that `F / k(x)` is a
finite separable extension. Only finitely many places of `F` ramify over `k(x)`
(`TauCeti.Place.finite_setOf_differentExponent_ne_zero`). A rational place `P` of `F` that is not
a pole of `x` lies over a rational finite place of `k(x)`, the zero of `X - a` for some `a ∈ k`;
if `P` is unramified there, `x - a` is a prime element at `P`. A place of arbitrary degree that
is not a pole of `x` lies over the zero of some irreducible `q ∈ k[X]`, and if it is unramified
there, `q(x)` is a prime element.

An unramified place has a separable residue extension over the place below it. Over an infinite
field `k` there are infinitely many rational places `X - a` of `k(x)`, and the places of `F` above
all but finitely many of them are unramified, so their residue fields are separable over `k`. Over
a finite field every residue field is separable. Either way a separably generated function field
has infinitely many places with residue field separable over `k`, even when `k` is imperfect and
`F` has only finitely many rational places.

## Main results

* `TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one`: at all but finitely many rational
  places that are not poles of a separating `x`, some `x - a` is a prime element.
* `TauCeti.Place.finite_setOf_forall_irreducible_ord_aeval_ne_one`: at all but finitely many places
  that are not poles of a separating `x`, some `q(x)` with `q` irreducible is a prime element.
* `TauCeti.Place.infinite_setOf_isSeparable_residueField`: if `F / k` has a separating element,
  infinitely many places of `F` have residue field separable over `k`.
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Separating.lean:57` (proof source at `5a01f5fe3621`).
 **Almost every rational place has a translate of `x` as a prime element**: for a separating
element `x`, only finitely many rational places `P` with `ord_P x ≥ 0` admit no constant `a` with
`ord_P (x - a) = 1`. -/
theorem finite_setOf_forall_ord_sub_algebraMap_ne_one (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | P.degree = 1 ∧ 0 ≤ P.ord x ∧
      ∀ a : k, P.ord (x - algebraMap k F a) ≠ 1}.Finite := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X hx
  refine (finite_setOf_differentExponent_ne_zero (k' := k) (F' := F) k (RatFunc k)
    (IsFunctionField.ratFunc k)).subset fun P ⟨hP, hx0, hne⟩ ↦ ?_
  refine (differentExponent_pos_of_one_lt_ramificationIdx k (RatFunc k) P ?_).ne'
  refine lt_of_le_of_ne (ramificationIdx_pos (RatFunc k) P) fun he ↦ ?_
  rcases eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C (Nat.eq_one_of_mul_eq_one_right
    (hP ▸ degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P).symm) with h | ⟨a, h⟩
  · -- `x` would have a pole at `P`, lying over the pole of `X`.
    rw [← hX, ord_algebraMap_restrict k (RatFunc k) P, h, ord_infty, RatFunc.intDegree_X,
      ← he] at hx0
    omega
  · -- `x - a` is a prime element at `P`, lying unramified over the zero of `X - a`.
    refine hne a ?_
    rw [← hX, IsScalarTower.algebraMap_apply k (RatFunc k) F, RatFunc.algebraMap_eq_C, ← map_sub,
      ord_algebraMap_restrict k (RatFunc k) P, h, ord_adicOfIrreducible_X_sub_C_self, ← he,
      Nat.cast_one, mul_one]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Separating.lean:84` (proof source at `5a01f5fe3621`).
 **Almost every place has a prime element `q(x)`**: for a separating element `x`, only finitely
many places `P` with `ord_P x ≥ 0` admit no irreducible `q ∈ k[X]` with `ord_P q(x) = 1`. -/
theorem finite_setOf_forall_irreducible_ord_aeval_ne_one (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | 0 ≤ P.ord x ∧
      ∀ q : Polynomial k, Irreducible q → P.ord (Polynomial.aeval x q) ≠ 1}.Finite := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X hx
  refine (finite_setOf_differentExponent_ne_zero (k' := k) (F' := F) k (RatFunc k)
    (IsFunctionField.ratFunc k)).subset fun P ⟨hx0, hne⟩ ↦ ?_
  refine (differentExponent_pos_of_one_lt_ramificationIdx k (RatFunc k) P ?_).ne'
  refine lt_of_le_of_ne (ramificationIdx_pos (RatFunc k) P) fun he ↦ ?_
  rcases eq_infty_or_exists_eq_adicOfIrreducible (P.restrict k (RatFunc k)) with h | ⟨q, hq, h⟩
  · -- `x` would have a pole at `P`, lying over the pole of `X`.
    rw [← hX, ord_algebraMap_restrict k (RatFunc k) P, h, ord_infty, RatFunc.intDegree_X,
      ← he] at hx0
    omega
  · -- `q(x)` is a prime element at `P`, lying unramified over the zero of `q`.
    classical
    refine hne q hq ?_
    rw [← hX, Polynomial.aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
      ord_algebraMap_restrict k (RatFunc k) P, h,
      ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl _), ← he,
      Nat.cast_one, mul_one]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Different/Separating.lean:114` (proof source at `5a01f5fe3621`).
 **Infinitely many places have a separable residue field**: if `F / k` has a separating element
`x`, then infinitely many places of `F` have residue field separable over `k`. Over an infinite
field these include the places above all but finitely many rational places `X - a` of `k(x)`, where
`F / k(x)` is unramified; over a finite field every place qualifies. -/
theorem infinite_setOf_isSeparable_residueField (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | Algebra.IsSeparable k P.ResidueField}.Infinite := by
  rcases finite_or_infinite k with hk | hk
  · -- A finite field is perfect, so every residue field is separable over it.
    have := infinite hF
    simpa [isSeparable_residueField_of_perfectField _ hF] using Set.infinite_univ (α := Place k F)
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  -- Choose a place `P a` of `F` above the rational place `X - a` of `k(x)`, for each `a ∈ k`.
  choose P hP using fun a : k ↦ restrict_surjective (k := k) (F := RatFunc k) hF
    (adicOfIrreducible (Polynomial.irreducible_X_sub_C a))
  replace hP (a : k) :
      (P a).restrict k (RatFunc k) = adicOfIrreducible (Polynomial.irreducible_X_sub_C a) :=
    hP a
  have hinj : Function.Injective P := fun a b h ↦ adicOfIrreducible_X_sub_C_injective (by
    simp only
    rw [← hP a, ← hP b, h])
  refine ((Set.infinite_range_of_injective hinj).sdiff (finite_setOf_differentExponent_ne_zero
    (k' := k) (F' := F) k (RatFunc k) (IsFunctionField.ratFunc k))).mono ?_
  rintro _ ⟨⟨a, rfl⟩, hd⟩
  simp only [Set.mem_ofPred_eq, not_not] at hd
  -- `P a` is unramified over `X - a`, hence tame, so its residue extension is separable.
  have hle := ramificationIdx_le_differentExponent_add_one k (RatFunc k) (P a)
  have hpos := ramificationIdx_pos (RatFunc k) (P a)
  have htame := (ramificationIdx_eq_differentExponent_add_one_iff k (RatFunc k) (P a)).mp
    (by omega)
  have := ((isTame_iff_isSeparable_residueField k (RatFunc k) (P a)).mp htame).1
  -- The residue field of `X - a` is `k`.
  have := ((P a).restrict k (RatFunc k)).isSeparable_residueField_of_degree_eq_one
    (by rw [hP a]; exact degree_adicOfIrreducible_X_sub_C a)
  exact Algebra.IsSeparable.trans k ((P a).restrict k (RatFunc k)).ResidueField (P a).ResidueField

end Place

end TauCeti
end

end

/-! ## Source 21: `TauCeti.FieldTheory.FunctionField.Differential.ConstantExtension`
Original source SHA256: `89f13f8ad95af853aae41dfacc03bafdc365ab001948b0889cb331fd710c1dc2`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The differential `dx` under a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of an algebraic function field
`F / k`, and let `x` be a separating element of `F / k`. Its image in `F'` is separating for
`F' / k'`. This file proves that the cotrace from `F` to `F'` carries the Weil differential `dx` of
`F` (`TauCeti.weilDifferentialOfSeparating`) to the Weil differential `dx` of `F'`. The key case
is the rational function field: the cotrace from `k(X)` to `k'(X)` carries the canonical
differential `η` of `k(X)` to that of `k'(X)`.

Since the cotrace is injective and `F`-semilinear, identities between Weil differentials of `F`
can be checked after a constant field extension, where more places are rational. This is how the
chain rule `dy = (dy/dx) · dx` is proved over an arbitrary exact constant field
(`TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul`).

## Main results

* `TauCeti.weilDifferentialCotrace_ratFuncWeilDifferential`: the cotrace from `k(X)` to `k'(X)`
  carries `η` to `η'`.
* `TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating`: the cotrace from `F` to
  `F · k'` carries `dx` to `dx`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.4, Definition 3.4.5, Proposition 3.4.11 and Theorem 4.3.2.
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

/-! ### The rational function field -/

section RatFunc

variable {k k' : Type*} [Field k] [Field k']
variable [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
variable [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/ConstantExtension.lean:59` (proof source at `5a01f5fe3621`).
 **The cotrace of `η` under a constant field extension is `η`**: for a finite separable
extension `k' / k`, the cotrace from `k(X)` to `k'(X)` carries the canonical Weil differential `η`
of `k(X)` to that of `k'(X)`. -/
theorem weilDifferentialCotrace_ratFuncWeilDifferential
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    letI := isSeparable_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
        (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ =
      ⟨ratFuncWeilDifferential k', ratFuncWeilDifferential_mem k'⟩ := by
  have h := constantCompositum_ratFunc_eq_top (k := k) hX
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_of_constantCompositum_eq_top (k := k) h
  set ω := weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
    (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩
  have hη : (⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
      ↥(weilDifferentialSpace k (RatFunc k))) ≠ 0 := by
    simpa [← Subtype.coe_ne_coe] using ratFuncWeilDifferential_ne_zero k
  have hω : (ω : Module.Dual k' ↥(repartitionSpace k' (RatFunc k'))) ≠ 0 := by
    simpa [ZeroMemClass.coe_eq_zero, ω] using hη
  refine Subtype.ext (eq_ratFuncWeilDifferential ω.2 ?_ ?_)
  · -- `(Cotr η) = Con (-2 P_∞) + Diff = -2 P'_∞`: the extension is unramified with trivial
    -- different, and `P'_∞` is the only place over `P_∞`.
    convert isGreatest_weilDifferentialDivisor (IsFunctionField.ratFunc k')
      isIntegrallyClosedIn_ratFunc ω.2 hω using 1
    rw [weilDifferentialDivisor_weilDifferentialCotrace (IsFunctionField.ratFunc k)
      (IsFunctionField.ratFunc k') isIntegrallyClosedIn_ratFunc isIntegrallyClosedIn_ratFunc _ hη]
    simp only [weilDifferentialDivisor_ratFuncWeilDifferential]
    ext Q'
    rw [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_add, Divisor.coeff_conorm, Divisor.coeff_different,
      Place.differentExponent_eq_zero_of_constantCompositum_eq_top (k := k) h,
      Place.ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h]
    simp only [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul]
    by_cases hQ : Q' = Place.infty k'
    · rw [hQ, (Place.restrict_ratFunc_eq_infty_iff hX _).mpr rfl]
      simp
    · rw [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ,
        _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
          (mt (Place.restrict_ratFunc_eq_infty_iff hX _).mp hQ)]
      simp
  · -- After `Tr_{k'/k}`, the local components of `Cotr η` over `P_∞` add up to `η_{P_∞} ∘ Tr`, and
    -- `P'_∞` is alone over `P_∞`; evaluating at `α X⁻¹` gives `Tr (α c) = -Tr α` for every `α`,
    -- where `c` is the value to compute, and the trace form is nondegenerate.
    set c := repartitionDualComponent (ω : Module.Dual k' ↥(repartitionSpace k' (RatFunc k')))
      (Place.infty k') (RatFunc.X : RatFunc k')⁻¹
    have htr (α : k') : Algebra.trace k k' (α * c) = -Algebra.trace k k' α := by
      have hsum := trace_finsum_repartitionDualComponent_weilDifferentialCotrace
        (IsFunctionField.ratFunc k) (IsFunctionField.ratFunc k')
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ (Place.infty k)
        (algebraMap k' (RatFunc k') α * (RatFunc.X : RatFunc k')⁻¹)
      simp_rw [Place.restrict_ratFunc_eq_infty_iff hX] at hsum
      rw [finsum_cond_eq_left, ← Algebra.smul_def, map_smul, smul_eq_mul] at hsum
      have hsmul : α • (RatFunc.X : RatFunc k')⁻¹ =
          (RatFunc.X : RatFunc k)⁻¹ • algebraMap k' (RatFunc k') α := by
        rw [Algebra.smul_def, Algebra.smul_def, map_inv₀, hX, mul_comm]
      rw [hsum, hsmul, map_smul,
        trace_algebraMap_of_constantCompositum_eq_top isIntegrallyClosedIn_ratFunc h,
        smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
        repartitionDualComponent_ratFuncWeilDifferential_inv_X, smul_eq_mul, mul_neg_one]
    by_contra hne
    obtain ⟨β, hβ⟩ := Algebra.trace_surjective k k' 1
    have h1 := htr (β / (c + 1))
    rw [div_mul_eq_mul_div, eq_neg_iff_add_eq_zero, ← map_add, ← add_div, ← mul_add_one,
      mul_div_assoc, div_self (by rwa [Ne, add_eq_zero_iff_eq_neg]), mul_one, hβ] at h1
    exact one_ne_zero h1

end RatFunc

/-! ### Separating elements under a constant field extension -/

section ConstantExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/ConstantExtension.lean:138` (proof source at `5a01f5fe3621`).
 **`dx` is stable under constant field extension**: for a finite separable constant field
extension `F' = F · k'` and a separating element `x` of `F / k`, whose image in `F'` is separating
over `k'`, the cotrace to `F'` of the Weil differential `dx` of `F` is the Weil differential `dx`
of `F'`. -/
theorem weilDifferentialCotrace_weilDifferentialOfSeparating [FiniteDimensional k k']
    [Algebra.IsSeparable k k'] (h : constantCompositum F k' F' = ⊤) (hF : IsFunctionField k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) h
    letI := isSeparable_of_constantCompositum_eq_top (k := k) h
    letI := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := x) h
    weilDifferentialCotrace k' F' hF (hF.of_constantCompositum_eq_top h)
        (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating (hF.of_constantCompositum_eq_top h)
        (((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars
          k') := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := x) h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hx' : Transcendental k' (algebraMap F F' x) :=
    ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars k'
  rw [weilDifferentialOfSeparating_def, weilDifferentialOfSeparating_def]
  -- The rational function fields `k(X) ⊆ k'(X)`, with `X` acting as `x` on `F` and on `F'`.
  have hX : Transcendental k (RatFunc.X : RatFunc k') := fun h ↦
    RatFunc.transcendental_X (h.tower_top k')
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  let _ := ratFuncAlgebraOfTranscendental hx'
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  let _ := isFunctionField_iff_functionField.mp hF'
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx'
  let _ := ratFuncAlgebraOfTranscendental hX
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hX
  have hXX := algebraMap_ratFuncAlgebraOfTranscendental_X hX
  -- `k(X)` acts on `F'` through `F`; the two routes through `F` and through `k'(X)` agree, as
  -- both are `k`-algebra maps sending `X` to `x`.
  let _ : Algebra (RatFunc k) F' := ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  let _ : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower k (RatFunc k) F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply (RatFunc k) F F', ← IsScalarTower.algebraMap_apply k,
      ← IsScalarTower.algebraMap_apply k F F']
  let _ : IsScalarTower (RatFunc k) (RatFunc k') F' := .of_algebraMap_eq fun r ↦ by
    -- Both ring maps `k(X) → F'` are determined by their values on `k[X]`.
    refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k))
      (j := algebraMap (RatFunc k) F')
      (k := (algebraMap (RatFunc k') F').comp (algebraMap (RatFunc k) (RatFunc k')))
      (Polynomial.ringHom_ext (fun c ↦ ?_) ?_)) r
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply k (RatFunc k) F',
        ← IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc k'),
        IsScalarTower.algebraMap_apply k k' (RatFunc k'),
        ← IsScalarTower.algebraMap_apply k' (RatFunc k') F',
        ← IsScalarTower.algebraMap_apply k k' F']
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X]
      rw [hXX, algebraMap_ratFuncAlgebraOfTranscendental_X,
        IsScalarTower.algebraMap_apply (RatFunc k) F F',
        algebraMap_ratFuncAlgebraOfTranscendental_X]
  have hcomp := constantCompositum_ratFunc_eq_top (k := k) (k' := k') hXX
  let _ := finiteDimensional_of_constantCompositum_eq_top (k := k) hcomp
  let _ := isSeparable_of_constantCompositum_eq_top (k := k) hcomp
  rw [weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k) (F₁ := F),
    ← weilDifferentialCotrace_ratFuncWeilDifferential hXX,
    weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k') (F₁ := RatFunc k')]

end ConstantExtension

end TauCeti
end

end

/-! ## Source 22: `TauCeti.FieldTheory.FunctionField.Place.Completion.Basic`
Original source SHA256: `5b678ea69627877aeb91ba59f29a1693e7d4cd5cbed86d94eb928f4c22ea1c9d`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Completion at a place

The completion of a field at a place carries the same normalized valuation and constant field
embedding. Its valuation ring is a complete discrete valuation ring, and a uniformizer of the
original field is still a uniformizer after completion. Completeness can be read through the
order filtration: a sequence whose terms agree to increasing order has a limit to which it agrees
to the same orders. In particular the completed valuation ring is complete for the adic topology
of its maximal ideal, hence a Henselian local ring.

The inclusion identifies every finite interval of the order filtration with the corresponding
interval in the completion. In particular, completion does not change the residue field. These
identifications allow local calculations with finitely many coefficients to pass between the
field and its completion. No finiteness or perfectness of the residue field is assumed.

The underlying complete field and extension of the valuation are Mathlib's
`Valuation.Completion` and `Valued.valuedCompletion`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.7.
-/

section
open UniformSpace Topology
open scoped WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- Kind: ABBREV. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:45` (proof source at `5a01f5fe3621`).
 The completion of `F` for the valuation of `P`. -/
abbrev Completion := P.valuation.Completion

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:48` (proof source at `5a01f5fe3621`).
 The constants act on the completion through their embedding in `F`. -/
noncomputable instance instAlgebraCompletion : Algebra k P.Completion :=
  ((UniformSpace.Completion.coeRingHom.comp
    (WithVal.equiv P.valuation).symm.toRingHom).comp (algebraMap k F)).toAlgebra

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:53` (proof source at `5a01f5fe3621`).
 The canonical embedding of the field into its completion at `P`. -/
noncomputable def completionEmbedding : F →ₐ[k] P.Completion :=
  { UniformSpace.Completion.coeRingHom.comp (WithVal.equiv P.valuation).symm.toRingHom with
    commutes' _ := rfl }

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:58` (proof source at `5a01f5fe3621`).
 The canonical embedding is the uniform-space completion map on the valued field. -/
theorem completionEmbedding_apply (x : F) :
    P.completionEmbedding x =
      ((WithVal.toVal P.valuation x : WithVal P.valuation) : P.Completion) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:64` (proof source at `5a01f5fe3621`).
 The embedding into the completion preserves the normalized valuation. -/
@[simp]
theorem valuation_completionEmbedding (x : F) :
    Valued.v (P.completionEmbedding x) = P.valuation x :=
  Valued.valuedCompletion_apply (WithVal.toVal P.valuation x)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:69` (proof source at `5a01f5fe3621`).
 The original field is dense in its completion at `P`. -/
theorem denseRange_completionEmbedding : DenseRange P.completionEmbedding := by
  have h : (P.completionEmbedding : F → P.Completion) ∘ WithVal.ofVal =
      ((↑) : WithVal P.valuation → P.Completion) := by
    funext x
    exact congrArg ((↑) : WithVal P.valuation → P.Completion)
      (WithVal.toVal_ofVal P.valuation x)
  exact (h.symm ▸ UniformSpace.Completion.denseRange_coe).of_comp

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:78` (proof source at `5a01f5fe3621`).
 The extension of `P` to the completed field, with its original normalization. -/
noncomputable def completionPlace : Place k P.Completion where
  valuation := Valued.v
  valuation_surjective := fun γ ↦ by
    obtain ⟨x, rfl⟩ := P.valuation_surjective γ
    exact ⟨P.completionEmbedding x, P.valuation_completionEmbedding x⟩
  isTrivialOn := ⟨fun c hc ↦ by
    rw [← P.completionEmbedding.commutes c, valuation_completionEmbedding]
    exact P.isTrivialOn.eq_one c hc⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:88` (proof source at `5a01f5fe3621`).
-/
@[simp]
theorem completionPlace_valuation (x : P.Completion) :
    P.completionPlace.valuation x = Valued.v x := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:93` (proof source at `5a01f5fe3621`).
 Completion preserves the order of every function, including the junk value at zero. -/
@[simp]
theorem ord_completionEmbedding (x : F) :
    P.completionPlace.ord (P.completionEmbedding x) = P.ord x := by
  simp [ord_def]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:98` (proof source at `5a01f5fe3621`).
 A uniformizer in the original field remains a uniformizer in the completion. -/
theorem isUniformizer_completionEmbedding_iff (x : F) :
    P.completionPlace.valuation.IsUniformizer (P.completionEmbedding x) ↔
      P.valuation.IsUniformizer x := by
  simp only [isUniformizer_iff_ord_eq_one, ord_completionEmbedding]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:104` (proof source at `5a01f5fe3621`).
 The embedding preserves every step of the order filtration. -/
theorem completionEmbedding_mem_filtration_iff {a : ℤ} {x : F} :
    P.completionEmbedding x ∈ P.completionPlace.filtration a ↔ x ∈ P.filtration a := by
  simp only [mem_filtration_iff, completionPlace_valuation, valuation_completionEmbedding]

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:109` (proof source at `5a01f5fe3621`).
 The valuation ring of the completed field is complete for the induced uniform structure. -/
instance completeSpace_completionIntegers : CompleteSpace P.completionPlace.integers := by
  have h : (P.completionPlace.integers : Set P.Completion) =
      ((Valued.v (R := P.Completion)).valuationSubring : Set P.Completion) := by
    ext x
    simp only [SetLike.mem_coe, mem_integers_iff, completionPlace_valuation,
      Valuation.mem_valuationSubring_iff]
  exact (h.symm ▸ Valued.isClosed_valuationSubring P.Completion).completeSpace_coe

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:118` (proof source at `5a01f5fe3621`).
 Each step of the order filtration of the completed field is closed. -/
theorem isClosed_completionPlace_filtration (a : ℤ) :
    IsClosed (P.completionPlace.filtration a : Set P.Completion) := by
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq a
  convert Valued.isClosed_closedBall P.Completion
    (Valued.v.restrict (P.completionEmbedding s)) using 1
  ext x
  simp only [SetLike.mem_coe, mem_filtration_iff, completionPlace_valuation, Set.mem_ofPred_eq,
    Valuation.restrict_le_iff, valuation_completionEmbedding, P.valuation_eq_exp_neg_ord hs0, hs]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:130` (proof source at `5a01f5fe3621`).
 Completeness of the completed field, read through the order filtration: if the terms of a
sequence agree to increasing order, `g n ≡ g m` to order `m` whenever `m ≤ n`, then some completed
function agrees with each term `g n` to order `n`. -/
theorem exists_forall_sub_mem_completionPlace_filtration {g : ℕ → P.Completion}
    (hg : ∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.completionPlace.filtration m) :
    ∃ x : P.Completion, ∀ n : ℕ, x - g n ∈ P.completionPlace.filtration n := by
  have hcauchy : CauchySeq g := by
    refine (Valued.hasBasis_uniformity P.Completion ℤᵐ⁰).cauchySeq_iff.mpr fun γ _ ↦ ?_
    obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
    refine ⟨n, fun m hm l hl ↦ ?_⟩
    have hdiff : g l - g m ∈ P.completionPlace.filtration n := by
      simpa using (P.completionPlace.filtration n).sub_mem (hg hl) (hg hm)
    rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact (P.completionPlace.mem_filtration_iff.mp hdiff).trans_lt hn
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, fun n ↦ ?_⟩
  have hclosed := (P.isClosed_completionPlace_filtration n).preimage
    (continuous_id.sub (continuous_const (y := g n)))
  exact hclosed.mem_of_tendsto hx (Filter.eventually_ge_atTop n |>.mono fun m hm ↦ hg hm)

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:150` (proof source at `5a01f5fe3621`).
 The completed valuation ring is complete for the adic topology of its maximal ideal. In
particular it is a Henselian local ring (`TauCeti.IsAdicComplete.henselianLocalRing`). -/
instance isAdicComplete_completionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal P.completionPlace.integers)
      P.completionPlace.integers where
  toIsHausdorff := inferInstance
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      mem_maximalIdeal_pow_iff_coe_mem_filtration] at hf ⊢
    obtain ⟨x, hx⟩ := P.exists_forall_sub_mem_completionPlace_filtration
      (g := fun n ↦ (f n : P.Completion)) fun m n hmn ↦ by
        simpa using (P.completionPlace.filtration m).neg_mem (hf hmn)
    have hx0 : x ∈ P.completionPlace.integers := by
      have h := (P.completionPlace.filtration 0).add_mem (hx 0)
        (P.completionPlace.mem_filtration_zero_iff.mpr (f 0).2)
      simpa [P.completionPlace.mem_filtration_zero_iff] using h
    refine ⟨⟨x, hx0⟩, fun n ↦ ?_⟩
    simpa using (P.completionPlace.filtration n).neg_mem (hx n)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:168` (proof source at `5a01f5fe3621`).
 A completed function can be approximated by a function in `F` to any prescribed order. -/
theorem exists_sub_completionEmbedding_mem_filtration (x : P.Completion) (b : ℤ) :
    ∃ y : F, x - P.completionEmbedding y ∈ P.completionPlace.filtration b := by
  obtain ⟨t, ht0, ht⟩ := P.exists_ne_zero_ord_eq b
  have ht' : Valued.v.restrict (P.completionEmbedding t) ≠ 0 := by
    simp [ht0]
  have hU : {z : P.Completion | Valued.v (z - x) < WithZero.exp (-b)} ∈ 𝓝 x := by
    refine Valued.mem_nhds.mpr ⟨Units.mk0 _ ht', fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hz
    simpa [P.valuation_eq_exp_neg_ord ht0, ht] using hz
  obtain ⟨y, hy⟩ := P.denseRange_completionEmbedding.mem_nhds hU
  refine ⟨y, ?_⟩
  rw [mem_filtration_iff, completionPlace_valuation, Valuation.map_sub_swap]
  exact hy.le

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:185` (proof source at `5a01f5fe3621`).
 An element of the completed filtration has an approximation in the original filtration,
with error in any smaller step. -/
theorem exists_filtration_sub_completionEmbedding_mem {a b : ℤ} (hab : a ≤ b)
    (x : P.completionPlace.filtration a) :
    ∃ y : P.filtration a,
      (x : P.Completion) - P.completionEmbedding y ∈ P.completionPlace.filtration b := by
  obtain ⟨y, hy⟩ := P.exists_sub_completionEmbedding_mem_filtration x b
  have hya : P.completionEmbedding y ∈ P.completionPlace.filtration a := by
    have h := (P.completionPlace.filtration a).sub_mem x.2
      (P.completionPlace.filtration_antitone hab hy)
    simpa using h
  exact ⟨⟨y, P.completionEmbedding_mem_filtration_iff.mp hya⟩, hy⟩

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:197` (proof source at `5a01f5fe3621`).
 The inclusion of a step of the order filtration into its completed counterpart. -/
noncomputable def completionFiltrationMap (a : ℤ) :
    P.filtration a →ₗ[k] P.completionPlace.filtration a :=
  (P.completionEmbedding.toLinearMap.domRestrict (P.filtration a)).codRestrict
    (P.completionPlace.filtration a) (fun x ↦ P.completionEmbedding_mem_filtration_iff.mpr x.2)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:203` (proof source at `5a01f5fe3621`).
-/
@[simp]
theorem completionFiltrationMap_apply (a : ℤ) (x : P.filtration a) :
    (P.completionFiltrationMap a x : P.Completion) = P.completionEmbedding x := (rfl)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:208` (proof source at `5a01f5fe3621`).
 Completion preserves every finite interval of the order filtration. The isomorphism is
induced by the canonical embedding, rather than by choices of representatives. -/
noncomputable def completionFiltrationQuotientEquiv {a b : ℤ} (hab : a ≤ b) :
    (P.filtration a ⧸ (P.filtration b).submoduleOf (P.filtration a)) ≃ₗ[k]
      (P.completionPlace.filtration a ⧸
        (P.completionPlace.filtration b).submoduleOf (P.completionPlace.filtration a)) := by
  let f := P.completionFiltrationMap a
  let q := (P.filtration b).submoduleOf (P.filtration a)
  let q' := (P.completionPlace.filtration b).submoduleOf (P.completionPlace.filtration a)
  have hf : q ≤ q'.comap f := fun x hx ↦
    P.completionEmbedding_mem_filtration_iff.mpr hx
  refine LinearEquiv.ofBijective (q.mapQ q' f hf) ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective q x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective q y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
    apply (Submodule.Quotient.eq q).mpr
    -- Read membership in the relative submodule as membership of the underlying function.
    have h' : P.completionEmbedding ((x : F) - (y : F)) ∈
        P.completionPlace.filtration b := by
      simpa only [q', f, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.subtype_apply, map_sub, completionFiltrationMap_apply, Submodule.coe_sub] using h
    exact P.completionEmbedding_mem_filtration_iff.mp h'
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective q' x
    obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem hab x
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    have h := (P.completionPlace.filtration b).neg_mem hy
    simpa only [q', f, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, neg_sub,
      completionFiltrationMap_apply, Submodule.coe_sub] using h

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:241` (proof source at `5a01f5fe3621`).
 The filtration quotient equivalence sends the class of a function to the class of its
canonical image in the completion. -/
@[simp]
theorem completionFiltrationQuotientEquiv_apply_mk {a b : ℤ} (hab : a ≤ b)
    (x : P.filtration a) :
    P.completionFiltrationQuotientEquiv hab (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (P.completionFiltrationMap a x) := (rfl)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:247` (proof source at `5a01f5fe3621`).
 The canonical map of valuation rings induced by completion. -/
noncomputable def completionIntegersEmbedding : P.integers →ₐ[k] P.completionPlace.integers where
  toFun x := ⟨P.completionEmbedding x, by
    simpa only [mem_integers_iff, completionPlace_valuation, valuation_completionEmbedding]
      using x.2⟩
  map_zero' := Subtype.ext (map_zero P.completionEmbedding)
  map_one' := Subtype.ext (map_one P.completionEmbedding)
  map_add' x y := Subtype.ext (map_add P.completionEmbedding (x : F) (y : F))
  map_mul' x y := Subtype.ext (map_mul P.completionEmbedding (x : F) (y : F))
  commutes' c := Subtype.ext (by simp)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:258` (proof source at `5a01f5fe3621`).
-/
@[simp]
theorem completionIntegersEmbedding_apply (x : P.integers) :
    (P.completionIntegersEmbedding x : P.Completion) = P.completionEmbedding x := (rfl)

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:262` (proof source at `5a01f5fe3621`).
 Completion reflects units of the valuation ring. -/
instance isLocalHom_completionIntegersEmbedding : IsLocalHom P.completionIntegersEmbedding where
  map_nonunit x hx := by
    rw [P.isUnit_iff_valuation_eq_one]
    simpa only [P.completionPlace.isUnit_iff_valuation_eq_one, completionPlace_valuation,
      completionIntegersEmbedding_apply, valuation_completionEmbedding] using hx

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:269` (proof source at `5a01f5fe3621`).
 Completion induces an isomorphism of residue fields over the original constants. -/
noncomputable def residueFieldEquivCompletion : P.ResidueField ≃ₐ[k]
    P.completionPlace.ResidueField := by
  let f := IsLocalRing.ResidueField.mapAlgHom P.completionIntegersEmbedding
  refine AlgEquiv.ofBijective f ⟨f.injective, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := P.completionPlace.integers) x
  have hx : (x : P.Completion) ∈ P.completionPlace.filtration 0 :=
    P.completionPlace.mem_filtration_zero_iff.mpr x.2
  obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem (by norm_num : (0 : ℤ) ≤ 1)
    ⟨x, hx⟩
  let y' : P.integers := ⟨y, P.mem_filtration_zero_iff.mp y.2⟩
  refine ⟨IsLocalRing.residue P.integers y', ?_⟩
  rw [IsLocalRing.ResidueField.mapAlgHom_residue]
  apply (P.completionPlace.residue_eq_iff_sub_mem_filtration_one).mpr
  have h := (P.completionPlace.filtration 1).neg_mem hy
  simpa only [neg_sub, completionIntegersEmbedding_apply] using h

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:288` (proof source at `5a01f5fe3621`).
 The residue-field isomorphism commutes with reduction of integral functions. -/
@[simp]
theorem residueFieldEquivCompletion_apply_residue (x : P.integers) :
    P.residueFieldEquivCompletion (IsLocalRing.residue P.integers x) =
      IsLocalRing.residue P.completionPlace.integers (P.completionIntegersEmbedding x) :=
  IsLocalRing.ResidueField.mapAlgHom_residue P.completionIntegersEmbedding x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:295` (proof source at `5a01f5fe3621`).
 Reading the residue of a function regular at `P` back in `F_P` gives its value at `P`. -/
@[simp]
theorem residueFieldEquivCompletion_symm_residue_completionIntegersEmbedding (x : P.integers) :
    P.residueFieldEquivCompletion.symm
        (IsLocalRing.residue P.completionPlace.integers (P.completionIntegersEmbedding x)) =
      IsLocalRing.residue P.integers x := by
  rw [← residueFieldEquivCompletion_apply_residue, AlgEquiv.symm_apply_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/Basic.lean:303` (proof source at `5a01f5fe3621`).
 Completing a place preserves its degree over the constants. -/
@[simp]
theorem degree_completionPlace : P.completionPlace.degree = P.degree := by
  simp only [degree_eq_finrank]
  exact P.residueFieldEquivCompletion.toLinearEquiv.finrank_eq.symm

end TauCeti.Place
end

end

/-! ## Source 23: `TauCeti.RingTheory.Ideal.Quotient.SquareZero`
Original source SHA256: `dbfa5accc693de9d8ada64db138b3a9d8b7f02901d7185747cd80be4b41162d9`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The `p`-th power map modulo a square-zero ideal

Let `B` be a commutative ring in which a prime `p` is zero, and let `I` be an ideal of `B` with
`I ^ 2 = ⊥`. Two lifts of an element of `B ⧸ I` differ by some `i ∈ I`, and `i ^ p = 0`, so their
`p`-th powers agree. The `p`-th power map of `B` therefore factors through `B ⧸ I` as a ring
homomorphism `B ⧸ I →+* B`.

## Main definitions

* `Ideal.Quotient.powLift`: the ring homomorphism `B ⧸ I →+* B` sending the class of `b` to
  `b ^ p`.
-/

section
namespace Ideal.Quotient

variable {B : Type*} [CommRing B] (p : ℕ) [hp : Fact p.Prime]

/-- Kind: DEF. Locator: `TauCeti/RingTheory/Ideal/Quotient/SquareZero.lean:34` (proof source at `5a01f5fe3621`).
 Modulo a square-zero ideal of a ring in which `p = 0`, the `p`-th power of a lift does not
depend on the lift: the `p`-th power map factors through `B ⧸ I`. -/
def powLift (hpB : (p : B) = 0) {I : Ideal B} (hI : I ^ 2 = ⊥) : B ⧸ I →+* B :=
  lift I
    { toFun := (· ^ p)
      map_one' := one_pow p
      map_mul' := fun x y ↦ mul_pow x y p
      map_zero' := zero_pow hp.out.ne_zero
      map_add' := fun x y ↦ by
        simp only [add_pow_prime_eq' hp.out, hpB, zero_mul, add_zero] }
    fun i hi ↦ by
      have hi2 : i ^ 2 = 0 := by simpa [hI] using pow_mem_pow hi 2
      exact pow_eq_zero_of_le hp.out.two_le hi2

variable (hpB : (p : B) = 0) {I : Ideal B} (hI : I ^ 2 = ⊥)

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Ideal/Quotient/SquareZero.lean:50` (proof source at `5a01f5fe3621`).
 `powLift` sends the class of `b` to `b ^ p`. -/
@[simp]
theorem powLift_mk (b : B) : powLift p hpB hI (mk I b) = b ^ p :=
  lift_mk _ _ _

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Ideal/Quotient/SquareZero.lean:55` (proof source at `5a01f5fe3621`).
 Reducing `powLift p hpB hI z` modulo `I` gives `z ^ p`. -/
@[simp]
theorem mk_powLift (z : B ⧸ I) : mk I (powLift p hpB hI z) = z ^ p := by
  obtain ⟨b, rfl⟩ := mk_surjective z
  rw [powLift_mk, map_pow]

end Ideal.Quotient
end

end

/-! ## Source 24: `TauCeti.RingTheory.Smooth.Field`
Original source SHA256: `518600e9ed060eb0f86f6fbcd22d2f18f51921a55573f37bad1ee354debf2701`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Extensions of perfect fields are formally smooth

Every field extension `L / K` of a perfect field `K` is formally smooth: an algebra map
`L →ₐ[K] B ⧸ I` lifts to `L →ₐ[K] B` along every square-zero ideal `I`. Mathlib proves this for
`L / K` essentially of finite type (`Algebra.FormallySmooth.of_perfectField`), through a separating
transcendence basis. A general extension need not have one: `𝔽_p(t ^ (1 / p ^ ∞))` is not
separably generated over `𝔽_p`. This file removes the finiteness hypothesis.

In characteristic zero a transcendence basis is still separating, and Mathlib's
`Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` applies. In characteristic `p` the
proof uses the Frobenius map instead. Since `I ^ 2 = 0` and `p = 0` in `B`, the `p`-th power of a
lift of `z ∈ B ⧸ I` does not depend on the lift. This gives a ring homomorphism `B ⧸ I → B`, and
composed with the given map, the only possible lift `ψ` on the subfield `L ^ p`. Zorn's lemma
gives a maximal lift extending it. It is defined on all of `L`: if `a ∉ M`, then `a ^ p ∈ M` and
`X ^ p - a ^ p` is the minimal polynomial of `a` over `M`. Any lift `b` of the image of `a` has
`b ^ p = ψ(a ^ p)`, so `a ↦ b` extends the lift to `M(a)`.

This is the input of Cohen's structure theorem for complete local rings in equal characteristic,
which constructs coefficient fields by lifting the identity of the residue field.

## Main results

* `TauCeti.formallySmooth_of_perfectField`: every field extension of a perfect field is formally
  smooth.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Première partie, Publ. Math. IHÉS 20
  (1964), Chapitre 0, Théorème 19.6.1.
* H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1986, Theorem 26.9 and
  Section 28.

The chain argument for partial lifts follows Mathlib's `IntermediateField.Lifts`, whose target is
a field, adapted here to a ring target.
-/

section
open Polynomial _root_.IntermediateField

namespace TauCeti

section PartialLift

variable (K L B : Type*) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]

/-- Kind: STRUCTURE. Locator: `TauCeti/RingTheory/Smooth/Field.lean:62` (proof source at `5a01f5fe3621`).
 A `K`-algebra map from an intermediate field of `L / K` into `B`. -/
private structure PartialLift where
  /-- Kind: FIELD. Locator: `TauCeti/RingTheory/Smooth/Field.lean:63`.
 The domain of the partial lift. -/
  carrier : IntermediateField K L
  /-- Kind: FIELD. Locator: `TauCeti/RingTheory/Smooth/Field.lean:65`.
 The partial lift. -/
  emb : carrier →ₐ[K] B

variable {K L B}

namespace PartialLift

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/Smooth/Field.lean:73` (proof source at `5a01f5fe3621`).
 A partial lift is below another one when the latter extends it. -/
private instance : Preorder (PartialLift K L B) where
  le φ₁ φ₂ := ∃ h : φ₁.carrier ≤ φ₂.carrier, ∀ x, φ₂.emb (inclusion h x) = φ₁.emb x
  le_refl φ := ⟨le_rfl, by simp⟩
  le_trans φ₁ φ₂ φ₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ ↦ ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃, h₂₃', h₁₂']

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:81` (proof source at `5a01f5fe3621`).
-/
private theorem directed_carrier {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c) :
    Directed (· ≤ ·) fun i : c ↦ i.val.carrier :=
  hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:86` (proof source at `5a01f5fe3621`).
 The members of a chain of partial lifts agree on the intersections of their domains. -/
private theorem emb_compat {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c) (i j : c)
    (h : i.val.carrier.toSubalgebra ≤ j.val.carrier.toSubalgebra) :
    i.val.emb = j.val.emb.comp (Subalgebra.inclusion h) :=
  AlgHom.ext fun x ↦ (hc.total i.2 j.2).elim (fun hij ↦ (hij.snd x).symm) fun hji ↦ by
    rw [AlgHom.comp_apply, ← inclusion, ← hji.snd (inclusion h x), inclusion_inclusion,
      inclusion_self, AlgHom.id_apply x]

/-- Kind: DEF. Locator: `TauCeti/RingTheory/Smooth/Field.lean:94` (proof source at `5a01f5fe3621`).
 The union of a nonempty chain of partial lifts. -/
private noncomputable def union (c : Set (PartialLift K L B)) (hc : IsChain (· ≤ ·) c)
    [Nonempty c] : PartialLift K L B :=
  ⟨⨆ i : c, i.val.carrier, Subalgebra.iSupLift (fun i : c ↦ i.val.carrier.toSubalgebra)
    (directed_carrier hc) (fun i ↦ i.val.emb) (emb_compat hc)
    (⨆ i : c, i.val.carrier).toSubalgebra (toSubalgebra_iSup_of_directed (directed_carrier hc)).le⟩

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:101` (proof source at `5a01f5fe3621`).
 On the domain of a member of the chain, the union of the chain is that member. -/
private theorem union_emb_of_mem {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c)
    [Nonempty c] (x : (union c hc).carrier) {φ : PartialLift K L B} (hφ : φ ∈ c)
    (hx : (x : L) ∈ φ.carrier) : (union c hc).emb x = φ.emb ⟨x, hx⟩ :=
  Subalgebra.iSupLift_of_mem (K := fun i : c ↦ i.val.carrier.toSubalgebra)
    (dir := directed_carrier hc) (hf := emb_compat hc) (i := ⟨φ, hφ⟩) x hx

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:107` (proof source at `5a01f5fe3621`).
-/
private theorem le_union {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c) [Nonempty c]
    {φ : PartialLift K L B} (hφ : φ ∈ c) : φ ≤ union c hc :=
  ⟨le_iSup (fun i : c ↦ i.val.carrier) ⟨φ, hφ⟩, fun x ↦ union_emb_of_mem hc _ hφ x.2⟩

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:112` (proof source at `5a01f5fe3621`).
 Every point of the union of a chain lies in the domain of one of its members. -/
private theorem exists_mem_of_mem_union {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c)
    [Nonempty c] (x : (union c hc).carrier) : ∃ φ ∈ c, (x : L) ∈ φ.carrier := by
  have hx : (x : L) ∈ ⋃ i : c, (i.val.carrier : Set L) := by
    rw [← coe_iSup_of_directed (directed_carrier hc)]
    exact x.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, i.2, hi⟩

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:122` (proof source at `5a01f5fe3621`).
 A partial lift defined at `a ^ p`, but not at `a`, extends to `a`, with any value `b` such
that `b ^ p` is the value at `a ^ p`. -/
private theorem exists_le_of_pow_mem (p : ℕ) [Fact p.Prime] [CharP L p] (φ : PartialLift K L B)
    {a : L} (ha : a ∉ φ.carrier) (hap : a ^ p ∈ φ.carrier) {b : B}
    (hb : φ.emb ⟨a ^ p, hap⟩ = b ^ p) :
    ∃ φ' : PartialLift K L B, φ ≤ φ' ∧ φ'.carrier = φ.carrier⟮a⟯.restrictScalars K ∧
      ∃ h : a ∈ φ'.carrier, φ'.emb ⟨a, h⟩ = b := by
  set M := φ.carrier
  -- `X ^ p - a ^ p` is the minimal polynomial of `a` over `M`
  have hirr : Irreducible (X ^ p - C (⟨a ^ p, hap⟩ : M)) :=
    X_pow_sub_C_irreducible_of_prime Fact.out fun c hc ↦ ha <| by
      have hc' : (c : L) ^ p = a ^ p := congrArg Subtype.val hc
      rw [← frobenius_def p, ← frobenius_def p] at hc'
      exact frobenius_inj L p hc' ▸ c.2
  have hroot : aeval a (X ^ p - C (⟨a ^ p, hap⟩ : M)) = 0 := by simp
  have hint : IsIntegral M a := ⟨_, monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, by
    rwa [← aeval_def]⟩
  have hmin : minpoly M a = X ^ p - C (⟨a ^ p, hap⟩ : M) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot
      (monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero)).symm
  let : Algebra M B := φ.emb.toRingHom.toAlgebra
  let carrier := M⟮a⟯.restrictScalars K
  let : Algebra M carrier := M⟮a⟯.toSubalgebra.algebra
  have hb' : aeval b (minpoly M (adjoin.powerBasis hint).gen) = 0 := by
    rw [adjoin.powerBasis_gen, minpoly_gen, hmin, map_sub, map_pow, aeval_X, aeval_C]
    simp [RingHom.algebraMap_toAlgebra, ← hb]
  let σ : carrier →ₐ[M] B := (adjoin.powerBasis hint).lift b hb'
  have : IsScalarTower K M carrier := IsScalarTower.of_algebraMap_eq fun c ↦
    Subtype.ext (IsScalarTower.algebraMap_apply K M L c)
  refine ⟨⟨carrier, (algHomEquivSigma (A := K) (B := M) (C := carrier) (D := B)).symm ⟨φ.emb, σ⟩⟩,
    ⟨fun z hz ↦ IntermediateField.algebraMap_mem M⟮a⟯ ⟨z, hz⟩, σ.commutes⟩, rfl,
    mem_adjoin_simple_self M a, ?_⟩
  exact (adjoin.powerBasis hint).lift_gen b hb'

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:156` (proof source at `5a01f5fe3621`).
 A partial lift extending a lift `φ` to the adjunction of `a` lifts `f` if `φ` does and the
value at `a` lifts `f a`. -/
private theorem mk_emb_of_le {I : Ideal B} {f : L →ₐ[K] B ⧸ I} {φ φ' : PartialLift K L B}
    (hφφ' : φ ≤ φ') {a : L} (hcarrier : φ'.carrier = φ.carrier⟮a⟯.restrictScalars K)
    (ha : a ∈ φ'.carrier)
    (hφa : Ideal.Quotient.mk I (φ'.emb ⟨a, ha⟩) = f a)
    (hφ : ∀ x, Ideal.Quotient.mk I (φ.emb x) = f x) (x : φ'.carrier) :
    Ideal.Quotient.mk I (φ'.emb x) = f x := by
  have hS : φ'.carrier = adjoin K (φ.carrier ∪ {a}) := by rw [hcarrier, restrictScalars_adjoin]
  have h := algHom_ext_of_eq_adjoin K hS (φ₁ := (Ideal.Quotient.mkₐ K I).comp φ'.emb)
    (φ₂ := f.comp φ'.carrier.val) fun y hy ↦ by
      rcases hy with hy | rfl
      · exact (congrArg (Ideal.Quotient.mk I) (hφφ'.2 ⟨y, hy⟩)).trans (hφ ⟨y, hy⟩)
      · simpa using hφa
  exact AlgHom.congr_fun h x

end PartialLift

end PartialLift

section CharP

variable (p : ℕ) [Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharP K p] [PerfectField K]
variable {B : Type*} [CommRing B] [Algebra K B] (hpB : (p : B) = 0) {I : Ideal B}
  (hI : I ^ 2 = ⊥)

/-- Kind: DEF. Locator: `TauCeti/RingTheory/Smooth/Field.lean:183` (proof source at `5a01f5fe3621`).
 The only possible lift of `f` on the field `L ^ p`, as a ring homomorphism: it sends `x ^ p`
to the `p`-th power of a lift of `f x`. -/
private noncomputable def powFieldRingHom (f : L →ₐ[K] B ⧸ I) : frobeniusPowers K L p 1 →+* B :=
  ((Ideal.Quotient.powLift p hpB hI).comp f.toRingHom).comp
    (iterateFrobeniusEquivPowers K L p 1).symm.toRingHom

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:187` (proof source at `5a01f5fe3621`).
-/
private theorem powFieldRingHom_apply (f : L →ₐ[K] B ⧸ I) (x : L) :
    powFieldRingHom p hpB hI f (iterateFrobeniusEquivPowers K L p 1 x) =
      Ideal.Quotient.powLift p hpB hI (f x) := by
  simp [powFieldRingHom]

/-- Kind: DEF. Locator: `TauCeti/RingTheory/Smooth/Field.lean:193` (proof source at `5a01f5fe3621`).
 The only possible lift of `f` on the field `L ^ p`. -/
private noncomputable def powFieldLift (f : L →ₐ[K] B ⧸ I) : frobeniusPowers K L p 1 →ₐ[K] B :=
  { powFieldRingHom p hpB hI f with
    commutes' c := by
      obtain ⟨d, rfl⟩ := (iterateFrobeniusEquiv K p 1).surjective c
      -- the underlying function of `powFieldLift` is `powFieldRingHom`
      change powFieldRingHom p hpB hI f _ = _
      -- write the constant as a `p`-th power of a constant of `L`, then compute
      rw [← iterateFrobeniusEquivPowers_algebraMap]
      simp [-iterateFrobeniusEquivPowers_algebraMap, powFieldRingHom_apply,
        ← Ideal.Quotient.mk_algebraMap, frobenius_def] }

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:204` (proof source at `5a01f5fe3621`).
-/
private theorem powFieldLift_apply (f : L →ₐ[K] B ⧸ I) (x : L) :
    powFieldLift p hpB hI f (iterateFrobeniusEquivPowers K L p 1 x) =
      Ideal.Quotient.powLift p hpB hI (f x) :=
  powFieldRingHom_apply p hpB hI f x

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:210` (proof source at `5a01f5fe3621`).
 The lift of `f` on `L ^ p` lifts `f`. -/
private theorem mk_powFieldLift (f : L →ₐ[K] B ⧸ I) (y : frobeniusPowers K L p 1) :
    Ideal.Quotient.mk I (powFieldLift p hpB hI f y) = f y := by
  obtain ⟨x, rfl⟩ := (iterateFrobeniusEquivPowers K L p 1).surjective y
  simp [powFieldLift_apply]

open PartialLift in
include hpB hI in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Smooth/Field.lean:219` (proof source at `5a01f5fe3621`).
 **In characteristic `p`, a map of a field `L` over a perfect field `K` into `B ⧸ I` lifts to
`B` along a square-zero ideal `I`.** -/
private theorem exists_comp_eq_of_charP [CharP L p] (f : L →ₐ[K] B ⧸ I) :
    ∃ g : L →ₐ[K] B, (Ideal.Quotient.mkₐ K I).comp g = f := by
  -- the partial lifts of `f` which extend its lift on `L ^ p`
  let base : PartialLift K L B := ⟨frobeniusPowers K L p 1, powFieldLift p hpB hI f⟩
  let S : Set (PartialLift K L B) :=
    {φ | base ≤ φ ∧ ∀ x, Ideal.Quotient.mk I (φ.emb x) = f x}
  obtain ⟨φ, -, hφ⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy ↦ by
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    refine ⟨union c hc, ⟨(hcS hy).1.trans (le_union hc hy), fun x ↦ ?_⟩,
      fun z hz ↦ le_union hc hz⟩
    obtain ⟨ψ, hψ, hx⟩ := exists_mem_of_mem_union hc x
    rw [union_emb_of_mem hc x hψ hx]
    exact (hcS hψ).2 _) base ⟨le_rfl, mk_powFieldLift p hpB hI f⟩
  -- a maximal partial lift is defined everywhere
  have htop : φ.carrier = ⊤ := by
    refine eq_top_iff.mpr fun a _ ↦ by_contra fun ha ↦ ?_
    let ap := iterateFrobeniusEquivPowers K L p 1 a
    have hap : a ^ p ∈ φ.carrier := by simpa [ap] using hφ.prop.1.1 ap.2
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f a)
    have hbp : φ.emb ⟨a ^ p, hap⟩ = b ^ p := by
      have h : (⟨a ^ p, hap⟩ : φ.carrier) = inclusion hφ.prop.1.1 ap := Subtype.ext (by simp [ap])
      rw [h, hφ.prop.1.2, powFieldLift_apply, ← hb, Ideal.Quotient.powLift_mk]
    obtain ⟨φ', hφφ', hcarrier, ha', hφ'a⟩ := PartialLift.exists_le_of_pow_mem p φ ha hap hbp
    have hφ' : φ' ∈ S := ⟨hφ.prop.1.trans hφφ',
      mk_emb_of_le hφφ' hcarrier ha' (by rw [hφ'a, hb]) hφ.prop.2⟩
    exact ha ((hφ.2 hφ' hφφ').1 ha')
  refine ⟨φ.emb.comp ((equivOfEq htop).trans topEquiv).symm.toAlgHom, AlgHom.ext fun x ↦ ?_⟩
  simpa using hφ.prop.2 (((equivOfEq htop).trans topEquiv).symm x)

end CharP

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/Smooth/Field.lean:253` (proof source at `5a01f5fe3621`).
 **Every field extension of a perfect field is formally smooth**: a `K`-algebra map from `L` to
`B ⧸ I`, for a square-zero ideal `I`, lifts to `B`. No finiteness hypothesis on `L / K` is needed,
unlike for Mathlib's `Algebra.FormallySmooth.of_perfectField`. -/
instance (priority := low) formallySmooth_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [PerfectField K] : Algebra.FormallySmooth K L := by
  obtain _ | ⟨p, hp, hpK⟩ := CharP.exists' K
  · -- in characteristic zero, every transcendence basis is separating
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
    have := hs.isAlgebraic_field
    have := charZero_of_injective_algebraMap (algebraMap K L).injective
    have := Algebra.IsAlgebraic.isSeparable_of_perfectField
      (K := IntermediateField.adjoin K (Set.range ((↑) : s → L))) (L := L)
    exact .of_algebraicIndependent_of_isSeparable hs.1
  · have : CharP L p := .of_ringHom_of_ne_zero (algebraMap K L) p hp.out.ne_zero
    refine .of_comp_surjective fun B _ _ I hI f ↦ exists_comp_eq_of_charP p ?_ hI f
    rw [← map_natCast (algebraMap K B), CharP.cast_eq_zero, map_zero]

end TauCeti
end

end

/-! ## Source 25: `TauCeti.RingTheory.LocalRing.CoefficientField`
Original source SHA256: `37b7bf4b3f026aada332ef9d57e8c257258773d259bf8ce0fe5d6352c3d65a09`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Coefficient fields of complete local rings

Let `R` be a local ring which is complete for the adic topology of its maximal ideal `𝔪`, and let
`k → R` be a ring homomorphism such that the residue field `R ⧸ 𝔪` is formally étale over `k`; the
main case is a field `k` over which `R ⧸ 𝔪` is separable (`Algebra.FormallyEtale.of_isSeparable`).
Then reduction `R → R ⧸ 𝔪` has a unique `k`-algebra section: the residue field lifts to a
*coefficient field* of `R` containing the image of `k`.

Existence is Hensel's lemma in the guise of formal smoothness: the identity of `R ⧸ 𝔪` lifts along
the `𝔪`-adically complete ring `R` (`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`).
Uniqueness only needs formal unramifiedness and the Krull intersection `⋂ 𝔪 ^ n = 0`.

Without separability the section need not exist over `k`: in `𝔽_p(s)[[T]]`, viewed as an
`𝔽_p(u)`-algebra through `u ↦ s ^ p + T`, a section would send `s` to a `p`-th root of `s ^ p + T`,
and there is none, since every `p`-th power in `𝔽_p(s)[[T]]` is a power series in `T ^ p`.

Over a perfect field `k` every residue field is formally smooth
(`TauCeti.formallySmooth_of_perfectField`), so a `k`-algebra section always exists, although it
need no longer be unique. Applied to the prime field, this is Cohen's theorem that a complete local
ring containing a field has a coefficient field (`TauCeti.exists_residueFieldSection`). Such a
coefficient field need not contain the image of the given field.

In the theory of algebraic function fields this is the device that turns the completion of the
function field at a place with residue field `F_P` into a field of Laurent series over `F_P`, and
so gives `F_P`-valued expansion coefficients and residues at places that are not rational.

## Main definitions

* `TauCeti.residueFieldSection`: the coefficient field, as a `k`-algebra map
  `ResidueField R →ₐ[k] R`.

## Main results

* `TauCeti.residue_residueFieldSection`: it is a section of reduction.
* `TauCeti.eq_residueFieldSection`: it is the only `k`-algebra section of reduction.
* `TauCeti.exists_residueFieldSection`: **Cohen's theorem**, a complete local ring containing a
  field has a coefficient field.

## References

* I. S. Cohen, *On the structure and ideal theory of complete local rings*, Trans. Amer. Math.
  Soc. 59 (1946), 54–106.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

section
namespace TauCeti

open _root_.IsLocalRing

section FormallySmooth

variable (k R : Type*) [CommRing k] [CommRing R] [IsLocalRing R] [Algebra k R]
  [IsAdicComplete (maximalIdeal R) R]

/-- Kind: DEF. Locator: `TauCeti/RingTheory/LocalRing/CoefficientField.lean:75` (proof source at `5a01f5fe3621`).
 The **coefficient field** of a complete local `k`-algebra `R` whose residue field is formally
smooth over `k` (for instance a field separable over a field `k`): a `k`-algebra section
`ResidueField R →ₐ[k] R` of reduction (`TauCeti.residue_residueFieldSection`). When the residue
field is moreover formally unramified over `k` it is the only one
(`TauCeti.eq_residueFieldSection`). -/
noncomputable def residueFieldSection [Algebra.FormallySmooth k (ResidueField R)] :
    ResidueField R →ₐ[k] R :=
  (Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (AlgHom.id k (ResidueField R))).choose

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LocalRing/CoefficientField.lean:82` (proof source at `5a01f5fe3621`).
 The coefficient field is a section of reduction. -/
@[simp]
theorem residue_residueFieldSection [Algebra.FormallySmooth k (ResidueField R)]
    (a : ResidueField R) : residue R (residueFieldSection k R a) = a :=
  -- `residue R` is the quotient map by `𝔪`, which `Ideal.Quotient.mkₐ k` bundles over `k`.
  AlgHom.congr_fun (Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (AlgHom.id k (ResidueField R))).choose_spec a

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LocalRing/CoefficientField.lean:90` (proof source at `5a01f5fe3621`).
 The coefficient field is the only `k`-algebra section of reduction when the residue field is
formally étale over `k`. Uniqueness uses only the Krull intersection `⋂ 𝔪 ^ n = 0`. -/
theorem eq_residueFieldSection [Algebra.FormallySmooth k (ResidueField R)]
    [Algebra.FormallyUnramified k (ResidueField R)]
    {s : ResidueField R →ₐ[k] R} (hs : ∀ a, residue R (s a) = a) :
    s = residueFieldSection k R := by
  have hI : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ := by
    simpa only [smul_eq_mul, Ideal.mul_top] using
      (IsAdicComplete.toIsHausdorff (I := maximalIdeal R) (M := R)).iInf_pow_smul
  -- As above, `residue R` is the quotient map `Ideal.Quotient.mk (maximalIdeal R)`.
  exact Algebra.FormallyUnramified.ext_of_iInf _ hI fun a ↦
    (hs a).trans (residue_residueFieldSection k R a).symm

end FormallySmooth

variable (k R : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  [IsAdicComplete (maximalIdeal R) R]

include k in
/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LocalRing/CoefficientField.lean:111` (proof source at `5a01f5fe3621`).
 **Cohen's theorem: a complete local ring containing a field has a coefficient field.** If the
complete local ring `R` is an algebra over some field `k`, then reduction `R → ResidueField R` has
a ring homomorphism section. When `k` is perfect, `TauCeti.residueFieldSection k R` is even a
`k`-algebra section. In general a `k`-linear section need not exist. -/
theorem exists_residueFieldSection :
    ∃ s : ResidueField R →+* R, ∀ a, residue R (s a) = a := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · -- in characteristic zero `k` is perfect
    exact ⟨residueFieldSection k R, residue_residueFieldSection k R⟩
  · -- in characteristic `p`, use the perfect prime field `𝔽_p`
    let : Algebra (ZMod p) R := ((algebraMap k R).comp (ZMod.castHom dvd_rfl k)).toAlgebra
    exact ⟨residueFieldSection (ZMod p) R, residue_residueFieldSection (ZMod p) R⟩

end TauCeti
end

end

/-! ## Source 26: `TauCeti.FieldTheory.FunctionField.Place.Completion.CoefficientField`
Original source SHA256: `8c5831e5abe198dd2f7bf2e370f015b896682b2b019fdf5feb9806cad2b79f26`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The coefficient field of the completion at a place

Let `P` be a place of `F / k` whose residue field `F_P` is separable over `k`; over a perfect
constant field this holds at every place with finite residue field, in particular at every place
of an algebraic function field. The completed valuation ring `𝒪̂_P` is complete for the adic
topology of its maximal ideal (`TauCeti.Place.isAdicComplete_completionIntegers`), so it contains
a unique copy of `F_P` over `k` mapping onto the residue field: a `k`-algebra embedding
`F_P → 𝒪̂_P` which reduces to the identity of `F_P`.

At a rational place this embedding is just the constant field `k`, and expansions in a
uniformizer `t` have coefficients in `k`. At a place of higher degree the coefficients of the
`P`-adic expansion `∑ aᵢ tⁱ` of a completed function are taken in the image of this embedding,
which is what makes them, and the residue `a₋₁`, elements of `F_P`.

Without separability `𝒪̂_P` still has a coefficient field, by Cohen's theorem for complete local
rings containing a field, but it is only linear over the prime field: there may be no `k`-algebra
embedding of `F_P` into `𝒪̂_P` at all.

## Main definitions

* `TauCeti.Place.completionResidueFieldSection`: the coefficient field `F_P →ₐ[k] 𝒪̂_P`.

## Main results

* `TauCeti.Place.residue_completionResidueFieldSection`: it reduces to the identification of
  `F_P` with the residue field of the completion.
* `TauCeti.Place.eq_completionResidueFieldSection`: it is the only `k`-algebra embedding of `F_P`
  with this property.
* `TauCeti.Place.sub_completionResidueFieldSection_mem_filtration_one` and
  `TauCeti.Place.completionEmbedding_sub_completionResidueFieldSection_mem_filtration_one`: every
  integral completed function, in particular every function regular at `P`, agrees with the
  coefficient-field lift of its value at `P` up to a function vanishing at `P`.
* `TauCeti.Place.exists_completionResidueFieldSection`: at every place, separable residue field or
  not, `𝒪̂_P` has a coefficient field, in general not `k`-linear.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

section
namespace TauCeti.Place

open _root_.IsLocalRing

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:68` (proof source at `5a01f5fe3621`).
 **The completion at any place has a coefficient field**: a ring embedding of the residue field
`F_P` into the completed valuation ring `𝒪̂_P` which reduces to the identification of `F_P` with
the residue field of the completion. No separability of `F_P` over `k` is assumed (Cohen's theorem,
`TauCeti.exists_residueFieldSection`). When `F_P / k` is separable,
`TauCeti.Place.completionResidueFieldSection` is a `k`-linear one. Otherwise there may be no
`k`-linear one (`TauCeti.Place.isEmpty_algHom_residueField_completion`). -/
theorem exists_completionResidueFieldSection :
    ∃ s : P.ResidueField →+* P.completionPlace.integers,
      ∀ a, residue P.completionPlace.integers (s a) = P.residueFieldEquivCompletion a := by
  obtain ⟨s, hs⟩ := exists_residueFieldSection k P.completionPlace.integers
  exact ⟨s.comp P.residueFieldEquivCompletion.toRingHom, fun a ↦ hs _⟩

variable [Algebra.IsSeparable k P.ResidueField]

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:78` (proof source at `5a01f5fe3621`).
 Completion does not change the residue field, so it preserves its separability over the
constants. -/
instance isSeparable_completionPlace_residueField :
    Algebra.IsSeparable k P.completionPlace.ResidueField :=
  AlgEquiv.Algebra.isSeparable P.residueFieldEquivCompletion

/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:84` (proof source at `5a01f5fe3621`).
 The residue field of the completion is formally étale over the constants, being separable;
this is the hypothesis under which `TauCeti.residueFieldSection` exists and is unique. -/
instance formallyEtale_completionPlace_residueField :
    Algebra.FormallyEtale k P.completionPlace.ResidueField :=
  Algebra.FormallyEtale.of_isSeparable k _

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:92` (proof source at `5a01f5fe3621`).
 The **coefficient field** of the completion at a place with separable residue field: the
unique `k`-algebra embedding of the residue field `F_P` into the completed valuation ring whose
reduction is the identification `TauCeti.Place.residueFieldEquivCompletion` of `F_P` with the
residue field of the completion. -/
noncomputable def completionResidueFieldSection :
    P.ResidueField →ₐ[k] P.completionPlace.integers :=
  (residueFieldSection k P.completionPlace.integers).comp
    P.residueFieldEquivCompletion.toAlgHom

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:99` (proof source at `5a01f5fe3621`).
 The coefficient field of the completion at `P` is the coefficient field of the complete local
ring `𝒪̂_P`, read through the identification of the residue fields. -/
theorem completionResidueFieldSection_apply (a : P.ResidueField) :
    P.completionResidueFieldSection a =
      residueFieldSection k P.completionPlace.integers (P.residueFieldEquivCompletion a) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:105` (proof source at `5a01f5fe3621`).
 The coefficient field reduces to the identification of the residue fields. -/
@[simp]
theorem residue_completionResidueFieldSection (a : P.ResidueField) :
    residue P.completionPlace.integers (P.completionResidueFieldSection a) =
      P.residueFieldEquivCompletion a :=
  residue_residueFieldSection k P.completionPlace.integers _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:112` (proof source at `5a01f5fe3621`).
 The coefficient field is the only `k`-algebra embedding of the residue field into the
completed valuation ring which reduces to the identification of the residue fields. -/
theorem eq_completionResidueFieldSection {s : P.ResidueField →ₐ[k] P.completionPlace.integers}
    (hs : ∀ a, residue P.completionPlace.integers (s a) = P.residueFieldEquivCompletion a) :
    s = P.completionResidueFieldSection := by
  have h := eq_residueFieldSection k P.completionPlace.integers
    (s := s.comp P.residueFieldEquivCompletion.symm.toAlgHom) fun a ↦ by simp [hs]
  ext a
  simpa [completionResidueFieldSection_apply] using
    congrArg (fun g ↦ (g (P.residueFieldEquivCompletion a) : P.Completion)) h

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:123` (proof source at `5a01f5fe3621`).
 An integral completed function agrees with the coefficient-field lift of its value at `P` up
to a completed function vanishing at `P`. -/
theorem sub_completionResidueFieldSection_mem_filtration_one (x : P.completionPlace.integers) :
    (x : P.Completion) - P.completionResidueFieldSection
      (P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers x)) ∈
      P.completionPlace.filtration 1 :=
  P.completionPlace.residue_eq_iff_sub_mem_filtration_one.mp (by simp)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Completion/CoefficientField.lean:131` (proof source at `5a01f5fe3621`).
 A function regular at `P` agrees, in the completion, with the coefficient-field lift of its
value at `P` up to a completed function vanishing at `P`. -/
theorem completionEmbedding_sub_completionResidueFieldSection_mem_filtration_one
    (x : P.integers) :
    P.completionEmbedding x - P.completionResidueFieldSection (residue P.integers x) ∈
      P.completionPlace.filtration 1 := by
  have h := P.sub_completionResidueFieldSection_mem_filtration_one
    (P.completionIntegersEmbedding x)
  rwa [← residueFieldEquivCompletion_apply_residue, AlgEquiv.symm_apply_apply,
    completionIntegersEmbedding_apply] at h

end TauCeti.Place
end

end

/-! ## Source 27: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Basic`
Original source SHA256: `44642118f07a6bcd9811873920277c583b78e48db055a3b1f9ad1688f4467a47`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Truncated uniformizer expansions at rational places

Let `P` be a rational place of `F / k` and let `t` have order one at `P`. Every function
integral at `P` has a unique expansion modulo the `n`-th order filtration as a polynomial in
`t` with `n` coefficients in `k`. This file constructs these finite coefficient vectors and
characterizes them by the order of the remainder. The coefficients depend only on the
function modulo the same filtration, and successive truncations agree. Constants have only
a constant coefficient, the chosen uniformizer has only a degree-one coefficient, and
multiplication of integral functions gives coefficient convolution.

Peeling off leading terms one at a time also shows that a `k`-linear map on `F` is determined
by its values on a step of the order filtration and on the powers of the uniformizer below it.

These are finite truncations: no completeness assumption or infinite series is used. They
provide the finite approximation and uniqueness statements for the power-series construction
in a completed valuation ring. In particular, the statements also apply to the place on a
completion once that place and its constant-field algebra have been supplied.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

section
open scoped BigOperators

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F}

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:46` (proof source at `5a01f5fe3621`).
-/
private theorem div_uniformizer_mem_filtration_iff (ht : P.ord t = 1) (a : ℤ) (x : F) :
    x / t ∈ P.filtration a ↔ x ∈ P.filtration (a + 1) := by
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [P.mem_filtration_iff_le_ord (div_ne_zero hx ht0),
      P.mem_filtration_iff_le_ord hx, P.ord_div hx ht0, ht]
    omega

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:57` (proof source at `5a01f5fe3621`).
-/
private theorem constant_sub_mem_filtration_one_iff (c d : k) :
    algebraMap k F c - algebraMap k F d ∈ P.filtration 1 ↔ c = d := by
  rw [← map_sub]
  rcases eq_or_ne c d with rfl | hcd
  · simp
  · have h0 : algebraMap k F (c - d) ≠ 0 :=
      (map_ne_zero (algebraMap k F)).mpr (sub_ne_zero.mpr hcd)
    rw [P.mem_filtration_iff_le_ord h0, P.ord_algebraMap]
    simp [hcd]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:67` (proof source at `5a01f5fe3621`).
-/
private theorem exists_sub_sum_mem_filtration (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : F) (hx : x ∈ P.integers) :
    ∃ c : Fin n → k, x - ∑ i, algebraMap k F (c i) * t ^ (i : ℕ) ∈ P.filtration n := by
  induction n generalizing x with
  | zero =>
    exact ⟨Fin.elim0, by simpa using P.mem_filtration_zero_iff.mpr hx⟩
  | succ n ih =>
    obtain ⟨c₀, hc₀⟩ :=
      (P.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hP) x hx
    have hy : (x - algebraMap k F c₀) / t ∈ P.integers := by
      apply P.mem_filtration_zero_iff.mp
      exact (P.div_uniformizer_mem_filtration_iff ht 0 _).mpr
        (P.mem_filtration_one_iff.mpr hc₀)
    obtain ⟨c, hc⟩ := ih _ hy
    refine ⟨Fin.cons c₀ c, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
      pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc, ← Finset.sum_mul]
    have ht0 : t ≠ 0 := by
      intro h
      simp [h] at ht
    have hm := P.mul_mem_filtration hc (P.mem_filtration_ord t)
    rw [ht] at hm
    simpa only [Nat.cast_add, Nat.cast_one, sub_mul, div_mul_cancel₀ _ ht0,
      sub_add_eq_sub_sub] using hm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:92` (proof source at `5a01f5fe3621`).
-/
private theorem sum_mem_filtration_iff (ht : P.ord t = 1) (n : ℕ) (c : Fin n → k) :
    (∑ i, algebraMap k F (c i) * t ^ (i : ℕ)) ∈ P.filtration n ↔ c = 0 := by
  induction n with
  | zero =>
    constructor
    · intro _
      ext i
      exact Fin.elim0 i
    · intro _
      simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      pow_succ, ← mul_assoc, ← Finset.sum_mul]
    have ht0 : t ∈ P.filtration 1 := by
      simpa [ht] using P.mem_filtration_ord t
    have hsum0 : (∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) ∈
        P.filtration 0 := by
      apply Submodule.sum_mem
      intro i _
      exact P.mem_filtration_zero_iff.mpr
        (mul_mem (P.algebraMap_mem_integers _) (pow_mem
          (P.mem_integers_iff_ord_nonneg.mpr (by omega : 0 ≤ P.ord t)) _))
    constructor
    · intro h
      have htail1 : (∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) * t ∈
          P.filtration 1 := by simpa using P.mul_mem_filtration hsum0 ht0
      have hconstant := (P.filtration 1).sub_mem
        (P.filtration_antitone (by omega) h) htail1
      have hc₀ : c 0 = 0 := by
        apply (P.constant_sub_mem_filtration_one_iff (c 0) 0).mp
        simpa using hconstant
      have htail : (∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) ∈
          P.filtration n := by
        have htne : t ≠ 0 := by
          intro h
          simp [h] at ht
        have hh := (P.div_uniformizer_mem_filtration_iff ht n
          ((∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) * t)).mpr
          (by simpa [hc₀] using h)
        simpa [mul_div_cancel_right₀ _ htne] using hh
      have hcz := (ih fun i ↦ c i.succ).mp htail
      ext i
      exact Fin.cases hc₀ (fun j ↦ congrFun hcz j) i
    · intro hc
      simp [hc]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:141` (proof source at `5a01f5fe3621`).
 At a rational place, an integral function has a unique polynomial expansion of length
`n` in a chosen uniformizer, with remainder vanishing to order at least `n`. The filtration
condition includes the zero remainder, unlike an unguarded inequality for `ord`. -/
theorem existsUnique_sub_sum_mem_filtration (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : F) (hx : x ∈ P.integers) :
    ∃! c : Fin n → k, x - ∑ i, algebraMap k F (c i) * t ^ (i : ℕ) ∈ P.filtration n := by
  obtain ⟨c, hc⟩ := P.exists_sub_sum_mem_filtration hP ht n x hx
  refine ⟨c, hc, fun d hd ↦ ?_⟩
  have h := (P.filtration n).sub_mem hc hd
  have hz : (∑ i, algebraMap k F ((d - c) i) * t ^ (i : ℕ)) ∈ P.filtration n := by
    convert h using 1
    simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  exact sub_eq_zero.mp ((P.sum_mem_filtration_iff ht n (d - c)).mp hz)

/-! ### Canonical finite coefficient vectors -/

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:158` (proof source at `5a01f5fe3621`).
 The coefficients of the unique length-`n` uniformizer expansion of an integral function
at a rational place. Its remainder is characterized by
`TauCeti.Place.truncatedExpansion_eq_iff`; successive lengths agree on their common indices. -/
noncomputable def truncatedExpansion (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) : Fin n → k :=
  (P.existsUnique_sub_sum_mem_filtration hP ht n x x.2).exists.choose

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:163` (proof source at `5a01f5fe3621`).
 Subtracting the truncated expansion leaves a function vanishing to the stated order. -/
theorem sub_sum_truncatedExpansion_mem_filtration (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) :
    (x : F) - ∑ i, algebraMap k F (P.truncatedExpansion hP ht n x i) * t ^ (i : ℕ) ∈
      P.filtration n :=
  (P.existsUnique_sub_sum_mem_filtration hP ht n x x.2).exists.choose_spec

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:172` (proof source at `5a01f5fe3621`).
 A coefficient vector is the truncated expansion precisely when its remainder vanishes
to order at least the length of the vector. This characterizes the coefficients without
unfolding their construction. -/
theorem truncatedExpansion_eq_iff (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) (c : Fin n → k) :
    P.truncatedExpansion hP ht n x = c ↔
      (x : F) - ∑ i, algebraMap k F (c i) * t ^ (i : ℕ) ∈ P.filtration n := by
  constructor
  · intro h
    rw [← h]
    exact P.sub_sum_truncatedExpansion_mem_filtration hP ht n x
  · intro hc
    exact (P.existsUnique_sub_sum_mem_filtration hP ht n x x.2).unique
      (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x) hc

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:186` (proof source at `5a01f5fe3621`).
 The zero function has zero coefficients at every truncation length. -/
@[simp]
theorem truncatedExpansion_zero (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
    P.truncatedExpansion hP ht n 0 = 0 := by
  apply (P.truncatedExpansion_eq_iff hP ht n 0 0).mpr
  simp

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:193` (proof source at `5a01f5fe3621`).
 Uniformizer coefficients respect addition of integral functions. -/
@[simp]
theorem truncatedExpansion_add (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x y : P.integers) :
    P.truncatedExpansion hP ht n (x + y) =
      P.truncatedExpansion hP ht n x + P.truncatedExpansion hP ht n y := by
  apply (P.truncatedExpansion_eq_iff hP ht n (x + y) _).mpr
  have h := (P.filtration n).add_mem
    (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x)
    (P.sub_sum_truncatedExpansion_mem_filtration hP ht n y)
  convert h using 1
  rw [← ValuationSubring.algebraMap_apply P.integers (x + y)]
  simp only [map_add, ValuationSubring.algebraMap_apply, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:209` (proof source at `5a01f5fe3621`).
 Uniformizer coefficients respect multiplication by constants. -/
@[simp]
theorem truncatedExpansion_smul (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (c : k) (x : P.integers) :
    P.truncatedExpansion hP ht n (c • x) = c • P.truncatedExpansion hP ht n x := by
  apply (P.truncatedExpansion_eq_iff hP ht n (c • x) _).mpr
  have h := (P.filtration n).smul_mem c
    (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x)
  convert h using 1
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
    mul_sub, mul_assoc, Finset.mul_sum]
  rw [← ValuationSubring.algebraMap_apply P.integers ((algebraMap k P.integers c) * x)]
  simp only [map_mul, ValuationSubring.algebraMap_apply, P.coe_algebraMap_constants]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:223` (proof source at `5a01f5fe3621`).
 Uniformizer coefficients respect negation of integral functions. -/
@[simp]
theorem truncatedExpansion_neg (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) :
    P.truncatedExpansion hP ht n (-x) = -P.truncatedExpansion hP ht n x := by
  simpa only [neg_one_smul] using P.truncatedExpansion_smul hP ht n (-1 : k) x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:230` (proof source at `5a01f5fe3621`).
 Uniformizer coefficients respect subtraction of integral functions. -/
@[simp]
theorem truncatedExpansion_sub (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x y : P.integers) :
    P.truncatedExpansion hP ht n (x - y) =
      P.truncatedExpansion hP ht n x - P.truncatedExpansion hP ht n y := by
  simp only [sub_eq_add_neg, P.truncatedExpansion_add, P.truncatedExpansion_neg]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:238` (proof source at `5a01f5fe3621`).
 The unit has constant coefficient one and all positive-degree coefficients zero. -/
@[simp]
theorem truncatedExpansion_one (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
    P.truncatedExpansion hP ht n 1 = fun i : Fin n ↦ if (i : ℕ) = 0 then 1 else 0 := by
  apply (P.truncatedExpansion_eq_iff hP ht n 1 _).mpr
  cases n <;> simp [P.mem_filtration_zero_iff]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:245` (proof source at `5a01f5fe3621`).
 Constants have their given constant coefficient and zero positive-degree coefficients. -/
@[simp]
theorem truncatedExpansion_algebraMap (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (c : k) :
    P.truncatedExpansion hP ht n (algebraMap k P.integers c) =
      fun i : Fin n ↦ if (i : ℕ) = 0 then c else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, P.truncatedExpansion_smul hP ht,
    P.truncatedExpansion_one hP ht]
  ext i
  by_cases hi : (i : ℕ) = 0 <;> simp [hi]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:257` (proof source at `5a01f5fe3621`).
 The chosen uniformizer has coefficient one in degree one and zero in every other degree,
including at truncation lengths zero and one. -/
@[simp]
theorem truncatedExpansion_uniformizer (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
    P.truncatedExpansion hP ht n
      ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      fun i : Fin n ↦ if (i : ℕ) = 1 then 1 else 0 := by
  apply (P.truncatedExpansion_eq_iff hP ht n _ _).mpr
  cases n with
  | zero =>
    simpa using P.mem_filtration_zero_iff.mpr
      (P.mem_integers_iff_ord_nonneg.mpr (by omega : 0 ≤ P.ord t))
  | succ n =>
    cases n with
    | zero => simpa [Fin.sum_univ_succ, ht] using P.mem_filtration_ord t
    | succ n => simp [Fin.sum_univ_succ]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:275` (proof source at `5a01f5fe3621`).
 The coefficient of a product is the convolution of the coefficients of its factors.
The sum ranges over bounded pairs of indices whose degrees add to the requested degree;
terms of degree at least `n` vanish modulo the `n`-th order filtration. -/
@[simp]
theorem truncatedExpansion_mul (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x y : P.integers) (i : Fin n) :
    P.truncatedExpansion hP ht n (x * y) i =
      ∑ j : Fin n × Fin n with (j.1 : ℕ) + (j.2 : ℕ) = (i : ℕ),
        P.truncatedExpansion hP ht n x j.1 * P.truncatedExpansion hP ht n y j.2 := by
  classical
  let a := P.truncatedExpansion hP ht n x
  let b := P.truncatedExpansion hP ht n y
  -- Encode the finite vectors as polynomials without unfolding coefficient extraction.
  let polynomial := Polynomial.ofFn (R := k) n
  let u := (polynomial a).eval₂ (algebraMap k F) t
  let v := (polynomial b).eval₂ (algebraMap k F) t
  have heval (c : Fin n → k) :
      (polynomial c).eval₂ (algebraMap k F) t =
        ∑ j, algebraMap k F (c j) * t ^ (j : ℕ) := by
    simp only [polynomial, Polynomial.ofFn_eq_sum_monomial,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  have hcoeff (c : Fin n → k) (j : Fin n) : (polynomial c).coeff j = c j := by
    exact Polynomial.ofFn_coeff_eq_val_of_lt c j.isLt
  have hu : u ∈ P.filtration 0 := by
    dsimp only [u]
    rw [heval]
    apply Submodule.sum_mem
    intro j _
    exact P.mem_filtration_zero_iff.mpr
      (mul_mem (P.algebraMap_mem_integers _) (pow_mem
        (P.mem_integers_iff_ord_nonneg.mpr (by omega : 0 ≤ P.ord t)) _))
  -- Replacing either integral factor by its finite expansion preserves the product modulo
  -- the filtration, since multiplying a remainder by an integral function preserves its order.
  have hrem : (x : F) * (y : F) - u * v ∈ P.filtration n := by
    have hx := P.mul_mem_filtration
      (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x)
      (P.mem_filtration_zero_iff.mpr y.2)
    have hy := P.mul_mem_filtration hu
      (P.sub_sum_truncatedExpansion_mem_filtration hP ht n y)
    rw [← heval a, add_zero] at hx
    rw [← heval b, zero_add] at hy
    convert (P.filtration n).add_mem hx hy using 1
    ring
  let q := polynomial a * polynomial b
  -- Mathlib supplies both multiplication of evaluations and coefficient convolution.
  -- Reindex its antidiagonal only to retain the bounded-pair public formula.
  have hconvolution (j : Fin n) : q.coeff j =
      ∑ l : Fin n × Fin n with (l.1 : ℕ) + (l.2 : ℕ) = (j : ℕ), a l.1 * b l.2 := by
    rw [Polynomial.coeff_mul]
    symm
    apply sum_fin_product_eq_sum_antidiagonal j.isLt
    intro l _
    simp only [hcoeff]
  -- Evaluate the product polynomial and discard only terms of degree at least `n`.
  -- Include missing low degrees as zero terms so the truncation ranges over all `Fin n`.
  let s := q.support ∪ Finset.range n
  let f := fun d : ℕ ↦ algebraMap k F (q.coeff d) * t ^ d
  have hprod : u * v = ∑ d ∈ s, f d := by
    rw [← Polynomial.eval₂_mul, Polynomial.eval₂_eq_sum]
    exact Polynomial.sum_eq_of_subset _ (by simp) Finset.subset_union_left
  have hlow : (∑ d ∈ s with d < n, f d) = ∑ j : Fin n, f j := by
    rw [Fin.sum_univ_eq_sum_range]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, s]
    tauto
  have hhigh : (∑ d ∈ s with ¬d < n, f d) ∈ P.filtration n := by
    apply Submodule.sum_mem
    intro d hd
    have hdegree : (n : ℤ) ≤ (d : ℤ) := by
      exact_mod_cast Nat.le_of_not_lt (Finset.mem_filter.mp hd).2
    have hpow := P.mem_filtration_ord (t ^ d)
    simp only [P.ord_pow, ht, mul_one] at hpow
    apply P.filtration_antitone hdegree
    have hm := P.mul_mem_filtration
      (P.mem_filtration_zero_iff.mpr (P.algebraMap_mem_integers (q.coeff d))) hpow
    simpa only [zero_add] using hm
  have heq := (P.truncatedExpansion_eq_iff hP ht n (x * y)
    (fun j ↦ q.coeff j)).mpr (by
      have hsplit := Finset.sum_filter_add_sum_filter_not s (fun d ↦ d < n) f
      rw [hlow] at hsplit
      convert (P.filtration n).add_mem hrem hhigh using 1
      rw [hprod, ← hsplit]
      -- Coercing the product in the valuation ring gives multiplication in `F`.
      change (x : F) * (y : F) - _ = _
      ring)
  exact (congrFun heq i).trans (hconvolution i)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:363` (proof source at `5a01f5fe3621`).
 Increasing the truncation length preserves every coefficient already extracted. This
compatibility allows the finite vectors to determine a single power-series coefficient
sequence. -/
@[simp]
theorem truncatedExpansion_castSucc (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) (i : Fin n) :
    P.truncatedExpansion hP ht (n + 1) x i.castSucc = P.truncatedExpansion hP ht n x i := by
  have hhigh := P.sub_sum_truncatedExpansion_mem_filtration hP ht (n + 1) x
  have hlast : algebraMap k F (P.truncatedExpansion hP ht (n + 1) x (Fin.last n)) * t ^ n ∈
      P.filtration n := by
    have hpow : t ^ n ∈ P.filtration n := by
      simpa [P.ord_pow, ht] using P.mem_filtration_ord (t ^ n)
    simpa using P.mul_mem_filtration
      (P.mem_filtration_zero_iff.mpr (P.algebraMap_mem_integers _)) hpow
  have hlow := (P.filtration n).add_mem
    (P.filtration_antitone (by omega) hhigh) hlast
  rw [Fin.sum_univ_castSucc] at hlow
  simp only [Fin.val_castSucc, Fin.val_last] at hlow
  have heq := (P.truncatedExpansion_eq_iff hP ht n x
    (fun j ↦ P.truncatedExpansion hP ht (n + 1) x j.castSucc)).mpr
    (by convert hlow using 1; ring)
  exact (congrFun heq i).symm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:385` (proof source at `5a01f5fe3621`).
 Increasing the truncation length preserves the coefficients at all indices of the
shorter expansion. -/
@[simp]
theorem truncatedExpansion_castLE (hP : P.degree = 1) (ht : P.ord t = 1)
    {n m : ℕ} (hnm : n ≤ m)
    (x : P.integers) (i : Fin n) :
    P.truncatedExpansion hP ht m x (i.castLE hnm) = P.truncatedExpansion hP ht n x i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    -- Both casts preserve the underlying natural index; expose the successor cast so the
    -- finite-expansion compatibility lemma applies.
    rw [show i.castLE (Nat.le_succ_of_le hnm) = (i.castLE hnm).castSucc from rfl,
      P.truncatedExpansion_castSucc hP ht]
    exact ih

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:401` (proof source at `5a01f5fe3621`).
 Two integral functions have the same length-`n` coefficient vector exactly when they
agree modulo the `n`-th order filtration. Thus coefficient extraction descends to finite
jets, with no choices of representatives visible in the coefficients. -/
theorem truncatedExpansion_eq_iff_sub_mem_filtration (hP : P.degree = 1)
    (ht : P.ord t = 1) (n : ℕ) (x y : P.integers) :
    P.truncatedExpansion hP ht n x = P.truncatedExpansion hP ht n y ↔
      (x : F) - (y : F) ∈ P.filtration n := by
  have hx := P.sub_sum_truncatedExpansion_mem_filtration hP ht n x
  have hy := P.sub_sum_truncatedExpansion_mem_filtration hP ht n y
  constructor
  · intro h
    rw [h] at hx
    convert (P.filtration n).sub_mem hx hy using 1
    ring
  · intro h
    apply (P.truncatedExpansion_eq_iff hP ht n x _).mpr
    convert (P.filtration n).add_mem h hy using 1
    ring

/-! ### Linear maps determined on powers of a uniformizer -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Basic.lean:422` (proof source at `5a01f5fe3621`).
 At a rational place, two `k`-linear maps on `F` that agree on the step `𝔪_P^m` of the order
filtration and on every power `t ^ j`, `j < m`, of a uniformizer `t` are equal: subtracting
the leading term `c * t ^ j` of a function of order `j < m` raises its order. -/
theorem linearMap_ext_zpow {M : Type*} [AddCommGroup M] [Module k M] (hP : P.degree = 1)
    (ht : P.ord t = 1) {m : ℤ} {f g : F →ₗ[k] M}
    (hfg : ∀ z ∈ P.filtration m, f z = g z) (h : ∀ j < m, f (t ^ j) = g (t ^ j)) : f = g := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have htj (j : ℤ) : t ^ j ∈ P.filtration j := by
    simpa [P.ord_zpow, ht] using P.mem_filtration_ord (t ^ j)
  -- Induction on how far below `m` the order of the function may lie.
  have key (d : ℕ) : ∀ z ∈ P.filtration (m - d), f z = g z := by
    induction d with
    | zero =>
      intro z hz
      rw [Nat.cast_zero, sub_zero] at hz
      exact hfg z hz
    | succ d ih =>
      intro z hz
      generalize hj' : m - ((d + 1 : ℕ) : ℤ) = j at hz
      have hj : j < m := by omega
      have hint := P.mul_mem_filtration (htj (-j)) hz
      rw [neg_add_cancel, mem_filtration_zero_iff] at hint
      obtain ⟨c, hc, -⟩ := P.existsUnique_sub_sum_mem_filtration hP ht 1 _ hint
      -- `z - c 0 • t ^ j = t ^ j * (t ^ (-j) * z - c 0)` has order at least `j + 1`.
      have heq : t ^ j * (t ^ (-j) * z - ∑ i : Fin 1, algebraMap k F (c i) * t ^ (i : ℕ)) =
          z - c 0 • t ^ j := by
        rw [Fin.sum_univ_one, Algebra.smul_def, mul_sub, ← mul_assoc, ← zpow_add₀ ht0]
        simp [mul_comm]
      have hrem : z - c 0 • t ^ j ∈ P.filtration (m - d) := by
        rw [← heq, show m - d = j + ((1 : ℕ) : ℤ) by omega]
        exact P.mul_mem_filtration (htj j) hc
      calc f z = f (z - c 0 • t ^ j) + c 0 • f (t ^ j) := by
            rw [← map_smul, ← map_add, sub_add_cancel]
        _ = g z := by
            rw [ih _ hrem, h _ hj, ← map_smul, ← map_add, sub_add_cancel]
  ext z
  exact key _ z (P.filtration_antitone (show m - ((m - P.ord z).toNat : ℕ) ≤ P.ord z by omega)
    (P.mem_filtration_ord z))

end TauCeti.Place
end

end

/-! ## Source 28: `TauCeti.FieldTheory.FunctionField.Place.Expansion.PowerSeries`
Original source SHA256: `dcf50b566e90b69e475fb7d86d05fa9f0e0029b78c3e6dd280fdbe62f1d112c0`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Power-series expansions at rational places

At a rational place with chosen uniformizer `t`, the compatible finite expansions define a
`k`-algebra embedding of the valuation ring into `k[[T]]`. Its coefficients characterize
congruence modulo every order-filtration step, so the embedding preserves orders and sends
`t` to `T`. These statements do not require completeness. When the field is complete for the
order filtration, every power series is an expansion
(`TauCeti.Place.powerSeriesExpansion_surjective`); this applies to the completion at a rational
place, and to the completion at any place with separable residue field viewed as a rational place
over its coefficient field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

section
open scoped BigOperators

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:40` (proof source at `5a01f5fe3621`).
 The uniformizer expansion of an integral function at a rational place, assembled from
its compatible finite coefficient vectors. -/
noncomputable def powerSeriesExpansion : P.integers →ₐ[k] PowerSeries k where
  toFun x := PowerSeries.mk fun n ↦ P.truncatedExpansion hP ht (n + 1) x ⟨n, by omega⟩
  map_zero' := by ext n; simp
  map_one' := by ext n; simp [PowerSeries.coeff_one]
  map_add' x y := by ext n; simp
  map_mul' x y := by
    ext n
    simp only [PowerSeries.coeff_mk, P.truncatedExpansion_mul, PowerSeries.coeff_mul]
    apply sum_fin_product_eq_sum_antidiagonal (Nat.lt_succ_self n)
    intro l hl
    congr 1
    · exact P.truncatedExpansion_castLE hP ht
        (n := (l.1 : ℕ) + 1) (m := n + 1) (by omega) x ⟨l.1, by omega⟩
    · exact P.truncatedExpansion_castLE hP ht
        (n := (l.2 : ℕ) + 1) (m := n + 1) (by omega) y ⟨l.2, by omega⟩
  commutes' c := by
    ext n
    simp [Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_C]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:62` (proof source at `5a01f5fe3621`).
 Every coefficient of the infinite expansion agrees with the corresponding coefficient
of any sufficiently long finite expansion. -/
@[simp]
theorem coeff_powerSeriesExpansion (n : ℕ) (x : P.integers) (i : Fin n) :
    PowerSeries.coeff i (P.powerSeriesExpansion hP ht x) =
      P.truncatedExpansion hP ht n x i := by
  simp only [powerSeriesExpansion, AlgHom.coe_mks, PowerSeries.coeff_mk]
  exact (P.truncatedExpansion_castLE hP ht
    (n := (i : ℕ) + 1) (m := n) (by omega) x ⟨i, by omega⟩).symm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:71` (proof source at `5a01f5fe3621`).
 Removing the first `n` coefficients of the power-series expansion leaves a function
vanishing to order at least `n`. -/
theorem sub_sum_coeff_powerSeriesExpansion_mem_filtration (n : ℕ) (x : P.integers) :
    (x : F) - ∑ i : Fin n, algebraMap k F
      (PowerSeries.coeff i (P.powerSeriesExpansion hP ht x)) * t ^ (i : ℕ) ∈
      P.filtration n := by
  simp only [P.coeff_powerSeriesExpansion hP ht]
  exact P.sub_sum_truncatedExpansion_mem_filtration hP ht n x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:80` (proof source at `5a01f5fe3621`).
 Vanishing of the first `n` expansion coefficients is exactly membership in the `n`-th
order filtration, including the zero function. -/
theorem mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero (n : ℕ) (x : P.integers) :
    (x : F) ∈ P.filtration n ↔
      ∀ i < n, PowerSeries.coeff i (P.powerSeriesExpansion hP ht x) = 0 := by
  have heq := P.truncatedExpansion_eq_iff_sub_mem_filtration hP ht n x 0
  simp only [P.truncatedExpansion_zero hP ht, ZeroMemClass.coe_zero, sub_zero] at heq
  rw [← heq]
  constructor
  · intro h i hi
    rw [P.coeff_powerSeriesExpansion hP ht n x ⟨i, hi⟩, h]
    rfl
  · intro h
    ext i
    exact (P.coeff_powerSeriesExpansion hP ht n x i).symm.trans (h i i.isLt)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:96` (proof source at `5a01f5fe3621`).
 The power-series embedding identifies the local order filtration with the usual
power-series order filtration. -/
theorem mem_filtration_iff_le_order_powerSeriesExpansion (n : ℕ) (x : P.integers) :
    (x : F) ∈ P.filtration n ↔
      (n : ℕ∞) ≤ (P.powerSeriesExpansion hP ht x).order := by
  rw [P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht,
    PowerSeries.nat_le_order_iff]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:104` (proof source at `5a01f5fe3621`).
 Uniformizer expansion is injective even before completion: an integral function is
determined by all its coefficients. -/
theorem powerSeriesExpansion_injective : Function.Injective (P.powerSeriesExpansion hP ht) := by
  apply (injective_iff_map_eq_zero (P.powerSeriesExpansion hP ht)).mpr
  intro x hx
  by_contra hx0
  have hxF : (x : F) ≠ 0 := by simpa using hx0
  let n := (P.ord (x : F)).toNat + 1
  have hn : P.ord (x : F) < (n : ℤ) := by dsimp [n]; omega
  have hm := (P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht n x).mpr
    (by simp [hx])
  exact (not_le.mpr hn) ((P.mem_filtration_iff_le_ord hxF).mp hm)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:117` (proof source at `5a01f5fe3621`).
 Two integral functions agree to order `n` precisely when their first `n` expansion
coefficients agree. -/
theorem sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq (n : ℕ) (x y : P.integers) :
    (x : F) - (y : F) ∈ P.filtration n ↔
      ∀ i < n, PowerSeries.coeff i (P.powerSeriesExpansion hP ht x) =
        PowerSeries.coeff i (P.powerSeriesExpansion hP ht y) := by
  simpa only [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero] using
    P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht n (x - y)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:126` (proof source at `5a01f5fe3621`).
 The chosen uniformizer expands as the power-series variable. -/
@[simp]
theorem powerSeriesExpansion_uniformizer :
    P.powerSeriesExpansion hP ht ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      PowerSeries.X := by
  ext n
  rw [P.coeff_powerSeriesExpansion hP ht (n + 1) _ ⟨n, by omega⟩,
    P.truncatedExpansion_uniformizer hP ht]
  simp [PowerSeries.coeff_X]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:138` (proof source at `5a01f5fe3621`).
 **Every power series is an expansion** when the field is complete for the order filtration of
the rational place: if every sequence whose terms agree to increasing order, `g n ≡ g m` to order
`m` whenever `m ≤ n`, is approximated to order `n` by a single function, then every power series
is the uniformizer expansion of an integral function. -/
theorem powerSeriesExpansion_surjective
    (hcomplete : ∀ g : ℕ → F, (∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.filtration m) →
      ∃ x : F, ∀ n : ℕ, x - g n ∈ P.filtration n) :
    Function.Surjective (P.powerSeriesExpansion hP ht) := by
  intro f
  -- The partial sums of `∑ cᵢ tⁱ` agree to increasing order, as `tⁱ` has order `i`.
  let g : ℕ → F := fun n ↦
    ∑ i ∈ Finset.range n, algebraMap k F (PowerSeries.coeff i f) * t ^ i
  have hg : ∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.filtration m := by
    intro m n hmn
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hmi : (m : ℤ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    refine P.filtration_antitone hmi ?_
    have hpow := P.mem_filtration_ord (t ^ i)
    rw [ord_pow, ht, mul_one] at hpow
    simpa only [zero_add] using P.mul_mem_filtration
      (P.mem_filtration_zero_iff.mpr (P.algebraMap_mem_integers _)) hpow
  obtain ⟨x, hx⟩ := hcomplete g hg
  have hxint : x ∈ P.integers := by
    simpa [g, mem_filtration_zero_iff] using hx 0
  refine ⟨⟨x, hxint⟩, ?_⟩
  ext n
  have heq := (P.truncatedExpansion_eq_iff hP ht (n + 1) ⟨x, hxint⟩
    (fun i ↦ PowerSeries.coeff i f)).mpr (by
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ algebraMap k F (PowerSeries.coeff i f) * t ^ i)]
      exact hx (n + 1))
  rw [P.coeff_powerSeriesExpansion hP ht (n + 1) _ ⟨n, by omega⟩, heq]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/PowerSeries.lean:170` (proof source at `5a01f5fe3621`).
 The order of a nonzero integral function is the first nonzero degree of its
power-series expansion. -/
theorem order_powerSeriesExpansion (x : P.integers) (hx : x ≠ 0) :
    (P.powerSeriesExpansion hP ht x).order = ((P.ord (x : F)).toNat : ℕ∞) := by
  have hxF : (x : F) ≠ 0 := by simpa using hx
  have ho : 0 ≤ P.ord (x : F) := P.mem_integers_iff_ord_nonneg.mp x.2
  have hlow := (P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht
    (P.ord (x : F)).toNat x).mp
    ((P.mem_filtration_iff_le_ord hxF).mpr (by omega))
  apply PowerSeries.order_eq_nat.mpr
  refine ⟨?_, hlow⟩
  intro hc
  have hm := (P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht
    ((P.ord (x : F)).toNat + 1) x).mpr (fun i hi ↦ by
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact hlow i hi
      · exact hc)
  have := (P.mem_filtration_iff_le_ord hxF).mp hm
  omega

end TauCeti.Place
end

end

/-! ## Source 29: `TauCeti.FieldTheory.FunctionField.Place.Expansion.CoefficientField`
Original source SHA256: `26682e86af1ba566bd1eaf7419bb81b47afbb57f32b20778262c73a306ab6f5d`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The completed valuation ring at a place with separable residue field

Let `P` be a place of `F / k` whose residue field `F_P` is separable over `k`, and let `t` be a
uniformizer of the completion `F̂_P`. Then the completed valuation ring `𝒪̂_P` is the power-series
ring `F_P[[T]]`: every completed integral function has a unique expansion `∑ aᵢ tⁱ` with
coefficients `aᵢ` in the coefficient field of `𝒪̂_P`
(`TauCeti.Place.completionResidueFieldSection`), the lift of `F_P` to `𝒪̂_P`.

This is the identification of a completed valuation ring with `k[[T]]` at a rational place
(`TauCeti.Place.completionIntegersEquivPowerSeries`) carried over to places of arbitrary degree.
The coefficients lie in `F_P` rather than `k`, which is what makes the `t⁻¹`-coefficient of a
Laurent expansion, the residue at `P`, an element of `F_P`.

The proof views `F̂_P` as an `F_P`-algebra through the coefficient field. The completed place is
then trivial on `F_P`, and its residue field is `F_P` itself, so it is a *rational* place over
`F_P`. The uniformizer expansions at rational places
(`TauCeti.Place.powerSeriesExpansion`) and the completeness of `F̂_P`
(`TauCeti.Place.powerSeriesExpansion_surjective`) apply to it verbatim.

## Main definitions

* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`: the isomorphism
  `𝒪̂_P ≃ₐ[k] F_P[[T]]` determined by the coefficient field and the uniformizer `t`.

## Main results

* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_eq_iff`: the expansion of `x` is
  the power series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} aᵢ tⁱ` vanishes to order `n` for every
  `n`.
* `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection` and
  `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_uniformizer`: the coefficient field
  expands to the constant power series and `t` to `T`.
* `TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesResidueField`: the constant
  coefficient is the value at `P`, also for functions of `F` regular at `P`.
* `TauCeti.Place.order_completionIntegersEquivPowerSeriesResidueField`: the expansion preserves
  orders.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

section
open _root_.IsLocalRing

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)
  [Algebra.IsSeparable k P.ResidueField]

/-! ### The completion as a rational place over its coefficient field -/

/-- Kind: ABBREV. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:68` (proof source at `5a01f5fe3621`).
 The residue field acts on the completion through the coefficient field. -/
private noncomputable abbrev residueFieldAlgebraCompletion :
    Algebra P.ResidueField P.Completion :=
  (P.completionPlace.integers.subtype.comp P.completionResidueFieldSection.toRingHom).toAlgebra

attribute [local instance] residueFieldAlgebraCompletion

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:74` (proof source at `5a01f5fe3621`).
-/
private theorem algebraMap_residueField_completion (a : P.ResidueField) :
    algebraMap P.ResidueField P.Completion a = P.completionResidueFieldSection a := (rfl)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:79` (proof source at `5a01f5fe3621`).
 The completed place, viewed as a place over the residue field through the coefficient field:
a nonzero element of the coefficient field is a unit of `𝒪̂_P`, so it has valuation one. -/
private noncomputable def residueFieldPlace : Place P.ResidueField P.Completion where
  valuation := P.completionPlace.valuation
  valuation_surjective := P.completionPlace.valuation_surjective
  isTrivialOn := ⟨fun a ha ↦ P.completionPlace.isUnit_iff_valuation_eq_one.mp
    ((IsUnit.mk0 a ha).map P.completionResidueFieldSection)⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:86` (proof source at `5a01f5fe3621`).
 Changing the constants to the coefficient field does not change the valuation. -/
private theorem residueFieldPlace_valuation :
    P.residueFieldPlace.valuation = P.completionPlace.valuation := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:90` (proof source at `5a01f5fe3621`).
 Changing the constants to the coefficient field does not change the filtration. -/
private theorem mem_residueFieldPlace_filtration_iff {a : ℤ} {x : P.Completion} :
    x ∈ P.residueFieldPlace.filtration a ↔ x ∈ P.completionPlace.filtration a := by
  simp only [mem_filtration_iff, residueFieldPlace_valuation]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:95` (proof source at `5a01f5fe3621`).
 Changing the constants to the coefficient field does not change orders. -/
private theorem ord_residueFieldPlace (x : P.Completion) :
    P.residueFieldPlace.ord x = P.completionPlace.ord x := by
  simp only [ord_def, residueFieldPlace_valuation]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:100` (proof source at `5a01f5fe3621`).
 Changing the constants to the coefficient field does not change the valuation ring. -/
private theorem residueFieldPlace_integers :
    P.residueFieldPlace.integers = P.completionPlace.integers :=
  SetLike.ext fun _ ↦ by simp only [mem_integers_iff, residueFieldPlace_valuation]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:106` (proof source at `5a01f5fe3621`).
 The two views of the completed valuation ring, as rings of functions with the same
underlying elements. -/
private noncomputable def integersEquivResidueFieldPlace :
    P.completionPlace.integers ≃+* P.residueFieldPlace.integers :=
  RingEquiv.subringCongr (congrArg ValuationSubring.toSubring P.residueFieldPlace_integers.symm)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:111` (proof source at `5a01f5fe3621`).
-/
@[simp]
private theorem coe_integersEquivResidueFieldPlace (x : P.completionPlace.integers) :
    (P.integersEquivResidueFieldPlace x : P.Completion) = x := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:115` (proof source at `5a01f5fe3621`).
-/
@[simp]
private theorem coe_integersEquivResidueFieldPlace_symm (x : P.residueFieldPlace.integers) :
    (P.integersEquivResidueFieldPlace.symm x : P.Completion) = x := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:120` (proof source at `5a01f5fe3621`).
 Changing the constants to the coefficient field does not change when two integral functions
have the same residue. -/
private theorem residue_integersEquivResidueFieldPlace_eq_iff
    {y z : P.completionPlace.integers} :
    residue P.residueFieldPlace.integers (P.integersEquivResidueFieldPlace y) =
        residue P.residueFieldPlace.integers (P.integersEquivResidueFieldPlace z) ↔
      residue P.completionPlace.integers y = residue P.completionPlace.integers z := by
  simp only [residue_eq_iff_sub_mem_filtration_one, coe_integersEquivResidueFieldPlace,
    mem_residueFieldPlace_filtration_iff]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:129` (proof source at `5a01f5fe3621`).
 The coefficient field is the image of the constants of the completed place over `F_P`. -/
private theorem integersEquivResidueFieldPlace_completionResidueFieldSection
    (a : P.ResidueField) :
    P.integersEquivResidueFieldPlace (P.completionResidueFieldSection a) =
      algebraMap P.ResidueField P.residueFieldPlace.integers a :=
  Subtype.ext (P.residueFieldPlace.coe_algebraMap_constants a).symm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:137` (proof source at `5a01f5fe3621`).
 Over its coefficient field, the completed place is rational: reduction of the coefficient
field is the identification of `F_P` with the residue field of the completion. -/
private theorem degree_residueFieldPlace : P.residueFieldPlace.degree = 1 := by
  refine P.residueFieldPlace.degree_eq_one_iff_algebraMap_surjective.mpr fun y ↦ ?_
  obtain ⟨z, rfl⟩ := residue_surjective y
  let w := P.integersEquivResidueFieldPlace.symm z
  refine ⟨P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers w), ?_⟩
  have h := P.residue_integersEquivResidueFieldPlace_eq_iff.mpr
    (P.residue_completionResidueFieldSection
      (P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers w)) |>.trans
      (P.residueFieldEquivCompletion.apply_symm_apply _))
  rwa [integersEquivResidueFieldPlace_completionResidueFieldSection,
    RingEquiv.apply_symm_apply, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply] at h

variable {t : P.Completion} (ht : P.completionPlace.ord t = 1)
include ht

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:153` (proof source at `5a01f5fe3621`).
-/
private theorem ord_residueFieldPlace_uniformizer : P.residueFieldPlace.ord t = 1 := by
  rwa [ord_residueFieldPlace]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:157` (proof source at `5a01f5fe3621`).
 The uniformizer expansion over the coefficient field is a bijection onto `F_P[[T]]`. -/
private theorem bijective_residueFieldPlace_powerSeriesExpansion :
    Function.Bijective (P.residueFieldPlace.powerSeriesExpansion P.degree_residueFieldPlace
      (P.ord_residueFieldPlace_uniformizer ht)) :=
  ⟨P.residueFieldPlace.powerSeriesExpansion_injective _ _,
    P.residueFieldPlace.powerSeriesExpansion_surjective _ _ fun _ hg ↦ by
      simp only [mem_residueFieldPlace_filtration_iff] at hg ⊢
      exact P.exists_forall_sub_mem_completionPlace_filtration hg⟩

/-! ### Power-series expansions with coefficients in the residue field -/

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:172` (proof source at `5a01f5fe3621`).
 **The completed valuation ring at a place with separable residue field is `F_P[[T]]`.** The
isomorphism sends a completed integral function to its expansion `∑ aᵢ Tⁱ` in the uniformizer
`t`, with coefficients `aᵢ ∈ F_P` read in the coefficient field
`TauCeti.Place.completionResidueFieldSection`; it is characterized by
`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_eq_iff`. -/
noncomputable def completionIntegersEquivPowerSeriesResidueField :
    P.completionPlace.integers ≃ₐ[k] PowerSeries P.ResidueField :=
  AlgEquiv.ofRingEquiv (f := P.integersEquivResidueFieldPlace.trans
    (AlgEquiv.ofBijective _ (P.bijective_residueFieldPlace_powerSeriesExpansion ht)).toRingEquiv)
    fun c ↦ by
      have h : P.integersEquivResidueFieldPlace (algebraMap k _ c) =
          algebraMap P.ResidueField _ (algebraMap k P.ResidueField c) :=
        Subtype.ext (by
          rw [coe_integersEquivResidueFieldPlace, P.residueFieldPlace.coe_algebraMap_constants,
            algebraMap_residueField_completion, P.completionResidueFieldSection.commutes c])
      simp [h, PowerSeries.algebraMap_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:184` (proof source at `5a01f5fe3621`).
-/
private theorem completionIntegersEquivPowerSeriesResidueField_apply
    (x : P.completionPlace.integers) :
    P.completionIntegersEquivPowerSeriesResidueField ht x =
      P.residueFieldPlace.powerSeriesExpansion P.degree_residueFieldPlace
        (P.ord_residueFieldPlace_uniformizer ht) (P.integersEquivResidueFieldPlace x) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:193` (proof source at `5a01f5fe3621`).
 **The expansion is characterized by its truncations**: the expansion of `x` is the power
series `∑ aᵢ Tⁱ` exactly when `x - ∑_{i < n} aᵢ tⁱ` vanishes to order `n` for every `n`, the
coefficients `aᵢ` being read in the coefficient field. -/
theorem completionIntegersEquivPowerSeriesResidueField_eq_iff (x : P.completionPlace.integers)
    (f : PowerSeries P.ResidueField) :
    P.completionIntegersEquivPowerSeriesResidueField ht x = f ↔
      ∀ n : ℕ, (x : P.Completion) - ∑ i : Fin n,
        (P.completionResidueFieldSection (PowerSeries.coeff i f) : P.Completion) * t ^ (i : ℕ) ∈
          P.completionPlace.filtration n := by
  rw [completionIntegersEquivPowerSeriesResidueField_apply]
  constructor
  · rintro rfl n
    have h := P.residueFieldPlace.sub_sum_coeff_powerSeriesExpansion_mem_filtration
      P.degree_residueFieldPlace (P.ord_residueFieldPlace_uniformizer ht) n
      (P.integersEquivResidueFieldPlace x)
    simpa only [coe_integersEquivResidueFieldPlace, algebraMap_residueField_completion,
      mem_residueFieldPlace_filtration_iff] using h
  · intro h
    ext n
    rw [P.residueFieldPlace.coeff_powerSeriesExpansion _ _ (n + 1) _ ⟨n, by omega⟩]
    refine congrFun ((P.residueFieldPlace.truncatedExpansion_eq_iff _ _ (n + 1) _
      fun i ↦ PowerSeries.coeff i f).mpr ?_) ⟨n, by omega⟩
    simpa only [coe_integersEquivResidueFieldPlace, algebraMap_residueField_completion,
      mem_residueFieldPlace_filtration_iff] using h (n + 1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:217` (proof source at `5a01f5fe3621`).
 Removing the first `n` terms of the expansion of a completed integral function leaves a
function vanishing to order at least `n`. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration
    (x : P.completionPlace.integers) (n : ℕ) :
    (x : P.Completion) - ∑ i : Fin n, (P.completionResidueFieldSection
      (PowerSeries.coeff i (P.completionIntegersEquivPowerSeriesResidueField ht x)) :
        P.Completion) * t ^ (i : ℕ) ∈ P.completionPlace.filtration n :=
  (P.completionIntegersEquivPowerSeriesResidueField_eq_iff ht x _).mp rfl n

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:226` (proof source at `5a01f5fe3621`).
 The inverse isomorphism realizes a power series over the residue field to every finite
order. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_symm_mem_filtration
    (f : PowerSeries P.ResidueField) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeriesResidueField ht).symm f : P.Completion) -
      ∑ i : Fin n, (P.completionResidueFieldSection (PowerSeries.coeff i f) : P.Completion) *
        t ^ (i : ℕ) ∈ P.completionPlace.filtration n :=
  (P.completionIntegersEquivPowerSeriesResidueField_eq_iff ht _ f).mp
    (AlgEquiv.apply_symm_apply _ f) n

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:236` (proof source at `5a01f5fe3621`).
 The coefficient field expands to the constant power series. -/
@[simp]
theorem completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection
    (a : P.ResidueField) :
    P.completionIntegersEquivPowerSeriesResidueField ht (P.completionResidueFieldSection a) =
      PowerSeries.C a := by
  have h : P.integersEquivResidueFieldPlace (P.completionResidueFieldSection a) =
      algebraMap P.ResidueField _ a :=
    Subtype.ext (by rw [coe_integersEquivResidueFieldPlace, coe_algebraMap_constants,
      algebraMap_residueField_completion])
  rw [completionIntegersEquivPowerSeriesResidueField_apply, h, AlgHom.commutes,
    PowerSeries.algebraMap_eq]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:249` (proof source at `5a01f5fe3621`).
 The uniformizer expands as the power-series variable. -/
@[simp]
theorem completionIntegersEquivPowerSeriesResidueField_uniformizer :
    P.completionIntegersEquivPowerSeriesResidueField ht
      ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ = PowerSeries.X := by
  rw [completionIntegersEquivPowerSeriesResidueField_apply]
  exact P.residueFieldPlace.powerSeriesExpansion_uniformizer _ _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:257` (proof source at `5a01f5fe3621`).
 The constant coefficient of the expansion is the value at `P`, read in `F_P`. -/
@[simp]
theorem constantCoeff_completionIntegersEquivPowerSeriesResidueField
    (x : P.completionPlace.integers) :
    PowerSeries.constantCoeff (P.completionIntegersEquivPowerSeriesResidueField ht x) =
      P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers x) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AlgEquiv.eq_symm_apply,
    ← residue_completionResidueFieldSection, eq_comm]
  apply P.completionPlace.residue_eq_iff_sub_mem_filtration_one.mpr
  simpa using P.sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration ht x 1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:267` (proof source at `5a01f5fe3621`).
 The constant coefficient of the expansion of a function regular at `P` is its value at `P`. -/
theorem constantCoeff_completionIntegersEquivPowerSeriesResidueField_completionIntegersEmbedding
    (x : P.integers) :
    PowerSeries.constantCoeff (P.completionIntegersEquivPowerSeriesResidueField ht
      (P.completionIntegersEmbedding x)) = residue P.integers x := by
  simp

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:274` (proof source at `5a01f5fe3621`).
 Vanishing to order `n` is vanishing of the first `n` coefficients of the expansion. -/
theorem mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField (n : ℕ)
    (x : P.completionPlace.integers) :
    (x : P.Completion) ∈ P.completionPlace.filtration n ↔
      (n : ℕ∞) ≤ (P.completionIntegersEquivPowerSeriesResidueField ht x).order := by
  rw [← P.mem_residueFieldPlace_filtration_iff, ← coe_integersEquivResidueFieldPlace,
    completionIntegersEquivPowerSeriesResidueField_apply]
  exact P.residueFieldPlace.mem_filtration_iff_le_order_powerSeriesExpansion _ _ n _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/CoefficientField.lean:284` (proof source at `5a01f5fe3621`).
 The order of a nonzero completed integral function is the first nonzero degree of its
expansion. -/
theorem order_completionIntegersEquivPowerSeriesResidueField (x : P.completionPlace.integers)
    (hx : x ≠ 0) :
    (P.completionIntegersEquivPowerSeriesResidueField ht x).order =
      ((P.completionPlace.ord (x : P.Completion)).toNat : ℕ∞) := by
  rw [completionIntegersEquivPowerSeriesResidueField_apply, ← ord_residueFieldPlace,
    ← coe_integersEquivResidueFieldPlace]
  exact P.residueFieldPlace.order_powerSeriesExpansion _ _ _
    ((map_ne_zero_iff _ P.integersEquivResidueFieldPlace.injective).mpr hx)

end TauCeti.Place
end

end

/-! ## Source 30: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Completion`
Original source SHA256: `d42190768052cdb284452d9504c25d7c9c86f76cc5fa0307fcb6ef7c4314db56`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The completed valuation ring at a rational place

Uniformizer expansion identifies the completed valuation ring at a rational place with
`k[[T]]`. Every coefficient sequence is realized: its polynomial partial sums are Cauchy,
and their limit has the prescribed finite expansions. The isomorphism sends a chosen
uniformizer to `T`, identifies the order filtrations, and restricts on the valuation ring
of `F` to the uniformizer expansion before completion. With the constants discrete and
power series given their coefficientwise topology, it is also a homeomorphism.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

section
open Filter Topology
open scoped BigOperators WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:40` (proof source at `5a01f5fe3621`).
 Every power series over the constants is the uniformizer expansion of an element of
the completed valuation ring at a rational place. -/
theorem completionPlace_powerSeriesExpansion_surjective :
    Function.Surjective (P.completionPlace.powerSeriesExpansion
      (by simpa using hP) (by simpa using ht :
        P.completionPlace.ord (P.completionEmbedding t) = 1)) :=
  P.completionPlace.powerSeriesExpansion_surjective _ _ fun _ ↦
    P.exists_forall_sub_mem_completionPlace_filtration

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:49` (proof source at `5a01f5fe3621`).
 Uniformizer expansion identifies the completed valuation ring at a rational place with
the power-series ring over the constants. -/
noncomputable def completionIntegersEquivPowerSeries :
    P.completionPlace.integers ≃ₐ[k] PowerSeries k :=
  AlgEquiv.ofBijective (P.completionPlace.powerSeriesExpansion
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1))
    ⟨P.completionPlace.powerSeriesExpansion_injective _ _,
      P.completionPlace_powerSeriesExpansion_surjective hP ht⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:58` (proof source at `5a01f5fe3621`).
 The completed-ring isomorphism is the uniformizer expansion map. -/
theorem completionIntegersEquivPowerSeries_apply (x : P.completionPlace.integers) :
    P.completionIntegersEquivPowerSeries hP ht x =
      P.completionPlace.powerSeriesExpansion (by simpa using hP)
        (by simpa using ht : P.completionPlace.ord (P.completionEmbedding t) = 1) x := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:64` (proof source at `5a01f5fe3621`).
 The inverse isomorphism realizes a power series to every finite order. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration
    (f : PowerSeries k) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) -
      ∑ i : Fin n, algebraMap k P.Completion (PowerSeries.coeff i f) *
        P.completionEmbedding t ^ (i : ℕ) ∈ P.completionPlace.filtration n := by
  have h := P.completionPlace.sub_sum_coeff_powerSeriesExpansion_mem_filtration
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) n
    ((P.completionIntegersEquivPowerSeries hP ht).symm f)
  rw [← P.completionIntegersEquivPowerSeries_apply hP ht,
    AlgEquiv.apply_symm_apply] at h
  exact h

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:80` (proof source at `5a01f5fe3621`).
 On integral functions of the original field, uniformizer expansion in the completion is
uniformizer expansion before completion. -/
@[simp]
theorem completionIntegersEquivPowerSeries_completionIntegersEmbedding (x : P.integers) :
    P.completionIntegersEquivPowerSeries hP ht (P.completionIntegersEmbedding x) =
      P.powerSeriesExpansion hP ht x := by
  ext n
  rw [P.completionIntegersEquivPowerSeries_apply hP ht,
    P.completionPlace.coeff_powerSeriesExpansion _ _ (n + 1) _ ⟨n, by omega⟩,
    P.coeff_powerSeriesExpansion hP ht (n + 1) x ⟨n, by omega⟩]
  have h := P.sub_sum_truncatedExpansion_mem_filtration hP ht (n + 1) x
  rw [← P.completionEmbedding_mem_filtration_iff] at h
  exact congrFun ((P.completionPlace.truncatedExpansion_eq_iff _ _ (n + 1) _ _).mpr
    (by simpa only [completionIntegersEmbedding_apply, map_sub, map_sum, map_mul,
      map_pow, AlgHom.commutes] using h)) _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:94` (proof source at `5a01f5fe3621`).
 The chosen uniformizer maps to the power-series variable. -/
theorem completionIntegersEquivPowerSeries_uniformizer :
    P.completionIntegersEquivPowerSeries hP ht
      (P.completionIntegersEmbedding
        ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩) = PowerSeries.X := by
  rw [completionIntegersEquivPowerSeries_completionIntegersEmbedding,
    powerSeriesExpansion_uniformizer]

section Topology

variable [TopologicalSpace k] [DiscreteTopology k]
open scoped PowerSeries.WithPiTopology

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:108` (proof source at `5a01f5fe3621`).
 Uniformizer expansion is continuous for the valuation topology on the completed ring
and the coefficientwise topology on power series over the discrete constant field. -/
theorem continuous_completionIntegersEquivPowerSeries :
    Continuous (P.completionIntegersEquivPowerSeries hP ht) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  rw [nhds_discrete k, tendsto_pure]
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq (n + 1 : ℕ)
  have hs' : Valued.v.restrict (P.completionEmbedding s) ≠ 0 := by simp [hs0]
  have hU : {y : P.Completion | y - (x : P.Completion) ∈
      P.completionPlace.filtration (n + 1 : ℕ)} ∈ 𝓝 (x : P.Completion) := by
    apply Valued.mem_nhds.mpr
    refine ⟨Units.mk0 _ hs', fun y hy ↦ ?_⟩
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [P.completionPlace.mem_filtration_iff, completionPlace_valuation]
    rw [Units.val_mk0, Valuation.restrict_lt_iff, valuation_completionEmbedding,
      P.valuation_eq_exp_neg_ord hs0, hs] at hy
    exact hy.le
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hU] with y hy
  have hc := (P.completionPlace.sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) (n + 1) y x).mp hy n (by omega)
  simpa only [P.completionIntegersEquivPowerSeries_apply hP ht] using hc

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:134` (proof source at `5a01f5fe3621`).
 Realizing a power series in the completed valuation ring is continuous: agreement of
finitely many coefficients gives approximation to any prescribed valuation precision. -/
theorem continuous_completionIntegersEquivPowerSeries_symm :
    Continuous (P.completionIntegersEquivPowerSeries hP ht).symm := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro f
  apply tendsto_iff_forall_eventually_mem.mpr
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  have hc : ∀ᶠ g in 𝓝 f, ∀ i : Fin n,
      PowerSeries.coeff i g = PowerSeries.coeff i f := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (PowerSeries.WithPiTopology.continuous_coeff k i).continuousAt (x := f)
    rw [ContinuousAt, nhds_discrete k, tendsto_pure] at hi
    exact hi
  filter_upwards [hc] with g hg
  apply hγ
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding]
  have hmem := (P.completionPlace.sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) n
    ((P.completionIntegersEquivPowerSeries hP ht).symm g)
    ((P.completionIntegersEquivPowerSeries hP ht).symm f)).mpr (fun i hi ↦ by
      simpa only [← P.completionIntegersEquivPowerSeries_apply hP ht,
        AlgEquiv.apply_symm_apply] using hg ⟨i, hi⟩)
  simpa only [completionPlace_valuation, Function.comp_apply] using
    (P.completionPlace.mem_filtration_iff.mp hmem).trans_lt hn

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:167` (proof source at `5a01f5fe3621`).
 The completed valuation ring at a rational place is topologically `k[[T]]`, with `k`
discrete and the power-series ring carrying its coefficientwise topology. -/
noncomputable def completionIntegersHomeomorphPowerSeries :
    P.completionPlace.integers ≃ₜ PowerSeries k where
  toEquiv := (P.completionIntegersEquivPowerSeries hP ht).toEquiv
  continuous_toFun := P.continuous_completionIntegersEquivPowerSeries hP ht
  continuous_invFun := P.continuous_completionIntegersEquivPowerSeries_symm hP ht

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:175` (proof source at `5a01f5fe3621`).
 The topological identification uses the same uniformizer expansion as the algebraic one. -/
@[simp]
theorem completionIntegersHomeomorphPowerSeries_apply (x : P.completionPlace.integers) :
    P.completionIntegersHomeomorphPowerSeries hP ht x =
      P.completionIntegersEquivPowerSeries hP ht x := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Completion.lean:181` (proof source at `5a01f5fe3621`).
 The inverse topological identification is the inverse algebraic identification. -/
@[simp]
theorem completionIntegersHomeomorphPowerSeries_symm_apply (f : PowerSeries k) :
    (P.completionIntegersHomeomorphPowerSeries hP ht).symm f =
      (P.completionIntegersEquivPowerSeries hP ht).symm f := (rfl)

end Topology

end TauCeti.Place
end

end

/-! ## Source 31: `TauCeti.RingTheory.PowerSeries.Derivative`
Original source SHA256: `df7dcfe2322801c3ff59a2d688c9133d1ddf370f3f5e1f6132b8e950fe09c19a`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# A coefficient identity for powers of a power series

For a power series `v` over a commutative semiring and `n : ℕ`,

`coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.

Over a ring in which `n + 1` is not a zero divisor this is the coefficient of `X ^ n` in
`(v ^ (n + 1))' = (n + 1) v ^ n v'`, divided by `n + 1`. The identity holds over every commutative
semiring because both sides are polynomials with natural-number coefficients in the coefficients
of `v`; the proof specializes the generic power series with coefficients the variables of
`MvPolynomial ℕ ℕ`.

In positive characteristic `p` the division by `n + 1` is unavailable when `p ∣ n + 1`, and this
identity is what replaces it. It is the coefficient computation behind the invariance of residues
under a change of uniformizer: the coefficient of `X⁻¹` in `φ ^ (-(n + 2)) * φ'` vanishes for
every power series `φ` of order one.

## Main results

* `PowerSeries.derivative_map`: the derivative commutes with change of coefficients.
* `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`:
  `coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.
-/

section
namespace PowerSeries

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/PowerSeries/Derivative.lean:44` (proof source at `5a01f5fe3621`).
 The derivative of power series commutes with change of coefficients. -/
@[simp]
theorem derivative_map (φ : R⟦X⟧) (f : R →+* S) : d⁄dX (map f φ) = map f (d⁄dX φ) := by
  ext n
  simp [coeff_derivative]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/PowerSeries/Derivative.lean:50` (proof source at `5a01f5fe3621`).
 The identity `coeff_succ_pow_succ_eq_coeff_pow_mul_derivative` when `n + 1` can be
cancelled. -/
private theorem coeff_succ_pow_succ_eq_of_hasUniqueDiv [HasUniqueDiv R] (v : R⟦X⟧)
    (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  have h := coeff_derivative (v ^ (n + 1)) n
  rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, ← map_natCast (C (R := R)), coeff_C_mul,
    Nat.cast_add_one] at h
  apply nsmul_right_injective (Nat.succ_ne_zero n)
  simp only [nsmul_eq_mul, Nat.cast_succ]
  rw [h, mul_comm]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/PowerSeries/Derivative.lean:62` (proof source at `5a01f5fe3621`).
 The coefficient of `X ^ (n + 1)` in `v ^ (n + 1)` is the coefficient of `X ^ n` in
`v ^ n * v'`, over any commutative semiring. -/
theorem coeff_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  -- Specialize the identity for the generic power series over `MvPolynomial ℕ ℕ`, which has
  -- no additive torsion.
  let V : (MvPolynomial ℕ ℕ)⟦X⟧ := mk fun i ↦ MvPolynomial.X i
  let f : MvPolynomial ℕ ℕ →+* R := MvPolynomial.eval₂Hom (Nat.castRingHom R) fun i ↦ coeff i v
  have hV : map f V = v := by
    ext i
    simp [V, f]
  have h := congrArg f (coeff_succ_pow_succ_eq_of_hasUniqueDiv V n)
  rwa [← coeff_map, ← coeff_map, (map f).map_pow, (map f).map_mul, (map f).map_pow,
    ← derivative_map, hV] at h

end PowerSeries
end

end

/-! ## Source 32: `TauCeti.RingTheory.LaurentSeries.Basic`
Original source SHA256: `217a268d7d7f171e89905abdc1b0a10d3356eea6c2ae5d1960e358cf1acb1dfe`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Scalar towers, the product rule, and residues of `φⁿ dφ` for Laurent series

For an `R`-algebra `A`, the `R`-algebra structure on `A⸨X⸩` is the one inherited from `A⟦X⟧`
through `HahnSeries.ofPowerSeries`, so its scalar action is multiplication by the image of a
constant power series. This is propositionally, but not definitionally, equal to the coefficientwise
action `HahnSeries.instSMul` found by default.

This file records that the algebra actions form a scalar tower `R → A⟦X⟧ → A⸨X⸩`. This is what
fraction-field constructions such as `IsFractionRing.algEquivOfAlgEquiv` require to extend an
`R`-algebra equivalence with `A⟦X⟧` to one with `A⸨X⸩`. Over a field `K`, it also records that
a nonzero Laurent series `f ∈ K⸨X⸩` has valuation `exp (-ord f)`, since its power series part is
a unit of `K⟦X⟧`.

The second part proves the product rule for the derivative of Laurent series,
`(f * g)' = f' * g + f * g'`. Mathlib defines `LaurentSeries.derivative` only as a linear map,
the first Hasse derivative; the product rule is what makes it a derivation, so that composing it
with a ring homomorphism into `R⸨X⸩` gives a derivation, as for Laurent expansions of functions.
It is reduced to the product rule for power series by writing a Laurent series as a monomial
times a power series.

The third part computes the residue, the coefficient of `X⁻¹`, of `φ ^ n * φ'` for a power
series `φ` of order one over a field and every integer `n`: it is `1` for `n = -1` and `0`
otherwise. This is the formal statement that the residue is unchanged by the substitution
`X ↦ φ`. For `n ≠ -1` in characteristic zero, `φ ^ n * φ'` is the derivative of
`φ ^ (n + 1) / (n + 1)`; in characteristic `p` this fails when `p ∣ n + 1`, and the proof
uses `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative` instead. By linearity this
extends to every Laurent series: a substitution `X ↦ φ` preserves the residue of `f(X) dX`.

## Main results

* `TauCeti.LaurentSeries.isScalarTower_powerSeries`: the algebra actions of `R` on `A⟦X⟧` and
  `A⸨X⸩` form a scalar tower.
* `TauCeti.LaurentSeries.coeff_algebraMap_mul`: multiplication by a constant of the algebra
  structure acts coefficientwise.
* `TauCeti.laurentSeries_algebraMap_mul_eq_smul`: the algebra action agrees with the
  coefficientwise scalar action.
* `TauCeti.LaurentSeries.valuation_eq_exp_neg_order`: a nonzero Laurent series `f` has valuation
  `exp (-ord f)`; `TauCeti.LaurentSeries.valuation_coe` gives the same for a nonzero power series.
* `LaurentSeries.derivative_mul`: the product rule for the derivative of Laurent series.
* `PowerSeries.coe_derivative`: the derivative of Laurent series extends that of power series.
* `LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le`: if `f` vanishes to order at least
  `m`, so does `f' - m X⁻¹ f`.
* `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative`: the residue of `φ ^ n * φ'` for a power
  series `φ` of order one is `1` if `n = -1` and `0` otherwise.
* `LaurentSeries.coeff_neg_one_map_mul_derivative`: the residue of `f(φ) φ'` is the residue of
  `f`, for the substitution `X ↦ φ`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9.
-/

section
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommSemiring R]

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:76` (proof source at `5a01f5fe3621`).
 For an `R`-algebra `A`, the scalars of `R` on `A⸨X⸩` factor through `A⟦X⟧`. The scalar
actions are stated through the algebra structures, since the `R`-algebra structure on `A⸨X⸩` is
the one inherited from `A⟦X⟧` rather than the coefficientwise action. -/
instance isScalarTower_powerSeries {A : Type*} [CommSemiring A] [Algebra R A] :
    @IsScalarTower R A⟦X⟧ A⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq' rfl

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:83` (proof source at `5a01f5fe3621`).
 Multiplying a Laurent series by a constant of the `R`-algebra structure on `R⸨X⸩` multiplies
each coefficient by that constant. -/
@[simp]
theorem coeff_algebraMap_mul (c : R) (f : R⸨X⸩) (n : ℤ) :
    (algebraMap R R⸨X⸩ c * f).coeff n = c * f.coeff n := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

section Valuation

open HahnSeries PowerSeries WithZero

variable {K : Type*} [Field K]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:96` (proof source at `5a01f5fe3621`).
 A unit of `K⟦X⟧`, that is a power series of nonzero constant coefficient, has valuation one
in `K⸨X⸩`. -/
theorem valuation_coe_of_isUnit {h : K⟦X⟧} (hh : IsUnit h) : Valued.v (h : K⸨X⸩) = 1 :=
  Valuation.Integers.one_of_isUnit' hh fun g ↦ (_root_.LaurentSeries.val_le_one_iff_eq_coe K _).mpr
    ⟨g, rfl⟩

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:102` (proof source at `5a01f5fe3621`).
 The power series part of a nonzero Laurent series is a unit: its constant coefficient is the
leading coefficient. -/
theorem isUnit_powerSeriesPart {f : K⸨X⸩} (hf : f ≠ 0) : IsUnit f.powerSeriesPart := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    _root_.LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero, isUnit_iff_ne_zero]
  exact coeff_order_eq_zero.not.mpr hf

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:108` (proof source at `5a01f5fe3621`).
 A nonzero Laurent series `f` has valuation `exp (-ord f)`. -/
theorem valuation_eq_exp_neg_order {f : K⸨X⸩} (hf : f ≠ 0) : Valued.v f = exp (-f.order) := by
  nth_rw 1 [← f.single_order_mul_powerSeriesPart]
  rw [map_mul, valuation_coe_of_isUnit (isUnit_powerSeriesPart hf), mul_one,
    _root_.LaurentSeries.valuation_single_zpow]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:114` (proof source at `5a01f5fe3621`).
 A nonzero power series `g` has valuation `exp (-ord g)` in `K⸨X⸩`. -/
theorem valuation_coe {g : K⟦X⟧} (hg : g ≠ 0) :
    Valued.v (g : K⸨X⸩) = exp (-(g.order.toNat : ℤ)) := by
  have hu : IsUnit g.divXPowOrder := by
    rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hg
  nth_rw 1 [← X_pow_order_mul_divXPowOrder (f := g)]
  rw [PowerSeries.coe_mul, map_mul, PowerSeries.coe_pow, _root_.LaurentSeries.valuation_X_pow,
    valuation_coe_of_isUnit hu, mul_one]

end Valuation

end TauCeti.LaurentSeries

namespace TauCeti

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:131` (proof source at `5a01f5fe3621`).
 Multiplication by a constant of the Laurent-series algebra structure agrees with the
coefficientwise scalar action, for Laurent series with coefficients in any `R`-algebra. -/
theorem laurentSeries_algebraMap_mul_eq_smul {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (c : R) (f : LaurentSeries A) :
    algebraMap R (LaurentSeries A) c * f = c • f := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, algebraMap_smul]

end TauCeti

namespace PowerSeries

open HahnSeries LaurentSeries

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:145` (proof source at `5a01f5fe3621`).
 The derivative of Laurent series extends the derivative of power series. -/
@[simp]
theorem coe_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) :
    ((d⁄dX f : R⟦X⟧) : R⸨X⸩) = LaurentSeries.derivative R (f : R⸨X⸩) := by
  ext i
  rw [derivative_apply, hasseDeriv_coeff, coeff_coe, coeff_coe]
  rcases i with m | m
  · have hm : ((m : ℤ) + 1).natAbs = m + 1 := by omega
    simp [coeff_derivative, mul_comm, hm, show ¬((m : ℤ) + 1 < 0) by omega]
  · rcases m with _ | m
    · simp
    · simp [Int.negSucc_lt_zero, show Int.negSucc (m + 1) + 1 < 0 by omega]

end PowerSeries

namespace LaurentSeries

open HahnSeries

variable {R : Type*} [CommRing R]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:165` (proof source at `5a01f5fe3621`).
 The product rule for a monomial: `(c X ^ m * f)' = m c X ^ (m - 1) * f + c X ^ m * f'`. -/
theorem derivative_single_mul (m : ℤ) (c : R) (f : R⸨X⸩) :
    derivative R (single m c * f) = single (m - 1) (m * c) * f + single m c * derivative R f := by
  ext n
  simp only [derivative_apply, hasseDeriv_coeff, coeff_add, coeff_single_mul,
    Ring.choose_one_right, zsmul_eq_mul]
  rw [show n - (m - 1) = n + 1 - m by ring, show n - m + (1 : ℕ) = n + 1 - m by push_cast; ring]
  push_cast
  ring

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:176` (proof source at `5a01f5fe3621`).
 The product rule for a monomial times a power series:
`(c X ^ m * φ)' = m c X ^ (m - 1) * φ + c X ^ m * φ'`. -/
theorem derivative_single_mul_coe (m : ℤ) (c : R) (φ : R⟦X⟧) :
    derivative R (single m c * (φ : R⸨X⸩)) =
      single (m - 1) (m * c) * φ + single m c * ((d⁄dX φ : R⟦X⟧) : R⸨X⸩) := by
  rw [derivative_single_mul, ← PowerSeries.coe_derivative]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:182` (proof source at `5a01f5fe3621`).
 **The product rule** for the derivative of Laurent series: `(f * g)' = f' * g + f * g'`. -/
theorem derivative_mul (f g : R⸨X⸩) :
    derivative R (f * g) = derivative R f * g + f * derivative R g := by
  -- Write `f = X ^ a * φ` and `g = X ^ b * ψ` with power series `φ` and `ψ`, so that
  -- `f * g = X ^ (a + b) * (φ * ψ)`, and use the product rule for power series.
  rw [← single_order_mul_powerSeriesPart f, ← single_order_mul_powerSeriesPart g]
  set a := f.order
  set b := g.order
  set φ := f.powerSeriesPart
  set ψ := g.powerSeriesPart
  have hab : (single (a + b) (1 : R) : R⸨X⸩) = single a 1 * single b 1 := by
    rw [single_mul_single, one_mul]
  have hfg : (single a (1 : R) * (φ : R⸨X⸩)) * (single b 1 * (ψ : R⸨X⸩)) =
      single (a + b) 1 * ((φ * ψ : R⟦X⟧) : R⸨X⸩) := by
    rw [PowerSeries.coe_mul, hab]
    ring
  -- The derivative of the monomial `X ^ (a + b)` splits as `(X ^ a)' X ^ b + X ^ a (X ^ b)'`.
  have hd : (single (a + b - 1) (((a + b : ℤ) : R) * 1) : R⸨X⸩) =
      single (a - 1) ((a : R) * 1) * single b 1 + single a 1 * single (b - 1) ((b : R) * 1) := by
    rw [single_mul_single, single_mul_single, show a - 1 + b = a + b - 1 by ring,
      show a + (b - 1) = a + b - 1 by ring, ← single_add]
    push_cast
    ring_nf
  simp only [hfg, derivative_single_mul_coe]
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.coe_add, PowerSeries.coe_mul]
  rw [hd, hab]
  ring

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:211` (proof source at `5a01f5fe3621`).
 The derivative of `f` agrees with `m X⁻¹ f` up to a correction whose coefficient of `Xⁿ` is
`(n + 1 - m)` times the coefficient of `Xⁿ⁺¹` in `f`. -/
theorem coeff_derivative_sub_zsmul_single_mul (m n : ℤ) (f : R⸨X⸩) :
    (derivative R f - m • (single (-1) 1 * f)).coeff n =
      ((n + 1 - m : ℤ) : R) * f.coeff (n + 1) := by
  rw [coeff_sub, coeff_smul, coeff_single_mul, derivative_apply, hasseDeriv_coeff,
    Ring.choose_one_right, sub_neg_eq_add, one_mul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:222` (proof source at `5a01f5fe3621`).
 **Differentiation lowers the order by at most one, with leading term `m X⁻¹ f`.** If `f` has
valuation at most `exp (-m)`, that is, vanishes to order at least `m`, then `f' - m X⁻¹ f` again
vanishes to order at least `m`. -/
theorem valuation_derivative_sub_zsmul_single_mul_le {K : Type*} [Field K] {m : ℤ} {f : K⸨X⸩}
    (hf : Valued.v f ≤ WithZero.exp (-m)) :
    Valued.v (derivative K f - m • (single (-1) 1 * f)) ≤ WithZero.exp (-m) := by
  rw [valuation_le_iff_coeff_lt_eq_zero] at hf ⊢
  intro n hn
  rw [coeff_derivative_sub_zsmul_single_mul]
  -- Below `m - 1` the coefficient of `f` vanishes; at `m - 1` the integer factor does.
  rcases lt_or_eq_of_le (show n + 1 ≤ m by omega) with h | h
  · rw [hf _ h, mul_zero]
  · simp [h]

end LaurentSeries

namespace PowerSeries

open HahnSeries LaurentSeries

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:242` (proof source at `5a01f5fe3621`).
 **The residue of `φ ^ n dφ`.** For a power series `φ` of order one over a field, the
coefficient of `X⁻¹` in the Laurent series `φ ^ n * φ'` is `1` if `n = -1` and `0` otherwise.
Equivalently, the residue of `X ^ n dX` is unchanged by the substitution `X ↦ φ`. -/
theorem coeff_neg_one_coe_zpow_mul_derivative {k : Type*} [Field k] {φ : k⟦X⟧} (hφ : φ.order = 1)
    (n : ℤ) :
    ((φ : k⸨X⸩) ^ n * LaurentSeries.derivative k (φ : k⸨X⸩)).coeff (-1) =
      if n = -1 then 1 else 0 := by
  rw [← coe_derivative]
  rcases n with m | m
  · -- For `n ≥ 0` the product is a power series.
    rw [Int.ofNat_eq_natCast, zpow_natCast, ← coe_pow, ← coe_mul, coeff_coe]
    simp [show (m : ℤ) ≠ -1 by omega]
  · -- Write `φ = X * u` with `u` a unit power series.
    obtain ⟨u, hu0, rfl⟩ : ∃ u : k⟦X⟧, constantCoeff u ≠ 0 ∧ φ = X * u := by
      refine ⟨φ.divXPowOrder, ?_, ?_⟩
      · rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]
        rintro rfl
        simp at hφ
      · conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := φ)]
        simp [hφ]
    have hvu : u⁻¹ * u = 1 := PowerSeries.inv_mul_cancel u hu0
    have hinv : (((X * u : k⟦X⟧) : k⸨X⸩) ^ (m + 1))⁻¹ =
        single (-((m + 1 : ℕ) : ℤ)) (1 : k) * ((u⁻¹ ^ (m + 1) : k⟦X⟧) : k⸨X⸩) := by
      refine inv_eq_of_mul_eq_one_right ?_
      -- Cancel `u` in `k⟦X⟧`, then cancel `X ^ (m + 1)` against `single (-(m + 1)) 1`.
      have hX : (X * u) ^ (m + 1) * u⁻¹ ^ (m + 1) = X ^ (m + 1) := by
        rw [mul_pow, mul_assoc, ← mul_pow, mul_comm u, hvu, one_pow, mul_one]
      rw [← coe_pow, mul_left_comm, ← coe_mul, hX, ofPowerSeries_X_pow]
      simp
    rw [zpow_negSucc, hinv, mul_assoc, ← coe_mul, coeff_single_mul, one_mul, coeff_coe,
      ite_eq_right (show ¬(-1 - -((m + 1 : ℕ) : ℤ) < 0) by omega),
      show (-1 - -((m + 1 : ℕ) : ℤ)).natAbs = m by omega]
    -- Since `u⁻¹ * u = 1`, `u⁻¹ ^ (m + 1) * (X * u)'` is `u⁻¹ ^ m + X * u⁻¹ ^ (m + 1) * u'`.
    have hd : u⁻¹ ^ (m + 1) * d⁄dX (X * u) = u⁻¹ ^ m + X * (u⁻¹ ^ (m + 1) * d⁄dX u) := by
      rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul, mul_one, pow_succ]
      linear_combination u⁻¹ ^ m * hvu
    rw [hd, map_add]
    rcases m with _ | m
    · simp
    · -- Since `(u⁻¹)' = -(u⁻¹) ^ 2 * u'`, the remaining coefficient is that of
      -- `u⁻¹ ^ (m + 1) - X * u⁻¹ ^ m * (u⁻¹)'`, which vanishes by
      -- `coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`.
      have hv : u⁻¹ ^ (m + 2) * d⁄dX u = -(u⁻¹ ^ m * d⁄dX u⁻¹) := by
        rw [derivative_inv']
        ring
      rw [hv, coeff_succ_X_mul, map_neg, ← coeff_succ_pow_succ_eq_coeff_pow_mul_derivative]
      simp [show Int.negSucc (m + 1) ≠ -1 by omega]

end PowerSeries

namespace LaurentSeries

open HahnSeries

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Basic.lean:297` (proof source at `5a01f5fe3621`).
 **Residues are invariant under substitution.** Let `ψ` be a ring endomorphism of `K⸨X⸩`
fixing the constants, sending power series to power series, and sending `X` to a power series `φ`
of order one, such as the substitution `X ↦ φ`. Then the coefficient of `X⁻¹` in `ψ f * φ'` is
the coefficient of `X⁻¹` in `f`: the residue of `f(X) dX` equals that of `f(φ) dφ`. -/
theorem coeff_neg_one_map_mul_derivative {K : Type*} [Field K] (ψ : K⸨X⸩ →+* K⸨X⸩)
    (hC : ∀ c : K, ψ (C c) = C c)
    (hψ : ∀ f : K⸨X⸩, Valued.v f ≤ 1 → Valued.v (ψ f) ≤ 1) {φ : K⟦X⟧} (hφ : φ.order = 1)
    (hX : ψ (single 1 1) = φ) (f : K⸨X⸩) :
    (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = f.coeff (-1) := by
  -- Both sides vanish on power series.
  have base (f : K⸨X⸩) (hf : Valued.v f ≤ 1) :
      (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = f.coeff (-1) := by
    obtain ⟨F, rfl⟩ := (val_le_one_iff_eq_coe K f).mp hf
    obtain ⟨G, hG⟩ := (val_le_one_iff_eq_coe K (ψ F)).mp (hψ F hf)
    rw [← hG, ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, PowerSeries.coeff_coe,
      PowerSeries.coeff_coe]
    simp
  -- Both sides agree on monomials, by the residue of `φ ^ j * φ'`.
  have mono (j : ℤ) (c : K) :
      (ψ (single j c) * derivative K (φ : K⸨X⸩)).coeff (-1) = (single j c : K⸨X⸩).coeff (-1) := by
    -- The substitution sends `c X ^ j` to `c φ ^ j`.
    have h : ψ (single j c) = C c * (φ : K⸨X⸩) ^ j := by
      rw [← hC, ← hX, ← map_zpow₀, ← map_mul]
      simp [← RatFunc.single_zpow]
    rw [h, mul_assoc, C_mul_eq_smul, coeff_smul,
      PowerSeries.coeff_neg_one_coe_zpow_mul_derivative hφ]
    simp [coeff_single, eq_comm]
  -- Induction on the order of the pole.
  have key (d : ℕ) (f : K⸨X⸩) (hf : Valued.v f ≤ WithZero.exp (d : ℤ)) :
      (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1) = f.coeff (-1) := by
    induction d generalizing f with
    | zero => exact base f (by simpa using hf)
    | succ d ih =>
      set s : K⸨X⸩ := single (-((d + 1 : ℕ) : ℤ)) (f.coeff (-((d + 1 : ℕ) : ℤ)))
      have hg : Valued.v (f - s) ≤ WithZero.exp (d : ℤ) := by
        rw [← neg_neg (d : ℤ), valuation_le_iff_coeff_lt_eq_zero]
        intro n hn
        rw [← neg_neg ((d + 1 : ℕ) : ℤ), valuation_le_iff_coeff_lt_eq_zero] at hf
        rw [coeff_sub]
        rcases lt_or_eq_of_le (show n ≤ -((d + 1 : ℕ) : ℤ) by omega) with h | rfl
        · rw [hf n h, coeff_single_of_ne h.ne, sub_zero]
        · rw [coeff_single_same, sub_self]
      calc (ψ f * derivative K (φ : K⸨X⸩)).coeff (-1)
          = (ψ (f - s) * derivative K (φ : K⸨X⸩)).coeff (-1) +
              (ψ s * derivative K (φ : K⸨X⸩)).coeff (-1) := by
            rw [map_sub, sub_mul, coeff_sub, sub_add_cancel]
        _ = f.coeff (-1) := by rw [ih _ hg, mono, coeff_sub, sub_add_cancel]
  refine key (-f.order).toNat f ?_
  rw [← neg_neg ((-f.order).toNat : ℤ), valuation_le_iff_coeff_lt_eq_zero]
  exact fun n hn ↦ coeff_eq_zero_of_lt_order (by omega)

end LaurentSeries
end

end

/-! ## Source 33: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Series`
Original source SHA256: `374b09e280f77563ae23d317f0afc52c192721d6b880e18a2dd9a28f37a32812`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Laurent-series expansions at rational places

The completion of a function field at a rational place is isomorphic to the Laurent-series field
over the constant field.  The isomorphism is the fraction-field extension of the uniformizer
expansion of the completed valuation ring, so it sends a chosen uniformizer to `X` and restricts
to the previously constructed power-series expansion on integral elements.

This supplies the local Laurent coefficients used to define residues of differentials.  Keeping
the construction as the canonical fraction-field extension makes its behaviour on quotients and
on the valuation ring available without choosing numerator-denominator presentations.

## Main results

* `TauCeti.Place.completionEquivLaurentSeries`: the completed local field is `k((X))`.
* `TauCeti.Place.completionEquivLaurentSeries_apply_integer`: the equivalence restricts to the
  power-series expansion on the completed valuation ring.
* `TauCeti.Place.completionEquivLaurentSeries_uniformizer`: a chosen uniformizer maps to `X`.
* `TauCeti.Place.valuation_algEquivOfAlgEquiv`: the fraction-field extension of any
  power-series expansion of the completed valuation ring preserves the valuation.
* `TauCeti.Place.completionLaurentCoeff_ext_iff`: Laurent coefficients determine a completed
  element.
* `TauCeti.Place.completionResidue_completionEquivLaurentSeries_symm_derivative`:
  completed residues kill formal derivatives.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section IV.2.
-/

section
open scoped LaurentSeries WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-! ### Fraction-field extensions of power-series expansions -/

section FractionField

variable {A : Type*} [Field A] [Algebra k A] (e : P.completionPlace.integers ≃ₐ[k] PowerSeries A)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:58` (proof source at `5a01f5fe3621`).
 The fraction-field extension of an isomorphism of the completed valuation ring with a
power-series ring sends exactly the completed integral elements to power series. -/
theorem exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers (z : P.Completion) :
    (∃ f : PowerSeries A, (f : LaurentSeries A) =
        (IsFractionRing.algEquivOfAlgEquiv e : P.Completion ≃ₐ[k] LaurentSeries A) z) ↔
      z ∈ P.completionPlace.integers := by
  let e' : P.Completion ≃ₐ[k] LaurentSeries A := IsFractionRing.algEquivOfAlgEquiv e
  have he' (x : P.completionPlace.integers) : e' x = (e x : LaurentSeries A) :=
    IsFractionRing.algEquivOfAlgEquiv_algebraMap e x
  constructor
  · rintro ⟨f, hf⟩
    have hz : z = (e.symm f : P.Completion) :=
      e'.injective (by rw [he', AlgEquiv.apply_symm_apply, hf])
    exact hz ▸ Subtype.property _
  · exact fun hz ↦ ⟨e ⟨z, hz⟩, (he' ⟨z, hz⟩).symm⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:74` (proof source at `5a01f5fe3621`).
 The fraction-field extension of an isomorphism of the completed valuation ring with a
power-series ring over a field preserves the normalized valuation. -/
theorem valuation_algEquivOfAlgEquiv (x : P.Completion) :
    Valued.v ((IsFractionRing.algEquivOfAlgEquiv e : P.Completion ≃ₐ[k] LaurentSeries A) x) =
      P.completionPlace.valuation x := by
  let e' : P.Completion ≃ₐ[k] LaurentSeries A := IsFractionRing.algEquivOfAlgEquiv e
  let w : Valuation (LaurentSeries A) ℤᵐ⁰ := Valued.v
  have hequiv : P.completionPlace.valuation.IsEquiv (w.comap e'.toRingEquiv.toRingHom) := by
    apply Valuation.isEquiv_of_val_le_one
    intro z
    rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      LaurentSeries.val_le_one_iff_eq_coe]
    exact P.completionPlace.mem_integers_iff.symm.trans
      (P.exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers e z).symm
  have hsurj : Function.Surjective (w.comap e'.toRingEquiv.toRingHom) := by
    intro γ
    obtain ⟨y, hy⟩ := LaurentSeries.valuation_surjective A γ
    exact ⟨e'.symm y, by simpa [Valuation.comap_apply] using hy⟩
  exact DFunLike.congr_fun (Valuation.eq_of_isEquiv_of_surjective
    P.completionPlace.valuation_surjective hsurj hequiv).symm x

end FractionField

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:98` (proof source at `5a01f5fe3621`).
 **Laurent-series expansion at a rational place.**  A chosen uniformizer identifies the
completion of the local function field with the Laurent-series field over the constants.  This is
the fraction-field extension of `TauCeti.Place.completionIntegersEquivPowerSeries`. -/
noncomputable def completionEquivLaurentSeries : P.Completion ≃ₐ[k] LaurentSeries k :=
  IsFractionRing.algEquivOfAlgEquiv (P.completionIntegersEquivPowerSeries hP ht)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:104` (proof source at `5a01f5fe3621`).
 Laurent-series expansion restricts to power-series expansion on the completed valuation
ring. -/
@[simp]
theorem completionEquivLaurentSeries_apply_integer (x : P.completionPlace.integers) :
    P.completionEquivLaurentSeries hP ht (x : P.Completion) =
      (P.completionIntegersEquivPowerSeries hP ht x : LaurentSeries k) := by
  rw [completionEquivLaurentSeries]
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap _ x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:112` (proof source at `5a01f5fe3621`).
 The inverse Laurent-series expansion restricts to the inverse power-series expansion. -/
@[simp]
theorem completionEquivLaurentSeries_symm_apply_powerSeries (f : PowerSeries k) :
    (P.completionEquivLaurentSeries hP ht).symm (f : LaurentSeries k) =
      ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) := by
  apply (P.completionEquivLaurentSeries hP ht).injective
  rw [AlgEquiv.apply_symm_apply, P.completionEquivLaurentSeries_apply_integer]
  simp

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:122` (proof source at `5a01f5fe3621`).
 A completed function is integral exactly when its Laurent expansion comes from a power
series. -/
@[simp]
theorem exists_powerSeries_eq_completionEquivLaurentSeries_iff_mem_integers
    (z : P.Completion) :
    (∃ f : PowerSeries k, (f : LaurentSeries k) = P.completionEquivLaurentSeries hP ht z) ↔
      z ∈ P.completionPlace.integers :=
  P.exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers _ z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:130` (proof source at `5a01f5fe3621`).
 The chosen uniformizer maps to the Laurent-series variable. -/
@[simp]
theorem completionEquivLaurentSeries_uniformizer :
    P.completionEquivLaurentSeries hP ht (P.completionEmbedding t) =
      ((PowerSeries.X : PowerSeries k) : LaurentSeries k) := by
  let t₀ : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  let tᵢ : P.completionPlace.integers := P.completionIntegersEmbedding t₀
  rw [← show (tᵢ : P.Completion) = P.completionEmbedding t by
      exact P.completionIntegersEmbedding_apply t₀,
    P.completionEquivLaurentSeries_apply_integer]
  exact congrArg ((↑) : PowerSeries k → LaurentSeries k)
    (P.completionIntegersEquivPowerSeries_uniformizer hP ht)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:144` (proof source at `5a01f5fe3621`).
 Laurent-series expansion preserves the normalized valuation.  Thus the power of `X` at the
first nonzero Laurent coefficient is the order at the original place. -/
@[simp]
theorem valuation_completionEquivLaurentSeries (x : P.Completion) :
    Valued.v (P.completionEquivLaurentSeries hP ht x) = P.completionPlace.valuation x :=
  P.valuation_algEquivOfAlgEquiv _ x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:151` (proof source at `5a01f5fe3621`).
 Laurent-series expansion preserves the additive order, including its conventional junk value
`0` at the zero element. -/
@[simp]
theorem ord_completionEquivLaurentSeries (x : P.Completion) :
    Valuation.ord (show Valuation (LaurentSeries k) ℤᵐ⁰ from Valued.v)
        (P.completionEquivLaurentSeries hP ht x) =
      P.completionPlace.ord x := by
  rw [Valuation.ord_def, ord_def, P.valuation_completionEquivLaurentSeries hP ht]

/-! ### Completed Laurent coefficients and residues -/

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:161` (proof source at `5a01f5fe3621`).
 The `n`-th Laurent coefficient on the completed local field, with respect to the uniformizer
`t`. -/
noncomputable def completionLaurentCoeff (n : ℤ) : P.Completion →ₗ[k] k :=
  -- `toLinearMap` targets `Algebra.toModule`, but `coeff.linearMap` expects
  -- `HahnSeries.instModule`; these are not definitionally equal. This scalar bridge
  -- supplies the coefficientwise module structure without changing the public maps.
  (HahnSeries.coeff.linearMap n).comp
    ({ toFun := (P.completionEquivLaurentSeries hP ht).toAlgHom
       map_add' := (P.completionEquivLaurentSeries hP ht).toAlgHom.map_add
       map_smul' := fun c z => by
         rw [Algebra.smul_def, map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply',
           PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
           RingHom.id_apply] } : P.Completion →ₗ[k] LaurentSeries k)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:176` (proof source at `5a01f5fe3621`).
 The completed Laurent coefficient is the corresponding coefficient of the Laurent-series
expansion. -/
@[simp]
theorem completionLaurentCoeff_apply (n : ℤ) (z : P.Completion) :
    P.completionLaurentCoeff hP ht n z =
      (P.completionEquivLaurentSeries hP ht z).coeff n :=
  (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:183` (proof source at `5a01f5fe3621`).
 Elements of the completed local field are equal exactly when all their Laurent coefficients
are equal. -/
theorem completionLaurentCoeff_ext_iff {x y : P.Completion} :
    x = y ↔ ∀ n : ℤ,
      P.completionLaurentCoeff hP ht n x = P.completionLaurentCoeff hP ht n y := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply (P.completionEquivLaurentSeries hP ht).injective
    apply HahnSeries.ext
    funext n
    simpa only [completionLaurentCoeff_apply] using h n

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:196` (proof source at `5a01f5fe3621`).
 The coefficient of a Laurent monomial is zero away from its exponent. -/
theorem completionLaurentCoeff_completionEquivLaurentSeries_symm_single (m n : ℤ) (c : k) :
    P.completionLaurentCoeff hP ht n
        ((P.completionEquivLaurentSeries hP ht).symm (HahnSeries.single m c)) =
      if n = m then c else 0 := by
  simp [completionLaurentCoeff_apply, HahnSeries.coeff_single]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:204` (proof source at `5a01f5fe3621`).
 The negative Laurent coefficients of an integral element of the completed local field
vanish. -/
theorem completionLaurentCoeff_coe_integer_eq_zero (z : P.completionPlace.integers)
    {n : ℤ} (hn : n < 0) :
    P.completionLaurentCoeff hP ht n (z : P.Completion) = 0 := by
  rw [completionLaurentCoeff_apply]
  apply LaurentSeries.coeff_zero_of_lt_valuation k (D := 0) _ hn
  rw [valuation_completionEquivLaurentSeries]
  simpa using P.completionPlace.mem_integers_iff.mp z.2

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:213` (proof source at `5a01f5fe3621`).
 The completed residue with respect to `t`, given by the coefficient of exponent `-1`. -/
noncomputable def completionResidue : P.Completion →ₗ[k] k :=
  P.completionLaurentCoeff hP ht (-1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:218` (proof source at `5a01f5fe3621`).
 The completed residue is the coefficient of exponent `-1`. -/
@[simp]
theorem completionResidue_apply (z : P.Completion) :
    P.completionResidue hP ht z =
      (P.completionEquivLaurentSeries hP ht z).coeff (-1) :=
  (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:224` (proof source at `5a01f5fe3621`).
 The completed residue vanishes on the completed valuation ring. -/
theorem completionResidue_coe_integer_eq_zero
    (z : P.completionPlace.integers) :
    P.completionResidue hP ht (z : P.Completion) = 0 :=
  P.completionLaurentCoeff_coe_integer_eq_zero hP ht z (by omega)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Series.lean:231` (proof source at `5a01f5fe3621`).
 The coefficient of `X⁻¹` in the formal derivative of a Laurent series is zero.  Equivalently,
the local residue kills formal derivatives. -/
theorem completionResidue_completionEquivLaurentSeries_symm_derivative (f : LaurentSeries k) :
    P.completionResidue hP ht
        ((P.completionEquivLaurentSeries hP ht).symm (LaurentSeries.derivative k f)) = 0 := by
  simp [completionResidue_apply, LaurentSeries.derivative_apply]

end TauCeti.Place
end

end

/-! ## Source 34: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic`
Original source SHA256: `e2a48c6ee96996d08f107384adf590eed9848ae62c103be4479f74843301dc0c`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Laurent expansions and residues at rational places

Let `P` be a rational place of `F / k` and let `t` have order one at `P`. Passing to fraction
fields, the identification of the completed valuation ring with `k[[T]]` becomes a
`k`-algebra isomorphism of the completion of `F` at `P` with the Laurent-series field
`k((T))`, sending `t` to `T`. It carries the valuation of `P` to the `T`-adic valuation.

Composing with the completion map gives the Laurent expansion of every function in `F`.
Its coefficients below `m` depend only on the function modulo the `m`-th order filtration,
and a finite sum `∑ cᵢ tⁱ` congruent to the function modulo that filtration has exactly the
coefficients `cᵢ`. The coefficient of `T⁻¹` is the residue `res_{P,t}` of a function with
respect to `t`. It vanishes on functions integral at `P` and is read off the power-series
expansion of `t ^ (n + 1) * z` whenever this product is integral.

## Main definitions

* `TauCeti.Place.completionEquivLaurentSeries`: the completion at a rational place is `k((T))`.
* `TauCeti.Place.laurentSeriesExpansion`: the Laurent expansion of functions at `P` in `t`.
* `TauCeti.Place.residue`: the residue `res_{P,t}`, the coefficient of `t⁻¹`.

## Main results

* `TauCeti.Place.valuation_completionEquivLaurentSeries`: the isomorphism with `k((T))`
  identifies the valuation of `P` with the `T`-adic valuation.
* `TauCeti.Place.coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration`: uniqueness of
  finite Laurent expansions.
* `TauCeti.Place.residue_eq_coeff_powerSeriesExpansion`: the residue as a power-series
  coefficient.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Definition 4.2.8.
-/

section
open scoped WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-! ### Laurent expansions of functions -/

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:59` (proof source at `5a01f5fe3621`).
 The Laurent expansion of a function at a rational place in a chosen uniformizer: the image
of the function under completion and `TauCeti.Place.completionEquivLaurentSeries`. -/
noncomputable def laurentSeriesExpansion : F →ₐ[k] LaurentSeries k :=
  (P.completionEquivLaurentSeries hP ht).toAlgHom.comp P.completionEmbedding

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:64` (proof source at `5a01f5fe3621`).
 The Laurent expansion of a function is the Laurent expansion of its image in the
completion. -/
theorem laurentSeriesExpansion_apply (z : F) :
    P.laurentSeriesExpansion hP ht z =
      P.completionEquivLaurentSeries hP ht (P.completionEmbedding z) := (rfl)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:69` (proof source at `5a01f5fe3621`).
 The `n`-th Laurent coefficient of a function at the rational place, with respect to `t`. -/
noncomputable def laurentCoeff (n : ℤ) : F →ₗ[k] k :=
  (P.completionLaurentCoeff hP ht n).comp P.completionEmbedding.toLinearMap

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:74` (proof source at `5a01f5fe3621`).
 The Laurent coefficient is the corresponding coefficient of the Laurent expansion. -/
@[simp]
theorem laurentCoeff_apply (n : ℤ) (z : F) :
    P.laurentCoeff hP ht n z = (P.laurentSeriesExpansion hP ht z).coeff n := by
  rw [laurentCoeff, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    completionLaurentCoeff_apply, laurentSeriesExpansion_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:81` (proof source at `5a01f5fe3621`).
 Completion preserves the Laurent coefficients of a function. -/
-- Not `@[simp]`: `completionLaurentCoeff_apply` already simplifies the left-hand side.
theorem completionLaurentCoeff_completionEmbedding (n : ℤ) (z : F) :
    P.completionLaurentCoeff hP ht n (P.completionEmbedding z) =
      P.laurentCoeff hP ht n z :=
  (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:88` (proof source at `5a01f5fe3621`).
 The Laurent expansion of an integral function is its power-series expansion. -/
@[simp]
theorem laurentSeriesExpansion_coe (x : P.integers) :
    P.laurentSeriesExpansion hP ht x =
      HahnSeries.ofPowerSeries ℤ k (P.powerSeriesExpansion hP ht x) := by
  rw [laurentSeriesExpansion_apply, ← P.completionIntegersEmbedding_apply,
    completionEquivLaurentSeries_apply_integer,
    completionIntegersEquivPowerSeries_completionIntegersEmbedding]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:98` (proof source at `5a01f5fe3621`).
 Every integer power of the chosen uniformizer expands as the corresponding monomial. -/
-- The left side already simplifies by `map_zpow₀` and `laurentSeriesExpansion_uniformizer`.
-- A `simp` annotation here is rejected by the `simpNF` linter.
theorem laurentSeriesExpansion_zpow_uniformizer (n : ℤ) :
    P.laurentSeriesExpansion hP ht (t ^ n) = HahnSeries.single n 1 := by
  rw [map_zpow₀, laurentSeriesExpansion_apply,
    completionEquivLaurentSeries_uniformizer, HahnSeries.ofPowerSeries_X]
  exact (RatFunc.single_zpow n).symm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:106` (proof source at `5a01f5fe3621`).
 The chosen uniformizer expands as the Laurent variable `T`. -/
@[simp]
theorem laurentSeriesExpansion_uniformizer :
    P.laurentSeriesExpansion hP ht t = HahnSeries.single 1 1 := by
  simpa using P.laurentSeriesExpansion_zpow_uniformizer hP ht 1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:112` (proof source at `5a01f5fe3621`).
 Laurent expansion carries the valuation of `P` to the `T`-adic valuation. -/
@[simp]
theorem valuation_laurentSeriesExpansion (z : F) :
    Valued.v (P.laurentSeriesExpansion hP ht z) = P.valuation z := by
  rw [laurentSeriesExpansion_apply, valuation_completionEquivLaurentSeries,
    completionPlace_valuation, valuation_completionEmbedding]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:118` (proof source at `5a01f5fe3621`).
 A function vanishing to order at least `m` has no Laurent coefficients below `m`. -/
theorem coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansion hP ht z).coeff i = 0 := by
  apply LaurentSeries.coeff_zero_of_lt_valuation k _ hi
  rwa [valuation_laurentSeriesExpansion, ← mem_filtration_iff]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:126` (proof source at `5a01f5fe3621`).
 The Laurent coefficients below `m` depend only on the function modulo the `m`-th order
filtration. -/
theorem coeff_laurentSeriesExpansion_eq_of_sub_mem_filtration {m : ℤ} {z w : F}
    (h : z - w ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansion hP ht z).coeff i = (P.laurentSeriesExpansion hP ht w).coeff i := by
  have h0 := P.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration hP ht h hi
  rwa [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h0

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:133` (proof source at `5a01f5fe3621`).
 A finite Laurent polynomial in the uniformizer expands with its own coefficients. -/
theorem coeff_laurentSeriesExpansion_sum (s : Finset ℤ) (c : ℤ → k) (i : ℤ) :
    (P.laurentSeriesExpansion hP ht (∑ j ∈ s, algebraMap k F (c j) * t ^ j)).coeff i =
      if i ∈ s then c i else 0 := by
  -- `HahnSeries.coeff_single` is stated with classical decidability of equality.
  simp only [map_sum, map_mul, AlgHom.commutes, laurentSeriesExpansion_zpow_uniformizer,
    HahnSeries.coeff_sum, TauCeti.LaurentSeries.coeff_algebraMap_mul, HahnSeries.coeff_single,
    mul_ite, mul_one, mul_zero]
  convert Finset.sum_ite_eq s i c

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:145` (proof source at `5a01f5fe3621`).
 Uniqueness of finite Laurent expansions: if a function agrees with `∑ cⱼ tʲ` modulo the
`m`-th order filtration, then its Laurent coefficients below `m` are the `cⱼ`, read as zero
outside the summation range. -/
theorem coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration {m : ℤ} {z : F}
    (s : Finset ℤ) (c : ℤ → k) (h : z - ∑ j ∈ s, algebraMap k F (c j) * t ^ j ∈ P.filtration m)
    {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansion hP ht z).coeff i = if i ∈ s then c i else 0 := by
  rw [P.coeff_laurentSeriesExpansion_eq_of_sub_mem_filtration hP ht h hi,
    coeff_laurentSeriesExpansion_sum]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:154` (proof source at `5a01f5fe3621`).
 Multiplying by `t ^ n` to make a function integral shifts its Laurent coefficients onto
the coefficients of a power-series expansion. -/
theorem coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion (n : ℤ) {z : F}
    (hz : t ^ n * z ∈ P.integers) (i : ℕ) :
    (P.laurentSeriesExpansion hP ht z).coeff ((i : ℤ) - n) =
      PowerSeries.coeff i (P.powerSeriesExpansion hP ht ⟨t ^ n * z, hz⟩) := by
  rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), ← laurentSeriesExpansion_coe]
  -- Reduce the coercion of the anonymous-constructor element of `P.integers`.
  dsimp only
  rw [map_mul, laurentSeriesExpansion_zpow_uniformizer,
    HahnSeries.coeff_single_mul, one_mul]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:166` (proof source at `5a01f5fe3621`).
 Functions are equal exactly when all coefficients of their Laurent expansions at a rational
place agree. -/
theorem laurentCoeff_ext_iff {x y : F} :
    x = y ↔ ∀ n : ℤ, P.laurentCoeff hP ht n x = P.laurentCoeff hP ht n y := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply P.completionEmbedding.injective
    apply (P.completionLaurentCoeff_ext_iff hP ht).2
    intro n
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      completionLaurentCoeff_completionEmbedding] using h n

/-! ### Residues -/

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:183` (proof source at `5a01f5fe3621`).
 The residue `res_{P,t}` of a function at a rational place with respect to a chosen
uniformizer: the coefficient of `t⁻¹` in its Laurent expansion (Stichtenoth,
Definition 4.2.8). It is `k`-linear. -/
noncomputable def residue : F →ₗ[k] k :=
  (P.completionResidue hP ht).comp P.completionEmbedding.toLinearMap

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:187` (proof source at `5a01f5fe3621`).
 The residue is the coefficient of `T⁻¹` in the Laurent expansion. -/
theorem residue_apply (z : F) :
    P.residue hP ht z = (P.laurentSeriesExpansion hP ht z).coeff (-1) := by
  rw [residue, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    completionResidue_apply, laurentSeriesExpansion_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:194` (proof source at `5a01f5fe3621`).
 Completion preserves the residue of a function at the chosen uniformizer. -/
-- Not `@[simp]`: `completionResidue_apply` already simplifies the left-hand side.
theorem completionResidue_completionEmbedding (z : F) :
    P.completionResidue hP ht (P.completionEmbedding z) = P.residue hP ht z := by
  rw [completionResidue_apply, residue_apply, laurentSeriesExpansion_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:199` (proof source at `5a01f5fe3621`).
 Functions integral at the place have residue zero. -/
theorem residue_eq_zero_of_mem_integers {z : F} (hz : z ∈ P.integers) :
    P.residue hP ht z = 0 := by
  rw [residue_apply]
  exact P.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration hP ht
    (P.mem_filtration_zero_iff.mpr hz) (by omega)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:206` (proof source at `5a01f5fe3621`).
 The residue depends only on the function modulo integral functions. -/
theorem residue_eq_of_sub_mem_integers {z w : F} (h : z - w ∈ P.integers) :
    P.residue hP ht z = P.residue hP ht w := by
  rw [← sub_eq_zero, ← map_sub, P.residue_eq_zero_of_mem_integers hP ht h]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:212` (proof source at `5a01f5fe3621`).
 The residue of an integer power of the uniformizer. -/
@[simp]
theorem residue_zpow_uniformizer (n : ℤ) :
    P.residue hP ht (t ^ n) = if n = -1 then 1 else 0 := by
  rw [residue_apply, laurentSeriesExpansion_zpow_uniformizer, HahnSeries.coeff_single]
  simp only [eq_comm]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:219` (proof source at `5a01f5fe3621`).
 The inverse of the uniformizer has residue one. -/
@[simp]
theorem residue_inv_uniformizer : P.residue hP ht t⁻¹ = 1 := by
  simpa using P.residue_zpow_uniformizer hP ht (-1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Basic.lean:224` (proof source at `5a01f5fe3621`).
 If `t ^ (n + 1) * z` is integral, the residue of `z` is the degree-`n` coefficient of the
power-series expansion of `t ^ (n + 1) * z`. -/
theorem residue_eq_coeff_powerSeriesExpansion (n : ℕ) {z : F}
    (hz : t ^ (n + 1) * z ∈ P.integers) :
    P.residue hP ht z =
      PowerSeries.coeff n (P.powerSeriesExpansion hP ht ⟨t ^ (n + 1) * z, hz⟩) := by
  have h := P.coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion
    hP ht ((n + 1 : ℕ) : ℤ)
    (by simpa only [zpow_natCast] using hz) n
  simp only [zpow_natCast] at h
  rw [residue_apply, ← h]
  congr 1
  omega

end TauCeti.Place
end

end

/-! ## Source 35: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.CoefficientField`
Original source SHA256: `1880c8ffcacb82cb2ec7f878fb4c0a3a36155ce023a2e9d9eff09143b115a5c4`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Laurent expansions and residues at places with separable residue field

Let `P` be a place of `F / k` whose residue field `F_P` is separable over `k`, and let `t` have
order one at `P`. The identification of the completed valuation ring with `F_P[[T]]` through the
coefficient field (`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`) extends to
fraction fields: the completion of `F` at `P` is the Laurent-series field `F_P((T))`, with `t`
sent to `T`. Every function `z ∈ F` therefore has a Laurent expansion `∑ aᵢ tⁱ` with
coefficients `aᵢ ∈ F_P`, and its coefficient of `t⁻¹` is the residue `res_{P,t}(z) ∈ F_P`.
Composing with the trace of `F_P / k` gives a `k`-valued residue, the form in which residues at
places of arbitrary degree enter the residue theorem and the comparison of Weil differentials with
differentials.

At a rational place the coefficient field is `k` itself, and these expansions and residues are
the ones of `TauCeti.Place.laurentSeriesExpansion` and `TauCeti.Place.residue`, read in `F_P`
(`TauCeti.Place.residueResidueField_eq_algebraMap_residue`); the trace of the residue is then the
residue (`TauCeti.Place.traceResidue_eq_residue`).

## Main definitions

* `TauCeti.Place.completionEquivLaurentSeriesResidueField`: the completion at `P` is `F_P((T))`.
* `TauCeti.Place.laurentSeriesExpansionResidueField`: the Laurent expansion of functions at `P`
  in `t`, with coefficients in `F_P`.
* `TauCeti.Place.residueResidueField`: the residue `res_{P,t} : F → F_P`, the coefficient of
  `t⁻¹`.
* `TauCeti.Place.traceResidue`: the `k`-valued residue `Tr_{F_P/k} ∘ res_{P,t}`.
* `TauCeti.Place.traceResidue_mul_inv_uniformizer`: for an integral numerator `u`, the
  `k`-valued residue of `u / t` is the trace of its value at `P`.

## Main results

* `TauCeti.Place.mem_filtration_iff_le_order_powerSeriesExpansionResidueField`: a regular
  function vanishes to order `n` exactly when its expansion has order at least `n`.
* `TauCeti.Place.exists_trunc_powerSeriesExpansionResidueField_eq`: every power series over
  `F_P` is the expansion of a regular function up to any prescribed order.
* `TauCeti.Place.valuation_laurentSeriesExpansionResidueField`: Laurent expansion carries the
  valuation of `P` to the `T`-adic valuation.
* `TauCeti.Place.coeff_zero_laurentSeriesExpansionResidueField`: the constant coefficient of a
  function regular at `P` is its value at `P`.
* `TauCeti.Place.residueResidueField_mul_inv_uniformizer`: `res_{P,t}(u / t) = u(P)` for `u`
  regular at `P`.
* `TauCeti.Place.residueResidueField_eq_algebraMap_residue` and
  `TauCeti.Place.traceResidue_eq_residue`: at a rational place these residues are the residue
  `TauCeti.Place.residue` with coefficients in `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Definition 4.2.8, and Remark 4.3.7.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

section
open scoped LaurentSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)
  [Algebra.IsSeparable k P.ResidueField]

/-! ### Laurent expansions in the completion -/

section Completion

variable {t : P.Completion} (ht : P.completionPlace.ord t = 1)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:82` (proof source at `5a01f5fe3621`).
 **The completion at a place with separable residue field is `F_P((T))`.** A uniformizer `t`
of the completion identifies it with the Laurent-series field over the residue field, sending `t`
to `T`; this is the fraction-field extension of
`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`. -/
noncomputable def completionEquivLaurentSeriesResidueField :
    P.Completion ≃ₐ[k] LaurentSeries P.ResidueField :=
  IsFractionRing.algEquivOfAlgEquiv (P.completionIntegersEquivPowerSeriesResidueField ht)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:89` (proof source at `5a01f5fe3621`).
 Laurent-series expansion restricts to power-series expansion on the completed valuation
ring. -/
@[simp]
theorem completionEquivLaurentSeriesResidueField_apply_integer
    (x : P.completionPlace.integers) :
    P.completionEquivLaurentSeriesResidueField ht (x : P.Completion) =
      (P.completionIntegersEquivPowerSeriesResidueField ht x :
        LaurentSeries P.ResidueField) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:98` (proof source at `5a01f5fe3621`).
 A completed function is integral exactly when its Laurent expansion comes from a power
series. -/
theorem exists_powerSeries_eq_completionEquivLaurentSeriesResidueField_iff_mem_integers
    (z : P.Completion) :
    (∃ f : PowerSeries P.ResidueField,
        (f : LaurentSeries P.ResidueField) = P.completionEquivLaurentSeriesResidueField ht z) ↔
      z ∈ P.completionPlace.integers :=
  P.exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers _ z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:107` (proof source at `5a01f5fe3621`).
 The uniformizer expands as the Laurent variable `T`. -/
@[simp]
theorem completionEquivLaurentSeriesResidueField_uniformizer :
    P.completionEquivLaurentSeriesResidueField ht t = HahnSeries.single 1 1 := by
  have h := P.completionEquivLaurentSeriesResidueField_apply_integer ht
    ⟨t, P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  rw [completionIntegersEquivPowerSeriesResidueField_uniformizer,
    HahnSeries.ofPowerSeries_X] at h
  exact h

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:116` (proof source at `5a01f5fe3621`).
 The coefficient field expands to the constant Laurent series. -/
theorem completionEquivLaurentSeriesResidueField_completionResidueFieldSection
    (a : P.ResidueField) :
    P.completionEquivLaurentSeriesResidueField ht (P.completionResidueFieldSection a) =
      HahnSeries.C a := by
  rw [completionEquivLaurentSeriesResidueField_apply_integer,
    completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection,
    HahnSeries.ofPowerSeries_C]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:126` (proof source at `5a01f5fe3621`).
 Laurent-series expansion preserves the normalized valuation. -/
@[simp]
theorem valuation_completionEquivLaurentSeriesResidueField (x : P.Completion) :
    Valued.v (P.completionEquivLaurentSeriesResidueField ht x) =
      P.completionPlace.valuation x :=
  P.valuation_algEquivOfAlgEquiv _ x

end Completion

/-! ### Expansions of functions -/

variable {t : F} (ht : P.ord t = 1)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:140` (proof source at `5a01f5fe3621`).
 The power-series expansion of a function regular at a place with separable residue field in a
chosen uniformizer `t`, with coefficients in the residue field: the image of the function under
completion and `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`. -/
noncomputable def powerSeriesExpansionResidueField : P.integers →ₐ[k] PowerSeries P.ResidueField :=
  (P.completionIntegersEquivPowerSeriesResidueField
    (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])).toAlgHom.comp
    P.completionIntegersEmbedding

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:147` (proof source at `5a01f5fe3621`).
 The power-series expansion of a function is the expansion of its image in the completed
valuation ring. -/
theorem powerSeriesExpansionResidueField_apply (x : P.integers) :
    P.powerSeriesExpansionResidueField ht x =
      P.completionIntegersEquivPowerSeriesResidueField
        (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])
        (P.completionIntegersEmbedding x) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:156` (proof source at `5a01f5fe3621`).
 The constant coefficient of the power-series expansion of a function regular at `P` is its
value at `P`. -/
@[simp]
theorem constantCoeff_powerSeriesExpansionResidueField (x : P.integers) :
    PowerSeries.constantCoeff (P.powerSeriesExpansionResidueField ht x) =
      IsLocalRing.residue P.integers x :=
  P.constantCoeff_completionIntegersEquivPowerSeriesResidueField_completionIntegersEmbedding
    (by rwa [ord_completionEmbedding]) x

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:164` (proof source at `5a01f5fe3621`).
 A function regular at `P` vanishes to order at least `n` exactly when its power-series
expansion has order at least `n`. -/
theorem mem_filtration_iff_le_order_powerSeriesExpansionResidueField (n : ℕ) (x : P.integers) :
    (x : F) ∈ P.filtration n ↔ (n : ℕ∞) ≤ (P.powerSeriesExpansionResidueField ht x).order := by
  rw [powerSeriesExpansionResidueField_apply,
    ← mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField,
    completionIntegersEmbedding_apply, completionEmbedding_mem_filtration_iff]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:172` (proof source at `5a01f5fe3621`).
 The chosen uniformizer expands as the power-series variable. -/
@[simp]
theorem powerSeriesExpansionResidueField_uniformizer :
    P.powerSeriesExpansionResidueField ht ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      PowerSeries.X := by
  rw [powerSeriesExpansionResidueField_apply]
  convert P.completionIntegersEquivPowerSeriesResidueField_uniformizer
    (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding]) using 2
  exact Subtype.ext (completionIntegersEmbedding_apply _ _)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:182` (proof source at `5a01f5fe3621`).
 **Expansions are onto modulo `Tⁿ`**: every power series over the residue field agrees with
the expansion of some function regular at `P` up to order `n`. -/
theorem exists_trunc_powerSeriesExpansionResidueField_eq (g : PowerSeries P.ResidueField)
    (n : ℕ) : ∃ x : P.integers,
      PowerSeries.trunc n (P.powerSeriesExpansionResidueField ht x) = PowerSeries.trunc n g := by
  have ht' : P.completionPlace.ord (P.completionEmbedding t) = 1 := by
    rwa [ord_completionEmbedding]
  set e := P.completionIntegersEquivPowerSeriesResidueField ht'
  -- Approximate the completed function with expansion `g` by a function regular at `P`.
  obtain ⟨y, hy⟩ := P.exists_filtration_sub_completionEmbedding_mem (b := n) (Nat.cast_nonneg n)
    ⟨(e.symm g : P.Completion), P.completionPlace.mem_filtration_zero_iff.mpr (e.symm g).2⟩
  have hyint : (y : F) ∈ P.integers := P.mem_filtration_zero_iff.mp y.2
  refine ⟨⟨y, hyint⟩, ?_⟩
  have hdiff : ((e.symm g - P.completionIntegersEmbedding ⟨y, hyint⟩ :
      P.completionPlace.integers) : P.Completion) ∈ P.completionPlace.filtration n := by
    simpa using hy
  rw [mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField _ ht' n,
    map_sub, AlgEquiv.apply_symm_apply, PowerSeries.nat_le_order_iff] at hdiff
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, powerSeriesExpansionResidueField_apply]
  split_ifs with hi
  · exact (sub_eq_zero.mp (by simpa using hdiff i hi)).symm
  · rfl

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:207` (proof source at `5a01f5fe3621`).
 The Laurent expansion of a function at a place with separable residue field in a chosen
uniformizer `t`, with coefficients in the residue field: the image of the function under
completion and `TauCeti.Place.completionEquivLaurentSeriesResidueField`. -/
noncomputable def laurentSeriesExpansionResidueField : F →ₐ[k] LaurentSeries P.ResidueField :=
  (P.completionEquivLaurentSeriesResidueField
    (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])).toAlgHom.comp
    P.completionEmbedding

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:214` (proof source at `5a01f5fe3621`).
 The Laurent expansion of a function is the Laurent expansion of its image in the
completion. -/
theorem laurentSeriesExpansionResidueField_apply (z : F) :
    P.laurentSeriesExpansionResidueField ht z =
      P.completionEquivLaurentSeriesResidueField
        (t := P.completionEmbedding t) (by rwa [ord_completionEmbedding])
        (P.completionEmbedding z) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:222` (proof source at `5a01f5fe3621`).
 The Laurent expansion of a function regular at `P` is its power-series expansion. -/
@[simp]
theorem laurentSeriesExpansionResidueField_coe (x : P.integers) :
    P.laurentSeriesExpansionResidueField ht x =
      HahnSeries.ofPowerSeries ℤ P.ResidueField (P.powerSeriesExpansionResidueField ht x) := by
  rw [laurentSeriesExpansionResidueField_apply, ← completionIntegersEmbedding_apply,
    completionEquivLaurentSeriesResidueField_apply_integer, powerSeriesExpansionResidueField_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:231` (proof source at `5a01f5fe3621`).
 Every integer power of the chosen uniformizer expands as the corresponding monomial. -/
-- Not `@[simp]`: the left side already simplifies by `map_zpow₀` and
-- `laurentSeriesExpansionResidueField_uniformizer`.
theorem laurentSeriesExpansionResidueField_zpow_uniformizer (n : ℤ) :
    P.laurentSeriesExpansionResidueField ht (t ^ n) = HahnSeries.single n 1 := by
  rw [map_zpow₀, laurentSeriesExpansionResidueField_apply,
    completionEquivLaurentSeriesResidueField_uniformizer]
  exact (RatFunc.single_zpow n).symm

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:239` (proof source at `5a01f5fe3621`).
 The chosen uniformizer expands as the Laurent variable `T`. -/
@[simp]
theorem laurentSeriesExpansionResidueField_uniformizer :
    P.laurentSeriesExpansionResidueField ht t = HahnSeries.single 1 1 := by
  simpa using P.laurentSeriesExpansionResidueField_zpow_uniformizer ht 1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:245` (proof source at `5a01f5fe3621`).
 Laurent expansion carries the valuation of `P` to the `T`-adic valuation. -/
@[simp]
theorem valuation_laurentSeriesExpansionResidueField (z : F) :
    Valued.v (P.laurentSeriesExpansionResidueField ht z) = P.valuation z := by
  rw [laurentSeriesExpansionResidueField_apply,
    valuation_completionEquivLaurentSeriesResidueField, completionPlace_valuation,
    valuation_completionEmbedding]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:252` (proof source at `5a01f5fe3621`).
 A function vanishing to order at least `m` has no Laurent coefficients below `m`. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansionResidueField ht z).coeff i = 0 := by
  apply LaurentSeries.coeff_zero_of_lt_valuation P.ResidueField _ hi
  rwa [valuation_laurentSeriesExpansionResidueField, ← mem_filtration_iff]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:260` (proof source at `5a01f5fe3621`).
 The Laurent coefficients below `m` depend only on the function modulo the `m`-th order
filtration. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_of_sub_mem_filtration {m : ℤ} {z w : F}
    (h : z - w ∈ P.filtration m) {i : ℤ} (hi : i < m) :
    (P.laurentSeriesExpansionResidueField ht z).coeff i =
      (P.laurentSeriesExpansionResidueField ht w).coeff i := by
  have h0 := P.coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration ht h hi
  rwa [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h0

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:269` (proof source at `5a01f5fe3621`).
 Multiplying by `t ^ n` to make a function integral shifts its Laurent coefficients onto the
coefficients of the power-series expansion of the product. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField
    (n : ℤ) {z : F} (hz : t ^ n * z ∈ P.integers) (i : ℕ) :
    (P.laurentSeriesExpansionResidueField ht z).coeff ((i : ℤ) - n) =
      PowerSeries.coeff i (P.powerSeriesExpansionResidueField ht ⟨t ^ n * z, hz⟩) := by
  rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), ← laurentSeriesExpansionResidueField_coe,
    map_mul, laurentSeriesExpansionResidueField_zpow_uniformizer, HahnSeries.coeff_single_mul,
    one_mul]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:279` (proof source at `5a01f5fe3621`).
 The constant coefficient of the Laurent expansion of a function regular at `P` is its value
at `P`. -/
theorem coeff_zero_laurentSeriesExpansionResidueField (x : P.integers) :
    (P.laurentSeriesExpansionResidueField ht x).coeff 0 = IsLocalRing.residue P.integers x := by
  rw [laurentSeriesExpansionResidueField_coe, ← Nat.cast_zero,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_powerSeriesExpansionResidueField]

/-! ### Residues -/

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:290` (proof source at `5a01f5fe3621`).
 The residue `res_{P,t}` of a function at a place with separable residue field with respect to
a chosen uniformizer: the coefficient of `t⁻¹` in its Laurent expansion, an element of the
residue field `F_P` (Stichtenoth, Definition 4.2.8). It is `k`-linear. -/
noncomputable def residueResidueField : F →ₗ[k] P.ResidueField where
  toFun z := (P.laurentSeriesExpansionResidueField ht z).coeff (-1)
  map_add' z w := by rw [map_add, HahnSeries.coeff_add]
  map_smul' c z := by
    simp [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:297` (proof source at `5a01f5fe3621`).
 The residue is the coefficient of `T⁻¹` in the Laurent expansion. -/
theorem residueResidueField_apply (z : F) :
    P.residueResidueField ht z = (P.laurentSeriesExpansionResidueField ht z).coeff (-1) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:301` (proof source at `5a01f5fe3621`).
 Functions integral at the place have residue zero. -/
theorem residueResidueField_eq_zero_of_mem_integers {z : F} (hz : z ∈ P.integers) :
    P.residueResidueField ht z = 0 :=
  P.coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration ht
    (P.mem_filtration_zero_iff.mpr hz) (by omega)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:307` (proof source at `5a01f5fe3621`).
 The residue depends only on the function modulo integral functions. -/
theorem residueResidueField_eq_of_sub_mem_integers {z w : F} (h : z - w ∈ P.integers) :
    P.residueResidueField ht z = P.residueResidueField ht w := by
  rw [← sub_eq_zero, ← map_sub, P.residueResidueField_eq_zero_of_mem_integers ht h]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:313` (proof source at `5a01f5fe3621`).
 The residue of an integer power of the uniformizer. -/
@[simp]
theorem residueResidueField_zpow_uniformizer (n : ℤ) :
    P.residueResidueField ht (t ^ n) = if n = -1 then 1 else 0 := by
  rw [residueResidueField_apply, laurentSeriesExpansionResidueField_zpow_uniformizer,
    HahnSeries.coeff_single]
  simp only [eq_comm]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:321` (proof source at `5a01f5fe3621`).
 The inverse of the uniformizer has residue one. -/
@[simp]
theorem residueResidueField_inv_uniformizer : P.residueResidueField ht t⁻¹ = 1 := by
  simpa using P.residueResidueField_zpow_uniformizer ht (-1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:326` (proof source at `5a01f5fe3621`).
 If `t ^ (n + 1) * z` is integral, the residue of `z` is the degree-`n` coefficient of the
power-series expansion of `t ^ (n + 1) * z`. -/
theorem residueResidueField_eq_coeff_powerSeriesExpansionResidueField (n : ℕ) {z : F}
    (hz : t ^ (n + 1) * z ∈ P.integers) :
    P.residueResidueField ht z =
      PowerSeries.coeff n (P.powerSeriesExpansionResidueField ht ⟨t ^ (n + 1) * z, hz⟩) := by
  have h := P.coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField
    ht ((n + 1 : ℕ) : ℤ) (by simpa only [zpow_natCast] using hz) n
  simp only [zpow_natCast] at h
  rw [residueResidueField_apply, ← h]
  congr 1
  omega

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:339` (proof source at `5a01f5fe3621`).
 **The residue of `u / t` is the value of `u` at `P`** for a function `u` regular at `P`. -/
@[simp]
theorem residueResidueField_mul_inv_uniformizer (u : P.integers) :
    P.residueResidueField ht (u * t⁻¹) = IsLocalRing.residue P.integers u := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hu : t ^ (0 + 1) * (u * t⁻¹) = u := by
    rw [zero_add, pow_one, mul_left_comm, mul_inv_cancel₀ ht0, mul_one]
  have hmem : t ^ (0 + 1) * (u * t⁻¹) ∈ P.integers := by rw [hu]; exact u.2
  -- The power-series expansion is taken of `t ^ (0 + 1) * (u * t⁻¹)` as an element of
  -- `P.integers`; identify that element with `u`.
  have hsub : (⟨t ^ (0 + 1) * (u * t⁻¹), hmem⟩ : P.integers) = u := Subtype.ext hu
  rw [P.residueResidueField_eq_coeff_powerSeriesExpansionResidueField ht 0 hmem, hsub,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_powerSeriesExpansionResidueField]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:362` (proof source at `5a01f5fe3621`).
 The `k`-valued residue at a place with separable residue field: the trace from `F_P` to `k`
of the residue `res_{P,t}` (Stichtenoth, Remark 4.3.7).

This is the classical residue-field trace precisely when `Module.Finite k P.ResidueField`, which
`TauCeti.Place.finiteDimensional_residueField` supplies for every place of a function field.
Absent that, `Algebra.trace` is the junk value `0` (`Algebra.trace_eq_zero_of_not_exists_basis`),
the convention `TauCeti.Place.normResidue` and `TauCeti.Place.degree` follow as well. -/
-- Finiteness is documented rather than assumed: `Algebra.trace` consumes no such argument, so a
-- hypothesis here would be unused, which `unusedArguments` rejects.
noncomputable def traceResidue : F →ₗ[k] k :=
  (Algebra.trace k P.ResidueField).comp (P.residueResidueField ht)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:366` (proof source at `5a01f5fe3621`).
 The `k`-valued residue is the trace of the residue. -/
theorem traceResidue_apply (z : F) :
    P.traceResidue ht z = Algebra.trace k P.ResidueField (P.residueResidueField ht z) := (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:373` (proof source at `5a01f5fe3621`).
 **The trace residue of `u / t` is the trace of the value of `u` at `P`**, for a function `u`
regular at `P`. This is the `k`-valued form of
`TauCeti.Place.residueResidueField_mul_inv_uniformizer`, used when local components are expressed
as trace residues at places with nontrivial residue field. -/
theorem traceResidue_mul_inv_uniformizer (u : P.integers) :
    P.traceResidue ht (u * t⁻¹) =
      Algebra.trace k P.ResidueField (IsLocalRing.residue P.integers u) := by
  rw [traceResidue_apply, residueResidueField_mul_inv_uniformizer]

/-! ### Comparison with residues at rational places -/

section Rational

variable (hP : P.degree = 1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:386` (proof source at `5a01f5fe3621`).
 **At a rational place, the power-series expansion in the residue field is the power-series
expansion over `k`**, read in `F_P`. -/
theorem powerSeriesExpansionResidueField_eq_map (x : P.integers) :
    P.powerSeriesExpansionResidueField ht x =
      PowerSeries.map (algebraMap k P.ResidueField) (P.powerSeriesExpansion hP ht x) := by
  rw [powerSeriesExpansionResidueField_apply,
    ← completionIntegersEquivPowerSeries_completionIntegersEmbedding]
  refine (P.completionIntegersEquivPowerSeriesResidueField_eq_iff _ _ _).mpr fun n ↦ ?_
  have h := P.sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration hP ht
    (P.completionIntegersEquivPowerSeries hP ht (P.completionIntegersEmbedding x)) n
  rw [AlgEquiv.symm_apply_apply] at h
  simpa only [PowerSeries.coeff_map, AlgHom.commutes, coe_algebraMap_constants] using h

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:399` (proof source at `5a01f5fe3621`).
 **At a rational place, Laurent coefficients in the residue field are the Laurent coefficients
over `k`**, read in `F_P`. -/
theorem coeff_laurentSeriesExpansionResidueField_eq_algebraMap (z : F) (n : ℤ) :
    (P.laurentSeriesExpansionResidueField ht z).coeff n =
      algebraMap k P.ResidueField ((P.laurentSeriesExpansion hP ht z).coeff n) := by
  -- Shift `z` by a power of `t` making it integral, with the shift large enough that `n`
  -- becomes a nonnegative index, and compare the two power-series expansions.
  have hz : t ^ (-min (P.ord z) n) * z ∈ P.integers :=
    P.mul_mem_integers_of_mem_filtration (by simp [ht])
      (P.filtration_antitone (min_le_left (P.ord z) n) (P.mem_filtration_ord z))
  have hn : (((n - min (P.ord z) n).toNat : ℕ) : ℤ) - -min (P.ord z) n = n := by omega
  rw [← hn,
    P.coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField ht _ hz,
    P.coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion hP ht _ hz,
    P.powerSeriesExpansionResidueField_eq_map ht hP, PowerSeries.coeff_map]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:415` (proof source at `5a01f5fe3621`).
 **At a rational place the residue in the residue field is the residue over `k`**, read in
`F_P`. -/
theorem residueResidueField_eq_algebraMap_residue (z : F) :
    P.residueResidueField ht z = algebraMap k P.ResidueField (P.residue hP ht z) := by
  rw [residueResidueField_apply, residue_apply,
    P.coeff_laurentSeriesExpansionResidueField_eq_algebraMap ht hP]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/CoefficientField.lean:421` (proof source at `5a01f5fe3621`).
 **At a rational place the `k`-valued residue is the residue over `k`.** -/
theorem traceResidue_eq_residue (z : F) : P.traceResidue ht z = P.residue hP ht z := by
  rw [traceResidue_apply, P.residueResidueField_eq_algebraMap_residue ht hP,
    Algebra.trace_algebraMap, ← degree_eq_finrank, hP, one_smul]

end Rational

end TauCeti.Place
end

end

/-! ## Source 36: `TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Residue`
Original source SHA256: `df16be2e27682376293e93572dd794831cb5e648162474e78054e9a460291df9`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The local components of `dx` on `k(x)` are residues

Let `η` be the canonical Weil differential of the rational function field `k(x)`, the
differential classically written `dx` (`TauCeti.ratFuncWeilDifferential`).  At every rational
place its local component is a residue of a Laurent expansion:

* at the place `P_a` of `x - a`, with the uniformizer `x - a`, `η_{P_a} (z) = res_{P_a, x - a} (z)`;
* at the place at infinity, with the uniformizer `x⁻¹`, `η_{P_∞} (z) = -res_{P_∞, x⁻¹} (x² z)`.

These are the two faces of `η_P (z) = res_P (z dx)`: `dx = d(x - a)`, while `dx = -x² d(x⁻¹)`.
This is the rational-function-field case of Stichtenoth's identification of local components
with residues, and the base case from which it is transported to a separable extension of
`k(x)` along the cotrace.

Feeding the identification back into the abstract residue theorem gives the **residue theorem
for `k(x)`**: if every pole of `z` is a rational place, then
`∑_{a ∈ k} res_{P_a, x - a} (z) = res_{P_∞, x⁻¹} (x² z)`, the classical statement that the
residues of `z dx` over `ℙ¹(k)` sum to zero.  Over an algebraically closed field every place is
rational, and the hypothesis disappears.

## Main results

* `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_infty`:
  `η_{P_∞} (z) = -res_{P_∞, x⁻¹} (x² z)`.
* `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C`:
  `η_{P_a} (z) = res_{P_a, x - a} (z)`.
* `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C`: the residue theorem for a rational
  function whose poles are rational places.
* `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C_of_isAlgClosed`: the residue theorem for
  `k(x)` over an algebraically closed field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.4, Theorem 4.3.2(d) and Corollary 4.3.3.
-/

section
open Polynomial

namespace TauCeti

open Place

variable {k : Type*} [Field k]

/-! ### The local component at infinity -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:65` (proof source at `5a01f5fe3621`).
 **The local component of `dx` at infinity is a residue** (Stichtenoth, Theorem 4.3.2(d), for
`k(x)`): `η_{P_∞} (z) = -res_{P_∞, x⁻¹} (x² z)`, which is `res_{P_∞} (z dx)` since
`dx = -x² d(x⁻¹)`. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_infty (z : RatFunc k) :
    repartitionDualComponent (ratFuncWeilDifferential k) (infty k) z =
      -(infty k).residue (degree_infty k) ord_infty_inv_X (RatFunc.X ^ 2 * z) := by
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  -- `x²` lies in `𝔪_∞^(-2)`, so it carries `𝔪_∞^2` into the valuation ring.
  have hX2 : (RatFunc.X : RatFunc k) ^ 2 ∈ (infty k).filtration (-2) := by
    rw [mem_filtration_iff_le_ord _ (pow_ne_zero 2 hX0), ord_pow, ord_infty, RatFunc.intDegree_X]
    norm_num
  let g : RatFunc k →ₗ[k] k :=
    -((infty k).residue (degree_infty k) ord_infty_inv_X ∘ₗ
      LinearMap.mulLeft k (RatFunc.X ^ 2))
  -- Both sides are `k`-linear in `z`, vanish once `z` vanishes to high enough order at `P_∞`,
  -- and agree on the powers of `x⁻¹`, so they are equal by `Place.linearMap_ext_zpow`.
  refine LinearMap.congr_fun
    (?_ : repartitionDualComponent (ratFuncWeilDifferential k) (infty k) = g) z
  refine (infty k).linearMap_ext_zpow (degree_infty k) ord_infty_inv_X (m := 2)
    (fun w hw ↦ ?_) (fun j _ ↦ ?_)
  · -- Both sides vanish on `𝔪_∞^2`: the divisor of `η` is `-2 · P_∞`, and `x² w` is integral.
    have hint : RatFunc.X ^ 2 * w ∈ (infty k).integers := by
      simpa using (infty k).mul_mem_filtration hX2 hw
    rw [repartitionDualComponent_apply_eq_zero_of_le (isGreatest_ratFuncWeilDifferential k).1
      (infty k) (by simpa using hw)]
    simp [g, residue_eq_zero_of_mem_integers _ _ _ hint]
  · -- On `x⁻ʲ` both sides are `-1` for `j = 1` and `0` otherwise.
    have hpow : (RatFunc.X : RatFunc k) ^ 2 * (RatFunc.X⁻¹) ^ j = (RatFunc.X⁻¹) ^ (j - 2) := by
      rw [inv_zpow', inv_zpow', ← zpow_natCast, ← zpow_add₀ hX0]
      congr 1
      omega
    rw [inv_zpow', repartitionDualComponent_ratFuncWeilDifferential_zpow]
    simp only [g, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, ← inv_zpow',
      hpow, residue_zpow_uniformizer]
    split_ifs <;> first | omega | simp

/-! ### The local components at the finite rational places -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:102` (proof source at `5a01f5fe3621`).
 `x - a` is a unit at every place other than `P_a` and `P_∞`, so all its integer powers are
integral there. -/
private theorem zpow_X_sub_C_mem_integers {a : k} {P : Place k (RatFunc k)}
    (ha : P ≠ adicOfIrreducible (irreducible_X_sub_C a)) (hinf : P ≠ infty k) (n : ℤ) :
    (RatFunc.X - RatFunc.C a) ^ n ∈ P.integers := by
  obtain ⟨q, hq, rfl⟩ := (eq_infty_or_exists_eq_adicOfIrreducible P).resolve_left hinf
  have hassoc : ¬Associated q (X - C a) := fun h ↦
    ha ((adicOfIrreducible_eq_adicOfIrreducible_iff hq (irreducible_X_sub_C a)).mpr h)
  rw [mem_integers_iff_ord_nonneg, ord_zpow, ord_adicOfIrreducible_X_sub_C_of_not_associated hq
    hassoc, mul_zero]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:113` (proof source at `5a01f5fe3621`).
 The residue at infinity of `x² (x - a)ⁿ` for `n < 0`: it is `1` for `n = -1`, where
`x² / (x - a) = x + a + a² / (x - a)`, and `0` for `n ≤ -2`, where `x² (x - a)ⁿ` is integral. -/
private theorem residue_infty_X_sq_mul_X_sub_C_zpow (a : k) {n : ℤ} (hn : n < 0) :
    (infty k).residue (degree_infty k) ord_infty_inv_X
        (RatFunc.X ^ 2 * (RatFunc.X - RatFunc.C a) ^ n) =
      if n = -1 then 1 else 0 := by
  set t : RatFunc k := RatFunc.X - RatFunc.C a
  have htinf : (infty k).ord t = -1 := by
    simp only [t]
    rw [ord_infty, ← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub,
      RatFunc.intDegree_polynomial, natDegree_X_sub_C, Nat.cast_one]
  have ht0 : t ≠ 0 := by
    rintro h
    simp [h] at htinf
  split_ifs with h1
  · -- `x² / (x - a) - x = a x / (x - a)` is integral at infinity, and `x = (x⁻¹)⁻¹`.
    subst h1
    have heq : RatFunc.X ^ 2 * t ^ (-1 : ℤ) - (RatFunc.X⁻¹)⁻¹ =
        RatFunc.C a * RatFunc.X * t⁻¹ := by
      field_simp
      simp [t]
    have hint : RatFunc.X ^ 2 * t ^ (-1 : ℤ) - (RatFunc.X⁻¹)⁻¹ ∈ (infty k).integers := by
      rw [heq, mem_integers_iff_ord_nonneg]
      rcases eq_or_ne a 0 with rfl | ha0
      · simp
      have hC : RatFunc.C a ≠ 0 := by simpa using ha0
      rw [(infty k).ord_mul (mul_ne_zero hC RatFunc.X_ne_zero) (inv_ne_zero ht0),
        (infty k).ord_mul hC RatFunc.X_ne_zero, ord_inv, htinf, ord_infty, ord_infty,
        RatFunc.intDegree_C, RatFunc.intDegree_X]
      norm_num
    rw [residue_eq_of_sub_mem_integers _ _ _ hint, residue_inv_uniformizer]
  · -- For `n ≤ -2`, `x² tⁿ` is integral at infinity.
    refine residue_eq_zero_of_mem_integers _ _ _ ?_
    rw [mem_integers_iff_ord_nonneg, (infty k).ord_mul (pow_ne_zero _ RatFunc.X_ne_zero)
      (zpow_ne_zero _ ht0), ord_pow, ord_zpow, htinf, ord_infty, RatFunc.intDegree_X]
    omega

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:150` (proof source at `5a01f5fe3621`).
 The local component of `dx` at `P_a` on the powers of `x - a`: `1` on `(x - a)⁻¹` and `0`
on every other power. -/
private theorem repartitionDualComponent_ratFuncWeilDifferential_X_sub_C_zpow (a : k) (n : ℤ) :
    repartitionDualComponent (ratFuncWeilDifferential k)
        (adicOfIrreducible (irreducible_X_sub_C a)) ((RatFunc.X - RatFunc.C a) ^ n) =
      if n = -1 then 1 else 0 := by
  classical
  set Pa := adicOfIrreducible (irreducible_X_sub_C a)
  have hPa : Pa ≠ infty k := adicOfIrreducible_ne_infty _
  rcases le_or_gt 0 n with hn | hn
  · -- A nonnegative power is integral at `P_a`.
    rw [ite_eq_right (by omega)]
    refine repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hPa ?_
    rw [mem_integers_iff_ord_nonneg, ord_zpow, ord_adicOfIrreducible_X_sub_C_self]
    simpa using hn
  -- A negative power: by the abstract residue theorem only `P_a` and `P_∞` contribute, so
  -- `η_{P_a} (tⁿ) = -η_{P_∞} (tⁿ) = res_{P_∞, x⁻¹} (x² tⁿ)`.
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (ratFuncWeilDifferential_mem k) ((RatFunc.X - RatFunc.C a) ^ n)
  rw [finsum_eq_sum_of_support_subset _ (s := {Pa, infty k}) (fun P hP ↦ by
    by_contra hmem
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hmem
    exact hP (repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hmem.2
      (zpow_X_sub_C_mem_integers hmem.1 hmem.2 n))),
    Finset.sum_pair hPa, repartitionDualComponent_ratFuncWeilDifferential_infty,
    add_neg_eq_zero] at hsum
  rw [hsum, residue_infty_X_sq_mul_X_sub_C_zpow a hn]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:180` (proof source at `5a01f5fe3621`).
 **The local component of `dx` at the place of `x - a` is a residue** (Stichtenoth,
Theorem 4.3.2(d), for `k(x)`): `η_{P_a} (z) = res_{P_a, x - a} (z)`, which is
`res_{P_a} (z dx)` since `dx = d(x - a)`. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C (a : k)
    (z : RatFunc k) :
    repartitionDualComponent (ratFuncWeilDifferential k)
        (adicOfIrreducible (irreducible_X_sub_C a)) z =
      (adicOfIrreducible (irreducible_X_sub_C a)).residue (degree_adicOfIrreducible_X_sub_C a)
        (ord_adicOfIrreducible_X_sub_C_self a) z := by
  -- Both sides are `k`-linear in `z`, vanish on the functions integral at `P_a`, and agree on
  -- the powers of `x - a`, so they are equal by `Place.linearMap_ext_zpow`.
  refine LinearMap.congr_fun ?_ z
  refine (adicOfIrreducible (irreducible_X_sub_C a)).linearMap_ext_zpow
    (degree_adicOfIrreducible_X_sub_C a) (ord_adicOfIrreducible_X_sub_C_self a) (m := 0)
    (fun w hw ↦ ?_) (fun j _ ↦ ?_)
  · -- Both sides vanish on the functions integral at `P_a`.
    rw [mem_filtration_zero_iff] at hw
    rw [repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty
      (adicOfIrreducible_ne_infty _) hw, residue_eq_zero_of_mem_integers _ _ _ hw]
  · rw [repartitionDualComponent_ratFuncWeilDifferential_X_sub_C_zpow, residue_zpow_uniformizer]

/-! ### The residue theorem -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:207` (proof source at `5a01f5fe3621`).
 **The residue theorem for `k(x)`** (Stichtenoth, Corollary 4.3.3, for `k(x)`): if every pole
of `z` is a rational place, then the residues of `z dx` over `ℙ¹(k)` sum to zero, in the form
`∑_{a ∈ k} res_{P_a, x - a} (z) = res_{P_∞, x⁻¹} (x² z)`.

The hypothesis is needed: over `ℚ`, `z = 2x / (x² - 2)` is integral at every place `P_a`, so the
left side vanishes, while `res_{P_∞, x⁻¹} (x² z) = 2`; the missing residue sits at the place of
`x² - 2`, which has degree two. -/
theorem finsum_residue_adicOfIrreducible_X_sub_C {z : RatFunc k}
    (hz : ∀ P : Place k (RatFunc k), P.degree ≠ 1 → z ∈ P.integers) :
    ∑ᶠ a : k, (adicOfIrreducible (irreducible_X_sub_C a)).residue
        (degree_adicOfIrreducible_X_sub_C a) (ord_adicOfIrreducible_X_sub_C_self a) z =
      (infty k).residue (degree_infty k) ord_infty_inv_X (RatFunc.X ^ 2 * z) := by
  set f : Place k (RatFunc k) → k :=
    fun P ↦ repartitionDualComponent (ratFuncWeilDifferential k) P z
  set g : k → Place k (RatFunc k) := fun a ↦ adicOfIrreducible (irreducible_X_sub_C a)
  have hfin : (Function.support f).Finite := by
    simpa [f] using finite_support_repartitionDualComponent_apply (ratFuncWeilDifferential_mem k)
      ⟨_, const_mem_repartitionSpace (IsFunctionField.ratFunc k) z⟩
  -- Off the rational places, `z` is integral, so its local component vanishes.
  have hsupp : ∀ P ∈ Function.support f, P ∈ insert (infty k) (Set.range g) := by
    intro P hP
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_range, not_or, not_exists] at hmem
    refine hP (repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hmem.1 (hz P ?_))
    intro hdeg
    rcases eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C hdeg with h | ⟨a, h⟩
    exacts [hmem.1 h, hmem.2 a h.symm]
  have hinf : infty k ∉ Set.range g := by
    rintro ⟨a, h⟩
    exact adicOfIrreducible_ne_infty _ h
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (ratFuncWeilDifferential_mem k) z
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' f _ _ fun P hP ↦
      iff_of_true (Set.mem_univ P) (hsupp P hP),
    finsum_mem_insert' f hinf (hfin.subset Set.inter_subset_right),
    finsum_mem_range (adicOfIrreducible_X_sub_C_injective (k := k))] at hsum
  simp only [f, repartitionDualComponent_ratFuncWeilDifferential_infty,
    repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C] at hsum
  linear_combination hsum

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/RatFunc/Residue.lean:243` (proof source at `5a01f5fe3621`).
 **The residue theorem for `k(x)` over an algebraically closed field** (Stichtenoth,
Corollary 4.3.3, for `k(x)`): `∑_{a ∈ k} res_{P_a, x - a} (z) = res_{P_∞, x⁻¹} (x² z)` for every
rational function `z`. -/
theorem finsum_residue_adicOfIrreducible_X_sub_C_of_isAlgClosed [IsAlgClosed k]
    (z : RatFunc k) :
    ∑ᶠ a : k, (adicOfIrreducible (irreducible_X_sub_C a)).residue
        (degree_adicOfIrreducible_X_sub_C a) (ord_adicOfIrreducible_X_sub_C_self a) z =
      (infty k).residue (degree_infty k) ord_infty_inv_X (RatFunc.X ^ 2 * z) :=
  finsum_residue_adicOfIrreducible_X_sub_C fun P hP ↦
    absurd (P.degree_eq_one_of_isAlgClosed_of_isFunctionField (IsFunctionField.ratFunc k)) hP

end TauCeti
end

end

/-! ## Source 37: `TauCeti.RingTheory.PowerSeries.Trunc`
Original source SHA256: `7a12858811d41d1ceaafc6edc857edb0ae253a3e6b7f03fd9714e5539792528f`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Truncations and finite expansions of power series

Two facts used to compare power series to a finite order `m`: the truncation `trunc m φ`
vanishes exactly when `φ` has order at least `m`, and the coefficients of a finite expansion
`∑_{i < m} aᵢ Xⁱ` are the `aᵢ`, read as zero from degree `m` on.

## Main results

* `PowerSeries.trunc_eq_zero_iff_le_order`: `trunc m φ = 0 ↔ m ≤ order φ`.
* `PowerSeries.coeff_sum_C_mul_X_pow`: the coefficients of `∑ i : Fin m, C (a i) * X ^ i`.
-/

section
namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/PowerSeries/Trunc.lean:32` (proof source at `5a01f5fe3621`).
 The truncation below degree `m` of a power series vanishes exactly when the series has
order at least `m`. -/
theorem trunc_eq_zero_iff_le_order {m : ℕ} {φ : R⟦X⟧} : trunc m φ = 0 ↔ (m : ℕ∞) ≤ φ.order := by
  rw [nat_le_order_iff]
  refine ⟨fun h i hi ↦ ?_, fun h ↦ Polynomial.ext fun i ↦ ?_⟩
  · simpa [coeff_trunc, hi] using congrArg (Polynomial.coeff · i) h
  · rw [coeff_trunc, Polynomial.coeff_zero]
    split_ifs with hi
    exacts [h i hi, rfl]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/PowerSeries/Trunc.lean:42` (proof source at `5a01f5fe3621`).
 The coefficients of the finite expansion `∑_{i < m} aᵢ Xⁱ` are the `aᵢ`, and vanish from
degree `m` on. -/
theorem coeff_sum_C_mul_X_pow {m : ℕ} (a : Fin m → R) (n : ℕ) :
    coeff n (∑ i : Fin m, C (a i) * X ^ (i : ℕ)) = if h : n < m then a ⟨n, h⟩ else 0 := by
  simp only [map_sum, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨n, h⟩ fun i hi ↦ by
      have hni : n ≠ (i : ℕ) := fun hn ↦ hi (Fin.ext hn.symm)
      simp [hni]]
    simp
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hni : n ≠ (i : ℕ) := (i.2.trans_le (not_lt.mp h)).ne'
    simp [hni]

end PowerSeries
end

end

/-! ## Source 38: `TauCeti.RingTheory.Trace.Quotient`
Original source SHA256: `58d4656e72fc609b3cffe61628b1901976afb3db71a458a9cceea96f218a1ae9`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The trace modulo an ideal

Let `S` be a finite free `R`-algebra and `I` an ideal of `R`. The trace of `S ⧸ IS` over `R ⧸ I`
of the class of `x` is the class of the trace of `x`. Mathlib's `Algebra.trace_quotient_mk` is the
case where `R` is local and `I` is its maximal ideal; here `I` is arbitrary, which is what a
computation of the trace modulo a power `𝔪 ^ n` of a maximal ideal needs. It is the trace
counterpart of `TauCeti.Algebra.norm_quotient_mk`.

It also computes the trace modulo `I` of an element acting through a summand of `S ⧸ IS` with a
known basis, which is how the trace of a finite extension of function fields is computed locally
at one place.

## Main results

* `TauCeti.Algebra.trace_quotient_map_mk`: the trace of `S ⧸ IS` over `R ⧸ I` of the class of `x`
  is the class of the trace of `x`.
* `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`: if, modulo `IS`, multiplication
  by `w` projects onto the span of linearly independent `b j`, and `z` acts through that
  projection by the matrix `a`, then `Tr_{S/R} z ≡ ∑ j, a j j` modulo `I`.
* `TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem`: its rank-one case, an idempotent of
  rank one modulo `I` has trace `1` modulo `I`.
-/

section
namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Trace/Quotient.lean:46` (proof source at `5a01f5fe3621`).
 **The trace commutes with reduction modulo an ideal.** For a finite free algebra `S` over `R`
and an ideal `I` of `R`, the trace of `S ⧸ IS` over `R ⧸ I` of the class of `x` is the class of the
trace of `x`. -/
@[simp]
theorem Algebra.trace_quotient_map_mk (I : Ideal R) (x : S) :
    Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk I (Algebra.trace R S x) := by
  -- `S ⧸ IS` is the base change `(R ⧸ I) ⊗[R] S`, on which multiplication by `1 ⊗ x` is the base
  -- change of multiplication by `x`; the trace commutes with base change.
  rw [← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I),
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.trace_apply, Algebra.trace_apply,
    ← Ideal.Quotient.algebraMap_eq, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Trace/Quotient.lean:59` (proof source at `5a01f5fe3621`).
 The trace of an element of `IS` lies in `I`. -/
theorem Algebra.trace_mem_of_mem_map {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    Algebra.trace R S x ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← trace_quotient_map_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Trace/Quotient.lean:73` (proof source at `5a01f5fe3621`).
 **The trace on a summand with a known basis, modulo an ideal.** Let `J = IS`. Suppose that
modulo `J`, multiplication by `w` maps `S` onto the span of `b j`, fixes every `b j`, and that the
`b j` are linearly independent over `R ⧸ I`: every `w * s` is congruent to some `∑ c j * b j`, and
`∑ c j * b j ∈ J` only when every `c j ∈ I`. If `z` is congruent to `z * w` and acts on the `b j`
by the matrix `a`, that is `z * b j ≡ ∑ l, a j l * b l`, then `Tr_{S/R} z ≡ ∑ j, a j j` modulo `I`.

Modulo `J`, the class of `z` acts through the projection `w`, whose range is free with basis the
classes of the `b j`, so its trace is the trace of the matrix `a`. No hypothesis on `R ⧸ I` is
needed: the basis of the range is given. -/
theorem Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem {ι : Type*} [Fintype ι]
    {I : Ideal R} {w z : S} {b : ι → S} {a : ι → ι → R}
    (hwb : ∀ j, w * b j - b j ∈ I.map (algebraMap R S))
    (hspan : ∀ s : S, ∃ c : ι → R,
      w * s - ∑ j, algebraMap R S (c j) * b j ∈ I.map (algebraMap R S))
    (hindep : ∀ c : ι → R, ∑ j, algebraMap R S (c j) * b j ∈ I.map (algebraMap R S) →
      ∀ j, c j ∈ I)
    (hz : z * w - z ∈ I.map (algebraMap R S))
    (hzb : ∀ j, z * b j - ∑ l, algebraMap R S (a j l) * b l ∈ I.map (algebraMap R S)) :
    Algebra.trace R S z - ∑ j, a j j ∈ I := by
  classical
  set J := I.map (algebraMap R S)
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have : Module.Free (R ⧸ I) (S ⧸ J) := .of_equiv e.symm.toLinearEquiv
  have : Module.Finite (R ⧸ I) (S ⧸ J) := .equiv e.symm.toLinearEquiv
  have hmk (c : R) : Ideal.Quotient.mk J (algebraMap R S c) =
      algebraMap (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk I c) :=
    (Ideal.Quotient.algebraMap_quotient_map_quotient c).symm
  -- The classes of the `b j` give a linear map `φ : (ι → R ⧸ I) → S ⧸ J`.
  let φ : (ι → R ⧸ I) →ₗ[R ⧸ I] S ⧸ J :=
    Fintype.linearCombination (R ⧸ I) fun j ↦ Ideal.Quotient.mk J (b j)
  have hφ (c : ι → R) : φ (fun j ↦ Ideal.Quotient.mk I (c j)) =
      Ideal.Quotient.mk J (∑ j, algebraMap R S (c j) * b j) := by
    simp [φ, Fintype.linearCombination_apply, map_sum, hmk, Algebra.smul_def]
  have hlift (c : ι → R ⧸ I) : ∃ c' : ι → R, (fun j ↦ Ideal.Quotient.mk I (c' j)) = c :=
    ⟨fun j ↦ (Ideal.Quotient.mk_surjective (c j)).choose,
      funext fun j ↦ (Ideal.Quotient.mk_surjective (c j)).choose_spec⟩
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨c, rfl⟩ := hlift c
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact funext fun j ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hindep c hc j)
  -- Multiplication by the class of `w` lands in the range of `φ` and fixes it.
  let W := Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J w)
  have hWa (s : S ⧸ J) : W s = Ideal.Quotient.mk J w * s := rfl
  have hW (s : S ⧸ J) : W s ∈ LinearMap.range φ := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨c, hc⟩ := hspan s
    refine ⟨fun j ↦ Ideal.Quotient.mk I (c j), ?_⟩
    rw [hφ]
    exact (Ideal.Quotient.eq.mpr hc).symm
  have hWφ (c : ι → R ⧸ I) : W (φ c) = φ c := by
    obtain ⟨c, rfl⟩ := hlift c
    rw [hφ, hWa, ← map_mul, Finset.mul_sum]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← Finset.sum_sub_distrib]
    exact J.sum_mem fun j _ ↦ by
      rw [mul_left_comm, ← mul_sub]
      exact J.mul_mem_left _ (hwb j)
  -- So `W = φ ∘ ρ` with `ρ ∘ φ = id`.
  let ψ := LinearEquiv.ofInjective φ hφinj
  let ρ : S ⧸ J →ₗ[R ⧸ I] ι → R ⧸ I :=
    ψ.symm.toLinearMap ∘ₗ W.codRestrict (LinearMap.range φ) hW
  have hφρ' (s : S ⧸ J) : φ (ρ s) = W s := by
    have h := congrArg Subtype.val (ψ.apply_symm_apply ⟨W s, hW s⟩)
    rwa [LinearEquiv.ofInjective_apply] at h
  have hφρ : φ ∘ₗ ρ = W := LinearMap.ext hφρ'
  have hρφ (c : ι → R ⧸ I) : ρ (φ c) = c := hφinj (by rw [hφρ', hWφ])
  -- The class of `z` acts through `W`.
  let L := Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z)
  have hL : Algebra.lmul (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z) = L := rfl
  have hLa (s : S ⧸ J) : L s = Ideal.Quotient.mk J z * s := rfl
  have hLW : L ∘ₗ W = L := by
    refine LinearMap.ext fun s ↦ ?_
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [LinearMap.comp_apply, hLa, hLa, hWa, ← map_mul, ← map_mul, ← map_mul]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← mul_assoc, ← sub_mul]
    exact J.mul_mem_right _ hz
  -- On the coordinates, `z` acts by the transpose of `a`.
  have hmat : ρ ∘ₗ L ∘ₗ φ =
      Matrix.toLin' (Matrix.of fun l j ↦ Ideal.Quotient.mk I (a j l)) := by
    ext j l
    have hb : φ (Pi.single j 1) = Ideal.Quotient.mk J (b j) := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    have hzbj : L (Ideal.Quotient.mk J (b j)) = φ fun l ↦ Ideal.Quotient.mk I (a j l) := by
      rw [hφ, hLa, ← map_mul]
      exact Ideal.Quotient.eq.mpr (hzb j)
    simp only [LinearMap.comp_apply, LinearMap.coe_single, hb, hzbj, hρφ, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.of_apply]
  have htr : Algebra.trace (R ⧸ I) (S ⧸ J) (Ideal.Quotient.mk J z) =
      ∑ j, Ideal.Quotient.mk I (a j j) := by
    rw [Algebra.trace_apply, hL, ← hLW, ← hφρ, ← LinearMap.comp_assoc,
      LinearMap.trace_comp_comm', hmat, Matrix.trace_toLin'_eq]
    simp [Matrix.trace]
  rw [← Ideal.Quotient.eq, map_sum, ← trace_quotient_map_mk, htr]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Trace/Quotient.lean:168` (proof source at `5a01f5fe3621`).
 **An idempotent of rank one modulo an ideal has trace one.** Suppose the class of `w` in
`S ⧸ IS` is idempotent, and that the ideal it generates is free of rank one over `R ⧸ I` with basis
that class: every `w * b` is congruent to some `c * w` with `c ∈ R`, and `c * w ∈ IS` only for
`c ∈ I`. Then `Tr_{S/R} w ≡ 1` modulo `I`.

This is the rank-one case of `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`, with
the single basis vector `w` acting on itself by `1`. -/
theorem Algebra.trace_sub_one_mem_of_mul_self_sub_mem {I : Ideal R} {w : S}
    (hw : w * w - w ∈ I.map (algebraMap R S))
    (hspan : ∀ b : S, ∃ c : R, w * b - algebraMap R S c * w ∈ I.map (algebraMap R S))
    (hinj : ∀ c : R, algebraMap R S c * w ∈ I.map (algebraMap R S) → c ∈ I) :
    Algebra.trace R S w - 1 ∈ I := by
  simpa using Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem (ι := Unit) (w := w) (z := w)
    (b := fun _ ↦ w) (a := fun _ _ ↦ 1) (fun _ ↦ hw)
    (fun s ↦ let ⟨c, hc⟩ := hspan s; ⟨fun _ ↦ c, by simpa using hc⟩)
    (fun c hc _ ↦ hinj (c ()) (by simpa using hc)) hw (fun _ ↦ by simpa using hw)

end TauCeti
end

end

/-! ## Source 39: `TauCeti.FieldTheory.FunctionField.Place.Extension.Trace`
Original source SHA256: `413097dd63e3fc5e1f7030bb7ef32959c81164138bb397520a68afa2383b9823`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The trace near an unramified place

Let `F' / k'` be a finite separable extension of the algebraic function field `F / k`, and let
`P'` be a place of `F'` over the place `P` of `F`. Classically, `Tr_{F'/F}` decomposes as the sum
`∑_{Q' ∣ P} Tr_{F'_{Q'}/F_P}` of the traces of the completions over `P` (Stichtenoth,
Section IV.2). This file proves two completion-free consequences, for functions `z` that are regular
at `P'` and vanish to order at least `e(Q' ∣ P) · m` at every other place `Q'` over `P`, so that
the local traces at those places are negligible to order `m`.

* **Local degree one.** If `e(P' ∣ P) = f(P' ∣ P) = 1`, the completions at `P'` and at `P`
  coincide and the trace is, near `P'`, the identity: `ord_{P'} (Tr_{F'/F} z - z) ≥ m`.
* **Unramified over a rational place.** If `P` is rational with uniformizer `t` and
  `e(P' ∣ P) = 1`, so that the completion at `P'` is `F'_{P'}((t))` with `F'_{P'}` separable over
  `k`, the trace acts on expansions coefficientwise:
  `Tr_{F'/F} z ≡ ∑_{i < m} Tr_{F'_{P'}/k} (aᵢ) tⁱ` to order `m`, where `∑ aᵢ tⁱ` is the expansion
  of `z` at `P'`. In residue form, `res_{P,t} (Tr_{F'/F} v) = Tr_{F'_{P'}/k} (res_{P',t} v)` for
  every `v` regular at the other places over `P`.

These identify the local components of a cotrace of Weil differentials with those of the
differential it comes from, at places of arbitrary degree.

Both proofs work in the local model `𝒪'_P ⊇ 𝒪_P`, the integral closure of the valuation ring of
`P` in `F'`, which is finite and free over `𝒪_P`. Let `x` be a uniformizer of `P` and reduce
modulo `x ^ m`: the trace of `𝒪'_P ⧸ x ^ m` over `𝒪_P ⧸ x ^ m` is the reduction of the trace
(`TauCeti.Algebra.trace_quotient_map_mk`). By weak approximation some `w` is congruent to `1` at
`P'` and to `0` at the other places over `P`, to order `m`; multiplication by its class is a
projection onto the summand of `𝒪'_P ⧸ x ^ m` belonging to `P'`, through which `z` acts. When
`e = f = 1` that summand is free of rank one with basis the class of `w`, and the class of `z` is
`a • w` for an `a ∈ 𝒪_P` congruent to `z` at `P'`, so the trace of `z` is `a` modulo `x ^ m`
(`TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem`). Over a rational place with `e = 1`,
the summand is free with basis functions whose expansions at `P'` are constant to order `m` and
run over a `k`-basis `βⱼ` of `F'_{P'}`; on it `z` acts by the matrix `∑ᵢ [aᵢ] xⁱ`, where `[aᵢ]`
is the matrix of multiplication by `aᵢ` in the basis `βⱼ`, whose trace is `∑ᵢ Tr (aᵢ) xⁱ`
(`TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`).

## Main results

* `TauCeti.Place.exists_sub_algebraMap_mem_filtration`: at a place with `e = f = 1`, every
  regular function of `F'` is congruent to a regular function of `F` to any prescribed order.
* `TauCeti.Place.algebraMap_trace_sub_mem_filtration`: at a place with `e = f = 1`, the trace is
  the identity to order `m` near `P'`.
* `TauCeti.Place.trace_sub_sum_mem_filtration`: at an unramified place over a rational place, the
  trace acts on expansions as the coefficientwise trace of `F'_{P'} / k`, to order `m`.
* `TauCeti.Place.residue_trace`: in that situation,
  `res_{P,t} (Tr_{F'/F} v) = Tr_{F'_{P'}/k} (res_{P',t} v)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2 and Remark 4.3.7.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §2 and §4.
-/

section
open scoped nonZeroDivisors

namespace TauCeti

namespace Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F) (P' : Place k' F')

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:89` (proof source at `5a01f5fe3621`).
 The image in `F'` of a uniformizer of the place below has order `e(P' ∣ P)` at `P'`. -/
private theorem ord_algebraMap_uniformizer {x : F} (hx : (P'.restrict k F).ord x = 1) :
    P'.ord (algebraMap F F' x) = ramificationIdx F P' := by
  rw [ord_algebraMap_restrict k F P', hx, mul_one]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:95` (proof source at `5a01f5fe3621`).
 **Expansion at a place of local degree one**: if `e(P' ∣ P) = f(P' ∣ P) = 1`, every function
regular at `P'` is congruent to a function of `F` regular at `P`, to any prescribed order `n`. -/
theorem exists_sub_algebraMap_mem_filtration (he : ramificationIdx F P' = 1)
    (hf : relativeDegree k F P' = 1) (n : ℕ) {z : F'} (hz : z ∈ P'.integers) :
    ∃ a ∈ (P'.restrict k F).integers, z - algebraMap F F' a ∈ P'.filtration n := by
  set P := P'.restrict k F
  obtain ⟨x, hx⟩ := P.exists_isUniformizer
  have hxo : P.ord x = 1 := P.isUniformizer_iff_ord_eq_one.mp hx
  have hxi : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hx'0 : algebraMap F F' x ≠ 0 := (map_ne_zero _).mpr hx.ne_zero
  have hx'o : P'.ord (algebraMap F F' x) = 1 := by
    rw [ord_algebraMap_uniformizer k F P' hxo, he, Nat.cast_one]
  -- `f(P' ∣ P) = 1` makes the residue fields equal.
  have hsurj : Function.Surjective (algebraMap P.ResidueField P'.ResidueField) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (relativeDegree_def k F P' ▸ hf)).2
  induction n with
  | zero => exact ⟨0, zero_mem _, by simpa [mem_filtration_zero_iff] using hz⟩
  | succ n ih =>
    obtain ⟨a, ha, han⟩ := ih
    -- Divide the remainder by `x ^ n` and match its residue with a residue from below.
    have hpow : algebraMap F F' x ^ n ∈ P'.filtration n := by
      simpa [P'.ord_pow, hx'o] using P'.mem_filtration_ord (algebraMap F F' x ^ n)
    have hy : (z - algebraMap F F' a) / algebraMap F F' x ^ n ∈ P'.integers := by
      have hinv : (algebraMap F F' x ^ n)⁻¹ ∈ P'.filtration (-n) := by
        simpa [P'.ord_inv, P'.ord_pow, hx'o] using
          P'.mem_filtration_ord (algebraMap F F' x ^ n)⁻¹
      simpa [div_eq_mul_inv, mem_filtration_zero_iff] using P'.mul_mem_filtration han hinv
    obtain ⟨r, hr⟩ := hsurj (IsLocalRing.residue P'.integers ⟨_, hy⟩)
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective r
    rw [IsLocalRing.ResidueField.algebraMap_residue, residue_eq_iff_sub_mem_filtration_one,
      coe_algebraMap_integers] at hr
    refine ⟨a + c * x ^ n, add_mem ha (mul_mem c.2 (pow_mem hxi n)), ?_⟩
    have hrem := P'.mul_mem_filtration hpow (neg_mem hr)
    rw [neg_sub, mul_sub, mul_div_cancel₀ _ (pow_ne_zero n hx'0)] at hrem
    rw [Nat.cast_succ]
    convert hrem using 1
    simp only [map_add, map_mul, map_pow]
    ring

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:134` (proof source at `5a01f5fe3621`).
 By weak approximation, some `w` is congruent to `y` at `P'` and to `0` at the other places over
`P`, to order `e(Q' ∣ P) · m` at each place `Q'` over `P`. -/
private theorem exists_sub_mem_filtration_and_forall_mem_filtration (y : F') (m : ℕ) :
    ∃ w : F', w - y ∈ P'.filtration (ramificationIdx F P' * m) ∧
      ∀ Q' : Place k' F', Q'.restrict k F = P'.restrict k F → Q' ≠ P' →
        w ∈ Q'.filtration (ramificationIdx F Q' * m) := by
  classical
  have := (finite_setOf_restrict_eq (k' := k') (F' := F') k F (P'.restrict k F)).to_subtype
  obtain ⟨w, hw⟩ := exists_forall_ord_sub_eq
    (P := fun Q' : {Q' : Place k' F' | Q'.restrict k F = P'.restrict k F} ↦ (Q' : Place k' F'))
    Subtype.val_injective (fun Q' ↦ if (Q' : Place k' F') = P' then y else 0)
    (fun Q' ↦ ramificationIdx F (Q' : Place k' F') * m)
  have hwfil (Q' : Place k' F') (hQ' : Q'.restrict k F = P'.restrict k F) :
      w - (if Q' = P' then y else 0) ∈ Q'.filtration (ramificationIdx F Q' * m) := by
    have := Q'.mem_filtration_ord (w - if Q' = P' then y else 0)
    rwa [hw ⟨Q', hQ'⟩] at this
  exact ⟨w, by simpa using hwfil P' rfl, fun Q' hQ' hne ↦ by simpa [hne] using hwfil Q' hQ'⟩

variable {k F} in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:153` (proof source at `5a01f5fe3621`).
 An integral function vanishing to order `m` at a place lies in the `m`-th power of the ideal
generated by a uniformizer. -/
private theorem mem_span_pow_of_mem_filtration {P : Place k F} {x : P.integers}
    (hx : P.ord (x : F) = 1) {m : ℕ} {c : P.integers} (hc : (c : F) ∈ P.filtration m) :
    c ∈ Ideal.span {x ^ m} := by
  have hx0 : (x : F) ≠ 0 := by
    rintro h
    rw [h, ord_zero] at hx
    omega
  rw [Ideal.mem_span_singleton']
  have hcx : (c : F) * (x : F) ^ (-(m : ℤ)) ∈ P.integers := by
    have h2 : (x : F) ^ (-(m : ℤ)) ∈ P.filtration (-m) := by
      simpa [P.ord_zpow, hx] using P.mem_filtration_ord ((x : F) ^ (-(m : ℤ)))
    simpa using P.mul_mem_filtration hc h2
  refine ⟨⟨_, hcx⟩, Subtype.ext ?_⟩
  simp [zpow_neg, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx0)]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:169` (proof source at `5a01f5fe3621`).
 A uniformizer of the place below has order `e(Q' ∣ P)` at every place `Q'` above it. -/
private theorem zpow_mem_filtration {P : Place k F} {x : F} (hx : P.ord x = 1)
    {Q' : Place k' F'} (hQ' : Q'.restrict k F = P) (j : ℤ) :
    algebraMap F F' x ^ j ∈ Q'.filtration (ramificationIdx F Q' * j) := by
  have := Q'.mem_filtration_ord (algebraMap F F' x ^ j)
  rwa [Q'.ord_zpow, ord_algebraMap_restrict k F Q', hQ', hx, mul_one, mul_comm] at this

variable [Algebra.IsIntegral k k']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:179` (proof source at `5a01f5fe3621`).
 An element of the local model `𝒪'_P` vanishing to order `e(Q' ∣ P) · m` at every place `Q'` over
`P` lies in `x ^ m 𝒪'_P`, for a uniformizer `x` of `P`. -/
private theorem mem_map_span_pow_of_forall_mem_filtration (hF' : IsFunctionField k' F')
    {P : Place k F} {x : P.integers} (hx : P.ord (x : F) = 1) (m : ℕ)
    (s : integralClosure P.integers F')
    (hs : ∀ Q' : Place k' F', Q'.restrict k F = P →
      (s : F') ∈ Q'.filtration (ramificationIdx F Q' * m)) :
    s ∈ (Ideal.span {x ^ m}).map (algebraMap P.integers (integralClosure P.integers F')) := by
  have hx0 : algebraMap F F' x ≠ 0 := (map_ne_zero _).mpr fun h ↦ by
    rw [h, ord_zero] at hx
    omega
  have hs' : (s : F') * algebraMap F F' x ^ (-(m : ℤ)) ∈ integralClosure P.integers F' :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun Q' hQ' ↦ by
      have := Q'.mul_mem_filtration (hs Q' hQ') (zpow_mem_filtration k F hx hQ' (-m))
      rwa [mul_neg, add_neg_cancel, mem_filtration_zero_iff] at this
  have hs_eq : s = algebraMap P.integers (integralClosure P.integers F') (x ^ m) * ⟨_, hs'⟩ := by
    refine Subtype.ext ?_
    simp only [map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
      zpow_neg, zpow_natCast]
    rw [IsScalarTower.algebraMap_apply P.integers F F', mul_left_comm,
      ValuationSubring.algebraMap_apply, mul_inv_cancel₀ (pow_ne_zero m hx0), mul_one]
  rw [hs_eq]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:203` (proof source at `5a01f5fe3621`).
 Conversely, an element of `x ^ m 𝒪'_P` vanishes to order `e(Q' ∣ P) · m` at every place `Q'`
over `P`. -/
private theorem mem_filtration_of_mem_map_span_pow (hF' : IsFunctionField k' F')
    {P : Place k F} {x : P.integers} (hx : P.ord (x : F) = 1) {m : ℕ}
    {s : integralClosure P.integers F'}
    (hs : s ∈ (Ideal.span {x ^ m}).map (algebraMap P.integers (integralClosure P.integers F')))
    {Q' : Place k' F'} (hQ' : Q'.restrict k F = P) :
    (s : F') ∈ Q'.filtration (ramificationIdx F Q' * m) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hs
  obtain ⟨s', rfl⟩ := hs
  have := Q'.mul_mem_filtration (Q'.mem_filtration_zero_iff.mpr
    ((isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp s'.2 Q' hQ'))
    (zpow_mem_filtration k F hx hQ' m)
  simpa [IsScalarTower.algebraMap_apply P.integers F F'] using this

variable [Algebra.IsSeparable F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:222` (proof source at `5a01f5fe3621`).
 **The trace is the identity near a place of local degree one.** Let `P'` be a place of `F'`
over `P` with `e(P' ∣ P) = f(P' ∣ P) = 1`. If `z` is regular at `P'` and vanishes to order at
least `e(Q' ∣ P) · m` at every other place `Q'` of `F'` over `P`, then `Tr_{F'/F} z` is congruent
to `z` at `P'` to order `m`. -/
theorem algebraMap_trace_sub_mem_filtration (hF' : IsFunctionField k' F')
    (he : ramificationIdx F P' = 1) (hf : relativeDegree k F P' = 1) (m : ℕ) {z : F'}
    (hz : z ∈ P'.integers)
    (hzQ : ∀ Q' : Place k' F', Q'.restrict k F = P'.restrict k F → Q' ≠ P' →
      z ∈ Q'.filtration (ramificationIdx F Q' * m)) :
    algebraMap F F' (Algebra.trace F F' z) - z ∈ P'.filtration m := by
  classical
  set P := P'.restrict k F with hPdef
  -- The local model `𝒪'_P`, finite and free over `𝒪_P`.
  let S := integralClosure P.integers F'
  have : Module.Free P.integers S := .of_basis (integralClosureFinBasis F' P)
  have := isLocalization_integralClosure F' P
  have hreg (s : S) (Q' : Place k' F') (hQ' : Q'.restrict k F = P) : (s : F') ∈ Q'.integers :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp s.2 Q' hQ'
  have hint {s : F'} (hP' : s ∈ P'.integers) (hs : ∀ Q' : Place k' F', Q'.restrict k F = P →
      Q' ≠ P' → s ∈ Q'.filtration (ramificationIdx F Q' * m)) : s ∈ S :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun Q' hQ' ↦ by
      by_cases h : Q' = P'
      · exact h ▸ hP'
      · exact Q'.mem_filtration_zero_iff.mp (Q'.filtration_antitone (by positivity) (hs Q' hQ' h))
  let zS : S := ⟨z, hint hz hzQ⟩
  -- A uniformizer `x` of `P`; it is also one at `P'`.
  obtain ⟨x, hx⟩ := P.exists_isUniformizer
  have hxo : P.ord x = 1 := P.isUniformizer_iff_ord_eq_one.mp hx
  let xR : P.integers := ⟨x, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  -- `z` is congruent at `P'` to some `a ∈ 𝒪_P`; it remains to see that so is its trace.
  obtain ⟨a, ha, hza⟩ := exists_sub_algebraMap_mem_filtration k F P' he hf m hz
  suffices hkey : Algebra.trace P.integers S zS - ⟨a, ha⟩ ∈ Ideal.span {xR ^ m} by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hkey
    have htr : Algebra.trace F F' z = algebraMap P.integers F (Algebra.trace P.integers S zS) :=
      Algebra.trace_localization P.integers P.integers⁰ (Sₘ := F') zS
    have hr' : Algebra.trace F F' z - a = (r : F) * x ^ m := by
      rw [htr]
      exact (congrArg Subtype.val hr).symm
    have hrm : algebraMap F F' ((r : F) * x ^ m) ∈ P'.filtration m := by
      have := P'.mul_mem_filtration ((P'.mem_filtration_zero_iff).mpr
        ((mem_integers_restrict_iff k F P' _).mp r.2)) (zpow_mem_filtration k F hxo rfl m)
      simpa [he] using this
    rw [← sub_add_sub_cancel _ (algebraMap F F' a), ← map_sub, hr']
    exact add_mem hrm (by simpa using neg_mem hza)
  -- Work modulo `I = (x ^ m)`.
  set I : Ideal P.integers := Ideal.span {xR ^ m} with hI
  -- `w ≡ 1` at `P'` and `w ≡ 0` at the other places over `P`, to order `m`.
  obtain ⟨w, hw1, hw0⟩ := exists_sub_mem_filtration_and_forall_mem_filtration k F P' 1 m
  rw [he, Nat.cast_one, one_mul] at hw1
  have hwP : w ∈ P'.integers := by
    have := add_mem (P'.filtration_antitone (Nat.cast_nonneg m) hw1)
      (P'.mem_filtration_zero_iff.mpr P'.integers.one_mem)
    rwa [sub_add_cancel, mem_filtration_zero_iff] at this
  let wS : S := ⟨w, hint hwP hw0⟩
  -- A product of an element small at `P'` and one small at the other places lies in `I 𝒪'_P`.
  have hprod (u v : S) (hu : (u : F') ∈ P'.filtration m)
      (hv : ∀ Q' : Place k' F', Q'.restrict k F = P → Q' ≠ P' →
        (v : F') ∈ Q'.filtration (ramificationIdx F Q' * m)) :
      u * v ∈ I.map (algebraMap P.integers S) := by
    refine mem_map_span_pow_of_forall_mem_filtration k F hF' hxo m _ fun Q' hQ' ↦ ?_
    by_cases h : Q' = P'
    · subst h
      simpa [he] using Q'.mul_mem_filtration hu (Q'.mem_filtration_zero_iff.mpr (hreg v Q' hQ'))
    · simpa using Q'.mul_mem_filtration (Q'.mem_filtration_zero_iff.mpr (hreg u Q' hQ'))
        (hv Q' hQ' h)
  -- Modulo `I 𝒪'_P`, an element `b` congruent at `P'` to `c ∈ 𝒪_P` acts on `w` as `c`.
  have hact (b : S) (c : P.integers) (hbc : (b : F') - algebraMap F F' c ∈ P'.filtration m) :
      b * wS - algebraMap P.integers S c * wS ∈ I.map (algebraMap P.integers S) := by
    rw [← sub_mul]
    exact hprod _ wS (by simpa [IsScalarTower.algebraMap_apply P.integers F F'] using hbc) hw0
  -- So the class of `w` is an idempotent of rank one, and its trace is `1` modulo `I`.
  have htrw : Algebra.trace P.integers S wS - 1 ∈ I := by
    refine Algebra.trace_sub_one_mem_of_mul_self_sub_mem ?_ (fun b ↦ ?_) (fun c hc ↦ ?_)
    · simpa using hact wS 1 (by simpa using hw1)
    · obtain ⟨c, hc, hbc⟩ := exists_sub_algebraMap_mem_filtration k F P' he hf m (hreg b P' rfl)
      exact ⟨⟨c, hc⟩, by simpa [mul_comm wS] using hact b ⟨c, hc⟩ hbc⟩
    · -- `c = c w - c (w - 1)` vanishes to order `m` at `P'`, hence at `P`, so `c ∈ I`.
      have h2 : algebraMap F F' c * (w - 1) ∈ P'.filtration m := by
        simpa using P'.mul_mem_filtration (P'.mem_filtration_zero_iff.mpr
          ((mem_integers_restrict_iff k F P' _).mp c.2)) hw1
      have hcw := mem_filtration_of_mem_map_span_pow k F hF' hxo hc (Q' := P') rfl
      rw [he, Nat.cast_one, one_mul] at hcw
      have hc' : algebraMap F F' c ∈ P'.filtration m := by
        convert sub_mem hcw h2 using 1
        simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, wS,
          IsScalarTower.algebraMap_apply P.integers F F', ValuationSubring.algebraMap_apply]
        ring
      refine mem_span_pow_of_mem_filtration hxo ?_
      rcases eq_or_ne (c : F) 0 with h | h
      · simp [h]
      rw [mem_filtration_iff_le_ord _ h]
      have := (P'.mem_filtration_iff_le_ord ((map_ne_zero _).mpr h)).mp hc'
      rwa [ord_algebraMap_restrict k F P', he, Nat.cast_one, one_mul] at this
  -- The class of `z` is `a` times the class of `w`, so its trace is `a` modulo `I`.
  have hzw : zS - algebraMap P.integers S ⟨a, ha⟩ * wS ∈ I.map (algebraMap P.integers S) := by
    have h1 : zS - zS * wS ∈ I.map (algebraMap P.integers S) := by
      rw [show zS - zS * wS = (1 - wS) * zS by ring]
      exact hprod _ _ (by simpa using neg_mem hw1) hzQ
    simpa using add_mem h1 (hact zS ⟨a, ha⟩ hza)
  have hlin : Algebra.trace P.integers S (zS - algebraMap P.integers S ⟨a, ha⟩ * wS) +
      ⟨a, ha⟩ * (Algebra.trace P.integers S wS - 1) =
        Algebra.trace P.integers S zS - ⟨a, ha⟩ := by
    rw [map_sub, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    ring
  rw [← hlin]
  exact add_mem (Algebra.trace_mem_of_mem_map hzw) (I.mul_mem_left _ htrw)


/-! ### The trace at an unramified place over a rational place -/

section Expansion

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
variable [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
variable (P' : Place k F') [Algebra.IsSeparable k P'.ResidueField]
variable {P : Place k F} (hPP' : P'.restrict k F = P) {t : F} (ht : P.ord t = 1)
  (ht' : P'.ord (algebraMap F F' t) = 1)

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

include hPP' ht ht' in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:352` (proof source at `5a01f5fe3621`).
 **The trace commutes with expansions at an unramified place over a rational place.** Let `P`
be a rational place of `F` with uniformizer `t`, and let `P'` be a place of `F'` over `P` at which
`t` is still a uniformizer, that is `e(P' ∣ P) = 1`, with residue field `F'_{P'}` separable over
`k`. If `z` is regular at `P'` and vanishes to order at least `e(Q' ∣ P) · m` at every other place
`Q'` over `P`, then, to order `m` at `P`,

`Tr_{F'/F} z ≡ ∑_{i < m} Tr_{F'_{P'}/k} (aᵢ) tⁱ`,

where `∑ aᵢ tⁱ` is the expansion of `z` at `P'` with coefficients in `F'_{P'}`.

Classically, the completion of `F'` at `P'` is `F'_{P'}((t))`, whose trace over `k((t))` is the
coefficientwise trace, and the hypothesis on `z` makes the local traces at the other places over
`P` negligible to order `m`. -/
theorem trace_sub_sum_mem_filtration (hF' : IsFunctionField k F') (hP : P.degree = 1) (m : ℕ)
    (z : P'.integers) (hzQ : ∀ Q' : Place k F', Q'.restrict k F = P → Q' ≠ P' →
      (z : F') ∈ Q'.filtration (ramificationIdx F Q' * m)) :
    Algebra.trace F F' z - ∑ i : Fin m, algebraMap k F (Algebra.trace k P'.ResidueField
      (PowerSeries.coeff i (P'.powerSeriesExpansionResidueField ht' z))) * t ^ (i : ℕ) ∈
        P.filtration m := by
  -- Outline: in the local model `S = 𝒪'_P`, modulo `I = (t ^ m)`, apply
  -- `Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem` with `w = W ≡ 1` at `P'`, the basis
  -- `b j` of lifts of a `k`-basis `β j` of `F'_{P'}` with constant expansions, and the matrix
  -- `a j l = ∑ᵢ [cᵢ]ⱼₗ tⁱ` of multiplication by the expansion coefficients `cᵢ` of `z`. Each of
  -- its five hypotheses is a membership in `I S`, checked at `P'` on truncated expansions
  -- (`hfilt`) and at the other places over `P` by smallness (`Small`).
  classical
  subst hPP'
  set P := P'.restrict k F with hPdef
  have he : ramificationIdx F P' = 1 := by
    have h := ord_algebraMap_restrict k F P' t
    rw [ht', ← hPdef, ht, mul_one] at h
    exact_mod_cast h.symm
  have : FiniteDimensional k P'.ResidueField := P'.finiteDimensional_residueField hF'
  -- The local model `𝒪'_P`, finite and free over `𝒪_P`.
  let S := integralClosure P.integers F'
  have : Module.Free P.integers S := .of_basis (integralClosureFinBasis F' P)
  have := isLocalization_integralClosure F' P
  have hreg (s : S) (Q' : Place k F') (hQ' : Q'.restrict k F = P) : (s : F') ∈ Q'.integers :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp s.2 Q' hQ'
  -- Functions vanishing to order `e(Q' ∣ P) · m` at the places `Q' ≠ P'` over `P`.
  let Small (y : F') : Prop := ∀ Q' : Place k F', Q'.restrict k F = P → Q' ≠ P' →
    y ∈ Q'.filtration (ramificationIdx F Q' * m)
  have hint {y : F'} (hy : y ∈ P'.integers) (hs : Small y) : y ∈ S :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun Q' hQ' ↦ by
      by_cases h : Q' = P'
      · exact h ▸ hy
      · exact Q'.mem_filtration_zero_iff.mp (Q'.filtration_antitone (by positivity) (hs Q' hQ' h))
  have hsmall_mul {y : F'} (hy : Small y) (s : S) : Small (y * s) := fun Q' hQ' h ↦ by
    simpa using Q'.mul_mem_filtration (hy Q' hQ' h)
      (Q'.mem_filtration_zero_iff.mpr (hreg s Q' hQ'))
  have hsmall_mul' (s : S) {y : F'} (hy : Small y) : Small (s * y) := by
    simpa only [mul_comm] using hsmall_mul hy s
  have hsmall_sub {y y' : F'} (hy : Small y) (hy' : Small y') : Small (y - y') :=
    fun Q' hQ' h ↦ sub_mem (hy Q' hQ' h) (hy' Q' hQ' h)
  have hsmall_sum {n : ℕ} {y : Fin n → F'} (hy : ∀ i, Small (y i)) : Small (∑ i, y i) :=
    fun Q' hQ' h ↦ sum_mem fun i _ ↦ hy i Q' hQ' h
  -- Work modulo `I = (t ^ m)`; membership in `I 𝒪'_P` is read off at the places over `P`.
  let xR : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  set I : Ideal P.integers := Ideal.span {xR ^ m} with hI
  have hIS (s : S) (h1 : (s : F') ∈ P'.filtration m) (h2 : Small s) :
      s ∈ I.map (algebraMap P.integers S) := by
    refine mem_map_span_pow_of_forall_mem_filtration k F hF' (x := xR) ht m s fun Q' hQ' ↦ ?_
    by_cases h : Q' = P'
    · subst h
      simpa [he] using h1
    · exact h2 Q' hQ' h
  -- Expansions at `P'`, as a ring homomorphism on `𝒪'_P`.
  set E := P'.powerSeriesExpansionResidueField ht'
  let ιS : S →+* P'.integers :=
    { toFun := fun s ↦ ⟨s, hreg s P' rfl⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  let Φ : S →+* PowerSeries P'.ResidueField := E.toRingHom.comp ιS
  have hΦ (s : S) : Φ s = E ⟨s, hreg s P' rfl⟩ := rfl
  have hfiltE (y : P'.integers) : (y : F') ∈ P'.filtration m ↔ PowerSeries.trunc m (E y) = 0 := by
    rw [PowerSeries.trunc_eq_zero_iff_le_order,
      mem_filtration_iff_le_order_powerSeriesExpansionResidueField]
  have hfilt (s : S) : (s : F') ∈ P'.filtration m ↔ PowerSeries.trunc m (Φ s) = 0 :=
    hfiltE ⟨s, hreg s P' rfl⟩
  have hΦk (c : k) : Φ (algebraMap P.integers S (algebraMap k P.integers c)) =
      PowerSeries.C (algebraMap k P'.ResidueField c) := by
    have h : (⟨_, hreg (algebraMap P.integers S (algebraMap k P.integers c)) P' rfl⟩ :
        P'.integers) = algebraMap k P'.integers c := Subtype.ext (by
      rw [coe_algebraMap_constants]
      simp [IsScalarTower.algebraMap_apply P.integers F F', coe_algebraMap_constants,
        ← IsScalarTower.algebraMap_apply k F F'])
    rw [hΦ, h, AlgHom.commutes, PowerSeries.algebraMap_apply]
  have hΦt : Φ (algebraMap P.integers S xR) = PowerSeries.X := by
    rw [hΦ, ← powerSeriesExpansionResidueField_uniformizer P' ht']
    congr 1
  -- Lifts with prescribed expansion to order `m`, small at the other places over `P`.
  have hlift (g : PowerSeries P'.ResidueField) :
      ∃ s : S, Small s ∧ PowerSeries.trunc m (Φ s) = PowerSeries.trunc m g := by
    obtain ⟨y, hy⟩ := P'.exists_trunc_powerSeriesExpansionResidueField_eq ht' g m
    obtain ⟨w, hw, hwQ⟩ := exists_sub_mem_filtration_and_forall_mem_filtration k F P' (y : F') m
    rw [he, Nat.cast_one, one_mul] at hw
    have hwint : w ∈ P'.integers := by
      have := add_mem (P'.filtration_antitone (Nat.cast_nonneg m) hw)
        (P'.mem_filtration_zero_iff.mpr y.2)
      rwa [sub_add_cancel, mem_filtration_zero_iff] at this
    refine ⟨⟨w, hint hwint hwQ⟩, hwQ, ?_⟩
    have hdiff := (hfiltE (⟨w, hwint⟩ - y)).mp (by simpa using hw)
    rw [map_sub, map_sub, sub_eq_zero] at hdiff
    rw [hΦ, ← hy]
    exact hdiff
  -- A basis of `F'_{P'}` over `k`, lifted to functions with constant expansions to order `m`.
  let β := Module.finBasis k P'.ResidueField
  choose b hbS hbt using fun j ↦ hlift (PowerSeries.C (β j))
  obtain ⟨W, hWS, hWt⟩ := hlift 1
  have hW1 : (W : F') - 1 ∈ P'.filtration m := by
    have := (hfilt (W - 1)).mpr (by rw [map_sub Φ, map_one, map_sub, hWt, sub_self])
    simpa using this
  have hWmul (y : F') (hy : y ∈ P'.integers) : (W : F') * y - y ∈ P'.filtration m := by
    simpa [sub_mul] using P'.mul_mem_filtration hW1 (P'.mem_filtration_zero_iff.mpr hy)
  -- The truncated expansion of `∑ⱼ (∑ᵢ cᵢⱼ tⁱ) bⱼ` is `∑ᵢ (∑ⱼ cᵢⱼ βⱼ) Xⁱ`.
  have htrunc_sum (c : Fin (Module.finrank k P'.ResidueField) → Fin m → k) :
      PowerSeries.trunc m (Φ (∑ j, algebraMap P.integers S
        (∑ i : Fin m, algebraMap k P.integers (c j i) * xR ^ (i : ℕ)) * b j)) =
      PowerSeries.trunc m (∑ i : Fin m, PowerSeries.C (∑ j, c j i • β j) *
        PowerSeries.X ^ (i : ℕ)) := by
    have hj (j) : PowerSeries.trunc m (Φ (algebraMap P.integers S
        (∑ i : Fin m, algebraMap k P.integers (c j i) * xR ^ (i : ℕ)) * b j)) =
        PowerSeries.trunc m ((∑ i : Fin m, PowerSeries.C (algebraMap k P'.ResidueField (c j i)) *
          PowerSeries.X ^ (i : ℕ)) * PowerSeries.C (β j)) := by
      rw [map_mul, ← PowerSeries.trunc_mul_trunc, hbt j, PowerSeries.trunc_mul_trunc]
      simp only [map_sum, map_mul, map_pow, hΦk, hΦt]
    rw [map_sum, map_sum, Finset.sum_congr rfl fun j _ ↦ hj j, ← map_sum]
    congr 1
    ext n
    rw [PowerSeries.coeff_sum_C_mul_X_pow, map_sum]
    simp_rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_sum_C_mul_X_pow]
    split_ifs with hn
    · simp [Algebra.smul_def]
    · simp
  have htrunc_self (φ : PowerSeries P'.ResidueField) : PowerSeries.trunc m φ =
      PowerSeries.trunc m (∑ i : Fin m, PowerSeries.C (PowerSeries.coeff i φ) *
        PowerSeries.X ^ (i : ℕ)) := by
    ext n
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, PowerSeries.coeff_sum_C_mul_X_pow]
    split_ifs <;> rfl
  have hcoe (r : P.integers) : algebraMap P.integers F' r = algebraMap F F' r := by
    rw [IsScalarTower.algebraMap_apply P.integers F F', ValuationSubring.algebraMap_apply]
  have hsmallR (r : P.integers) {y : F'} (hy : Small y) : Small (algebraMap P.integers F' r * y) :=
    by simpa using hsmall_mul' (algebraMap P.integers S r) hy
  have hmapfilt {r : F} (hr : r ∈ P.filtration m) : algebraMap F F' r ∈ P'.filtration m := by
    rcases eq_or_ne r 0 with rfl | h0
    · simp
    rw [mem_filtration_iff_le_ord _ h0] at hr
    rw [mem_filtration_iff_le_ord _ ((map_ne_zero _).mpr h0), ord_algebraMap_restrict k F P', he]
    simpa using hr
  -- The data of `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`.
  let zS : S := ⟨z, hint z.2 hzQ⟩
  have hΦz : Φ zS = E z := rfl
  set c : Fin m → P'.ResidueField := fun i ↦ PowerSeries.coeff i (E z) with hc
  let M : Fin m → Fin (Module.finrank k P'.ResidueField) →
    Fin (Module.finrank k P'.ResidueField) → k := fun i j l ↦ β.repr (c i * β j) l
  let a : Fin (Module.finrank k P'.ResidueField) → Fin (Module.finrank k P'.ResidueField) →
    P.integers := fun j l ↦ ∑ i : Fin m, algebraMap k P.integers (M i j l) * xR ^ (i : ℕ)
  have hwb (j) : W * b j - b j ∈ I.map (algebraMap P.integers S) :=
    hIS _ (by push_cast; exact hWmul _ (hreg (b j) P' rfl))
      (by push_cast; exact hsmall_sub (hsmall_mul' W (hbS j)) (hbS j))
  have hspan (s : S) : ∃ cs : Fin (Module.finrank k P'.ResidueField) → P.integers,
      W * s - ∑ j, algebraMap P.integers S (cs j) * b j ∈ I.map (algebraMap P.integers S) := by
    let cs : Fin (Module.finrank k P'.ResidueField) → P.integers := fun j ↦
      ∑ i : Fin m, algebraMap k P.integers (β.repr (PowerSeries.coeff i (Φ s)) j) * xR ^ (i : ℕ)
    refine ⟨cs, hIS _ ?_ ?_⟩
    · have h2 := (hfilt (s - ∑ j, algebraMap P.integers S (cs j) * b j)).mpr (by
        rw [map_sub, map_sub, htrunc_sum, htrunc_self (Φ s), sub_eq_zero]
        simp only [β.sum_repr])
      have h1 := hWmul _ (hreg s P' rfl)
      convert add_mem h1 h2 using 1
      push_cast
      ring
    · push_cast
      exact hsmall_sub (hsmall_mul hWS s) (hsmall_sum fun j ↦ hsmallR _ (hbS j))
  have hindep (cs : Fin (Module.finrank k P'.ResidueField) → P.integers)
      (hcs : ∑ j, algebraMap P.integers S (cs j) * b j ∈ I.map (algebraMap P.integers S))
      (j) : cs j ∈ I := by
    have h := mem_filtration_of_mem_map_span_pow k F hF' (x := xR) ht hcs (Q' := P') rfl
    rw [he, Nat.cast_one, one_mul] at h
    -- Replace each `cs j` by its truncated expansion at `P`.
    let τ := fun j ↦ P.truncatedExpansion hP ht m (cs j)
    let r := fun j ↦ ∑ i : Fin m, algebraMap k P.integers (τ j i) * xR ^ (i : ℕ)
    have hτ (j) : ((cs j - r j : P.integers) : F) ∈ P.filtration m := by
      simpa [r, xR, coe_algebraMap_constants] using
        P.sub_sum_truncatedExpansion_mem_filtration hP ht m (cs j)
    have hr : ((∑ j, algebraMap P.integers S (r j) * b j : S) : F') ∈ P'.filtration m := by
      have hd : ((∑ j, algebraMap P.integers S (cs j - r j) * b j : S) : F') ∈
          P'.filtration m := by
        push_cast
        refine sum_mem fun j _ ↦ ?_
        simpa [hcoe] using P'.mul_mem_filtration (hmapfilt (hτ j))
          (P'.mem_filtration_zero_iff.mpr (hreg (b j) P' rfl))
      convert sub_mem h hd using 1
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      push_cast
      ring
    have hzero := (hfilt _).mp hr
    rw [htrunc_sum] at hzero
    have hτ0 (i : Fin m) (j) : τ j i = 0 := by
      have hi := congrArg (Polynomial.coeff · (i : ℕ)) hzero
      simp only [PowerSeries.coeff_trunc, PowerSeries.coeff_sum_C_mul_X_pow, i.2, ↓reduceIte,
        ↓reduceDIte, Polynomial.coeff_zero] at hi
      exact Fintype.linearIndependent_iff.mp β.linearIndependent (fun j ↦ τ j i) hi j
    have hcs : ((cs j : P.integers) : F) ∈ P.filtration m := by
      simpa [r, hτ0] using hτ j
    exact mem_span_pow_of_mem_filtration ht hcs
  have hz : zS * W - zS ∈ I.map (algebraMap P.integers S) :=
    hIS _ (by push_cast; rw [mul_comm]; exact hWmul _ z.2)
      (by push_cast; exact hsmall_sub (hsmall_mul hzQ W) hzQ)
  have hzb (j) : zS * b j - ∑ l, algebraMap P.integers S (a j l) * b l ∈
      I.map (algebraMap P.integers S) := by
    refine hIS _ ((hfilt _).mpr ?_) ?_
    · rw [map_sub, map_sub, htrunc_sum (fun l i ↦ M i j l), map_mul, ← PowerSeries.trunc_mul_trunc,
        hbt j, PowerSeries.trunc_mul_trunc, hΦz, sub_eq_zero]
      ext n
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, PowerSeries.coeff_sum_C_mul_X_pow,
        PowerSeries.coeff_mul_C]
      split_ifs with hn
      · simp only [M, β.sum_repr, hc]
      · rfl
    · push_cast
      exact hsmall_sub (hsmall_mul hzQ (b j)) (hsmall_sum fun l ↦ hsmallR _ (hbS l))
  have key := Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem hwb hspan hindep hz hzb
  -- The diagonal of `a` is the trace of the coefficients.
  have hdiag : ∑ j, a j j = ∑ i : Fin m,
      algebraMap k P.integers (Algebra.trace k P'.ResidueField (c i)) * xR ^ (i : ℕ) := by
    simp only [a, M]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_mul, ← map_sum, Algebra.trace_eq_matrix_trace β, Matrix.trace]
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [hdiag] at key
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp key
  have htr : Algebra.trace F F' z = algebraMap P.integers F (Algebra.trace P.integers S zS) :=
    Algebra.trace_localization P.integers P.integers⁰ (Sₘ := F') zS
  have hq' := congrArg (fun u : P.integers ↦ (u : F)) hq
  push_cast at hq'
  have htm : t ^ m ∈ P.filtration m := by
    have := P.mem_filtration_ord (t ^ m)
    rwa [P.ord_pow, ht, mul_one] at this
  have heq : ((Algebra.trace P.integers S zS : P.integers) : F) - ∑ i : Fin m, algebraMap k F
      (Algebra.trace k P'.ResidueField (PowerSeries.coeff i (E z))) * t ^ (i : ℕ) =
      (q : F) * t ^ m := by
    rw [hq']
  rw [htr, ValuationSubring.algebraMap_apply, heq]
  simpa using P.mul_mem_filtration (P.mem_filtration_zero_iff.mpr q.2) htm

include hPP' ht ht' in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/Trace.lean:598` (proof source at `5a01f5fe3621`).
 **Residues commute with the trace at an unramified place over a rational place.** Let `P` be
a rational place of `F` with uniformizer `t`, and let `P'` be a place of `F'` over `P` at which `t`
is still a uniformizer, with residue field `F'_{P'}` separable over `k`. For a function `v` regular
at every other place of `F'` over `P`,

`res_{P,t} (Tr_{F'/F} v) = Tr_{F'_{P'}/k} (res_{P',t} v)`.

This is the residue form of `TauCeti.Place.trace_sub_sum_mem_filtration`. -/
theorem residue_trace (hF' : IsFunctionField k F') (hP : P.degree = 1) {v : F'}
    (hv : ∀ Q' : Place k F', Q'.restrict k F = P → Q' ≠ P' → v ∈ Q'.integers) :
    P.residue hP ht (Algebra.trace F F' v) = P'.traceResidue ht' v := by
  set n := (-P'.ord v).toNat
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  -- `t ^ (n + 1) v` is regular at `P'` and vanishes to order `e(Q' ∣ P) (n + 1)` at the others.
  have hz : algebraMap F F' t ^ (n + 1) * v ∈ P'.integers := by
    have h1 : algebraMap F F' t ^ (n + 1) ∈ P'.filtration (-P'.ord v) :=
      P'.filtration_antitone (by rw [P'.ord_pow, ht']; omega) (P'.mem_filtration_ord _)
    rw [← mem_filtration_zero_iff]
    simpa using P'.mul_mem_filtration h1 (P'.mem_filtration_ord v)
  have hzQ (Q' : Place k F') (hQ' : Q'.restrict k F = P) (hne : Q' ≠ P') :
      algebraMap F F' t ^ (n + 1) * v ∈ Q'.filtration (ramificationIdx F Q' * (n + 1 : ℕ)) := by
    have h := zpow_mem_filtration k F ht hQ' ((n + 1 : ℕ) : ℤ)
    rw [zpow_natCast] at h
    simpa using Q'.mul_mem_filtration h (Q'.mem_filtration_zero_iff.mpr (hv Q' hQ' hne))
  have hT := trace_sub_sum_mem_filtration P' hPP' ht ht' hF' hP (n + 1) ⟨_, hz⟩ hzQ
  have htr : Algebra.trace F F' (algebraMap F F' t ^ (n + 1) * v) =
      t ^ (n + 1) * Algebra.trace F F' v := by
    rw [← map_pow, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [htr] at hT
  -- The truncated expansion of `t ^ (n + 1) Tr v` at `P` is the trace of that of `t ^ (n + 1) v`.
  have hint : t ^ (n + 1) * Algebra.trace F F' v ∈ P.integers := by
    have hsum : ∑ i : Fin (n + 1), algebraMap k F (Algebra.trace k P'.ResidueField
        (PowerSeries.coeff i (P'.powerSeriesExpansionResidueField ht' ⟨_, hz⟩))) *
          t ^ (i : ℕ) ∈ P.integers :=
      sum_mem fun i _ ↦ mul_mem (by rw [← coe_algebraMap_constants]; exact SetLike.coe_mem _)
        (pow_mem (P.mem_integers_iff_ord_nonneg.mpr (by omega)) _)
    have := add_mem (P.mem_filtration_zero_iff.mp (P.filtration_antitone (by omega) hT)) hsum
    rwa [sub_add_cancel] at this
  rw [P.residue_eq_coeff_powerSeriesExpansion hP ht n hint,
    P.coeff_powerSeriesExpansion hP ht (n + 1) _ ⟨n, by omega⟩,
    (P.truncatedExpansion_eq_iff hP ht (n + 1) ⟨_, hint⟩ _).mpr hT, traceResidue_apply,
    P'.residueResidueField_eq_coeff_powerSeriesExpansionResidueField ht' n hz]

end Expansion

end Place

end TauCeti
end

end

/-! ## Source 40: `TauCeti.FieldTheory.FunctionField.Differential.Residue`
Original source SHA256: `0e151c4ec36873bd0ad52814b8960369605072ea9355029a7fb21287eb9f9512`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The local components of `dt` at a zero of `t - a` are residues

Let `F / k` be an algebraic function field and `t ∈ F` a separating element, and let `dt` be the
Weil differential `TauCeti.weilDifferentialOfSeparating`, the cotrace to `F` of the canonical
differential `η` of `k(t)`. At a place `P` of `F` whose residue field `F_P` is separable over `k`
and at which `t - a` is a prime element for some constant `a ∈ k`, `ord_P (t - a) = 1`, the local
component of `dt` is the trace residue in `t - a`:

`(dt)_P (u) = Tr_{F_P/k} (res_{P,t-a} (u))` for every `u ∈ F`.

At a rational place the trace is the identity and this is the residue `res_{P,t-a} (u)`. This is
Stichtenoth's Theorem 4.3.2(d), `(z · δ(x))_P (u) = res_P (u z dx)`, in its form for places of
arbitrary degree (Remark 4.3.7(d)), for `x = t` with `t - a` a prime element at `P` and `z = 1`.
It identifies the abstract local components of Weil differentials with the classical residues of
Laurent expansions.

The proof transports the rational-function-field case
(`TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C`) along the
cotrace. The place `P` lies over the zero `P_a` of `t - a` in `k(t)` with `e(P ∣ P_a) = 1`, and
`dt` is regular at every place over `P_a` because the different is effective. Weak approximation
moves `u`, without changing its principal part at `P`, to a function that is regular at the other
places over `P_a`; for such a function the local components of the cotrace over `P_a`
(`TauCeti.trace_finsum_repartitionDualComponent_weilDifferentialCotrace`) give
`(dt)_P (u) = η_{P_a} (Tr u) = res_{P_a,t-a} (Tr u)`. Finally the residue of the trace is the
trace residue (`TauCeti.Place.residue_trace`).

## Main results

* `repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue`:
  for a finite separable extension `F` of `k(t)`, the local component of the cotrace of `η` at a
  place with separable residue field where `t - a` is a prime element is `Tr ∘ res_{P,t-a}`.
* `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue`:
  `(dt)_P = Tr ∘ res_{P,t-a}`.
* `TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential` and
  `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`: at a rational place,
  `(dt)_P = res_{P,t-a}`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2(d) and Remark 4.3.7(d).
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

open _root_.TauCeti.AlgebraicGeometry Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-! ### The place below a place at which `t - a` is a prime element -/

section Below

variable {P : Place k F} {a : k}
  (ht : P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1)
include ht

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:84` (proof source at `5a01f5fe3621`).
 A place at which `t - a` is a prime element is unramified over `k(t)`, and `t - a` is a prime
element at the place below. -/
private theorem ramificationIdx_eq_one_and_ord_X_sub_C_eq_one :
    ramificationIdx (RatFunc k) P = 1 ∧
      (P.restrict k (RatFunc k)).ord (RatFunc.X - RatFunc.C a) = 1 := by
  have hord := ord_algebraMap_restrict k (RatFunc k) P (RatFunc.X - RatFunc.C a)
  rw [ht] at hord
  have he : ramificationIdx (RatFunc k) P = 1 := by
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) hord.symm
  rw [he, Nat.cast_one, one_mul] at hord
  exact ⟨he, hord.symm⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:95` (proof source at `5a01f5fe3621`).
 A place at which `t - a` is a prime element lies over the zero `P_a` of `t - a`. -/
private theorem restrict_eq_adicOfIrreducible_X_sub_C :
    P.restrict k (RatFunc k) = adicOfIrreducible (Polynomial.irreducible_X_sub_C a) := by
  have hX₀ := (ramificationIdx_eq_one_and_ord_X_sub_C_eq_one ht).2
  rcases eq_infty_or_exists_eq_adicOfIrreducible (P.restrict k (RatFunc k)) with h | ⟨q, hq, h⟩
  · -- `t - a` has a pole at infinity.
    rw [h, ord_infty, ← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub,
      RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C] at hX₀
    omega
  · -- `t - a` is a unit at the place of `q` unless `q` is associated to `X - a`.
    rw [h] at hX₀ ⊢
    by_contra hne
    rw [ord_adicOfIrreducible_X_sub_C_of_not_associated hq fun hassoc ↦
      hne ((adicOfIrreducible_eq_adicOfIrreducible_iff hq _).mpr hassoc)] at hX₀
    omega

omit ht in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:113` (proof source at `5a01f5fe3621`).
 **Moving a function off the other places over `P₀`**: every `u` agrees at `P`, modulo
functions regular there, with a function `v` that is regular at the other places over `P₀`. -/
private theorem exists_sub_mem_integers_forall_mem_integers (u : F) :
    ∃ v : F, v - u ∈ P.integers ∧
      ∀ Q : Place k F, Q.restrict k (RatFunc k) = P.restrict k (RatFunc k) → Q ≠ P →
        v ∈ Q.integers := by
  classical
  have hfin := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k)
    (P.restrict k (RatFunc k))).to_subtype
  -- By weak approximation, `v ≡ u` at `P` and `v ≡ 0` at the other places over `P₀`.
  obtain ⟨v, hv⟩ := exists_forall_ord_sub_eq
    (P := fun Q : {Q : Place k F | Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)} ↦
      (Q : Place k F))
    Subtype.val_injective (fun Q ↦ if (Q : Place k F) = P then u else 0) (fun _ ↦ 0)
  have hvQ (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)) :
      v - (if Q = P then u else 0) ∈ Q.integers := by
    rw [mem_integers_iff_ord_nonneg, hv ⟨Q, hQ⟩]
  exact ⟨v, by simpa using hvQ P rfl, fun Q hQ hne ↦ by simpa [hne] using hvQ Q hQ⟩

end Below

variable [Algebra.IsSeparable (RatFunc k) F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:139` (proof source at `5a01f5fe3621`).
 **The local component of `dt` at a zero of `t - a` is the trace residue in `t - a`**
(Stichtenoth, Theorem 4.3.2(d) and Remark 4.3.7(d)): for a finite separable extension `F` of
`k(t)` and a place `P` of `F` with residue field separable over `k`, at which the image of `t - a`
is a prime element, the local component at `P` of the cotrace of the canonical differential
`η = dt` of `k(t)` is `Tr_{F_P/k} ∘ res_{P,t-a}`. -/
theorem repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue
    (hF : IsFunctionField k F) {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {a : k}
    (ht : P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) P u =
      P.traceResidue ht u := by
  classical
  set η : ↥(weilDifferentialSpace k (RatFunc k)) :=
    ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ with hη
  set ω := weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF η with hω
  have hP₀ := restrict_eq_adicOfIrreducible_X_sub_C ht
  -- `dt` is regular at every place over `P_a`, since the different is effective.
  have hkill (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)) {v : F}
      (hv : v ∈ Q.integers) : repartitionDualComponent (ω : Module.Dual k _) Q v = 0 := by
    refine repartitionDualComponent_apply_eq_zero_of_le
      (weilDifferentialCotrace_mem_weilDifferentialFiltration (IsFunctionField.ratFunc k) hF η
        (isGreatest_ratFuncWeilDifferential k).1) Q ?_
    simp only [_root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_add, Divisor.coeff_conorm, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, hQ, hP₀,
      _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne (adicOfIrreducible_ne_infty _), mul_zero, zero_add,
      Divisor.coeff_different]
    exact (Q.mem_integers_iff.mp hv).trans (by simp)
  obtain ⟨v, hvu, hvQ⟩ := exists_sub_mem_integers_forall_mem_integers (P := P) u
  -- Over `P_a`, only `P` contributes to the local components of `dt` at `v`.
  have hsum : (∑ᶠ (Q : Place k F) (_ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)),
      repartitionDualComponent (ω : Module.Dual k _) Q v) =
        repartitionDualComponent (ω : Module.Dual k _) P v := by
    rw [finsum_eq_single _ P fun Q hne ↦ ?_]
    · simp
    · by_cases hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)
      · simp [hQ, hkill Q hQ (hvQ Q hQ hne)]
      · simp [hQ]
  have hfib := trace_finsum_repartitionDualComponent_weilDifferentialCotrace
    (IsFunctionField.ratFunc k) hF η (P.restrict k (RatFunc k)) v
  rw [← hω, Algebra.trace_self_apply, hsum, hη, hP₀,
    repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C,
    residue_trace P hP₀ (ord_adicOfIrreducible_X_sub_C_self a) ht hF
      (degree_adicOfIrreducible_X_sub_C a) fun Q hQ hne ↦ hvQ Q (hQ.trans hP₀.symm) hne] at hfib
  calc repartitionDualComponent (ω : Module.Dual k _) P u
      = repartitionDualComponent (ω : Module.Dual k _) P v := by
        rw [← sub_eq_zero, ← map_sub, hkill P rfl (by simpa using neg_mem hvu)]
    _ = P.traceResidue ht v := hfib
    _ = P.traceResidue ht u := by
        rw [traceResidue_apply, traceResidue_apply,
          P.residueResidueField_eq_of_sub_mem_integers ht hvu]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:189` (proof source at `5a01f5fe3621`).
 **The local component of `dt` at a zero of `t - a` is the residue in `t - a`** (Stichtenoth,
Theorem 4.3.2(d)): for a finite separable extension `F` of `k(t)` and a rational place `P` of `F`
at which the image of `t - a` is a prime element, the local component at `P` of the cotrace of the
canonical differential `η = dt` of `k(t)` is `res_{P,t-a}`. -/
theorem repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential
    (hF : IsFunctionField k F) {P : Place k F} (hP : P.degree = 1) {a : k}
    (ht : P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) P u =
      P.residue hP ht u := by
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue hF
    ht, P.traceResidue_eq_residue ht hP]

end RatFunc

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:206` (proof source at `5a01f5fe3621`).
 **The local component of `dt` at a zero of `t - a` is the trace residue in `t - a`**
(Stichtenoth, Theorem 4.3.2(d) and Remark 4.3.7(d)): for a separating element `t` of `F / k` and a
place `P` with residue field separable over `k` at which `t - a` is a prime element, the Weil
differential `dt` has local component `(dt)_P = Tr_{F_P/k} ∘ res_{P,t-a}`. -/
theorem repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue
    (hF : IsFunctionField k F) {t : F} (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {a : k}
    (ht : P.ord (t - algebraMap k F a) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialOfSeparating hF htr :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.traceResidue ht u := by
  let _ := ratFuncAlgebraOfTranscendental htr
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental htr
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental htr
  have hX : algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a) = t - algebraMap k F a := by
    rw [map_sub, algebraMap_ratFuncAlgebraOfTranscendental_X, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply]
  -- The trace residue only depends on the uniformizer, not on the proof that it is one.
  have hres {s : F} (hs : s = t - algebraMap k F a) (hs₁ : P.ord s = 1) :
      P.traceResidue hs₁ = P.traceResidue ht := by
    subst hs
    rfl
  rw [weilDifferentialOfSeparating_def,
    repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue hF
      (hX ▸ ht), hres hX]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Residue.lean:233` (proof source at `5a01f5fe3621`).
 **The local component of `dt` at a zero of `t - a` is the residue in `t - a`** (Stichtenoth,
Theorem 4.3.2(d)): for a separating element `t` of `F / k` and a rational place `P` at which
`t - a` is a prime element, the Weil differential `dt` has local component `(dt)_P = res_{P,t-a}`.
-/
theorem repartitionDualComponent_weilDifferentialOfSeparating (hF : IsFunctionField k F) {t : F}
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] {P : Place k F} (hP : P.degree = 1)
    {a : k} (ht : P.ord (t - algebraMap k F a) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialOfSeparating hF htr :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.residue hP ht u := by
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue hF htr ht,
    P.traceResidue_eq_residue ht hP]

end TauCeti
end

end

/-! ## Source 41: `TauCeti.FieldTheory.RatFunc.PowerTower`
Original source SHA256: `605fd0c8811c588e1e46ca5110e1cb58dea94f0592cb7cdaca8ea07b5162b46e`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Power subfields of a rational function field

For a field `K` and an exponent `n`, this file computes the degree of `K(X)` over the subfield
`K(X ^ n)`, and records that `K(X)` is purely inseparable over `K(X ^ q)` when `q` is the
exponential characteristic of `K`.  Transporting the first degree along the identification of
`K(X)` with `K⟮x⟯` gives `[K(x) : K(x ^ n)] = n` for an arbitrary transcendental element `x` of an
extension of `K`.

## Main results

* `TauCeti.RatFunc.finrank_adjoin_X_pow`: `[K(X) : K(X ^ n)] = n`.
* `TauCeti.RatFunc.isPurelyInseparable_adjoin_X_pow`: `K(X) / K(X ^ q)` is purely inseparable
  for `q` the exponential characteristic of `K`.
* `TauCeti.relfinrank_adjoin_pow_adjoin`: `[K(x) : K(x ^ n)] = n` for `x` transcendental.

## Mathematical context

Relative and finite-field Frobenius degree computations use this as the inner degree in the tower
`K(W) / K(x) / K(x^n)`.

## Provenance

The statement was extracted while porting the finite-field Frobenius tower from the AINTLIB
`HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil @ 513e83879e2f`). The source proves only the finite-field exponent; the arbitrary
field and exponent statement here is new, and follows directly from Mathlib's rational-function
degree formula.
-/

section
open Polynomial

namespace TauCeti.RatFunc

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/RatFunc/PowerTower.lean:51` (proof source at `5a01f5fe3621`).
 **`[K(X) : K(X ^ n)] = n`** for any field `K` and any `n`. At `n = 0` both sides read `0`:
`K⟮1⟯` is `K`, over which `K(X)` is infinite-dimensional, and `Module.finrank` reports `0`. -/
@[simp]
theorem finrank_adjoin_X_pow (K : Type*) [Field K] (n : ℕ) :
    Module.finrank (IntermediateField.adjoin K {(_root_.RatFunc.X : _root_.RatFunc K) ^ n})
      (_root_.RatFunc K) = n := by
  rw [← _root_.RatFunc.algebraMap_X, ← map_pow, _root_.RatFunc.finrank_eq_max_natDegree,
    _root_.RatFunc.num_algebraMap, _root_.RatFunc.denom_algebraMap, natDegree_X_pow,
    natDegree_one, Nat.max_zero]

open _root_.IntermediateField in
/-- Kind: INSTANCE. Locator: `TauCeti/FieldTheory/RatFunc/PowerTower.lean:62` (proof source at `5a01f5fe3621`).
 **`K(X)` is purely inseparable over `K(X ^ q)`** when `q` is the exponential characteristic of
`K`: it is generated by `X`, whose `q`-th power lies in `K(X ^ q)`. In characteristic zero `q = 1`
and the extension is trivial. -/
instance isPurelyInseparable_adjoin_X_pow (K : Type*) [Field K] (q : ℕ) [ExpChar K q] :
    IsPurelyInseparable K⟮(_root_.RatFunc.X : _root_.RatFunc K) ^ q⟯ (_root_.RatFunc K) := by
  set E := K⟮(_root_.RatFunc.X : _root_.RatFunc K) ^ q⟯
  have : IsPurelyInseparable E E⟮(_root_.RatFunc.X : _root_.RatFunc K)⟯ :=
    (isPurelyInseparable_adjoin_simple_iff_pow_mem E (_root_.RatFunc K) q).mpr
      ⟨1, AdjoinSimple.gen K _, by rw [pow_one, AdjoinSimple.algebraMap_gen]⟩
  exact (_root_.RatFunc.IntermediateField.adjoinXEquiv E).isPurelyInseparable

end TauCeti.RatFunc

namespace TauCeti

open scoped _root_.IntermediateField

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/RatFunc/PowerTower.lean:78` (proof source at `5a01f5fe3621`).
 **`[k(x) : k(x ^ n)] = n`** for an element `x` transcendental over `k`. This supplies the
power-subfield degree formula for arbitrary transcendental parameters. -/
theorem relfinrank_adjoin_pow_adjoin {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]
    {x : F} (hx : Transcendental k x) (n : ℕ) :
    IntermediateField.relfinrank k⟮x ^ n⟯ k⟮x⟯ = n := by
  let e : _root_.RatFunc k ≃ₐ[k] k⟮x⟯ := _root_.RatFunc.algEquivOfTranscendental x hx
  have heX : e _root_.RatFunc.X = (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) := by
    apply Subtype.ext
    exact _root_.RatFunc.algEquivOfTranscendental_X x hx
  have hePow : (IntermediateField.adjoin k
      {(_root_.RatFunc.X : _root_.RatFunc k) ^ n}).map e.toAlgHom =
      IntermediateField.adjoin k
        {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow]
    congr 2
    exact congrArg (· ^ n) heX
  have heTop : (⊤ : IntermediateField k (_root_.RatFunc k)).map e.toAlgHom = ⊤ := by
    rw [← AlgHom.fieldRange_eq_map]
    exact e.fieldRange_eq_top
  have hvalPow : (IntermediateField.adjoin k
      {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n}).map k⟮x⟯.val =
      k⟮x ^ n⟯ := by
    simpa only [IntermediateField.lift, IntermediateField.coe_pow] using
      (IntermediateField.lift_adjoin_simple k k⟮x⟯
        ((⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n))
  have hvalTop : (⊤ : IntermediateField k k⟮x⟯).map k⟮x⟯.val = k⟮x⟯ :=
    IntermediateField.lift_top (F := k) k⟮x⟯
  calc
    IntermediateField.relfinrank k⟮x ^ n⟯ k⟮x⟯ =
        IntermediateField.relfinrank
          ((IntermediateField.adjoin k
            {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n}).map
              k⟮x⟯.val)
          ((⊤ : IntermediateField k k⟮x⟯).map k⟮x⟯.val) := by rw [hvalPow, hvalTop]
    _ = IntermediateField.relfinrank
          (IntermediateField.adjoin k
            {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n}) ⊤ :=
      IntermediateField.relfinrank_map_map _ _ k⟮x⟯.val
    _ = IntermediateField.relfinrank
          (IntermediateField.adjoin k {(_root_.RatFunc.X : _root_.RatFunc k) ^ n}) ⊤ := by
      rw [← hePow, ← heTop]
      exact IntermediateField.relfinrank_map_map _ _ e.toAlgHom
    _ = n := by
      rw [IntermediateField.relfinrank_top_right]
      exact TauCeti.RatFunc.finrank_adjoin_X_pow k n

end TauCeti

end

end

/-! ## Source 42: `TauCeti.RingTheory.Valuation.Discrete.Frobenius`
Original source SHA256: `10362cb0b97fcf4a35b8c4819cb635cb7c184971d1950e28d9a3862b95c13b09`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Orders of Frobenius powers under a discrete valuation

Let `F` be a field of exponential characteristic `p`, and let `v : Valuation F ℤᵐ⁰`. Every
element in the image of the `n`-fold Frobenius has order under `v` divisible by `p ^ n`: if
`z = y ^ (p ^ n)`, then

`ord_v(z) = p ^ n * ord_v(y)`.

Consequently, an element whose order under a discrete valuation is not divisible by `p ^ n`
cannot lie in the image of the `n`-fold Frobenius. Applied to the valuation of a function-field
place, this is the valuation-theoretic input to the separating-element criterion in positive
characteristic. Since `z ^ p - b ^ p = (z - b) ^ p`, a difference of `p`-th powers also has order
divisible by `p`; this is what rules out `p`-th roots of constants in the completion at a place
with inseparable residue field.

## Main results

* `Valuation.ord_iterateFrobenius`: the order of an iterated Frobenius image.
* `Valuation.natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius`: membership in the
  `p ^ n`-power subfield forces divisibility of the order by `p ^ n`.
* `Valuation.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord`: the
  contrapositive, eliminating membership in the `p ^ n`-power subfield.
* `Valuation.natCast_dvd_ord_pow_sub_pow`: a difference of `p`-th powers has order divisible by
  `p`.

## References

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

section
open scoped WithZero

namespace Valuation

universe u

variable {F : Type u} [Field F]
variable (v : _root_.Valuation F ℤᵐ⁰) (p : ℕ) [ExpChar F p]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Valuation/Discrete/Frobenius.lean:56` (proof source at `5a01f5fe3621`).
 The order under a discrete valuation of an `n`-fold Frobenius image is multiplied by
`p ^ n`. -/
@[simp]
theorem ord_iterateFrobenius (n : ℕ) (z : F) :
    _root_.Valuation.ord v (iterateFrobenius F p n z) =
      (p ^ n : ℤ) * _root_.Valuation.ord v z := by
  rw [iterateFrobenius_def, _root_.Valuation.ord_pow]
  norm_num

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Valuation/Discrete/Frobenius.lean:64` (proof source at `5a01f5fe3621`).
 Membership in the image of the `n`-fold Frobenius forces the order under every discrete
valuation to be divisible by `p ^ n`. -/
theorem natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius (n : ℕ) {z : F}
    (hz : z ∈ RingHom.fieldRange (iterateFrobenius F p n)) :
    (p ^ n : ℤ) ∣ _root_.Valuation.ord v z := by
  obtain ⟨y, rfl⟩ := hz
  rw [ord_iterateFrobenius]
  exact dvd_mul_right _ _

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Valuation/Discrete/Frobenius.lean:73` (proof source at `5a01f5fe3621`).
 An element whose order under a discrete valuation is not divisible by `p ^ n` does not lie
in the image of the `n`-fold Frobenius. -/
theorem not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord (n : ℕ) {z : F}
    (hz : ¬(p ^ n : ℤ) ∣ _root_.Valuation.ord v z) :
    z ∉ RingHom.fieldRange (iterateFrobenius F p n) := fun h =>
  hz (natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius v p n h)

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/Valuation/Discrete/Frobenius.lean:80` (proof source at `5a01f5fe3621`).
 A difference of `p`-th powers is the `p`-th power of the difference, so its order under a
discrete valuation is divisible by `p`. -/
theorem natCast_dvd_ord_pow_sub_pow (z b : F) :
    (p : ℤ) ∣ _root_.Valuation.ord v (z ^ p - b ^ p) := by
  rw [← sub_pow_expChar, _root_.Valuation.ord_pow]
  exact dvd_mul_right _ _

end Valuation

end

end

/-! ## Source 43: `TauCeti.FieldTheory.FunctionField.Frobenius`
Original source SHA256: `5c32fc8b040f728912aa9a857bb9588fde7d9c01601b83485d4a7e1eba60f4ec`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Frobenius and separating elements of a function field

This file proves the fixed-parameter part of Stichtenoth's separable-generation criterion.  For a
one-variable function field `F / k` over a perfect field of exponential characteristic `p`, an
element outside the subfield `F^p` of Frobenius powers is separating.  Consequently, a place at
which the order of `x` is not divisible by `p` certifies that `x` is separating.

The proof combines three ingredients.  A separating parameter exists over a perfect field; the
rational function field has degree `p` over its `p`-th-power subfield; and the kernel of a nonzero
derivation is an intermediate field.  The first two facts give `[F : F^p] = p`.  Since this degree
is prime in positive characteristic, the kernel of a nonzero derivation that contains `F^p` must
equal `F^p`.

## Main results

* `TauCeti.IsFunctionField.finrank_fieldRange_frobenius`: `[F : F^p] = p`.
* `TauCeti.IsFunctionField.D_eq_zero_iff_mem_fieldRange_frobenius`: the kernel of the universal
  derivation is exactly `F^p`.
* `TauCeti.IsFunctionField.isSeparable_adjoin_iff_notMem_fieldRange_frobenius`: `x` is separating
  exactly when it lies outside `F^p`.
* `TauCeti.IsFunctionField.exists_pow_eq_and_adjoin_eq_top_of_finrank_prime_of_not_isSeparable`:
  an inseparable subextension `F / k(x)` of prime degree has `x = y ^ p` with `F = k(y)`.
* `TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`: the
  valuation-order criterion.
* `TauCeti.Place.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`: its form for places, in
  every characteristic: an element whose order at a place is not divisible by the characteristic
  is separating, and `TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`: in
  particular every prime element of a place is separating.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

section
noncomputable section

open Module KaehlerDifferential

open scoped _root_.IntermediateField WithZero

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:66` (proof source at `5a01f5fe3621`).
 The degree of a one-variable function field over its subfield of `p`-th powers is `p`.
This is the degree computation underlying the fixed-parameter separability criterion. -/
theorem finrank_fieldRange_frobenius [PerfectField k] (hF : TauCeti.IsFunctionField k F)
    (p : ℕ) [ExpChar F p] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  obtain ⟨y, hy⟩ := hF.exists_transcendental
  have hA : k⟮y⟯.toSubfield.map (frobenius F p) = k⟮y ^ p⟯.toSubfield := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [IntermediateField.mem_toSubfield, frobenius_def]
      induction hz using IntermediateField.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff.mp hz]
        exact IntermediateField.mem_adjoin_simple_self k (y ^ p)
      | algebraMap c =>
        rw [← map_pow]
        exact IntermediateField.algebraMap_mem _ _
      | add a b _ _ ha hb =>
        rw [add_pow_expChar]
        exact IntermediateField.add_mem _ ha hb
      | inv a _ ha =>
        rw [inv_pow]
        exact IntermediateField.inv_mem _ ha
      | mul a b _ _ ha hb =>
        rw [mul_pow]
        exact IntermediateField.mul_mem _ ha hb
    · intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff.mp hz]
        exact ⟨y, IntermediateField.mem_adjoin_simple_self k y, rfl⟩
      | algebraMap c =>
        obtain ⟨d, hd⟩ := surjective_frobenius k p c
        exact ⟨algebraMap k F d, IntermediateField.algebraMap_mem _ _, by
          rw [← RingHom.map_frobenius, hd]⟩
      | add a b _ _ ha hb => exact Subfield.add_mem _ ha hb
      | inv a _ ha => exact Subfield.inv_mem _ ha
      | mul a b _ _ ha hb => exact Subfield.mul_mem _ ha hb
  have hAB : k⟮y⟯.toSubfield.map (frobenius F p) ≤ k⟮y⟯.toSubfield := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [frobenius_def] using k⟮y⟯.toSubfield.pow_mem hz p
  have hAC : k⟮y⟯.toSubfield.map (frobenius F p) ≤ (frobenius F p).fieldRange := by
    rw [RingHom.fieldRange_eq_map]
    rintro _ ⟨z, _, rfl⟩
    exact ⟨z, trivial, rfl⟩
  have hrelAB : Subfield.relfinrank (k⟮y⟯.toSubfield.map (frobenius F p)) k⟮y⟯.toSubfield = p := by
    rw [hA]
    exact relfinrank_adjoin_pow_adjoin hy p
  have hrelAC : Subfield.relfinrank (k⟮y⟯.toSubfield.map (frobenius F p))
      (frobenius F p).fieldRange = Subfield.relfinrank k⟮y⟯.toSubfield ⊤ := by
    rw [RingHom.fieldRange_eq_map]
    exact Subfield.relfinrank_map_map k⟮y⟯.toSubfield ⊤ (frobenius F p)
  let _ : FiniteDimensional k⟮y⟯ F := hF.finiteDimensional_adjoin hy
  have hn : Subfield.relfinrank k⟮y⟯.toSubfield ⊤ ≠ 0 := by
    rw [Subfield.relfinrank_top_right]
    exact Module.finrank_pos.ne'
  have hABF := Subfield.relfinrank_mul_finrank_top hAB
  have hACF := Subfield.relfinrank_mul_finrank_top hAC
  rw [hrelAB] at hABF
  rw [← Subfield.relfinrank_top_right] at hABF
  rw [hrelAC] at hACF
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero hn)
  calc
    Subfield.relfinrank k⟮y⟯.toSubfield ⊤ * Module.finrank (frobenius F p).fieldRange F =
        Module.finrank (k⟮y⟯.toSubfield.map (frobenius F p)) F := hACF
    _ = p * Subfield.relfinrank k⟮y⟯.toSubfield ⊤ := hABF.symm
    _ = Subfield.relfinrank k⟮y⟯.toSubfield ⊤ * p := Nat.mul_comm _ _

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:136` (proof source at `5a01f5fe3621`).
 **The kernel of the universal derivation is the Frobenius subfield**: in a one-variable
function field over a perfect field, `d x = 0` exactly when `x` is a `p`-th power. This identifies
differential nonvanishing with the Frobenius-subfield obstruction used by separating criteria. -/
theorem D_eq_zero_iff_mem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact p.Prime] (x : F) :
    D k F x = 0 ↔ x ∈ (frobenius F p).fieldRange := by
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  let _ : CharP F p := by
    cases (inferInstance : ExpChar F p) with
    | zero => exact (Nat.not_prime_one Fact.out).elim
    | prime _ => infer_instance
  have hk : ∀ c : k, algebraMap k F c ∈ (frobenius F p).fieldRange := by
    intro c
    obtain ⟨d, hd⟩ := surjective_frobenius k p c
    exact ⟨algebraMap k F d, by rw [← RingHom.map_frobenius, hd]⟩
  let C : IntermediateField k F := (frobenius F p).fieldRange.toIntermediateField hk
  have hmemC (z : F) : z ∈ C ↔ z ∈ (frobenius F p).fieldRange := Iff.rfl
  let Z : Subfield F :=
    { carrier := {z | D k F z = 0}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simpa using congrArg₂ (· + ·) ha hb
      neg_mem' := by
        intro a ha
        simpa using congrArg Neg.neg ha
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [Derivation.leibniz_inv, ha, smul_zero] }
  have hkZ : ∀ c : k, algebraMap k F c ∈ Z := fun c ↦ by simp [Z]
  let K : IntermediateField k F := Z.toIntermediateField hkZ
  have hmemK (z : F) : z ∈ K ↔ D k F z = 0 := Iff.rfl
  have hCK : C ≤ K := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hmemC z).mp hz
    rw [hmemK, frobenius_def, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F,
      CharP.cast_eq_zero, zero_smul]
  have hK_ne_top : K ≠ ⊤ := by
    obtain ⟨y, hy, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    let _ := hsep
    intro hK
    have hyK : y ∈ K := hK.symm ▸ IntermediateField.mem_top
    exact D_ne_zero_of_separating hy ((hmemK y).mp hyK)
  have hdeg : Module.finrank C F = p := hF.finrank_fieldRange_frobenius p
  have hdiv : IntermediateField.relfinrank C K ∣ p := by
    rw [← hdeg]
    exact IntermediateField.relfinrank_dvd_finrank_top_of_le hCK
  have hrel : IntermediateField.relfinrank C K = 1 := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdiv with h | h
    · exact h
    · exfalso
      have htower := IntermediateField.relfinrank_mul_finrank_top hCK
      rw [h, hdeg] at htower
      have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
      have hfin : Module.finrank K F = 1 := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0)
        simpa using htower
      exact hK_ne_top (IntermediateField.finrank_eq_one_iff_eq_top.mp hfin)
  have hKC : K ≤ C := IntermediateField.relfinrank_eq_one_iff.mp hrel
  exact ⟨fun h ↦ (hmemC x).mp (hKC ((hmemK x).mpr h)), fun h ↦ (hmemK x).mp (hCK ((hmemC x).mpr h))⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:203` (proof source at `5a01f5fe3621`).
 **Separating elements are the elements outside `F^p`** (Stichtenoth, Proposition 3.10.2(a)):
in a one-variable function field over a perfect field of characteristic `p`, `F / k(x)` is
separable exactly when `x` is not a `p`-th power in `F`. -/
theorem isSeparable_adjoin_iff_notMem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact p.Prime] (x : F) :
    Algebra.IsSeparable k⟮x⟯ F ↔ x ∉ (frobenius F p).fieldRange := by
  rw [hF.isSeparable_adjoin_iff_D_ne_zero, ne_eq, hF.D_eq_zero_iff_mem_fieldRange_frobenius p x]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:213` (proof source at `5a01f5fe3621`).
 **An inseparable subextension of prime degree comes from a `p`-th root.** Over a perfect
field of exponential characteristic `p`, if `x` is transcendental, `[F : k(x)]` is prime and
`F / k(x)` is not separable, then `x = y ^ p` for an element `y` that generates `F` over `k`. So
`F` is then a rational function field, and `[F : k(x)] = p`. In characteristic zero the
hypotheses are contradictory. -/
theorem exists_pow_eq_and_adjoin_eq_top_of_finrank_prime_of_not_isSeparable [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] {x : F} (hx : Transcendental k x)
    (hprime : (Module.finrank k⟮x⟯ F).Prime) (hsep : ¬ Algebra.IsSeparable k⟮x⟯ F) :
    ∃ y : F, y ^ p = x ∧ k⟮y⟯ = ⊤ := by
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hsep inferInstance).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    -- `x` is a `p`-th power `y ^ p`, and `[k(y) : k(y ^ p)] = p` is a factor of the prime
    -- `[F : k(x)]`, so the complementary factor `[F : k(y)]` is one.
    obtain ⟨y, rfl⟩ : x ∈ (frobenius F p).fieldRange :=
      not_not.mp ((hF.isSeparable_adjoin_iff_notMem_fieldRange_frobenius p x).not.mp hsep)
    rw [frobenius_def] at hx hprime ⊢
    have hy : Transcendental k y := fun h ↦ hx (h.isIntegral.pow p).isAlgebraic
    have hle : k⟮y ^ p⟯ ≤ k⟮y⟯ := IntermediateField.adjoin_simple_le_iff.mpr
      (pow_mem (IntermediateField.mem_adjoin_simple_self k y) p)
    rw [← IntermediateField.relfinrank_mul_finrank_top hle, relfinrank_adjoin_pow_adjoin hy p,
      Nat.prime_mul_iff] at hprime
    refine ⟨y, rfl, IntermediateField.finrank_eq_one_iff_eq_top.mp ?_⟩
    rcases hprime with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact (hp.ne_one h).elim

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:240` (proof source at `5a01f5fe3621`).
 **The valuation-order criterion for a separating element** (Stichtenoth, Proposition
3.10.2): if the order of `x` at a discrete valuation is not divisible by the exponential
characteristic `p`, then `x` is transcendental and `F / k(x)` is separable. -/
theorem transcendental_and_isSeparable_adjoin_of_not_dvd_ord [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (v : Valuation F ℤᵐ⁰) (p : ℕ)
    [ExpChar F p] {x : F} (hx : ¬ (p : ℤ) ∣ v.ord x) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hx (one_dvd _)).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    have hnotmem : x ∉ (frobenius F p).fieldRange := by
      rw [← iterateFrobenius_one (R := F) p]
      apply v.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord p 1
      simpa using hx
    have hDx : D k F x ≠ 0 := fun h ↦
      hnotmem ((hF.D_eq_zero_iff_mem_fieldRange_frobenius p x).mp h)
    exact ⟨transcendental_of_D_ne_zero hDx, hF.isSeparable_adjoin_iff_D_ne_zero.mpr hDx⟩

end IsFunctionField

namespace Place

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:265` (proof source at `5a01f5fe3621`).
 **The valuation-order criterion for a separating element, at a place** (Stichtenoth,
Proposition 3.10.2): over a perfect field, if the order of `x` at a place is not divisible by the
characteristic of `F`, then `x` is transcendental and `F / k(x)` is separable. In characteristic
zero the hypothesis says that the order of `x` is nonzero. In particular every prime element of a
place, an element of order one, is separating. -/
theorem transcendental_and_isSeparable_adjoin_of_not_dvd_ord [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) {x : F}
    (hx : ¬ (ringChar F : ℤ) ∣ P.ord x) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  by_cases h0 : ringChar F = 0
  · -- In characteristic zero every algebraic extension is separable.
    have : CharP F 0 := ringChar.of_eq h0
    have : CharZero F := CharP.charP_to_charZero F
    have htr : Transcendental k x := P.transcendental_of_ord_ne_zero fun h ↦ hx (by simp [h])
    have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin htr
    exact ⟨htr, inferInstance⟩
  · have : CharP F (ringChar F) := ringChar.charP F
    have : ExpChar F (ringChar F) := .prime (CharP.char_prime_of_ne_zero F h0)
    exact hF.transcendental_and_isSeparable_adjoin_of_not_dvd_ord P.valuation (ringChar F)
      (by rwa [Valuation.ord_def, ← P.ord_def])

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Frobenius.lean:283` (proof source at `5a01f5fe3621`).
 **Every prime element of a place is separating** over a perfect field: an element of order one
at a place is transcendental, and `F` is separable over the subfield it generates. -/
theorem transcendental_and_isSeparable_adjoin_of_ord_eq_one [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) {t : F} (ht : P.ord t = 1) :
    Transcendental k t ∧ Algebra.IsSeparable k⟮t⟯ F :=
  P.transcendental_and_isSeparable_adjoin_of_not_dvd_ord hF <| by
    rw [ht, ← Nat.cast_one, Int.natCast_dvd_natCast, Nat.dvd_one]
    exact CharP.ringChar_ne_one

end Place

end TauCeti
end
end

end

/-! ## Source 44: `TauCeti.RingTheory.HahnSeries.Multiplication`
Original source SHA256: `9d61ef66687e3c0ed2e3f67f179acdcae755234755d16a50251909b2d93b2453`. -/

section

/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Powers of Hahn series and compatibility with coefficient scalars

Over a domain, taking a power multiplies the order and raises the leading coefficient to that
power. These formulas detect whether a leading pole term can be cancelled by a power.

The order formula allows semiring coefficients; Mathlib's `HahnSeries.addVal` requires ring
coefficients, so its `AddValuation.map_pow` does not cover this generality.

The formulas are `TauCeti.hahnSeries_leadingCoeff_pow n` and
`TauCeti.hahnSeries_orderTop_pow n`; both are also simplification lemmas. The exponent is
explicit, and the series is inferred from the equality being rewritten.

With the typeclasses below in scope, use the qualified names as follows:

```lean
example (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n :=
  TauCeti.hahnSeries_leadingCoeff_pow n (f := f)

example [Nontrivial R] (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).orderTop = n • f.orderTop :=
  TauCeti.hahnSeries_orderTop_pow n (f := f)
```

This file also records that coefficientwise scalar multiplication associates and commutes with
multiplication of Hahn series (`TauCeti.hahnSeries_isScalarTower` and
`TauCeti.hahnSeries_smulCommClass`). Mathlib provides this for the action of Hahn
series on Hahn modules, and for Hahn series through their algebra structure; but the default
algebra structure on Laurent series `R⸨X⸩` comes from `R⟦X⟧` and is not definitionally the
coefficientwise one, so for instance the `R⸨X⸩`-module structure on `R`-derivations of `R⸨X⸩`
needs this instance.
-/

section
namespace TauCeti

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/HahnSeries/Multiplication.lean:49` (proof source at `5a01f5fe3621`).
 Coefficientwise scalar multiplication commutes with multiplication of Hahn series. -/
instance hahnSeries_smulCommClass {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [CommSemiring R] :
    SMulCommClass R (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_comm r x y := by
    simp only [← HahnSeries.C_mul_eq_smul, smul_eq_mul, mul_left_comm]

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/HahnSeries/Multiplication.lean:56` (proof source at `5a01f5fe3621`).
 Coefficientwise scalar multiplication associates with multiplication of Hahn series. -/
instance hahnSeries_isScalarTower {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [Semiring R] :
    IsScalarTower R (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_assoc r x y := by
    simp only [← HahnSeries.C_mul_eq_smul, smul_eq_mul, mul_assoc]

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/HahnSeries/Multiplication.lean:67` (proof source at `5a01f5fe3621`).
 The leading coefficient of a power is the power of the leading coefficient. -/
@[simp]
theorem hahnSeries_leadingCoeff_pow (n : ℕ) {f : HahnSeries Γ R} :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/HahnSeries/Multiplication.lean:75` (proof source at `5a01f5fe3621`).
 The order of a power is the corresponding multiple of the order, including at zero. -/
@[simp]
theorem hahnSeries_orderTop_pow [Nontrivial R] (n : ℕ) {f : HahnSeries Γ R} :
    (f ^ n).orderTop = n • f.orderTop := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_nsmul]

end TauCeti
end

end

/-! ## Source 45: `TauCeti.RingTheory.LaurentSeries.Derivative`
Original source SHA256: `c30dfc7ae667c4063d9595e08baf7df4b3d66c36bc255fe72dbc4a45203e7c9f`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Differentiation of Laurent series

This file bundles the coefficientwise formal derivative `D` of Laurent series as a derivation over
any commutative ring, using the Leibniz rule from `LaurentSeries.Basic`. The bundle allows the
universal property of Kähler differentials to compare it with differentiation of algebraic
functions in a local parameter. Laurent derivations carry the commutator Lie algebra structure
over the coefficient ring, with `[aD, bD] = (a Db - b Da)D` over any commutative ring.

It then records how `D` interacts with the order `ord = HahnSeries.orderTop` and with the
valuation topology of `K⸨X⸩`. The coefficient of `Xⁿ⁻¹` in `D f` is `n` times the coefficient of
`Xⁿ` in `f`, so `D` lowers the order by at most one. The order drops by exactly one when the
leading exponent `r` times the leading coefficient is nonzero, for instance over a field in which
`r` is nonzero. In general the order of `D f` is one less than the first exponent `n` with
`n • f.coeff n ≠ 0`, and `D f = 0` when there is no such exponent. Without additive torsion, as
in characteristic zero, the kernel of `D` is the constants. Over a field, `D` satisfies the
inverse and quotient rules, and it maps the neighbourhood `{f | v f ≤ exp (-m)}` of zero into
`{f | v f ≤ exp (-(m - 1))}`, so it is continuous for the valuation topology.

The underlying linear map is Mathlib's `LaurentSeries.derivative`; no new differentiation
operation is introduced.

## Main results

* `TauCeti.laurentSeriesDerivation`: `D` as a derivation.
* `Derivation.laurentSeriesLieRing` and `Derivation.laurentSeriesLieAlgebra`: the commutator
  Lie structures on Laurent derivations.
* `LaurentSeries.lie_smul_laurentSeriesDerivation`: the coefficient formula for the commutator.
* `LaurentSeries.coeff_derivative_order_sub_one`: the coefficient of `X ^ (r - 1)` in `D f` is
  `r` times the leading coefficient of `f`, where `r = f.order`.
* `LaurentSeries.orderTop_le_orderTop_derivative_add_one`: `ord f ≤ ord (D f) + 1`.
* `LaurentSeries.orderTop_derivative_eq_sub_one`: the order of `D f` is one less than the first
  exponent whose coefficient survives differentiation.
* `LaurentSeries.orderTop_derivative_eq_order_sub_one_of_cast_ne_zero`: if the order `r` of
  `f ≠ 0` is nonzero in a ring without zero divisors, then `ord (D f) = r - 1`.
* `LaurentSeries.derivative_eq_zero_iff_exists_C`: without additive torsion the kernel of `D`
  consists of the constants.
* `LaurentSeries.derivative_inv` and `LaurentSeries.derivative_div`: the inverse and quotient
  rules over a field.
* `LaurentSeries.continuous_derivative`: `D` is continuous for the valuation topology.
-/

section
open HahnSeries Filter Topology
open scoped LaurentSeries

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- Kind: DEF. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:66` (proof source at `5a01f5fe3621`).
 Formal Laurent differentiation as a derivation. Its linear map is the existing
coefficientwise derivative. -/
noncomputable def laurentSeriesDerivation :
    Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun f := _root_.LaurentSeries.derivative R f
  map_add' f g := (_root_.LaurentSeries.derivative R).map_add f g
  map_smul' c f := by
    -- The source uses the algebra action; Mathlib's derivative uses the coefficientwise action.
    rw [Algebra.smul_def, laurentSeries_algebraMap_mul_eq_smul]
    exact map_smul (_root_.LaurentSeries.derivative R) c f
  map_one_eq_zero' := by
    ext n
    suffices n + 1 = 0 → (n : R) + 1 = 0 by
      simpa [_root_.LaurentSeries.derivative_apply, coeff_one]
    intro h
    simpa using congrArg (fun i : ℤ ↦ (i : R)) h
  leibniz' f g := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    rw [_root_.LaurentSeries.derivative_mul]
    ring

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:87` (proof source at `5a01f5fe3621`).
 The bundled Laurent derivation evaluates as the coefficientwise derivative. -/
@[simp]
theorem laurentSeriesDerivation_apply (f : LaurentSeries R) :
    laurentSeriesDerivation R f = _root_.LaurentSeries.derivative R f := (rfl)

end TauCeti

namespace Derivation

variable {R : Type*} [CommRing R]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:96` (proof source at `5a01f5fe3621`).
-/
private theorem laurentSeries_module_eq_algebraModule : (inferInstance : Module R R⸨X⸩) =
    (inferInstance : Algebra R R⸨X⸩).toModule :=
  Module.ext <| funext fun r ↦ funext fun f ↦
    (TauCeti.laurentSeries_algebraMap_mul_eq_smul r f).symm

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:104` (proof source at `5a01f5fe3621`).
 The commutator Lie ring on Laurent derivations with their coefficientwise codomain scalars.
The native derivation Lie ring uses the algebra-induced codomain module; these scalar actions
agree. Additive transport keeps the existing additive group on derivations. -/
noncomputable instance laurentSeriesLieRing : LieRing (Derivation R R⸨X⸩ R⸨X⸩) :=
  (@AddEquiv.cast _ (fun m : Module R R⸨X⸩ ↦ @Derivation R R⸨X⸩ R⸨X⸩ _ _ _ _ _ m)
    (fun m ↦ @Derivation.instAdd R R⸨X⸩ R⸨X⸩ _ _ _ _ _ m)
    (inferInstance : Module R R⸨X⸩) (inferInstance : Algebra R R⸨X⸩).toModule
    (by exact laurentSeries_module_eq_algebraModule)).lieRing

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:111` (proof source at `5a01f5fe3621`).
 Evaluation of the commutator through the coefficientwise Laurent scalar presentation. -/
theorem laurentSeries_commutator_apply (δ ε : Derivation R R⸨X⸩ R⸨X⸩) (f : R⸨X⸩) :
    ⁅δ, ε⁆ f = δ (ε f) - ε (δ f) := by
  have aux (m : Module R R⸨X⸩) (h : m = (inferInstance : Algebra R R⸨X⸩).toModule)
      (δ ε : @Derivation R R⸨X⸩ R⸨X⸩ _ _ _ _ _ m) :
      @Bracket.bracket _ _
        (@AddEquiv.cast _
          (fun m : Module R R⸨X⸩ ↦ @Derivation R R⸨X⸩ R⸨X⸩ _ _ _ _ _ m)
          (fun m ↦ @Derivation.instAdd R R⸨X⸩ R⸨X⸩ _ _ _ _ _ m)
          m (inferInstance : Algebra R R⸨X⸩).toModule h).lieRing.toBracket δ ε f =
        δ (ε f) - ε (δ f) := by
    cases h
    rfl
  exact aux _ laurentSeries_module_eq_algebraModule δ ε

/-- Kind: INSTANCE. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:127` (proof source at `5a01f5fe3621`).
 Laurent derivations form a Lie algebra over the coefficient ring, retaining the existing
coefficientwise scalar action on derivations. -/
noncomputable instance laurentSeriesLieAlgebra : LieAlgebra R (Derivation R R⸨X⸩ R⸨X⸩) where
  __ := (inferInstance : Module R (Derivation R R⸨X⸩ R⸨X⸩))
  lie_smul r δ ε := by
    ext1 f
    simp only [laurentSeries_commutator_apply, Derivation.smul_apply,
      smul_sub]
    congr 1
    -- The input action on a derivation is algebra-induced; its output action is coefficientwise.
    rw [← TauCeti.laurentSeries_algebraMap_mul_eq_smul, ← Algebra.smul_def, δ.map_smul]

end Derivation

namespace LaurentSeries

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:143` (proof source at `5a01f5fe3621`).
 The commutator of Laurent vector fields has coefficient `a D b - b D a`.
This formula uses no characteristic assumption. -/
theorem lie_smul_laurentSeriesDerivation {R : Type*} [CommRing R] (a b : R⸨X⸩) :
    ⁅a • TauCeti.laurentSeriesDerivation R, b • TauCeti.laurentSeriesDerivation R⁆ =
      (a * TauCeti.laurentSeriesDerivation R b - b * TauCeti.laurentSeriesDerivation R a) •
        TauCeti.laurentSeriesDerivation R := by
  ext1 f
  simp only [Derivation.laurentSeries_commutator_apply, Derivation.smul_apply, smul_eq_mul,
    Derivation.leibniz]
  ring

section Module

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:157` (proof source at `5a01f5fe3621`).
 The coefficient of `Xⁿ` in `f'` is `n + 1` times the coefficient of `Xⁿ⁺¹` in `f`. -/
theorem coeff_derivative (f : LaurentSeries V) (n : ℤ) :
    (derivative R f).coeff n = (n + 1) • f.coeff (n + 1) := by
  simp

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:162` (proof source at `5a01f5fe3621`).
 The coefficient of `Xⁿ⁻¹` in `f'` is `n` times the coefficient of `Xⁿ` in `f`. -/
theorem coeff_derivative_sub_one (f : LaurentSeries V) (n : ℤ) :
    (derivative R f).coeff (n - 1) = n • f.coeff n := by
  simp

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:168` (proof source at `5a01f5fe3621`).
 The coefficient of `X ^ (r - 1)` in `f'`, where `r` is the order of `f`, is `r` times the
leading coefficient of `f`. -/
theorem coeff_derivative_order_sub_one (f : LaurentSeries V) :
    (derivative R f).coeff (f.order - 1) = f.order • f.leadingCoeff := by
  rw [coeff_derivative_sub_one, leadingCoeff_eq]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:173` (proof source at `5a01f5fe3621`).
 **Differentiation lowers the order by at most one**: `ord f ≤ ord f' + 1`. -/
theorem orderTop_le_orderTop_derivative_add_one (f : LaurentSeries V) :
    f.orderTop ≤ (derivative R f).orderTop + 1 := by
  obtain h | h := eq_or_ne (derivative R f) 0
  · simp [h]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr h)
  have hc := coeff_orderTop_ne hk.symm
  rw [coeff_derivative] at hc
  rw [← hk, ← WithTop.coe_one, ← WithTop.coe_add]
  exact orderTop_le_of_coeff_ne_zero (right_ne_zero_of_smul hc)

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:184` (proof source at `5a01f5fe3621`).
 If `n` is the first exponent with `n • f.coeff n ≠ 0`, then `f'` has order `n - 1`. -/
theorem orderTop_derivative_eq_sub_one {f : LaurentSeries V} {n : ℤ} (hn : n • f.coeff n ≠ 0)
    (hlt : ∀ m < n, m • f.coeff m = 0) :
    (derivative R f).orderTop = (n - 1 : ℤ) := by
  refine orderTop_eq_of_le (by rwa [mem_support, coeff_derivative_sub_one]) fun m hm ↦ ?_
  by_contra! h
  rw [mem_support, ← add_sub_cancel_right m 1, coeff_derivative_sub_one] at hm
  exact hm (hlt _ (by omega))

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:194` (proof source at `5a01f5fe3621`).
 If the order `r` of `f` times its leading coefficient is nonzero, then `f'` has order
`r - 1`. -/
theorem orderTop_derivative_eq_order_sub_one {f : LaurentSeries V}
    (h : f.order • f.leadingCoeff ≠ 0) :
    (derivative R f).orderTop = (f.order - 1 : ℤ) := by
  rw [leadingCoeff_eq] at h
  exact orderTop_derivative_eq_sub_one h fun m hm ↦ by rw [coeff_eq_zero_of_lt_order hm, smul_zero]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:202` (proof source at `5a01f5fe3621`).
 A Laurent series has derivative zero exactly when `n • f.coeff n = 0` for every exponent
`n`. -/
theorem derivative_eq_zero_iff {f : LaurentSeries V} :
    derivative R f = 0 ↔ ∀ n : ℤ, n • f.coeff n = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← coeff_derivative_sub_one (R := R), h, coeff_zero]
  · ext n
    rw [coeff_derivative, h, coeff_zero]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:211` (proof source at `5a01f5fe3621`).
 Without additive torsion, a Laurent series has derivative zero exactly when it is
constant. -/
theorem derivative_eq_zero_iff_eq_single [IsAddTorsionFree V] {f : LaurentSeries V} :
    derivative R f = 0 ↔ f = single 0 (f.coeff 0) := by
  rw [derivative_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h n ↦ ?_⟩
  · ext n
    by_cases hn : n = 0
    · simp [hn]
    · simpa [coeff_single_of_ne hn, hn] using h n
  · rw [h]
    by_cases hn : n = 0 <;> simp [hn]

end Module

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:226` (proof source at `5a01f5fe3621`).
 If `f ≠ 0` has order `r` and `r` is nonzero in a ring `R` without zero divisors, for instance
a field in which `r` is nonzero, then `f'` has order `r - 1`. -/
theorem orderTop_derivative_eq_order_sub_one_of_cast_ne_zero {R : Type*} [Ring R]
    [NoZeroDivisors R] {f : R⸨X⸩} (hf : f ≠ 0) (h : (f.order : R) ≠ 0) :
    (derivative R f).orderTop = (f.order - 1 : ℤ) :=
  orderTop_derivative_eq_order_sub_one <| by
    rw [zsmul_eq_mul]
    exact mul_ne_zero h (leadingCoeff_ne_zero.mpr hf)

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:235` (proof source at `5a01f5fe3621`).
 **The kernel of the derivative.** Over a ring without additive torsion, for instance a field
of characteristic zero, the Laurent series with derivative zero are exactly the constants. -/
theorem derivative_eq_zero_iff_exists_C {R : Type*} [Ring R] [IsAddTorsionFree R] {f : R⸨X⸩} :
    derivative R f = 0 ↔ ∃ c : R, C c = f := by
  rw [derivative_eq_zero_iff_eq_single]
  refine ⟨fun h ↦ ⟨_, by simpa only [C_apply] using h.symm⟩, ?_⟩
  rintro ⟨c, rfl⟩
  simp

section Field

variable {K : Type*} [Field K]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:247` (proof source at `5a01f5fe3621`).
 **The inverse rule**: `(f⁻¹)' = -(f⁻¹ ^ 2 * f')`. -/
theorem derivative_inv (f : K⸨X⸩) :
    derivative K f⁻¹ = -(f⁻¹ ^ 2 * derivative K f) := by
  simpa using (TauCeti.laurentSeriesDerivation K).leibniz_inv f

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:252` (proof source at `5a01f5fe3621`).
 **The quotient rule**: `(f / g)' = (f' * g - f * g') / g ^ 2`. -/
theorem derivative_div (f g : K⸨X⸩) :
    derivative K (f / g) = (derivative K f * g - f * derivative K g) / g ^ 2 := by
  have h := (TauCeti.laurentSeriesDerivation K).leibniz_div f g
  simp only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul] at h
  rw [h]
  ring

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:260` (proof source at `5a01f5fe3621`).
 If `f` vanishes to order at least `m`, then `f'` vanishes to order at least `m - 1`. -/
theorem valuation_derivative_le {m : ℤ} {f : K⸨X⸩} (hf : Valued.v f ≤ WithZero.exp (-m)) :
    Valued.v (derivative K f) ≤ WithZero.exp (-(m - 1)) := by
  rw [valuation_le_iff_coeff_lt_eq_zero] at hf ⊢
  intro n hn
  rw [coeff_derivative, hf _ (by omega), smul_zero]

/-- Kind: THEOREM. Locator: `TauCeti/RingTheory/LaurentSeries/Derivative.lean:267` (proof source at `5a01f5fe3621`).
 The derivative of Laurent series is continuous for the valuation topology. -/
theorem continuous_derivative : Continuous (derivative K : K⸨X⸩ → K⸨X⸩) := by
  refine continuous_of_continuousAt_zero (derivative K) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)).symm⟩
  -- Series of valuation below `exp (k - 2)` have derivatives of valuation below `exp k`.
  have hU : {x : K⸨X⸩ | Valued.v x < Valued.v (single (2 - k) (1 : K))} ∈ 𝓝 0 :=
    Valued.mem_nhds_zero.mpr ⟨Units.mk0 (Valued.v.restrict (single (2 - k) (1 : K))) (by simp),
      fun _ hx ↦ Valued.v.restrict_lt_iff.mp hx⟩
  refine Filter.mem_map.mpr ?_
  filter_upwards [hU] with x hx
  rw [valuation_single_zpow] at hx
  apply hγ
  rw [Set.mem_ofPred_eq, Valued.v.restrict_lt_iff_lt_embedding]
  refine (valuation_derivative_le hx.le).trans_lt ?_
  rw [hk, WithZero.exp_lt_exp]
  omega

end Field

end LaurentSeries
end

end

/-! ## Source 46: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.ChangeOfUniformizer`
Original source SHA256: `3ae507cca5c61502f7a895ec245e89b8809834d639890b1effd299778181b75a`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Residues under a change of uniformizer

Let `P` be a rational place of `F / k` and let `s` and `t` both have order one at `P`. The
residue of a function `z` with respect to `s` can be computed from Laurent expansions in `t`:

`res_{P,s}(z) = coeff_{-1} (z(T) * s'(T))`,

where `z(T)` and `s(T)` are the Laurent expansions of `z` and `s` in `t` and `s'(T)` is the
formal derivative. This is the expansion-level form of Stichtenoth's transformation formula
`res_{P,s}(z) = res_{P,t}(z · ds/dt)` (Proposition 4.2.9). As a corollary, whenever a function
`w` has expansion `s'(T)` in `t`, `res_{P,s}(z) = res_{P,t}(z * w)`. The function-field derivative
`ds/dt` is such a `w` when `t` is separating
(`TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating`), which gives the formula in
Stichtenoth's form (`TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`).

The formula holds in every characteristic. Both sides are `k`-linear in `z` and vanish on
functions integral at `P`, so it suffices to compare them on the negative powers `s ^ j`. There
it is the formal identity `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative` for the expansion
of `s`, a power series of order one.

The same formula holds at every place `P` whose residue field `F_P` is separable over `k`, for
the `F_P`-valued residues `res_{P,s}` and `res_{P,t}` (`TauCeti.Place.residueResidueField`) and
the Laurent expansions with coefficients in `F_P`, hence also for the `k`-valued residues
`Tr_{F_P/k} ∘ res_{P,t}` (`TauCeti.Place.traceResidue`). Here the expansions in `s` and in `t`
are two identifications of the completion at `P` with `F_P((T))`. Both send the coefficient field
of the completion to the constants, so the expansion in `t` of a function, read as a series in
its expansion in `s`, is a substitution `T ↦ s(T)` fixing `F_P`. Such a substitution preserves
residues (`LaurentSeries.coeff_neg_one_map_mul_derivative`).

## Main results

* `TauCeti.Place.residue_eq_coeff_laurentSeriesExpansion_mul_derivative`: the residue with
  respect to `s`, computed from Laurent expansions in `t`.
* `TauCeti.Place.residue_eq_residue_mul`: `res_{P,s}(z) = res_{P,t}(z * w)` for a function `w`
  whose expansion in `t` is the derivative of that of `s`.
* `TauCeti.Place.residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative`
  and `TauCeti.Place.residueResidueField_eq_residueResidueField_mul`: the same at a place with
  separable residue field, with residues and coefficients in `F_P`.
* `TauCeti.Place.traceResidue_eq_traceResidue_mul`: the same for the `k`-valued residues.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9.
-/

section
open scoped LaurentSeries PowerSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/ChangeOfUniformizer.lean:69` (proof source at `5a01f5fe3621`).
 **Change of uniformizer for residues.** At a rational place, the residue with respect to a
uniformizer `s` is the coefficient of `T⁻¹` in `z(T) * s'(T)`, where `z(T)` and `s(T)` are the
Laurent expansions of `z` and `s` in another uniformizer `t` (Stichtenoth, Proposition 4.2.9). -/
theorem residue_eq_coeff_laurentSeriesExpansion_mul_derivative (hs : P.ord s = 1) (z : F) :
    P.residue hP hs z = (P.laurentSeriesExpansion hP ht z *
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)).coeff (-1) := by
  have hsint : s ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  -- The expansion of `s` in `t` is a power series `φ` of order one.
  have hs0 : (⟨s, hsint⟩ : P.integers) ≠ 0 := by
    intro h
    have : s = 0 := congrArg Subtype.val h
    simp [this] at hs
  have hφ : (P.powerSeriesExpansion hP ht ⟨s, hsint⟩).order = 1 := by
    rw [order_powerSeriesExpansion _ _ _ _ hs0, hs]
    simp
  have hLs := P.laurentSeriesExpansion_coe hP ht ⟨s, hsint⟩
  -- The right-hand side as a `k`-linear function of `z`.
  let R : F →ₗ[k] k :=
    { toFun z := (P.laurentSeriesExpansion hP ht z *
        LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)).coeff (-1)
      map_add' x y := by simp [add_mul]
      map_smul' c x := by simp [Algebra.smul_def, mul_assoc] }
  have hR_apply (z : F) : R z = (P.laurentSeriesExpansion hP ht z *
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)).coeff (-1) := rfl
  have hR : P.residue hP hs = R := by
    refine P.linearMap_ext_zpow hP hs (m := 0) (fun z hz ↦ ?_) (fun j _ ↦ ?_)
    · -- Both sides vanish on functions integral at `P`.
      obtain ⟨x, rfl⟩ : ∃ x : P.integers, (x : F) = z := ⟨⟨z, P.mem_filtration_zero_iff.mp hz⟩, rfl⟩
      rw [P.residue_eq_zero_of_mem_integers hP hs x.2, hR_apply, laurentSeriesExpansion_coe, hLs,
        ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, PowerSeries.coeff_coe]
      simp
    · rw [hR_apply, residue_zpow_uniformizer, map_zpow₀, hLs,
        PowerSeries.coeff_neg_one_coe_zpow_mul_derivative hφ]
  exact LinearMap.congr_fun hR z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/ChangeOfUniformizer.lean:104` (proof source at `5a01f5fe3621`).
 **Stichtenoth's transformation formula** `res_{P,s}(z) = res_{P,t}(z · ds/dt)`: if the
Laurent expansion of `w` in `t` is the derivative of that of `s`, then the residue of `z` with
respect to `s` is the residue of `z * w` with respect to `t`. -/
theorem residue_eq_residue_mul (hs : P.ord s = 1) {w : F}
    (hw : P.laurentSeriesExpansion hP ht w =
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)) (z : F) :
    P.residue hP hs z = P.residue hP ht (z * w) := by
  rw [P.residue_eq_coeff_laurentSeriesExpansion_mul_derivative hP ht hs, residue_apply, map_mul,
    hw]

/-! ### Places with separable residue field -/

section ResidueField

variable [Algebra.IsSeparable k P.ResidueField]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/ChangeOfUniformizer.lean:121` (proof source at `5a01f5fe3621`).
 **Change of uniformizer in the completion.** At a place with separable residue field, the
coefficient of `T⁻¹` in the expansion of a completed function `z` in a uniformizer `s` is the
coefficient of `T⁻¹` in `z(T) * s'(T)`, where `z(T)` and `s(T)` are the expansions in another
uniformizer `t`, all with coefficients in `F_P`. -/
theorem coeff_neg_one_completionEquivLaurentSeriesResidueField_mul_derivative {s t : P.Completion}
    (hs : P.completionPlace.ord s = 1) (ht : P.completionPlace.ord t = 1) (z : P.Completion) :
    (P.completionEquivLaurentSeriesResidueField ht z * LaurentSeries.derivative P.ResidueField
      (P.completionEquivLaurentSeriesResidueField ht s)).coeff (-1) =
      (P.completionEquivLaurentSeriesResidueField hs z).coeff (-1) := by
  set Φs := P.completionEquivLaurentSeriesResidueField hs
  set Φt := P.completionEquivLaurentSeriesResidueField ht
  -- The expansion of `s` in `t` is a power series `φ` of order one.
  have hsint : s ∈ P.completionPlace.integers :=
    P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hs0 : (⟨s, hsint⟩ : P.completionPlace.integers) ≠ 0 := by
    intro h
    have : s = 0 := congrArg Subtype.val h
    simp [this] at hs
  set φ := P.completionIntegersEquivPowerSeriesResidueField ht ⟨s, hsint⟩
  have hφ : φ.order = 1 := by
    rw [order_completionIntegersEquivPowerSeriesResidueField _ _ _ hs0]
    simp [hs]
  have hΦφ : Φt s = φ := P.completionEquivLaurentSeriesResidueField_apply_integer ht ⟨s, hsint⟩
  -- Passing from the expansion in `s` to the expansion in `t` is a substitution `T ↦ φ`: it
  -- fixes the constants, which both expansions read in the coefficient field, and it preserves
  -- the valuation.
  set ψ := (Φs.symm.trans Φt).toRingHom
  have hψ (f : LaurentSeries P.ResidueField) : ψ f = Φt (Φs.symm f) := (rfl)
  have h := LaurentSeries.coeff_neg_one_map_mul_derivative ψ
    (fun c ↦ by
      rw [hψ, ← P.completionEquivLaurentSeriesResidueField_completionResidueFieldSection hs c,
        AlgEquiv.symm_apply_apply,
        P.completionEquivLaurentSeriesResidueField_completionResidueFieldSection ht c,
        P.completionEquivLaurentSeriesResidueField_completionResidueFieldSection hs c])
    (fun f hf ↦ by
      rw [← Φs.apply_symm_apply f, valuation_completionEquivLaurentSeriesResidueField] at hf
      rwa [hψ, valuation_completionEquivLaurentSeriesResidueField])
    hφ (by
      rw [hψ, ← P.completionEquivLaurentSeriesResidueField_uniformizer hs,
        AlgEquiv.symm_apply_apply, hΦφ])
    (Φs z)
  rwa [hψ, AlgEquiv.symm_apply_apply, ← hΦφ] at h

variable (hs : P.ord s = 1)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/ChangeOfUniformizer.lean:166` (proof source at `5a01f5fe3621`).
 **Change of uniformizer for residues at a place with separable residue field.** The residue
`res_{P,s}(z) ∈ F_P` is the coefficient of `T⁻¹` in `z(T) * s'(T)`, where `z(T)` and `s(T)` are
the Laurent expansions of `z` and `s` in another uniformizer `t`, with coefficients in `F_P`
(Stichtenoth, Proposition 4.2.9). -/
theorem residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative
    (z : F) :
    P.residueResidueField hs z = (P.laurentSeriesExpansionResidueField ht z *
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht s)).coeff
        (-1) := by
  rw [residueResidueField_apply, laurentSeriesExpansionResidueField_apply,
    laurentSeriesExpansionResidueField_apply, laurentSeriesExpansionResidueField_apply,
    coeff_neg_one_completionEquivLaurentSeriesResidueField_mul_derivative]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/ChangeOfUniformizer.lean:178` (proof source at `5a01f5fe3621`).
 **The transformation formula** `res_{P,s}(z) = res_{P,t}(z · w)` at a place with separable
residue field, for a function `w` whose Laurent expansion in `t` is the derivative of that of
`s`. -/
theorem residueResidueField_eq_residueResidueField_mul {w : F}
    (hw : P.laurentSeriesExpansionResidueField ht w =
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht s))
    (z : F) :
    P.residueResidueField hs z = P.residueResidueField ht (z * w) := by
  rw [P.residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative ht hs,
    residueResidueField_apply, map_mul, hw]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/ChangeOfUniformizer.lean:189` (proof source at `5a01f5fe3621`).
 **The transformation formula for `k`-valued residues** `Tr_{F_P/k} res_{P,s}(z) =
Tr_{F_P/k} res_{P,t}(z · w)`, for a function `w` whose Laurent expansion in `t` is the derivative
of that of `s`. -/
theorem traceResidue_eq_traceResidue_mul {w : F}
    (hw : P.laurentSeriesExpansionResidueField ht w =
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht s))
    (z : F) :
    P.traceResidue hs z = P.traceResidue ht (z * w) := by
  rw [traceResidue_apply, traceResidue_apply,
    P.residueResidueField_eq_residueResidueField_mul ht hs hw]

end ResidueField

end TauCeti.Place
end

end

/-! ## Source 47: `TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Derivative`
Original source SHA256: `b177a209fd4b12884b3af5873ffdf1f90a46cf06bafcc505c3c566b096b91fc1`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Laurent expansions of derivatives, and residues of differentials

Let `P` be a rational place of `F / k` and let `t` have order one at `P`, with `F` separable over
`k(t)`. Differentiation with respect to `t` (`TauCeti.derivativeOfSeparating`) is then compatible
with Laurent expansion in `t`: the expansion of `dz/dt` is the formal derivative of the expansion
of `z`. Both sides are `k`-derivations of `F` into `k((T))` taking `t` to `1`, and a derivation of
`F` is determined by its value at a separating element
(`Derivation.apply_eq_derivativeOfSeparating_smul`).

This identifies the function-field derivative `ds/dt` with the series `s'(T)` used in the
change-of-uniformizer formula (`TauCeti.Place.residue_eq_residue_mul`), giving Stichtenoth's
transformation formula `res_{P,s}(z) = res_{P,t}(z · ds/dt)` for two uniformizers `s` and `t`
(Proposition 4.2.9). It holds in every characteristic.

The formula makes the residue of a Kähler differential well defined (Definition 4.2.10). Writing
`ω = z dt`, the residue `res_P(ω) := res_{P,t}(z)` does not depend on the separating uniformizer
`t`, since `z dt = (z · dt/ds) ds`. An exact differential `dy` has residue zero, because the formal
derivative of a Laurent series has no `T⁻¹` term.

Over a perfect field every prime element of a place is separating
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`), so the residue of a
differential at a rational place needs no choice of uniformizer at all:
`TauCeti.Place.kaehlerResidueOfPerfectField` computes it with any prime element.

The compatibility of expansions with derivatives holds for every `k`-algebra map `F → A((X))`
sending `t` to `X` (`TauCeti.algHom_derivativeOfSeparating`), so it also holds at a place of any
degree whose residue field `F_P` is separable over `k`, for the expansion with coefficients in
`F_P` (`TauCeti.Place.laurentSeriesExpansionResidueField`). It gives the order of a derivative
there: if `z` vanishes to order at least `m` at `P`, then `dz/dt ≡ m z / t` modulo functions
vanishing to order at least `m`, and iterating, `dⁱz/dtⁱ` is congruent to
`m (m - 1) ⋯ (m - i + 1) z / tⁱ`. In particular, for a separating uniformizer `t` at such a
place `P`, `dz/dt` is integral at `P` whenever `z` is. This is the local input for computing
orders of Wronskians, and for comparing regular Kähler differentials with regular Weil
differentials.

The transformation formula and the residue of a differential also carry over to a place `P` of
arbitrary degree whose residue field `F_P` is separable over `k`, with Laurent expansions and
residues taking values in `F_P`
(`TauCeti.Place.laurentSeriesExpansionResidueField`, `TauCeti.Place.residueResidueField`).
The residue `res_P(ω) ∈ F_P` of a Kähler differential is again well defined, and so is its trace
`Tr_{F_P/k} res_P(ω) ∈ k`, the `k`-valued residue at a place of higher degree (Stichtenoth,
Remark 4.3.7). At a rational place the latter is the residue `TauCeti.Place.kaehlerResidue`.

## Main definitions

* `TauCeti.Place.kaehlerResidue`: the residue `res_P(ω)` of a Kähler differential `ω` at a
  rational place, computed with a separating uniformizer.
* `TauCeti.Place.kaehlerResidueOfPerfectField`: the residue `res_P(ω)` at a rational place of a
  function field over a perfect field, with no uniformizer in its signature.
* `TauCeti.Place.kaehlerResidueResidueField`: the residue `res_P(ω) ∈ F_P` at a place with
  separable residue field, computed with a separating uniformizer.
* `TauCeti.Place.kaehlerTraceResidue`: its trace `Tr_{F_P/k} res_P(ω) ∈ k`.

## Main results

* `TauCeti.algHom_derivativeOfSeparating`: a `k`-algebra map `F → A((X))` sending `t` to `X`
  carries `dz/dt` to the formal derivative.
* `TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating`: the Laurent expansion of `dz/dt`
  in `t` is the derivative of the Laurent expansion of `z`.
* `TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`: **the transformation formula**
  `res_{P,s}(z) = res_{P,t}(z · ds/dt)`.
* `TauCeti.Place.residue_derivativeOfSeparating`: `res_{P,t}(dy/dt) = 0`.
* `TauCeti.Place.laurentSeriesExpansionResidueField_derivativeOfSeparating`: at a place with
  separable residue field, the Laurent expansion of `dz/dt` with coefficients in `F_P` is the
  derivative of the Laurent expansion of `z`.
* `TauCeti.Place.derivativeOfSeparating_mem_integers`: for a separating uniformizer `t` at a
  place `P` with separable residue field, `dz/dt` is integral at `P` whenever `z` is.
* `TauCeti.Place.iterate_derivativeOfSeparating_sub_zsmul_mem_filtration`: if `z` vanishes to
  order at least `m`, then `dⁱz/dtⁱ ≡ m (m - 1) ⋯ (m - i + 1) z / tⁱ` modulo order `m - i + 1`.
* `TauCeti.Place.kaehlerResidue_eq_kaehlerResidue`: the residue of a differential is independent
  of the uniformizer used to compute it.
* `TauCeti.Place.kaehlerResidue_D`: exact differentials have residue zero.
* `TauCeti.Place.kaehlerResidueOfPerfectField_smul_D`: over a perfect field, `res_P(z dt)` is
  `res_{P,t}(z)` for every prime element `t`.
* `TauCeti.Place.residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating`: the
  transformation formula at a place with separable residue field.
* `TauCeti.Place.kaehlerResidueResidueField_eq_kaehlerResidueResidueField` and
  `TauCeti.Place.kaehlerTraceResidue_eq_kaehlerTraceResidue`: there too, the residue of a
  differential is independent of the uniformizer used to compute it.
* `TauCeti.Place.kaehlerTraceResidue_eq_kaehlerResidue`: at a rational place the `k`-valued
  residue is `TauCeti.Place.kaehlerResidue`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9 and Definition 4.2.10, and Remark 4.3.7.
-/

section
open scoped LaurentSeries _root_.IntermediateField

open KaehlerDifferential

namespace TauCeti

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:115` (proof source at `5a01f5fe3621`).
 **Laurent expansions of derivatives.** Let `t` be a separating element of `F / k` and let
`e : F → A((X))` be a `k`-algebra map into Laurent series over a `k`-algebra `A` with `e t = X`.
Then `e` carries `dz/dt` to the formal derivative of `e z`. -/
theorem algHom_derivativeOfSeparating {k F A : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing A] [Algebra k A] {t : F} (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    {e : F →ₐ[k] LaurentSeries A} (he : e t = HahnSeries.single 1 1) (z : F) :
    e (derivativeOfSeparating htr z) = LaurentSeries.derivative A (e z) := by
  -- Give `A((X))` the `F`-algebra structure induced by the expansion map.
  let _ : Algebra F (LaurentSeries A) := e.toRingHom.toAlgebra
  -- The `k`-module structure on `A((X))` found by instance search is the coefficientwise one.
  have hek (c : k) (z : F) : e (c • z) = c • e z := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, laurentSeries_algebraMap_mul_eq_smul]
  have _ : IsScalarTower k F (LaurentSeries A) := ⟨fun c z f ↦ by
    -- The induced algebra acts by multiplication with the expansion of the scalar.
    change e (c • z) * f = c • (e z * f)
    rw [hek, ← laurentSeries_algebraMap_mul_eq_smul, ← laurentSeries_algebraMap_mul_eq_smul,
      mul_assoc]⟩
  -- The source of the Laurent derivation uses algebra scalars, while its target uses
  -- coefficientwise scalars. Both actions factor through `A`, giving scalar compatibility.
  have _ : @IsScalarTower k A (LaurentSeries A)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun c ↦ by
      simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
  have _ : IsScalarTower k A (LaurentSeries A) := ⟨fun c a f ↦ by
    ext n
    simp only [HahnSeries.coeff_smul, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply, mul_assoc]⟩
  let D : Derivation k F (LaurentSeries A) :=
    ((laurentSeriesDerivation A).restrictScalars k).compAlgebraMap F
  -- By the chain rule `D z = (dz/dt) • D t`, and `D t = (X)' = 1`. Unfolding `D` and the
  -- induced algebra's scalar action turns the chain rule into an identity of Laurent series.
  have h := D.apply_eq_derivativeOfSeparating_smul htr z
  simp only [D, Derivation.compAlgebraMap_apply, Derivation.restrictScalars_apply,
    laurentSeriesDerivation_apply, Algebra.smul_def] at h
  change LaurentSeries.derivative A (e z) =
    e (derivativeOfSeparating htr z) * LaurentSeries.derivative A (e t) at h
  rw [h, he]
  simp

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

section Expansion

variable (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:164` (proof source at `5a01f5fe3621`).
 **The Laurent expansion of a derivative.** At a rational place `P` at which the separating
element `t` has order one, the Laurent expansion in `t` of `dz/dt` is the formal derivative of the
Laurent expansion of `z`. -/
theorem laurentSeriesExpansion_derivativeOfSeparating (z : F) :
    P.laurentSeriesExpansion hP ht (derivativeOfSeparating htr z) =
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht z) :=
  algHom_derivativeOfSeparating htr (P.laurentSeriesExpansion_uniformizer hP ht) z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:171` (proof source at `5a01f5fe3621`).
 **Stichtenoth's transformation formula** `res_{P,s}(z) = res_{P,t}(z · ds/dt)` for two
uniformizers `s` and `t` at a rational place, with `t` separating (Proposition 4.2.9). -/
theorem residue_eq_residue_mul_derivativeOfSeparating (hs : P.ord s = 1) (z : F) :
    P.residue hP hs z = P.residue hP ht (z * derivativeOfSeparating htr s) :=
  P.residue_eq_residue_mul hP ht hs (P.laurentSeriesExpansion_derivativeOfSeparating hP ht htr s) z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:178` (proof source at `5a01f5fe3621`).
 The derivative `dy/dt` has residue zero with respect to `t`: the formal derivative of a
Laurent series has no `T⁻¹` term. -/
@[simp]
theorem residue_derivativeOfSeparating (y : F) :
    P.residue hP ht (derivativeOfSeparating htr y) = 0 := by
  rw [residue_apply, laurentSeriesExpansion_derivativeOfSeparating, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp

end Expansion

/-! ### Expansions with coefficients in the residue field -/

section ResidueField

variable [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable k⟮t⟯ F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:197` (proof source at `5a01f5fe3621`).
 **The Laurent expansion of a derivative, at a place of any degree.** At a place `P` whose
residue field is separable over `k`, with `t` separating and of order one at `P`, the Laurent
expansion in `t` of `dz/dt`, with coefficients in the residue field, is the formal derivative of
the Laurent expansion of `z`. -/
theorem laurentSeriesExpansionResidueField_derivativeOfSeparating (z : F) :
    P.laurentSeriesExpansionResidueField ht (derivativeOfSeparating htr z) =
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht z) :=
  algHom_derivativeOfSeparating htr (P.laurentSeriesExpansionResidueField_uniformizer ht) z

/-! ### Orders of derivatives -/

include ht in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:208` (proof source at `5a01f5fe3621`).
 **The leading term of a derivative.** If `z` vanishes to order at least `m` at `P`, then
`dz/dt ≡ m z / t` modulo functions vanishing to order at least `m`. This holds in every
characteristic. -/
theorem derivativeOfSeparating_sub_zsmul_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) :
    derivativeOfSeparating htr z - m • (t⁻¹ * z) ∈ P.filtration m := by
  have hinv : (HahnSeries.single (1 : ℤ) (1 : P.ResidueField))⁻¹ = HahnSeries.single (-1) 1 :=
    inv_eq_of_mul_eq_one_right (by simp [HahnSeries.single_mul_single])
  rw [mem_filtration_iff, ← P.valuation_laurentSeriesExpansionResidueField ht, map_sub, map_zsmul,
    map_mul, map_inv₀, laurentSeriesExpansionResidueField_uniformizer,
    laurentSeriesExpansionResidueField_derivativeOfSeparating, hinv]
  apply LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le
  rw [valuation_laurentSeriesExpansionResidueField]
  exact (P.mem_filtration_iff).mp hz

include ht in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:223` (proof source at `5a01f5fe3621`).
 Differentiation with respect to a separating uniformizer preserves the valuation ring
at a place with separable residue field, in every characteristic. -/
theorem derivativeOfSeparating_mem_integers {z : F} (hz : z ∈ P.integers) :
    derivativeOfSeparating htr z ∈ P.integers := by
  have hz' : z ∈ P.filtration 0 := by
    simpa [P.mem_filtration_iff, P.mem_integers_iff] using hz
  have h := P.derivativeOfSeparating_sub_zsmul_mem_filtration ht htr hz'
  simpa [P.mem_filtration_iff, P.mem_integers_iff] using h

include ht in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:232` (proof source at `5a01f5fe3621`).
 Differentiation with respect to a prime element lowers the order at `P` by at most one. -/
theorem derivativeOfSeparating_mem_filtration {m : ℤ} {z : F} (hz : z ∈ P.filtration m) :
    derivativeOfSeparating htr z ∈ P.filtration (m - 1) := by
  have ht' : t⁻¹ ∈ P.filtration (-1) := by
    simpa [ht] using P.mem_filtration_ord t⁻¹
  have h : m • (t⁻¹ * z) ∈ P.filtration (m - 1) :=
    zsmul_mem (by simpa [neg_add_eq_sub] using P.mul_mem_filtration ht' hz) m
  simpa using add_mem (P.filtration_antitone (by omega)
    (P.derivativeOfSeparating_sub_zsmul_mem_filtration ht htr hz)) h

include ht in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:244` (proof source at `5a01f5fe3621`).
 The `i`-th derivative with respect to a prime element lowers the order at `P` by at most
`i`. -/
theorem iterate_derivativeOfSeparating_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) (i : ℕ) :
    (⇑(derivativeOfSeparating htr))^[i] z ∈ P.filtration (m - i) := by
  induction i with
  | zero => simpa using hz
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    simpa [sub_sub] using P.derivativeOfSeparating_mem_filtration ht htr ih

include ht in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:257` (proof source at `5a01f5fe3621`).
 **The leading term of an iterated derivative.** If `z` vanishes to order at least `m` at `P`,
then `dⁱz/dtⁱ ≡ m (m - 1) ⋯ (m - i + 1) z / tⁱ` modulo functions vanishing to order at least
`m - i + 1`. The coefficient is the descending Pochhammer symbol evaluated at `m`. -/
theorem iterate_derivativeOfSeparating_sub_zsmul_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) (i : ℕ) :
    (⇑(derivativeOfSeparating htr))^[i] z - (descPochhammer ℤ i).eval m • (t⁻¹ ^ i * z) ∈
      P.filtration (m - i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hti : t⁻¹ ^ i ∈ P.filtration (-i) := by
      simpa [ht] using P.mem_filtration_ord (t⁻¹ ^ i)
    have hw : t⁻¹ ^ i * z ∈ P.filtration (m - i) := by
      convert P.mul_mem_filtration hti hz using 2
      ring
    have h1 := P.derivativeOfSeparating_mem_filtration ht htr ih
    have h2 := zsmul_mem (P.derivativeOfSeparating_sub_zsmul_mem_filtration ht htr hw)
      ((descPochhammer ℤ i).eval m)
    -- Differentiate the `i`-th congruence, and use the leading term of `d(t⁻ⁱ z)/dt`.
    have key : (⇑(derivativeOfSeparating htr))^[i + 1] z -
          (descPochhammer ℤ (i + 1)).eval m • (t⁻¹ ^ (i + 1) * z) =
        derivativeOfSeparating htr ((⇑(derivativeOfSeparating htr))^[i] z -
            (descPochhammer ℤ i).eval m • (t⁻¹ ^ i * z)) +
          (descPochhammer ℤ i).eval m • (derivativeOfSeparating htr (t⁻¹ ^ i * z) -
            (m - i : ℤ) • (t⁻¹ * (t⁻¹ ^ i * z))) := by
      rw [Function.iterate_succ_apply', descPochhammer_succ_eval, map_sub, map_zsmul]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [key]
    refine add_mem (P.filtration_antitone ?_ h1) (P.filtration_antitone ?_ h2) <;> omega

end ResidueField

/-! ### Residues of Kähler differentials -/

section Kaehler

variable (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:298` (proof source at `5a01f5fe3621`).
 The **residue** `res_P(ω)` of a Kähler differential `ω` at a rational place `P`
(Stichtenoth, Definition 4.2.10): writing `ω = z dt` for a separating uniformizer `t` at `P`, it
is the residue `res_{P,t}(z)`. It does not depend on `t`
(`TauCeti.Place.kaehlerResidue_eq_kaehlerResidue`). -/
noncomputable def kaehlerResidue : Ω[F⁄k] →ₗ[k] k :=
  P.residue hP ht ∘ₗ ((kaehlerBasisOfSeparating htr).coord ()).restrictScalars k

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:302` (proof source at `5a01f5fe3621`).
 The residue of `ω` is the residue of its coordinate `ω / dt` in the basis `dt`. -/
theorem kaehlerResidue_apply (ω : Ω[F⁄k]) :
    P.kaehlerResidue hP ht htr ω = P.residue hP ht ((kaehlerBasisOfSeparating htr).coord () ω) :=
  (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:308` (proof source at `5a01f5fe3621`).
 The residue of `z dt` is `res_{P,t}(z)`. -/
@[simp]
theorem kaehlerResidue_smul_D (z : F) : P.kaehlerResidue hP ht htr (z • D k F t) =
    P.residue hP ht z := by
  simp [kaehlerResidue_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:314` (proof source at `5a01f5fe3621`).
 **Exact differentials have residue zero**: `res_P(dy) = 0`. -/
@[simp]
theorem kaehlerResidue_D (y : F) : P.kaehlerResidue hP ht htr (D k F y) = 0 := by
  rw [← derivativeOfSeparating_smul_D htr y, kaehlerResidue_smul_D,
    residue_derivativeOfSeparating]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:320` (proof source at `5a01f5fe3621`).
 **The residue of a differential is well defined** (Stichtenoth, Definition 4.2.10): it does not
depend on the separating uniformizer used to compute it. -/
theorem kaehlerResidue_eq_kaehlerResidue (hs : P.ord s = 1) (hstr : Transcendental k s)
    [Algebra.IsSeparable k⟮s⟯ F] :
    P.kaehlerResidue hP hs hstr = P.kaehlerResidue hP ht htr := by
  -- Both sides are `F`-semilinear in `ω`, so it suffices to compare them on `ω = z ds`, where
  -- `z ds = (z · ds/dt) dt`.
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z : F, z • D k F s = ω :=
    ⟨(kaehlerBasisOfSeparating hstr).coord () ω, by
      simpa using (kaehlerBasisOfSeparating hstr).sum_repr ω⟩
  rw [kaehlerResidue_smul_D, ← derivativeOfSeparating_smul_D htr s, smul_smul,
    kaehlerResidue_smul_D, P.residue_eq_residue_mul_derivativeOfSeparating hP ht htr hs]

end Kaehler

/-! ### Residues of Kähler differentials over a perfect field -/

section PerfectField

variable [PerfectField k] (hF : IsFunctionField k F)

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:346` (proof source at `5a01f5fe3621`).
 The **residue** `res_P(ω)` of a Kähler differential `ω` at a rational place `P` of a function
field over a perfect field (Stichtenoth, Definition 4.2.10). Over a perfect field every prime
element of `P` is separating
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`), so this is
`TauCeti.Place.kaehlerResidue` computed with some prime element; it does not depend on the choice
(`TauCeti.Place.kaehlerResidueOfPerfectField_eq_kaehlerResidue`). -/
noncomputable def kaehlerResidueOfPerfectField : Ω[F⁄k] →ₗ[k] k :=
  have ht := (P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅).choose_spec.1
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  letI := hsep.2
  P.kaehlerResidue hP ht hsep.1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:354` (proof source at `5a01f5fe3621`).
 Over a perfect field, the residue of a differential is `TauCeti.Place.kaehlerResidue` computed
with any separating uniformizer. -/
theorem kaehlerResidueOfPerfectField_eq_kaehlerResidue (htr : Transcendental k t)
    [Algebra.IsSeparable k⟮t⟯ F] :
    P.kaehlerResidueOfPerfectField hP hF = P.kaehlerResidue hP ht htr :=
  -- The left side unfolds to `kaehlerResidue` at the prime element chosen in the definition.
  have ht' := (P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅).choose_spec.1
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht'
  letI := hsep.2
  P.kaehlerResidue_eq_kaehlerResidue hP ht htr ht' hsep.1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:365` (proof source at `5a01f5fe3621`).
 Over a perfect field, the residue of `z dt` is `res_{P,t}(z)` for every prime element `t`
of `P`. -/
theorem kaehlerResidueOfPerfectField_smul_D (z : F) :
    P.kaehlerResidueOfPerfectField hP hF (z • D k F t) = P.residue hP ht z := by
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep.2
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF hsep.1, kaehlerResidue_smul_D]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:373` (proof source at `5a01f5fe3621`).
 **Exact differentials have residue zero**: `res_P(dy) = 0`. -/
@[simp]
theorem kaehlerResidueOfPerfectField_D (y : F) :
    P.kaehlerResidueOfPerfectField hP hF (D k F y) = 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep.2
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF hsep.1, kaehlerResidue_D]

end PerfectField

/-! ### Places with separable residue field -/

section ResidueField

variable [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable k⟮t⟯ F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:392` (proof source at `5a01f5fe3621`).
 **Stichtenoth's transformation formula** `res_{P,s}(z) = res_{P,t}(z · ds/dt)` at a place
with separable residue field, for two uniformizers `s` and `t` with `t` separating, the residues
taking values in `F_P` (Proposition 4.2.9). -/
theorem residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating
    (hs : P.ord s = 1) (z : F) :
    P.residueResidueField hs z = P.residueResidueField ht (z * derivativeOfSeparating htr s) :=
  P.residueResidueField_eq_residueResidueField_mul ht hs
    (P.laurentSeriesExpansionResidueField_derivativeOfSeparating ht htr s) z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:400` (proof source at `5a01f5fe3621`).
 **The transformation formula for `k`-valued residues** at a place with separable residue
field: `Tr_{F_P/k} res_{P,s}(z) = Tr_{F_P/k} res_{P,t}(z · ds/dt)`. -/
theorem traceResidue_eq_traceResidue_mul_derivativeOfSeparating (hs : P.ord s = 1) (z : F) :
    P.traceResidue hs z = P.traceResidue ht (z * derivativeOfSeparating htr s) :=
  P.traceResidue_eq_traceResidue_mul ht hs
    (P.laurentSeriesExpansionResidueField_derivativeOfSeparating ht htr s) z

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:408` (proof source at `5a01f5fe3621`).
 The derivative `dy/dt` has residue zero with respect to `t` at a place with separable residue
field: the formal derivative of a Laurent series has no `T⁻¹` term. -/
@[simp]
theorem residueResidueField_derivativeOfSeparating (y : F) :
    P.residueResidueField ht (derivativeOfSeparating htr y) = 0 := by
  rw [residueResidueField_apply, laurentSeriesExpansionResidueField_derivativeOfSeparating,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:416` (proof source at `5a01f5fe3621`).
 The derivative `dy/dt` has `k`-valued residue zero with respect to `t`. -/
@[simp]
theorem traceResidue_derivativeOfSeparating (y : F) :
    P.traceResidue ht (derivativeOfSeparating htr y) = 0 := by
  rw [traceResidue_apply, residueResidueField_derivativeOfSeparating, map_zero]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:424` (proof source at `5a01f5fe3621`).
 The **residue** `res_P(ω) ∈ F_P` of a Kähler differential `ω` at a place with separable
residue field (Stichtenoth, Definition 4.2.10 and Remark 4.3.7): writing `ω = z dt` for a
separating uniformizer `t` at `P`, it is the residue `res_{P,t}(z)`. It does not depend on `t`
(`TauCeti.Place.kaehlerResidueResidueField_eq_kaehlerResidueResidueField`). -/
noncomputable def kaehlerResidueResidueField : Ω[F⁄k] →ₗ[k] P.ResidueField :=
  P.residueResidueField ht ∘ₗ ((kaehlerBasisOfSeparating htr).coord ()).restrictScalars k

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:428` (proof source at `5a01f5fe3621`).
 The residue of `ω` is the residue of its coordinate `ω / dt` in the basis `dt`. -/
theorem kaehlerResidueResidueField_apply (ω : Ω[F⁄k]) :
    P.kaehlerResidueResidueField ht htr ω =
      P.residueResidueField ht ((kaehlerBasisOfSeparating htr).coord () ω) :=
  (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:435` (proof source at `5a01f5fe3621`).
 The residue of `z dt` is `res_{P,t}(z)`. -/
@[simp]
theorem kaehlerResidueResidueField_smul_D (z : F) :
    P.kaehlerResidueResidueField ht htr (z • D k F t) = P.residueResidueField ht z := by
  simp [kaehlerResidueResidueField_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:441` (proof source at `5a01f5fe3621`).
 **Exact differentials have residue zero**: `res_P(dy) = 0`. -/
@[simp]
theorem kaehlerResidueResidueField_D (y : F) :
    P.kaehlerResidueResidueField ht htr (D k F y) = 0 := by
  rw [← derivativeOfSeparating_smul_D htr y, kaehlerResidueResidueField_smul_D,
    residueResidueField_derivativeOfSeparating]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:449` (proof source at `5a01f5fe3621`).
 **The residue of a differential at a place with separable residue field is well defined**
(Stichtenoth, Definition 4.2.10): it does not depend on the separating uniformizer used to
compute it. -/
theorem kaehlerResidueResidueField_eq_kaehlerResidueResidueField (hs : P.ord s = 1)
    (hstr : Transcendental k s) [Algebra.IsSeparable k⟮s⟯ F] :
    P.kaehlerResidueResidueField hs hstr = P.kaehlerResidueResidueField ht htr := by
  -- Both sides are `F`-semilinear in `ω`, so it suffices to compare them on `ω = z ds`, where
  -- `z ds = (z · ds/dt) dt`.
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z : F, z • D k F s = ω :=
    ⟨(kaehlerBasisOfSeparating hstr).coord () ω, by
      simpa using (kaehlerBasisOfSeparating hstr).sum_repr ω⟩
  rw [kaehlerResidueResidueField_smul_D, ← derivativeOfSeparating_smul_D htr s, smul_smul,
    kaehlerResidueResidueField_smul_D,
    P.residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating ht htr hs]

/-- Kind: DEF. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:467` (proof source at `5a01f5fe3621`).
 The `k`-valued **residue** `Tr_{F_P/k} res_P(ω)` of a Kähler differential `ω` at a place with
separable residue field (Stichtenoth, Remark 4.3.7). It does not depend on the separating
uniformizer `t` (`TauCeti.Place.kaehlerTraceResidue_eq_kaehlerTraceResidue`), and at a rational
place it is `TauCeti.Place.kaehlerResidue` (`TauCeti.Place.kaehlerTraceResidue_eq_kaehlerResidue`).
-/
noncomputable def kaehlerTraceResidue : Ω[F⁄k] →ₗ[k] k :=
  (Algebra.trace k P.ResidueField).comp (P.kaehlerResidueResidueField ht htr)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:471` (proof source at `5a01f5fe3621`).
 The `k`-valued residue is the trace of the residue. -/
theorem kaehlerTraceResidue_apply (ω : Ω[F⁄k]) :
    P.kaehlerTraceResidue ht htr ω =
      Algebra.trace k P.ResidueField (P.kaehlerResidueResidueField ht htr ω) :=
  (rfl)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:478` (proof source at `5a01f5fe3621`).
 The `k`-valued residue of `z dt` is `Tr_{F_P/k} res_{P,t}(z)`. -/
@[simp]
theorem kaehlerTraceResidue_smul_D (z : F) :
    P.kaehlerTraceResidue ht htr (z • D k F t) = P.traceResidue ht z := by
  rw [kaehlerTraceResidue_apply, kaehlerResidueResidueField_smul_D, traceResidue_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:484` (proof source at `5a01f5fe3621`).
 **Exact differentials have `k`-valued residue zero.** -/
@[simp]
theorem kaehlerTraceResidue_D (y : F) : P.kaehlerTraceResidue ht htr (D k F y) = 0 := by
  rw [kaehlerTraceResidue_apply, kaehlerResidueResidueField_D, map_zero]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:489` (proof source at `5a01f5fe3621`).
 **The `k`-valued residue of a differential is well defined**: it does not depend on the
separating uniformizer used to compute it. -/
theorem kaehlerTraceResidue_eq_kaehlerTraceResidue (hs : P.ord s = 1)
    (hstr : Transcendental k s) [Algebra.IsSeparable k⟮s⟯ F] :
    P.kaehlerTraceResidue hs hstr = P.kaehlerTraceResidue ht htr := by
  rw [kaehlerTraceResidue, kaehlerTraceResidue,
    P.kaehlerResidueResidueField_eq_kaehlerResidueResidueField ht htr hs hstr]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Expansion/Laurent/Derivative.lean:497` (proof source at `5a01f5fe3621`).
 At a rational place the `k`-valued residue of a differential is its residue
`TauCeti.Place.kaehlerResidue`. -/
theorem kaehlerTraceResidue_eq_kaehlerResidue :
    P.kaehlerTraceResidue ht htr = P.kaehlerResidue hP ht htr :=
  LinearMap.ext fun ω ↦ by
    rw [kaehlerTraceResidue_apply, kaehlerResidueResidueField_apply, ← traceResidue_apply,
      traceResidue_eq_residue _ _ hP, kaehlerResidue_apply]

end ResidueField

end Place

end TauCeti
end

end

/-! ## Source 48: `TauCeti.FieldTheory.FunctionField.Differential.LocalNonvanishing`
Original source SHA256: `0087edb7cf910379a8a346cab06aa7fce5f46fcfc6b0d27b7562803872ceb167`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Nonvanishing of local components of Weil differentials

Every local component of a nonzero Weil differential on an algebraic function field with exact
constants is nonzero.  Consequently, fixing any one place `P`, the map `ω ↦ ω_P` is injective on
the space of Weil differentials: one local component determines the global differential.

The key point is that allowing a double pole at `P` strictly enlarges the space of regular Weil
differentials.  Indeed,

`dim_k Ω_F(-2P) = 2 deg P - 1 + g > g = dim_k Ω_F(0)`.

Thus some differential in `Ω_F(-2P)` is not regular.  Its local component at `P` cannot vanish,
because the local-component characterization of the filtration would then make it regular after
all.  Since the full space of Weil differentials is one-dimensional over `F`, multiplication by a
function carries this witness to any prescribed nonzero differential, and multiplication cannot
create a zero local component.

This is the nonvanishing assertion and the final clause of Stichtenoth, *Algebraic Function Fields
and Codes*, 2nd ed., Proposition 1.7.3(a).  It is the local input for defining the order of a Weil
differential and for comparing Weil differentials with Kähler differentials through residues.

## Main results

* `TauCeti.repartitionDualComponent_ne_zero`: over an exact constant field, every local component
  of a nonzero Weil differential is nonzero.
* `TauCeti.repartitionDualComponent_eq_zero_iff`: over an exact constant field, a Weil differential
  is zero exactly when its local component at one fixed place is zero.
* `TauCeti.repartitionDualComponent_inj`: over an exact constant field, two Weil differentials are
  equal exactly when their local components at one fixed place are equal.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.3(a).
-/

section
namespace TauCeti

open _root_.TauCeti.AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/LocalNonvanishing.lean:62` (proof source at `5a01f5fe3621`).
 At every place of an algebraic function field with exact constants, some Weil differential
has a nonzero local component.

The witness can be taken from `Ω_F(-2P)`: this space has dimension
`2 * deg P - 1 + g`, strictly larger than the `g`-dimensional space `Ω_F(0)` of regular
differentials. -/
private theorem exists_repartitionDualComponent_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) :
    ∃ ω : Module.Dual k ↥(repartitionSpace k F),
      ω ∈ weilDifferentialSpace k F ∧ repartitionDualComponent ω P ≠ 0 := by
  let D : Divisor k F := (-2 : ℤ) • _root_.TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint P
  have hDneg : D < 0 := _root_.TauCeti.AlgebraicGeometry.WeilDivisor.zsmul_ofPoint_lt_zero P (by omega)
  have hle : weilDifferentialFiltration (0 : Divisor k F) ≤
      weilDifferentialFiltration D :=
    weilDifferentialFiltration_antitone hDneg.le
  have hfdD := finiteDimensional_weilDifferentialFiltration hF D
  have hdimD := finrank_weilDifferentialFiltration hF hex D
  have hdim0 := finrank_weilDifferentialFiltration_zero hF hex
  have hP : (1 : ℤ) ≤ P.degree := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hdimlt : Module.finrank k ↥(weilDifferentialFiltration (0 : Divisor k F)) <
      Module.finrank k ↥(weilDifferentialFiltration D) := by
    rw [hdim0]
    rw [Divisor.indexOfSpecialty_def,
      Divisor.dim_eq_zero_of_lt_zero hF hDneg, Divisor.degree_zsmul,
      Divisor.degree_ofPoint] at hdimD
    dsimp [D] at hdimD
    have hdimD' : (genus k F : ℤ) <
        Module.finrank k ↥(weilDifferentialFiltration D) := by
      rw [hdimD]
      omega
    exact_mod_cast hdimD'
  have hlt : weilDifferentialFiltration (0 : Divisor k F) <
      weilDifferentialFiltration D :=
    Submodule.lt_of_le_of_finrank_lt_finrank hle hdimlt
  obtain ⟨ω, hωD, hω0⟩ := IsConcreteLE.exists_of_lt hlt
  have hωspace : ω ∈ weilDifferentialSpace k F :=
    weilDifferentialFiltration_le_weilDifferentialSpace D hωD
  refine ⟨ω, hωspace, fun hcomponent ↦ hω0 ?_⟩
  rw [mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero hωspace]
  intro Q x hx
  rcases eq_or_ne Q P with rfl | hQP
  · rw [hcomponent]
    exact LinearMap.zero_apply _
  · exact repartitionDualComponent_apply_eq_zero_of_le hωD Q (by
      simpa [D, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQP] using hx)

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/LocalNonvanishing.lean:105` (proof source at `5a01f5fe3621`).
 Over an exact constant field, **every local component of a nonzero Weil differential is
nonzero** (Stichtenoth, Proposition 1.7.3(a)). -/
theorem repartitionDualComponent_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (hω0 : ω ≠ 0) (P : Place k F) :
    repartitionDualComponent ω P ≠ 0 := by
  obtain ⟨η, hη, hηP⟩ := exists_repartitionDualComponent_ne_zero hF hex P
  obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq hF hex hω hω0 hη
  intro hωP
  apply hηP
  ext x
  rw [← hc, repartitionDualComponent_repartitionDualMul, hωP, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/LocalNonvanishing.lean:120` (proof source at `5a01f5fe3621`).
 Over an exact constant field, a Weil differential is zero exactly when its local component at
one fixed place is zero. -/
@[simp]
theorem repartitionDualComponent_eq_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (P : Place k F) :
    repartitionDualComponent ω P = 0 ↔ ω = 0 := by
  refine ⟨fun h ↦ not_ne_iff.mp fun hω0 ↦
    repartitionDualComponent_ne_zero hF hex hω hω0 P h, ?_⟩
  rintro rfl
  ext x
  simp

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/LocalNonvanishing.lean:133` (proof source at `5a01f5fe3621`).
 Over an exact constant field, **one local component determines a Weil differential**: two Weil
differentials are equal if and only if their local components at any one fixed place are equal. -/
@[simp]
theorem repartitionDualComponent_inj (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω η : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (hη : η ∈ weilDifferentialSpace k F)
    (P : Place k F) :
    repartitionDualComponent ω P = repartitionDualComponent η P ↔ ω = η := by
  constructor
  · intro hcomponent
    have hsub : repartitionDualComponent (ω - η) P = 0 := by
      ext x
      have hx := LinearMap.congr_fun hcomponent x
      rw [repartitionDualComponent_apply, LinearMap.sub_apply, LinearMap.zero_apply]
      exact sub_eq_zero.mpr (by simpa only [repartitionDualComponent_apply] using hx)
    exact sub_eq_zero.mp <|
      (repartitionDualComponent_eq_zero_iff hF hex (Submodule.sub_mem _ hω hη) P).mp hsub
  · rintro rfl
    rfl

end TauCeti
end

end

/-! ## Source 49: `TauCeti.FieldTheory.FunctionField.Differential.TraceResidue`
Original source SHA256: `d82f05430f838174c673d43d10f72ccad2e5de1814293e78d8552a5e56a9bdd5`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Trace residues of Weil differentials

Let `F / k` be an algebraic function field with exact constant field `k`.
At a place `P` with separable residue field, choose a separating uniformizer `t`.
Every Weil differential has a unique expression `ω = z dt`, since the Weil differential
space is one-dimensional. Its local component at `u` is the residue-field trace of the
coefficient of `t⁻¹` in the Laurent expansion of `z u`.

Here `z` is obtained from the existing basis `weilDifferentialBasisOfSeparating`, rather
than from a new differential carrier. The formula extends
`repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue` from `dt` to
arbitrary Weil differentials, including at nonrational places. In particular, the trace
residue is independent of the separating uniformizer, because it equals the intrinsic
local component.

For a family of separating uniformizers, these trace residues have finite support on
every repartition. Their sum on a diagonal function is zero. This is the residue theorem
with residue-field traces; no algebraic closure or infinitude of the constant field is
required. The hypotheses explicitly require separable residue fields and separating
uniformizers, both available over a perfect constant field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Theorem 4.3.2(d),
  Corollary 4.3.3 and Remark 4.3.7(d).
-/

section
open scoped _root_.IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/TraceResidue.lean:49` (proof source at `5a01f5fe3621`).
 The local component of `ω = z dt` is the trace residue of `z u`, at a place of any
degree with separable residue field and a separating uniformizer `t`. The coefficient `z`
is the coordinate of `ω` in the basis `dt`. -/
theorem repartitionDualComponent_eq_traceResidue_coord
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {t : F}
    (ht : P.ord t = 1) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : ↥(weilDifferentialSpace k F)) (u : F) :
    letI := weilDifferentialSpaceModule hF
    let htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by simp [ht])
    repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P u =
      P.traceResidue ht ((weilDifferentialBasisOfSeparating hF hex htr).coord () ω * u) := by
  let := weilDifferentialSpaceModule hF
  dsimp only
  let htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by simp [ht])
  have hω : (weilDifferentialBasisOfSeparating hF hex htr).coord () ω •
      weilDifferentialOfSeparating hF htr = ω := by
    simpa using (weilDifferentialBasisOfSeparating hF hex htr).sum_repr ω
  -- Translate the uniformizer by zero to use the local formula for `dt`.
  have ht₀ : P.ord (t - algebraMap k F 0) = 1 := by simpa using ht
  have hres : P.traceResidue ht₀ = P.traceResidue ht := by
    simp only [map_zero, sub_zero]
  conv_lhs => rw [← hω]
  rw [coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue hF htr ht₀, hres]

section Family

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    [∀ P : Place k F, Algebra.IsSeparable k P.ResidueField]
    (t : Place k F → F) (ht : ∀ P : Place k F, P.ord (t P) = 1)
    [∀ P : Place k F, Algebra.IsSeparable k⟮t P⟯ F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/TraceResidue.lean:81` (proof source at `5a01f5fe3621`).
 The local trace residues of a Weil differential on a repartition are nonzero at only
finitely many places, even when the places are not rational. -/
theorem finite_support_traceResidue_coord (ω : ↥(weilDifferentialSpace k F))
    (a : ↥(repartitionSpace k F)) :
    letI := weilDifferentialSpaceModule hF
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    (Function.support fun P : Place k F ↦ P.traceResidue (ht P)
      ((weilDifferentialBasisOfSeparating hF hex (htr P)).coord () ω *
        (a : Place k F → F) P)).Finite := by
  let := weilDifferentialSpaceModule hF
  dsimp only
  let htr : ∀ P, Transcendental k (t P) :=
    fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
  have heq : (fun P : Place k F ↦ P.traceResidue (ht P)
      ((weilDifferentialBasisOfSeparating hF hex (htr P)).coord () ω *
        (a : Place k F → F) P)) =
      (fun P ↦ repartitionDualComponent (ω : Module.Dual k _) P
        ((a : Place k F → F) P)) := by
    funext P
    exact (repartitionDualComponent_eq_traceResidue_coord hF hex (ht P) ω _).symm
  rw [heq]
  exact finite_support_repartitionDualComponent_apply ω.2 a

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/TraceResidue.lean:106` (proof source at `5a01f5fe3621`).
 The residue theorem with residue-field traces: if `ω = z_P dt_P` at each place,
then `∑_P Tr(res_{P,t_P}(z_P u)) = 0` for every function `u`. The summands have finite
support by `finite_support_traceResidue_coord`, applied to the constant repartition. -/
theorem finsum_traceResidue_coord_eq_zero (ω : ↥(weilDifferentialSpace k F)) (u : F) :
    letI := weilDifferentialSpaceModule hF
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    ∑ᶠ P : Place k F, P.traceResidue (ht P)
      ((weilDifferentialBasisOfSeparating hF hex (htr P)).coord () ω * u) = 0 := by
  let := weilDifferentialSpaceModule hF
  simp_rw [← repartitionDualComponent_eq_traceResidue_coord hF hex (ht _)]
  exact finsum_repartitionDualComponent_eq_zero hF ω.2 u

end Family

end TauCeti
end

end

/-! ## Source 50: `TauCeti.FieldTheory.FunctionField.Place.ConstantField`
Original source SHA256: `30f8a1cc4db325d4662434bed5e7023ac3b647abc3e6f065b1aa8d2cecdc01c4`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# A rational place forces exact constants

A constant algebraic over the base field is regular at every place. At a rational place its
residue is the residue of a base-field element. Their difference is algebraic and has valuation
less than one, so it must vanish. Thus the existence of a rational place certifies exactness of
the constant field, including for composita with a completely split rational place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.1 and Corollary 3.9.7.
-/

section
namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/ConstantField.lean:33` (proof source at `5a01f5fe3621`).
 If `F / k` has a rational place, every element of `F` algebraic over `k` belongs to `k`.
No function-field or separability hypothesis is needed. -/
theorem isIntegrallyClosedIn_of_degree_eq_one (P : Place k F) (hP : P.degree = 1) :
    IsIntegrallyClosedIn k F := by
  rw [TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic]
  intro x hx
  obtain ⟨c, hc⟩ := (P.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hP)
    x (P.mem_integers_of_mem_algebraicClosure (mem_algebraicClosure_iff.mpr hx))
  refine ⟨c, (sub_eq_zero.mp ?_).symm⟩
  by_contra hne
  have halg : IsAlgebraic k (x - algebraMap k F c) :=
    mem_algebraicClosure_iff.mp <| (algebraicClosure k F).sub_mem
      (mem_algebraicClosure_iff.mpr hx) ((algebraicClosure k F).algebraMap_mem c)
  rw [P.valuation_eq_one_of_isAlgebraic halg hne] at hc
  exact lt_irrefl _ hc

end TauCeti.Place
end

end

/-! ## Source 51: `TauCeti.FieldTheory.FunctionField.Place.Extension.PrimeElement`
Original source SHA256: `c25e3ed3c2b6a27e69d6f173b96198d171d7e0e3b33129441aaa3d2f92c32cca`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Prime elements at a rational place above

Let `F' / F` be an integral extension, with `F` a field over `k` and `F'` a field over `k'`, and
let `P'` be a rational place of `F' / k'` lying over the place `P` of `F / k` with
`e(P' ∣ P) = 1`.  A prime element of `P` of the form `q(z)`, with `q` separable over `k` and `z`
regular at `P`, yields the prime element `z - a` of `P'`, where `a` is the value of `z` at `P'`.

## Main results

* `TauCeti.Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one`: at a rational place `P'`
  unramified over `P`, a prime element `q(z)` of `P` with `q` separable yields a prime element
  `z - a` of `P'`.
-/

section
namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}

variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

open _root_.Polynomial in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Place/Extension/PrimeElement.lean:45` (proof source at `5a01f5fe3621`).
 **A prime element `q(z)` below gives a prime element `z - a` at a rational place above**: at a
rational place `P'` of `F'` over a place `P` of `F` with `e(P' ∣ P) = 1`, a prime element `q(z)` of
`P`, with `q` separable over `k` and `z` regular at `P`, gives a prime element `z - a` of `P'` for
some constant `a`, namely the value of `z` at `P'`, which is a simple root of `q`. -/
theorem exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one [Algebra.IsIntegral F F']
    {P' : Place k' F'} (hdeg : P'.degree = 1) (he : P'.ramificationIdx F = 1) {z : F}
    (hz : 0 ≤ (P'.restrict k F).ord z) {q : Polynomial k} (hq : q.Separable)
    (hqz : (P'.restrict k F).ord (Polynomial.aeval z q) = 1) :
    ∃ a : k', P'.ord (algebraMap F F' z - algebraMap k' F' a) = 1 := by
  set z' := algebraMap F F' z
  have hzint : z' ∈ P'.integers := (mem_integers_restrict_iff k F P' z).mp
    ((P'.restrict k F).mem_integers_iff_ord_nonneg.mpr hz)
  obtain ⟨a, ha⟩ := (degree_eq_one_iff_forall_exists_valuation_sub_lt_one P').mp hdeg z' hzint
  refine ⟨a, ?_⟩
  -- `Q(z')`, with `Q` the image of `q` over `k'`, is a prime element of `P'`.
  set Q := q.map (algebraMap k k')
  have hQz : P'.ord (aeval z' Q) = 1 := by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, ord_algebraMap_restrict k F P', he, hqz]
    simp
  have hord_eq_zero {w : F'} (hw : P'.valuation w = 1) : P'.ord w = 0 := by
    rw [ord_def, hw, WithZero.log_one, neg_zero]
  -- `a` is a root of `Q`, simple because `Q` is separable, so `Q = (X - a) R` with `R(a) ≠ 0`.
  have hQa : Q.eval a = 0 := by
    by_contra hne
    rw [hord_eq_zero (valuation_aeval_eq_one_of_valuation_sub_lt_one ha hne)] at hQz
    exact zero_ne_one hQz
  set R := Q /ₘ (X - C a)
  have hQR : (X - C a) * R = Q := mul_divByMonic_eq_iff_isRoot.mpr hQa
  have hRa : R.eval a ≠ 0 := by
    have hsep : Q.Separable := hq.map
    have hder := hsep.aeval_derivative_ne_zero (x := a) (by rwa [coe_aeval_eq_eval])
    rw [coe_aeval_eq_eval] at hder
    rw [← hQR] at hder
    simpa using hder
  -- So `ord (z' - a) = ord Q(z') - ord R(z') = 1 - 0`.
  have hRz := hord_eq_zero (valuation_aeval_eq_one_of_valuation_sub_lt_one ha hRa)
  have hfac : aeval z' Q = (z' - algebraMap k' F' a) * aeval z' R := by
    rw [← hQR, map_mul, map_sub, aeval_X, aeval_C]
  have hne : aeval z' Q ≠ 0 := fun h0 ↦ by rw [h0, ord_zero] at hQz; exact zero_ne_one hQz
  rw [hfac] at hQz hne
  rw [P'.ord_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne), hRz, add_zero] at hQz
  exact hQz

end Place

end TauCeti
end

end

/-! ## Source 52: `TauCeti.FieldTheory.FunctionField.Differential.Independence`
Original source SHA256: `dede4cb03d7586cdb9b778a3e8a0e52db869d87298333b924d7b9682bdec8303`. -/

section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The chain rule, independence of the Kähler–Weil comparison, and the residue theorem

Let `F / k` be an algebraic function field with exact constants, and let `x` and `y` be separating
elements. The Weil differentials `dx` and `dy` (`TauCeti.weilDifferentialOfSeparating`) are the
cotraces of the canonical differential of the rational function field along `X ↦ x` and `X ↦ y`.
They satisfy the chain rule

`dy = (dy/dx) · dx`,

where `dy/dx` is the derivative of Kähler differentials (`TauCeti.derivativeOfSeparating`). This
is Stichtenoth's Theorem 4.3.2(a), `δ(y) = (dy/dx) · δ(x)`. Stichtenoth assumes a perfect
constant field; here the chain rule holds over every exact constant field.

The proof compares one local component. At a rational place `P` where `x - a` and `y - b` are both
prime elements, the local components are residues
(`TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`):
`(dy)_P (u) = res_{P,y-b} (u)` and `(dx)_P (u) = res_{P,x-a} (u)`. The transformation formula
(`TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`) rewrites the first as
`res_{P,x-a} (u · dy/dx)`, which is the local component of `(dy/dx) · dx`. Over an exact constant
field one local component determines a Weil differential
(`TauCeti.repartitionDualComponent_inj`).

`F` need not have such a rational place, but it has infinitely many places whose residue field is
separable over `k` (`TauCeti.Place.infinite_setOf_isSeparable_residueField`), even over an
imperfect field. At all but finitely many of them, `x` and `y` are units and some `q(x)` and `r(y)`
are prime elements (`TauCeti.Place.finite_setOf_forall_irreducible_ord_aeval_ne_one`), where `q`
and `r` are separable since the values of `x` and `y` are
(`TauCeti.Place.separable_of_ord_aeval_pos`). A finite separable constant field extension makes the
places above such a place rational
(`TauCeti.Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one`), without ramification,
so there `x - a` and `y - b` are prime elements, and the chain rule holds after extending the
constants. The cotrace to the extension is injective and carries `dx` and `dy` to their
counterparts (`TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating`), while the algebra
map carries `dy/dx` to its counterpart (`TauCeti.derivativeOfSeparating_algebraMap`), so the chain
rule descends.

Consequently the Kähler–Weil comparison
`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating` does not depend on the separating
element used to build it, and the local components of the Weil differential attached to a Kähler
differential `ω` are its residues. At a place `P` with separable residue field and a separating
prime element `t`, writing `u ω = z dt`, the local component at `u` is the trace residue
`Tr_{F_P/k} res_{P,t} (z)`, the form of Stichtenoth's Theorem 4.3.2(d) for places of arbitrary
degree (Remark 4.3.7(d)). At rational places it reads `ω_P (u) = res_P (u ω)`. Over a perfect
constant field every residue field is separable and every prime element separating.

These are the trace-residue formulas for Weil differentials of
`TauCeti.FieldTheory.FunctionField.Differential.TraceResidue` read through the comparison, which
preserves coordinates (`TauCeti.coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating`). The
residue theorem with trace residues for Weil differentials
(`TauCeti.finsum_traceResidue_coord_eq_zero`) thereby becomes **the residue theorem** for Kähler
differentials over a perfect field: the trace residues of `ω` at all places sum to zero
(Stichtenoth, Corollary 4.3.3 and Remark 4.3.7(d)). Over an algebraically closed field every place
is rational and this is `∑_P res_P (ω) = 0`.

## Main results

* `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one`:
  `dy = (dy/dx) · dx`, given a rational place at which `x - a` and `y - b` are prime elements.
* `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul`: **the chain rule
  `dy = (dy/dx) · dx`** over any exact constant field.
* `TauCeti.Place.ord_derivativeOfSeparating_eq_sub`: `ord_P (dy/dx) = v_P(dy) - v_P(dx)` at every
  place.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq`: the Kähler–Weil comparison is
  independent of the separating element.
* `TauCeti.Place.traceResidue_coord_smul_eq_repartitionDualComponent`: **local components are
  trace residues** at a place of any degree with separable residue field.
* `TauCeti.repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating`:
  **local components are residues**, `ω_P (u) = res_P (u ω)`, at rational places.
* `TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`: the same over a
  perfect field, with the uniformizer-free residue.
* `TauCeti.Place.kaehlerResidue_eq_traceResidue_coord` and
  `TauCeti.Place.kaehlerResidueOfPerfectField_eq_traceResidue_coord`: at a rational place the
  residue of a Kähler differential is its trace residue.
* `TauCeti.finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero`: **the residue theorem**
  over a perfect field, `∑_P Tr_{F_P/k} res_{P,t_P} (ω / dt_P) = 0` for prime elements `t_P`, a
  sum with finitely many nonzero terms
  (`TauCeti.finite_support_traceResidue_kaehlerBasisOfSeparating_coord`).
* `TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero`: **the residue theorem**
  `∑_P res_P (ω) = 0` over an algebraically closed field, a sum with finitely many nonzero terms
  (`TauCeti.finite_support_kaehlerResidueOfPerfectField`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2, Corollary 4.3.3 and Remark 4.3.7.
-/

section
open scoped _root_.IntermediateField

open KaehlerDifferential

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:121` (proof source at `5a01f5fe3621`).
 **The chain rule for Weil differentials, at a common rational place** (Stichtenoth,
Theorem 4.3.2(a)): over an exact constant field, if `x - a` and `y - b` are prime elements at the
same rational place, then the Weil differentials of the separating elements `x` and `y` satisfy
`dy = (dy/dx) · dx`. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] {P : Place k F} (hP : P.degree = 1)
    {a b : k} (hxa : P.ord (x - algebraMap k F a) = 1) (hyb : P.ord (y - algebraMap k F b) = 1) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  -- The translate `x - a` is separating, with the same derivative as `x`.
  have hxa' : Transcendental k (x - algebraMap k F a) := fun h ↦ hx <| by
    simpa using (h.isIntegral.add (isIntegral_algebraMap (x := a))).isAlgebraic
  have : Algebra.IsSeparable k⟮x - algebraMap k F a⟯ F := by
    rw [sub_eq_add_neg, ← map_neg, IntermediateField.adjoin_simple_add_algebraMap]
    infer_instance
  -- One local component determines a Weil differential; compare them at `P`.
  refine Subtype.ext ((repartitionDualComponent_inj hF hex (Submodule.coe_mem _)
    (Submodule.coe_mem _) P).mp (LinearMap.ext fun u ↦ ?_))
  rw [coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating hF hy hP hyb,
    repartitionDualComponent_weilDifferentialOfSeparating hF hx hP hxa,
    P.residue_eq_residue_mul_derivativeOfSeparating hP hxa hxa' hyb,
    derivativeOfSeparating_sub_algebraMap hx hxa', map_sub, Derivation.map_algebraMap, sub_zero,
    mul_comm]

section ConstantExtension

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:154` (proof source at `5a01f5fe3621`).
 The descent step of the chain rule: if a finite separable constant field extension `F' = F · k'`
has a rational place `P'` lying over a place at which `q(x)` and `r(y)` are prime elements, with
`q` and `r` separable, then `dy = (dy/dx) · dx` in `F`. -/
private theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_constantCompositum
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [FiniteDimensional F F']
    (h : constantCompositum F k' F' = ⊤) (hF : IsFunctionField k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] {P' : Place k' F'}
    (hdeg : P'.degree = 1) (hx0 : 0 ≤ (P'.restrict k F).ord x) (hy0 : 0 ≤ (P'.restrict k F).ord y)
    {q r : Polynomial k} (hq : q.Separable) (hr : r.Separable)
    (hqx : (P'.restrict k F).ord (Polynomial.aeval x q) = 1)
    (hry : (P'.restrict k F).ord (Polynomial.aeval y r) = 1) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  -- The rational place `P'` makes `k'` the exact constant field of `F'`.
  have hex' : IsIntegrallyClosedIn k' F' := P'.isIntegrallyClosedIn_of_degree_eq_one hdeg
  have hx' : Transcendental k' (algebraMap F F' x) :=
    ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars k'
  have hy' : Transcendental k' (algebraMap F F' y) :=
    ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hy).extendScalars k'
  have := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := x) h
  have := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := y) h
  have := isSeparable_of_constantCompositum_eq_top (k := k) h
  let := weilDifferentialSpaceModule hF'
  have he := Place.ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h P'
  obtain ⟨a, ha⟩ := Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one hdeg he hx0 hq hqx
  obtain ⟨b, hb⟩ := Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one hdeg he hy0 hr hry
  have hup := weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one hF' hex' hx'
    hy' hdeg ha hb
  refine weilDifferentialCotrace_injective (k' := k') (F' := F') hF hF' ?_
  rw [weilDifferentialCotrace_smul,
    weilDifferentialCotrace_weilDifferentialOfSeparating h hF hy,
    weilDifferentialCotrace_weilDifferentialOfSeparating h hF hx,
    ← derivativeOfSeparating_algebraMap hx hx', hup]

end ConstantExtension

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:195` (proof source at `5a01f5fe3621`).
 **The chain rule for Weil differentials** (Stichtenoth, Theorem 4.3.2(a)): over any exact
constant field, the Weil differentials of any two separating elements `x` and `y` satisfy
`dy = (dy/dx) · dx`. Stichtenoth assumes `k` perfect; here `k` is arbitrary, and `F` need not have
any rational place. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  -- Choose a place `P` with residue field separable over `k`, at which `x` and `y` are units and
  -- some `q(x)` and `r(y)` are prime elements.
  obtain ⟨P, hPsep, hP⟩ := ((Place.infinite_setOf_isSeparable_residueField hF hx).sdiff
    (((Place.finite_setOf_forall_irreducible_ord_aeval_ne_one hF hx).union
      (Place.finite_setOf_forall_irreducible_ord_aeval_ne_one hF hy)).union
        ((Place.finite_setOf_ord_ne_zero hF x).union
          (Place.finite_setOf_ord_ne_zero hF y)))).nonempty
  simp only [Set.mem_ofPred_eq, Set.mem_union, not_or, not_and, not_forall, not_not] at hPsep hP
  obtain ⟨⟨hxq, hyq⟩, hx0, hy0⟩ := hP
  obtain ⟨q, hq, hqx⟩ := hxq hx0.ge
  obtain ⟨r, hr, hry⟩ := hyq hy0.ge
  -- The values of `x` and `y` at `P` are separable over `k`, so `q` and `r` are separable.
  have hqs := P.separable_of_ord_aeval_pos hx0.ge hq (by rw [hqx]; exact one_pos)
  have hrs := P.separable_of_ord_aeval_pos hy0.ge hr (by rw [hry]; exact one_pos)
  -- Enlarge the constants until the places over `P` are rational, and pick one of them.
  have := P.finiteDimensional_residueField hF
  obtain ⟨F', k', _, _, h, hdeg⟩ :=
    Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one hF hex P
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  obtain ⟨P', rfl⟩ := Place.restrict_surjective (hF.of_constantCompositum_eq_top h) P
  exact weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_constantCompositum h hF hx hy
    (hdeg P' rfl) hx0.ge hy0.ge hqs hrs hqx hry

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:228` (proof source at `5a01f5fe3621`).
 **The order of a derivative is a difference of orders of differentials**: over an exact
constant field, for separating elements `x` and `y` and any place `P`,
`ord_P (dy/dx) = v_P(dy) - v_P(dx)`. This is the chain rule `dy = (dy/dx) · dx` read at `P`. -/
theorem Place.ord_derivativeOfSeparating_eq_sub (P : Place k F)
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    P.ord (derivativeOfSeparating hx y) =
      weilDifferentialOrder hF hex (weilDifferentialOfSeparating hF hy).2
          (by simpa using weilDifferentialOfSeparating_ne_zero hF hy) P -
        weilDifferentialOrder hF hex (weilDifferentialOfSeparating hF hx).2
          (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) P := by
  let := weilDifferentialSpaceModule hF
  have hchain := congrArg Subtype.val
    (weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul hF hex hx hy)
  rw [coe_weilDifferentialSpaceModule_smul] at hchain
  rw [weilDifferentialOrder_eq_ord_add_of_eq_repartitionDualMul hF hex _ _
    (weilDifferentialOfSeparating hF hx).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF hx)
    (derivativeOfSeparating_ne_zero hx hy) hchain P, add_sub_cancel_right]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:249` (proof source at `5a01f5fe3621`).
 **The Kähler–Weil comparison does not depend on the separating element** (Stichtenoth,
Theorem 4.3.2): over any exact constant field, the comparisons built from any two separating
elements are equal. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx =
      kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hy := by
  let := weilDifferentialSpaceModule hF
  -- Both are `F`-linear, so compare them on the basis `dx`.
  refine LinearEquiv.toLinearMap_injective ((kaehlerBasisOfSeparating hx).ext fun _ ↦ ?_)
  rw [kaehlerBasisOfSeparating_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D,
    weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul hF hex hy hx]

/-! ### Local components are residues -/

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:271` (proof source at `5a01f5fe3621`).
 **Local components are trace residues** (Stichtenoth, Theorem 4.3.2(d) and Remark 4.3.7(d)):
over an exact constant field, let `P` be a place of any degree whose residue field is separable over
`k`, and `t` a separating prime element of `P`. For a Kähler differential `ω`, the trace residue
`Tr_{F_P/k} res_{P,t} (u ω / dt)` is the local component at `P`, evaluated at `u`, of the Weil
differential attached to `ω` by the Kähler–Weil comparison, built from any separating element `x`.
No further condition on the constant field is needed. -/
theorem Place.traceResidue_coord_smul_eq_repartitionDualComponent (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) (u : F) :
    P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () (u • ω)) =
      repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u := by
  -- By independence, read the comparison built from `t`, whose coordinates are those in `dt`.
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF hex hx htr,
    repartitionDualComponent_eq_traceResidue_coord hF hex ht,
    coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating, map_smul, smul_eq_mul, mul_comm]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:286` (proof source at `5a01f5fe3621`).
 At a rational place, the residue `res_P (ω)` of a Kähler differential computed with a
separating prime element `t` is the trace residue `Tr_{F_P/k} res_{P,t} (ω / dt)`, the trace from
`F_P = k` being the identity. -/
theorem Place.kaehlerResidue_eq_traceResidue_coord {P : Place k F} (hP : P.degree = 1)
    [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (htr : Transcendental k t)
    [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) :
    P.kaehlerResidue hP ht htr ω =
      P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () ω) := by
  rw [Place.kaehlerResidue_apply, P.traceResidue_eq_residue ht hP]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:299` (proof source at `5a01f5fe3621`).
 **Local components are residues** (Stichtenoth, Theorem 4.3.2(d)): over an exact constant
field, let `ω` be a Kähler differential and `P` a rational place with a separating prime element
`t`. The local component at `P` of the Weil differential attached to `ω` by the Kähler–Weil
comparison is `u ↦ res_P (u ω)`. Over a perfect constant field every prime element is separating,
and the residue does not depend on it
(`TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`). -/
theorem repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    {t : F} (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : Ω[F⁄k]) (u : F) :
    repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.kaehlerResidue hP ht htr (u • ω) := by
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [← P.traceResidue_coord_smul_eq_repartitionDualComponent hF hex hx ht htr,
    P.kaehlerResidue_eq_traceResidue_coord hP ht htr]

section PerfectField

variable [PerfectField k]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:317` (proof source at `5a01f5fe3621`).
 Over a perfect field, the residue `res_P (ω)` of a Kähler differential at a rational place `P`
is the trace residue `Tr_{F_P/k} res_{P,t} (ω / dt)` for every prime element `t` of `P`. -/
theorem Place.kaehlerResidueOfPerfectField_eq_traceResidue_coord (hF : IsFunctionField k F)
    {P : Place k F} (hP : P.degree = 1) [Algebra.IsSeparable k P.ResidueField] {t : F}
    (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) :
    P.kaehlerResidueOfPerfectField hP hF ω =
      P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () ω) := by
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF htr,
    P.kaehlerResidue_eq_traceResidue_coord hP ht htr]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:329` (proof source at `5a01f5fe3621`).
 **Local components are residues, over a perfect field** (Stichtenoth, Theorem 4.3.2(d)): over
a perfect exact constant field, the residue `res_P (u ω)` of a Kähler differential at a rational
place `P` is the local component at `P` of the Weil differential attached to `ω`, evaluated at `u`.
Every prime element of `P` is separating here, so no uniformizer is needed. -/
theorem Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    (ω : Ω[F⁄k]) (u : F) :
    P.kaehlerResidueOfPerfectField hP hF (u • ω) =
      repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [P.kaehlerResidueOfPerfectField_eq_traceResidue_coord hF hP ht htr,
    P.traceResidue_coord_smul_eq_repartitionDualComponent hF hex hx ht htr]

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  [∀ P : Place k F, Algebra.IsSeparable k P.ResidueField]
  (t : Place k F → F) (ht : ∀ P : Place k F, P.ord (t P) = 1)
  [∀ P : Place k F, Algebra.IsSeparable k⟮t P⟯ F]

include hF hex in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:357` (proof source at `5a01f5fe3621`).
 Over a perfect field, the trace residues `Tr_{F_P/k} res_{P,t_P} (ω / dt_P)` of a Kähler
differential, computed with a prime element `t_P` at each place `P`, vanish at all but finitely
many places. The separability of each residue field over `k`
(`TauCeti.Place.isSeparable_residueField_of_perfectField`) and of `F` over each `k(t_P)`
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`) holds automatically over a
perfect field; it is assumed only so that the trace residues and the coordinates in `dt_P` can be
stated. This is `TauCeti.finite_support_traceResidue_coord` for the Weil differential attached to
`ω`, on the constant repartition `1`. -/
theorem finite_support_traceResidue_kaehlerBasisOfSeparating_coord (ω : Ω[F⁄k]) :
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    (Function.support fun P : Place k F ↦
      P.traceResidue (ht P) ((kaehlerBasisOfSeparating (htr P)).coord () ω)).Finite := by
  intro htr
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  -- The coordinates of `ω` in `dt_P` are those of the Weil differential attached to it.
  convert finite_support_traceResidue_coord hF hex t ht
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω)
    ⟨_, const_mem_repartitionSpace hF 1⟩ using 3 with P
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF hex hx (htr P),
    coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating]
  simp

include hF hex in
/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:382` (proof source at `5a01f5fe3621`).
 **The residue theorem over a perfect field** (Stichtenoth, Corollary 4.3.3 and
Remark 4.3.7(d)): over a perfect exact constant field, choose a prime element `t_P` at each place
`P`. Then the trace residues of a Kähler differential `ω` sum to zero,
`∑_P Tr_{F_P/k} res_{P,t_P} (ω / dt_P) = 0`, a sum with finitely many nonzero terms
(`TauCeti.finite_support_traceResidue_kaehlerBasisOfSeparating_coord`). This is the residue
theorem for Weil differentials `TauCeti.finsum_traceResidue_coord_eq_zero` at `u = 1`, applied to
the Weil differential attached to `ω`. Unlike `TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero`,
places of every degree contribute, so this applies over finite fields. -/
theorem finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero (ω : Ω[F⁄k]) :
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    ∑ᶠ P : Place k F, P.traceResidue (ht P) ((kaehlerBasisOfSeparating (htr P)).coord () ω) =
      0 := by
  intro htr
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  -- The coordinates of `ω` in `dt_P` are those of the Weil differential attached to it.
  refine Eq.trans (finsum_congr fun P ↦ ?_) (finsum_traceResidue_coord_eq_zero hF hex t ht
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω) 1)
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF hex hx (htr P),
    coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating, mul_one]

end PerfectField

section IsAlgClosed

variable [IsAlgClosed k]

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:405` (proof source at `5a01f5fe3621`).
 Over an algebraically closed field, the residues of a Kähler differential have finite support
and sum to zero: every place is rational, and its residue is the trace residue in any prime
element. -/
private theorem finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero
    (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    (Function.support fun P : Place k F ↦
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF
        ω).Finite ∧
    ∑ᶠ P : Place k F,
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF ω =
        0 := by
  choose t ht _ using fun P : Place k F ↦ P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  have := fun P : Place k F ↦ (P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF (ht P)).2
  have := fun P : Place k F ↦ P.isSeparable_residueField_of_perfectField hF
  have hres := funext fun P : Place k F ↦ P.kaehlerResidueOfPerfectField_eq_traceResidue_coord hF
    (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) (ht P)
    (P.transcendental_of_ord_ne_zero (by simp [ht P])) ω
  rw [hres]
  exact ⟨finite_support_traceResidue_kaehlerBasisOfSeparating_coord hF
    isIntegrallyClosedIn_of_isAlgClosed t ht ω,
    finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero hF
      isIntegrallyClosedIn_of_isAlgClosed t ht ω⟩

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:427` (proof source at `5a01f5fe3621`).
 Over an algebraically closed field, a Kähler differential has nonzero residue at only finitely
many places. -/
theorem finite_support_kaehlerResidueOfPerfectField (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    (Function.support fun P : Place k F ↦
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF
        ω).Finite :=
  (finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero hF ω).1

/-- Kind: THEOREM. Locator: `TauCeti/FieldTheory/FunctionField/Differential/Independence.lean:444` (proof source at `5a01f5fe3621`).
 **The residue theorem** (Stichtenoth, Corollary 4.3.3): over an algebraically closed field,
the residues of a Kähler differential `ω` at the places of `F` sum to zero,
`∑_P res_P (ω) = 0`. Every place is rational here, and only finitely many residues are nonzero
(`TauCeti.finite_support_kaehlerResidueOfPerfectField`).

Over a field that is not algebraically closed the rational places do not suffice: over `ℚ`, the
differential `2x / (x² - 2) dx` of `ℚ(x)` has residue zero at every rational place `x = a` and
residue `-2` at infinity; the missing residue sits at the place of `x² - 2`, which is not rational
(see `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C`). Over a perfect field the trace residues
at the places of every degree sum to zero
(`TauCeti.finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero`). -/
theorem finsum_kaehlerResidueOfPerfectField_eq_zero (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    ∑ᶠ P : Place k F,
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF ω =
        0 :=
  (finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero hF ω).2

end IsAlgClosed

end TauCeti
end

end

/-! ## Rational differential comparison and scalar consequences -/

namespace ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison

open TauCeti WeierstrassCurve.Affine
open ZInQ.Contrib.CloudB3RC53.ModularWeil
open scoped _root_.IntermediateField

/-- Kind: DEFINITION. The intrinsic function-field-linear comparison type.
Locator: `PullbackScalar/Reduction.lean`, `KaehlerWeilComparison`. -/
abbrev ComparisonType (K : Type) [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) : Type :=
  letI := weilDifferentialSpaceModule hK
  KaehlerDifferential ℚ K ≃ₗ[K] ↥(weilDifferentialSpace ℚ K)

/-- Kind: DEFINITION. Comparison data for exact one-variable function fields over `ℚ`.
Locator: `PullbackScalar/Reduction.lean`, `ComparisonFamily`. -/
abbrev ComparisonFamily : Type 1 :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (_hex : IsIntegrallyClosedIn ℚ K), ComparisonType K hK

/-- Kind: DEFINITION. Finite-separable cotrace compatibility, with exactly the quantifiers
of the constant-coefficient reduction. Locator: `PullbackScalar/Reduction.lean`,
`CotraceCompatibility`. -/
def CotraceCompatibility (C : ComparisonFamily) : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (hK : IsFunctionField ℚ K) (hL : IsFunctionField ℚ L)
    (hexK : IsIntegrallyClosedIn ℚ K) (hexL : IsIntegrallyClosedIn ℚ L)
    (η : KaehlerDifferential ℚ K),
    C L hL hexL (KaehlerDifferential.map ℚ ℚ K L η) =
      weilDifferentialCotrace ℚ L hK hL (C K hK hexK η)

/-- Kind: DEFINITION. Local vanishing of `Res_P(g df)` for integral `f,g`.
Locator: `PullbackScalar/Reduction.lean`, `LocalExactRegularity`. -/
def LocalExactRegularity (C : ComparisonFamily) : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (hex : IsIntegrallyClosedIn ℚ K) (P : Place ℚ K) (f g : K),
    f ∈ P.integers → g ∈ P.integers →
      repartitionDualComponent
        (C K hK hex (KaehlerDifferential.D ℚ K f) :
          Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0

/-- Kind: DEFINITION. The comparison-existence statement, definitionally the statement
in the committed reduction. Locator: `PullbackScalar/Reduction.lean`,
`RationalResidueComparisonFact`. -/
def ResidueComparisonFact : Prop :=
  ∃ C : ComparisonFamily, CotraceCompatibility C ∧ LocalExactRegularity C

section Choice

variable {K : Type} [Field K] [Algebra ℚ K]

/-- Kind: DEFINITION. A separating parameter, chosen from separable generation over `ℚ`.
Locator: `IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`. -/
def separatingParameter (hK : IsFunctionField ℚ K) : K :=
  hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose

/-- Kind: THEOREM. The chosen parameter is transcendental.
Locator: the defining separating-element existence theorem. -/
theorem separatingParameter_transcendental (hK : IsFunctionField ℚ K) :
    Transcendental ℚ (separatingParameter hK) :=
  hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec.1

/-- Kind: THEOREM. The chosen parameter is separating.
Locator: the defining separating-element existence theorem. -/
theorem separatingParameter_isSeparable (hK : IsFunctionField ℚ K) :
    Algebra.IsSeparable ℚ⟮separatingParameter hK⟯ K :=
  hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec.2

/-- Kind: THEOREM. Every transcendental element is separating over `ℚ`.
Locators: `IsFunctionField.finiteDimensional_adjoin`; separability in characteristic zero. -/
theorem isSeparable_adjoin_transcendental (hK : IsFunctionField ℚ K) {x : K}
    (hx : Transcendental ℚ x) : Algebra.IsSeparable ℚ⟮x⟯ K := by
  have := hK.finiteDimensional_adjoin hx
  have : CharZero ℚ⟮x⟯ :=
    charZero_of_injective_algebraMap (algebraMap ℚ ℚ⟮x⟯).injective
  infer_instance

/-- Kind: DEFINITION. The comparison attached to a chosen separating parameter; parameter
independence makes this the canonical comparison. Locators: `Differential/Comparison.lean`,
`kaehlerDifferentialEquivWeilDifferentialOfSeparating`; `Differential/Independence.lean`. -/
def normalizedComparison (hK : IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) :
    ComparisonType K hK := by
  have := separatingParameter_isSeparable hK
  exact kaehlerDifferentialEquivWeilDifferentialOfSeparating hK hex
    (separatingParameter_transcendental hK)

/-- Kind: THEOREM. The canonical comparison sends `df` to the normalized separating
Weil differential of `f`, for every nonconstant function `f`.
Locators: `Differential/Independence.lean`, parameter independence;
`Differential/Comparison.lean`, the value on the parameter differential. -/
theorem normalizedComparison_D (hK : IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K)
    {f : K} (hf : Transcendental ℚ f) :
    haveI := isSeparable_adjoin_transcendental hK hf
    normalizedComparison hK hex (KaehlerDifferential.D ℚ K f) =
      weilDifferentialOfSeparating hK hf := by
  have := separatingParameter_isSeparable hK
  have := isSeparable_adjoin_transcendental hK hf
  let _ := weilDifferentialSpaceModule hK
  rw [normalizedComparison,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hK hex
      (separatingParameter_transcendental hK) hf,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

end Choice

/-- Kind: DEFINITION. The canonical comparison family for exact rational constant fields.
Locator: `normalizedComparison`. -/
def comparisonFamily : ComparisonFamily :=
  fun K _ _ hK hex => normalizedComparison hK hex

section Extension

variable {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
  [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Kind: THEOREM. Pullback of Kähler differentials is semilinear over the function-field
embedding. Locators: `KaehlerDifferential.mapSemilinear_smul`,
`KaehlerDifferential.mapSemilinear_toAlgHom_apply`. -/
theorem kaehlerMap_smul (c : K) (η : KaehlerDifferential ℚ K) :
    KaehlerDifferential.map ℚ ℚ K L (c • η) =
      algebraMap K L c • KaehlerDifferential.map ℚ ℚ K L η := by
  simp only [← KaehlerDifferential.mapSemilinear_toAlgHom_apply,
    KaehlerDifferential.mapSemilinear_smul, IsScalarTower.toAlgHom_apply]

/-- Kind: THEOREM. Cotrace carries the normalized differential of a separating parameter
into the normalized differential of its image. Locators: `Differential/Cotrace.lean`,
`weilDifferentialCotrace_weilDifferentialCotrace`; `Differential/Comparison.lean`. -/
theorem cotrace_separating (hK : IsFunctionField ℚ K) (hL : IsFunctionField ℚ L)
    {x : K} (hx : Transcendental ℚ x) (hxL : Transcendental ℚ (algebraMap K L x))
    [Algebra.IsSeparable ℚ⟮x⟯ K] [Algebra.IsSeparable ℚ⟮algebraMap K L x⟯ L] :
    weilDifferentialCotrace ℚ L hK hL (weilDifferentialOfSeparating hK hx) =
      weilDifferentialOfSeparating hL hxL := by
  let : Algebra ℚ (_root_.RatFunc ℚ) := _root_.RatFunc.instAlgebraOfPolynomial ℚ ℚ
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := ratFuncAlgebraOfTranscendental hxL
  have := isScalarTower_ratFuncAlgebraOfTranscendental hx
  have := isScalarTower_ratFuncAlgebraOfTranscendental hxL
  have := isFunctionField_iff_functionField.mp hK
  have := isFunctionField_iff_functionField.mp hL
  have := isSeparable_ratFuncAlgebraOfTranscendental hx
  have := isSeparable_ratFuncAlgebraOfTranscendental hxL
  have hhom :
      (IsScalarTower.toAlgHom ℚ K L).comp (IsScalarTower.toAlgHom ℚ (_root_.RatFunc ℚ) K) =
        IsScalarTower.toAlgHom ℚ (_root_.RatFunc ℚ) L := by
    apply _root_.RatFunc.algHom_ext
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      algebraMap_ratFuncAlgebraOfTranscendental_X]
  have : IsScalarTower (_root_.RatFunc ℚ) K L :=
    IsScalarTower.of_algebraMap_eq fun r => (AlgHom.congr_fun hhom r).symm
  dsimp only [weilDifferentialOfSeparating]
  exact weilDifferentialCotrace_weilDifferentialCotrace
    (IsFunctionField.ratFunc ℚ) hK hL _

/-- Kind: THEOREM. The canonical Kähler–Weil comparison intertwines any finite separable
function-field pullback and Weil cotrace. Locators: `cotrace_separating`,
`normalizedComparison_D`, the separating differential basis. -/
theorem normalizedComparison_cotrace (hK : IsFunctionField ℚ K) (hL : IsFunctionField ℚ L)
    (hexK : IsIntegrallyClosedIn ℚ K) (hexL : IsIntegrallyClosedIn ℚ L)
    (η : KaehlerDifferential ℚ K) :
    normalizedComparison hL hexL (KaehlerDifferential.map ℚ ℚ K L η) =
      weilDifferentialCotrace ℚ L hK hL (normalizedComparison hK hexK η) := by
  let x := separatingParameter hK
  have hx : Transcendental ℚ x := separatingParameter_transcendental hK
  have := separatingParameter_isSeparable hK
  have hxL : Transcendental ℚ (algebraMap K L x) :=
    (transcendental_algebraMap_iff (algebraMap K L).injective).mpr hx
  have := isSeparable_adjoin_transcendental hL hxL
  let _ := weilDifferentialSpaceModule hK
  let _ := weilDifferentialSpaceModule hL
  obtain ⟨c, rfl⟩ := (Submodule.span_singleton_eq_top_iff K
    (KaehlerDifferential.D ℚ K x)).mp (span_D_eq_top_of_separating hx) η
  rw [kaehlerMap_smul, KaehlerDifferential.map_D]
  simp only [map_smul]
  rw [normalizedComparison_D hK hexK hx, normalizedComparison_D hL hexL hxL,
    weilDifferentialCotrace_smul, cotrace_separating hK hL hx hxL]

end Extension

/-- Kind: THEOREM. The comparison family satisfies the complete finite-separable
compatibility clause. Locator: `normalizedComparison_cotrace`. -/
theorem comparisonFamily_cotraceCompatible : CotraceCompatibility comparisonFamily := by
  intro K L _ _ _ _ _ _ _ _ hK hL hexK hexL η
  exact normalizedComparison_cotrace hK hL hexK hexL η

/-- Kind: THEOREM. At any place, an integral exact differential kills every integral test
function under the comparison. This includes places of arbitrary residue degree.
Locators: `normalizedComparison_D`, `Differential/Comparison.lean`, the divisor of `df`;
`Differential/LocalOrder.lean`, `le_weilDifferentialOrder_iff`. -/
theorem normalizedComparison_local_D (K : Type) [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K)
    (P : Place ℚ K) (f g : K) (hf : f ∈ P.integers) (hg : g ∈ P.integers) :
    repartitionDualComponent
      (normalizedComparison hK hex (KaehlerDifferential.D ℚ K f) :
        Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0 := by
  by_cases hfa : IsAlgebraic ℚ f
  · let _ := hex
    obtain ⟨a, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hfa.isIntegral
    simp only [Derivation.map_algebraMap, map_zero, Submodule.coe_zero,
      repartitionDualComponent_apply, LinearMap.zero_apply]
  · have hft : Transcendental ℚ f := hfa
    have := isSeparable_adjoin_transcendental hK hft
    let _ := weilDifferentialSpaceModule hK
    rw [normalizedComparison_D hK hex hft]
    let _ := ratFuncAlgebraOfTranscendental hft
    have := isScalarTower_ratFuncAlgebraOfTranscendental hft
    have := isFunctionField_iff_functionField.mp hK
    have := isSeparable_ratFuncAlgebraOfTranscendental hft
    have horder : 0 ≤ weilDifferentialOrder hK hex (weilDifferentialOfSeparating hK hft).2
        (coe_weilDifferentialOfSeparating_ne_zero hK hft) P := by
      rw [← coeff_weilDifferentialDivisor,
        weilDifferentialDivisor_weilDifferentialOfSeparating,
        _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_add, _root_.TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul,
        Divisor.coeff_poles, Divisor.coeff_different, Units.val_mk0]
      have hfP : 0 ≤ P.ord f := P.mem_integers_iff_ord_nonneg.mp hf
      rw [max_eq_right (neg_nonpos.mpr hfP)]
      simp only [mul_zero, zero_add]
      positivity
    exact (le_weilDifferentialOrder_iff hK hex (weilDifferentialOfSeparating hK hft).2
      (coe_weilDifferentialOfSeparating_ne_zero hK hft) P 0).mp horder g
      (by simpa only [WithZero.exp_zero] using P.mem_integers_iff.mp hg)

/-- Kind: THEOREM. The comparison family satisfies the generic local vanishing clause.
Locator: `normalizedComparison_local_D`. -/
theorem comparisonFamily_localExactRegularity : LocalExactRegularity comparisonFamily := by
  intro K _ _ hK hex P f g hf hg
  exact normalizedComparison_local_D K hK hex P f g hf hg

/-- Kind: THEOREM. The generic rational residue comparison exists, with finite-separable
naturality and the integral exact-differential vanishing law.
Locators: `comparisonFamily_cotraceCompatible`, `comparisonFamily_localExactRegularity`;
`PullbackScalar/Reduction.lean`, `RationalResidueComparisonFact`. -/
theorem rationalResidueComparisonFact : ResidueComparisonFact :=
  ⟨comparisonFamily, comparisonFamily_cotraceCompatible, comparisonFamily_localExactRegularity⟩

/-- Kind: THEOREM. A regular, nonzero Weil differential on an exact genus-one function
field has divisor zero. Locator: `PullbackScalar/Reduction.lean`,
`regular_weilDivisor_eq_zero`; `Differential/CanonicalDivisor.lean`. -/
theorem regular_divisor_zero {K : Type} [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) (hg : genus ℚ K = 1)
    {ω : Module.Dual ℚ ↥(repartitionSpace ℚ K)}
    (hm : ω ∈ weilDifferentialSpace ℚ K) (hne : ω ≠ 0)
    (hr : ω ∈ weilDifferentialFiltration (0 : Divisor ℚ K)) :
    weilDifferentialDivisor hK hex hm hne = 0 := by
  have hpos : (0 : Divisor ℚ K) ≤ weilDifferentialDivisor hK hex hm hne :=
    (mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor hK hex hm hne 0).mp hr
  have hd : Divisor.degree (weilDifferentialDivisor hK hex hm hne) = 0 := by
    rw [degree_weilDifferentialDivisor, hg]
    norm_num
  exact (Divisor.eq_of_le_of_degree_eq hK hpos (by rw [Divisor.degree_zero, hd])).symm

/-- Kind: THEOREM. A function taking a regular nonzero Weil differential into the regular
space is constant in genus one. Locator: `PullbackScalar/Reduction.lean`,
`constant_of_regular_weil_multiple`; `Divisor/Principal.lean`, `principal_eq_zero_iff`. -/
theorem constant_regular_multiple {K : Type} [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) (hg : genus ℚ K = 1)
    {ω : Module.Dual ℚ ↥(repartitionSpace ℚ K)}
    (hr : ω ∈ weilDifferentialFiltration (0 : Divisor ℚ K)) (hne : ω ≠ 0)
    (c : K) (hc : repartitionDualMul hK c ω ∈
      weilDifferentialFiltration (0 : Divisor ℚ K)) :
    c ∈ Set.range (algebraMap ℚ K) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨0, map_zero _⟩
  have hm : ω ∈ weilDifferentialSpace ℚ K :=
    weilDifferentialFiltration_le_weilDifferentialSpace 0 hr
  have hcm := repartitionDualMul_mem_weilDifferentialSpace hK c hm
  have hcne := repartitionDualMul_ne_zero hK hc0 hne
  have hd := regular_divisor_zero hK hex hg hm hne hr
  have hcd := regular_divisor_zero hK hex hg hcm hcne hc
  have ht := weilDifferentialDivisor_repartitionDualMul hK hex hm hne (Units.mk0 c hc0)
  simp only [Units.val_mk0] at ht
  have hp : Divisor.principal hK (Units.mk0 c hc0) = 0 := by
    rw [hcd, hd, add_zero] at ht
    exact ht.symm
  exact (Divisor.principal_eq_zero_iff hK hex (Units.mk0 c hc0)).mp hp

/-- Kind: THEOREM. The canonical comparison sends the concrete invariant differential of
an elliptic curve to a regular Weil differential. Locators: parameter independence;
`Affine/FunctionField/Divisor/InvariantDifferential.lean`, divisor zero. -/
theorem normalizedComparison_invariant_regular (W : WeierstrassCurve.Affine ℚ) [W.IsElliptic] :
    (normalizedComparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
      (invariantDifferential W) : Module.Dual ℚ ↥(repartitionSpace ℚ W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ W.FunctionField) := by
  have := separatingParameter_isSeparable W.isFunctionField
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [normalizedComparison,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq W.isFunctionField
      (isIntegrallyClosedIn_functionField W) (separatingParameter_transcendental W.isFunctionField)
      (transcendental_genericX W)]
  rw [mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor W.isFunctionField
    (isIntegrallyClosedIn_functionField W)
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating W.isFunctionField
      (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
      (invariantDifferential W)).prop
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero W),
    weilDifferentialDivisor_invariantDifferential W]

/-- Kind: THEOREM. The exact constant-coefficient glue is proved without a comparison
hypothesis or a printed assertion. Locators: the canonical comparison naturality,
`normalizedComparison_invariant_regular`, `constant_regular_multiple`;
`Isogeny/Unramified.lean`, `different_eq_zero`. -/
theorem pullbackCoefficientConstantGlue_proof : PullbackCoefficientConstantGlue := by
  intro E₁ E₂ h₁ h₂ β c hc
  let W₁ := E₁.toAffine
  let W₂ := E₂.toAffine
  let hF₁ := W₁.isFunctionField
  let hF₂ := W₂.isFunctionField
  let hex₁ := isIntegrallyClosedIn_functionField W₁
  let hex₂ := isIntegrallyClosedIn_functionField W₂
  let e₁ := normalizedComparison hF₁ hex₁
  let e₂ := normalizedComparison hF₂ hex₂
  let _ := weilDifferentialSpaceModule hF₁
  let _ := weilDifferentialSpaceModule hF₂
  have : CharZero β.fieldPullback.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap ℚ β.fieldPullback.fieldRange).injective
  let : Algebra W₂.FunctionField W₁.FunctionField := β.fieldPullback.toRingHom.toAlgebra
  have hmap : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = β.fieldPullback z :=
    fun z => RingHom.congr_fun (RingHom.algebraMap_toAlgebra β.fieldPullback.toRingHom) z
  have := β.isScalarTower_of_algebraMap_eq_fieldPullback hmap
  have := β.finiteDimensional_functionField hmap
  have := β.isSeparable_functionField hmap
  have hhom : IsScalarTower.toAlgHom ℚ W₂.FunctionField W₁.FunctionField = β.fieldPullback :=
    AlgHom.ext hmap
  have hη : KaehlerDifferential.map ℚ ℚ W₂.FunctionField W₁.FunctionField
      (invariantDifferential W₂) = β.pullbackDifferential (invariantDifferential W₂) := by
    rw [TauCeti.Isogeny.pullbackDifferential_apply,
      ← KaehlerDifferential.mapSemilinear_toAlgHom_apply, hhom]
  have hnat : e₁ (β.pullbackDifferential (invariantDifferential W₂)) =
      weilDifferentialCotrace ℚ W₁.FunctionField hF₂ hF₁ (e₂ (invariantDifferential W₂)) := by
    simpa only [hη] using normalizedComparison_cotrace hF₂ hF₁ hex₂ hex₁
      (invariantDifferential W₂)
  have hne : (e₁ (invariantDifferential W₁) :
      Module.Dual ℚ ↥(repartitionSpace ℚ W₁.FunctionField)) ≠ 0 := by
    intro hz
    have hz' : e₁ (invariantDifferential W₁) = 0 := Subtype.ext hz
    exact invariantDifferential_ne_zero W₁
      (e₁.injective (hz'.trans (map_zero e₁).symm))
  have himage : (e₁ (β.pullbackDifferential (invariantDifferential W₂)) :
      Module.Dual ℚ ↥(repartitionSpace ℚ W₁.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ W₁.FunctionField) := by
    rw [hnat]
    have h := weilDifferentialCotrace_mem_weilDifferentialFiltration hF₂ hF₁
      (e₂ (invariantDifferential W₂)) (normalizedComparison_invariant_regular W₂)
    have hdiff : Divisor.different ℚ W₁.FunctionField hF₂ = 0 :=
      β.different_eq_zero hmap
    simpa only [map_zero, hdiff, zero_add] using h
  have hscalar : repartitionDualMul hF₁ c (e₁ (invariantDifferential W₁) :
      Module.Dual ℚ ↥(repartitionSpace ℚ W₁.FunctionField)) =
      (e₁ (β.pullbackDifferential (invariantDifferential W₂)) :
        Module.Dual ℚ ↥(repartitionSpace ℚ W₁.FunctionField)) := by
    rw [← coe_weilDifferentialSpaceModule_smul, ← map_smul, hc]
  exact constant_regular_multiple hF₁ hex₁ (genus_functionField W₁)
    (normalizedComparison_invariant_regular W₁) hne c (hscalar.symm ▸ himage)

/-- Kind: THEOREM. Every rational isogeny pulls back the invariant differential by a
nonzero rational scalar, in the exact algebraic glue formulation. Locators:
`pullbackCoefficientConstantGlue_proof`; `ModularWeil/IsogenyScalar.lean`,
`isogenyScalarRationalGlue_of_constant`. -/
theorem isogenyScalarRationalGlue_proof : IsogenyScalarRationalGlue :=
  isogenyScalarRationalGlue_of_constant pullbackCoefficientConstantGlue_proof

end ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison
