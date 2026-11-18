import Mathlib

/-!
# RC53 PairedFunctional: no group-order denominator in the duality

Proof of Proposition `ex:arith-paired-functional`, tex L3818–3828:

> For completeness, there is also no hidden group-order denominator in duality. The coefficient
> pairing is the `A_i[G]`-valued Weil pairing. If one checks its perfection over `A_i`, the
> auxiliary pairing on the group algebra is `(a, b) ↦ [1](ab)`,
> `([1](gh))_{g,h∈G} = (𝟙_{h=g⁻¹})_{g,h∈G}`. Its matrix is a permutation matrix, with integral
> inverse. It is not the normalized trace `|G|⁻¹ Tr`.

Here `[1](x)` is the coefficient of the identity in `x ∈ R[G]` (`(x).coeff 1`), for any
commutative ring `R` and finite group `G`.

Nodes (all PROVED):
* `GroupAlgebraPairingPerfect`: the Gram matrix of `(a, b) ↦ [1](ab)` in the basis `G` is
  `𝟙_{h = g⁻¹}`, it is its own inverse (an integral inverse), the pairing is symmetric, and every
  `R`-valued functional on the basis is represented by a unique `a` (perfection over `R`, with no
  hypothesis on `|G|` in `R`).
* `TraceIsOrderTimesPairing`: the trace form is `|G|` times this pairing:
  `Tr_{R[G]/R}(x ↦ c x) = |G| · [1](c)`; so the normalized trace `|G|⁻¹ Tr` is this pairing exactly
  when `|G|` is invertible, which is the denominator the text avoids.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open MonoidAlgebra

variable {R G : Type*} [CommRing R] [Group G]

/-- The auxiliary pairing `(a, b) ↦ [1](ab)` on `R[G]` (tex L3822–3824). -/
def unitPairing (a b : MonoidAlgebra R G) : R := (a * b).coeff 1

theorem unitPairing_single_right (a : MonoidAlgebra R G) (h : G) :
    unitPairing a (single h 1) = a.coeff h⁻¹ := by
  simp [unitPairing]

theorem unitPairing_single_single [DecidableEq G] (g h : G) :
    unitPairing (single g (1 : R)) (single h 1) = if h = g⁻¹ then 1 else 0 := by
  rw [unitPairing_single_right, coeff_single, Finsupp.single_apply]
  by_cases e : h = g⁻¹
  · subst e; simp
  · have e' : g ≠ h⁻¹ := fun e' => e (by rw [e', inv_inv])
    simp [e, e']

/-- The Gram matrix `([1](gh))_{g,h}` of the pairing in the basis `G` (tex L3824). -/
def unitPairingGram (R G : Type*) [CommRing R] [Group G] : Matrix G G R :=
  fun g h => unitPairing (single g (1 : R)) (single h 1)

/-- **The group-algebra pairing is perfect with an integral inverse Gram matrix**
(tex L3818–3828). For every commutative ring `R` and finite group `G`:
(i) `([1](gh))_{g,h} = 𝟙_{h = g⁻¹}` (a permutation matrix); (ii) it is its own inverse, so its
inverse is integral; (iii) the pairing is symmetric; (iv) every `R`-valued function `f` on the
basis `G` is `h ↦ [1](a h)` for exactly one `a ∈ R[G]`. No inverse of `|G|` is used.
Classification: PROVED. -/
def GroupAlgebraPairingPerfect : Prop :=
  ∀ (R G : Type) [CommRing R] [Group G] [Fintype G] [DecidableEq G],
    (∀ g h : G, unitPairingGram R G g h = if h = g⁻¹ then 1 else 0) ∧
    unitPairingGram R G * unitPairingGram R G = 1 ∧
    (∀ a b : MonoidAlgebra R G, unitPairing a b = unitPairing b a) ∧
    (∀ f : G → R, ∃! a : MonoidAlgebra R G, ∀ h : G, unitPairing a (single h 1) = f h)

theorem groupAlgebraPairingPerfect_proof : GroupAlgebraPairingPerfect := by
  intro R G _ _ _ _
  have hgram : ∀ g h : G, unitPairingGram R G g h = if h = g⁻¹ then 1 else 0 :=
    fun g h => unitPairing_single_single g h
  refine ⟨hgram, ?_, ?_, ?_⟩
  · ext g k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hgram, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single g⁻¹]
    · simp only [inv_inv, ite_true]
      by_cases e : g = k
      · simp [e]
      · have e' : k ≠ g := fun e' => e e'.symm
        simp [e, e']
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a b
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [unitPairing]
    | add x y hx hy => simp only [unitPairing, add_mul, mul_add, coeff_add, Finsupp.add_apply] at *; rw [hx, hy]
    | single g r =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp [unitPairing]
      | add x y hx hy => simp only [unitPairing, add_mul, mul_add, coeff_add, Finsupp.add_apply] at *; rw [hx, hy]
      | single h s =>
        simp only [unitPairing, MonoidAlgebra.single_mul_single, coeff_single, Finsupp.single_apply]
        by_cases e : g * h = 1
        · have e' : h * g = 1 := by rw [mul_eq_one_iff_eq_inv.mp e, mul_inv_cancel]
          simp [e, e', mul_comm]
        · have e' : h * g ≠ 1 := fun e' => e (by rw [mul_eq_one_iff_eq_inv.mp e', mul_inv_cancel])
          simp [e, e']
  · intro f
    refine ⟨⟨Finsupp.equivFunOnFinite.symm (fun g => f g⁻¹)⟩, ?_, ?_⟩
    · intro h
      rw [unitPairing_single_right]
      simp
    · intro a ha
      apply MonoidAlgebra.coeff_injective
      ext g
      have := ha g⁻¹
      rw [unitPairing_single_right, inv_inv] at this
      simp [this]

/-- **The trace form is `|G|` times the pairing; the normalized trace needs `|G|⁻¹`**
(tex L3825–3826: "It is not the normalized trace `|G|⁻¹ Tr`"). For every `c ∈ R[G]`, the trace
over `R` of left multiplication by `c` on the free module `R[G]` is `|G| · [1](c)`; hence
`Tr(ab) = |G| · [1](ab)` and `|G|⁻¹ Tr` agrees with the pairing `[1](ab)` only after inverting
`|G|`. Classification: PROVED. -/
def TraceIsOrderTimesPairing : Prop :=
  ∀ (R G : Type) [CommRing R] [Group G] [Fintype G] [DecidableEq G] (c : MonoidAlgebra R G),
    LinearMap.trace R (MonoidAlgebra R G) (LinearMap.mulLeft R c) = (Fintype.card G : R) * c.coeff 1

theorem traceIsOrderTimesPairing_proof : TraceIsOrderTimesPairing := by
  intro R G _ _ _ _ c
  rw [LinearMap.trace_eq_matrix_trace R (MonoidAlgebra.basis G R), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    LinearMap.mulLeft_apply]
  have : ∀ g : G, (MonoidAlgebra.basis G R).repr (c * single g 1) g = c.coeff 1 := by
    intro g
    change (c * single g 1).coeff g = _
    simp
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
