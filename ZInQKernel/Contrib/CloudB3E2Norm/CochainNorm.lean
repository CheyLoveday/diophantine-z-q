import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# The actual norm identity at cochain level, for the support change at one unused prime

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4170):

> Let `i : C_P → C_R` be the primitive-to-relaxed map […] The actual norm identity is
> `z_R = e_q i(z_P)`, with its retained boundary.

and the point-level split norm relation (4.1) (tex 2924–2929; Cai–Chen–Liu, Theorem 2.15):
`Tr_{H_{dq}/H_d} y_{dq} = (a_q − σ_q − σ_q⁻¹) y_d` at a split prime `q`.

This file proves the group-cochain core of the norm identity at a finite coefficient stage, in
degree one, with the boundary explicit. The setting is abstract:

* `Γ` a group acting on an abelian group `A` (for the text: `Γ = G_K`, `A = E(ℚ̄)`);
* `HP` a normal subgroup of `Γ` (for the text: `G_{H_P}`, the absolute Galois group of the ring
  class field of support `P`; normal since `H_P/K` is Galois);
* `U` a subgroup of finite index of `HP` with a transversal `t` (for the text: `G_{H_R}`, support
  `R = P ∪ {q}`, and lifts of `Gal(H_R/H_P)`);
* points `y_P ∈ A` (fixed by `HP`) and `y_R ∈ A` (fixed by `U`), division points `Q_P`, `Q_R` with
  `m Q_P = y_P` and `m Q_R = y_R`, and a Frobenius lift `σ ∈ Γ`.

The Kummer cocycle of a division point `Q` on a subgroup `H` is `κ_H(Q)(h) = h Q − Q`, Tau Ceti's
`d0 H A Q` read as a cochain; when `m Q` is `H`-fixed it takes values in `A[m]`
(`kummer_mem_torsionBy`). This is the tree's `kummerCocycleOf` (`RC/CoefModules/Kummer.lean`) for
`H = G_F`, `A = B(F̄)`.

* `cor_kummer` (PROVED): Tau Ceti's degree-one corestriction cochain from `U` to `HP` sends the
  Kummer cocycle of `Q_R` to the Kummer cocycle of the transversal norm `∑ₜ t Q_R`, exactly.
* `conjCochain σ c` (definition): the conjugation action `(σ ⋆ c)(h) = σ c(σ⁻¹ h σ)` of `σ ∈ Γ` on
  `1`-cochains of the normal subgroup `HP`; `kummer_smul` (PROVED): `κ(σ Q) = σ ⋆ κ(Q)`.
* `normOp a σ c = a c − σ ⋆ c − σ⁻¹ ⋆ c` (definition): the point factor `e_q = a_q − σ − σ⁻¹`
  acting on cochains of `HP`.
* **`cor_kummer_eq_normOp_add_d0`** (PROVED): if `∑ₜ t y_R = a y_P − σ y_P − σ⁻¹ y_P` (the
  relation (4.1)), then
  `cor κ_U(Q_R) = e_q ⋆ κ_HP(Q_P) + d⁰ b`, with the retained boundary
  `b = ∑ₜ t Q_R − (a Q_P − σ Q_P − σ⁻¹ Q_P)` explicit and `m`-torsion (`m • b = 0`), so `d⁰ b` is a
  coboundary of the finite coefficient module `A[m]` (`d0_mem_torsionBy`).
* `cor_kummer_eq_normOp_add_d0_of_choice`: the same for any other division point of the norm.
* Non-vacuity (`nonVacuity`): a concrete instance of every hypothesis (trivial group acting on
  `ℤ`).

**What remains** for the consumer's hypothesis `hzR` (lane RC32's
`SupportTriangle.kmStep_of_supportTriangle`, `z_R = e_q • i z_P + d b` in the genuine complexes):
1. Shapiro / twisted transfer from `HP` to `G_K` (tex 3219–3250, `HeegnerCohomology/Transfer.lean`),
   which turns the conjugation action `σ ⋆` into multiplication by the scalar Frobenius value `z`
   on the twisted coefficients, and its compatibility with corestriction from `U`, both up to an
   explicit boundary;
2. the local components of `z_P`, `z_R` in the Selmer cones (the local Kummer cocycles lie in the
   Kummer condition, `RC/CoefModules/Kummer.lean`) and the identification of `i` with the identity
   on global cochains plus the inclusion of local conditions at the old places and at `q`;
3. the passage through the inner limit to the `Λ`-adic coefficients and the identification of the
   actual classes with the classes of the Heegner points `y_T` (the anchor of `CCLThm2_15Applied`).

Kinds: definitions and PROVED. The relation (4.1) is a hypothesis here (in the tree it is
`HeegnerPointData.NormRelations`, a PRINT of Cai–Chen–Liu Theorem 2.15 through `φ`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open TauCeti.ContCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {Γ : Type*} [Group Γ] {A : Type*} [AddCommGroup A] [DistribMulAction Γ A]

/-! ### The Kummer cocycle of a division point -/

/-- **The Kummer cocycle of a division point** `Q` on a subgroup `H`: `h ↦ h Q − Q` (Tau Ceti's
`d0 H A Q`). For `m Q = y` with `y` fixed by `H` it is the Kummer cocycle of `y`, with values in
`A[m]`. Kind: definition. -/
def kummer (H : Subgroup Γ) (Q : A) : H → A := d0 H A Q

theorem kummer_apply (H : Subgroup Γ) (Q : A) (h : H) : kummer H Q h = (h : Γ) • Q - Q := rfl

/-- **The Kummer cocycle takes values in `A[m]`** when `m Q` is fixed by `H`. -/
theorem kummer_mem_torsionBy (H : Subgroup Γ) (m : ℕ) (Q : A) (hQ : ∀ h : H, (h : Γ) • (m • Q) = m • Q)
    (h : H) : kummer H Q h ∈ AddSubgroup.torsionBy A (m : ℤ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff, kummer_apply, nsmul_sub, ← smul_comm, hQ h, sub_self]

/-- **A coboundary of an `m`-torsion element takes values in `A[m]`.** -/
theorem d0_mem_torsionBy (H : Subgroup Γ) (m : ℕ) (b : A) (hb : m • b = 0) (h : H) :
    d0 H A b h ∈ AddSubgroup.torsionBy A (m : ℤ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff, d0_apply, nsmul_sub, Subgroup.smul_def, ← smul_comm,
    hb, smul_zero, sub_zero]

/-! ### Corestriction of a Kummer cocycle -/

section Cor

variable (HP : Subgroup Γ) (U : Subgroup HP) [U.FiniteIndex] (t : HP ⧸ U → HP)
  (ht : ∀ u : HP ⧸ U, (QuotientGroup.mk (t u) : HP ⧸ U) = u)

/-- The transversal norm `∑ₜ t x` from `U` to `HP`. Kind: definition. -/
def trNorm (x : A) : A := ∑ u : HP ⧸ U, ((t u : HP) : Γ) • x

/-- **Corestriction of the Kummer cocycle** (PROVED): the degree-one corestriction cochain from
`U` to `HP` (Tau Ceti's `cochainsCor1` for the transversal `t`) sends the Kummer cocycle of `Q` on
`U` to the Kummer cocycle of the transversal norm `∑ₜ t Q` on `HP`, exactly. -/
theorem cor_kummer (Q : A) :
    cochainsCor1 HP A U t ht (d0 U A Q) = kummer HP (trNorm HP U t Q) := by
  rw [cochainsCor1_d0]
  rfl

/-- **The transversal norm of a division point is a division point of the norm.** -/
theorem nsmul_trNorm (m : ℕ) (x : A) : m • trNorm HP U t x = trNorm HP U t (m • x) := by
  simp only [trNorm, Finset.smul_sum, smul_comm m]

end Cor

/-! ### The conjugation action on cochains of a normal subgroup -/

section Conj

variable (HP : Subgroup Γ) [HP.Normal]

set_option linter.unusedSectionVars false

/-- The conjugate `σ⁻¹ h σ` of an element of the normal subgroup `HP`. -/
def conjElt (σ : Γ) (h : HP) : HP :=
  ⟨σ⁻¹ * (h : Γ) * σ, by simpa using (inferInstance : HP.Normal).conj_mem _ h.2 σ⁻¹⟩

@[simp] theorem coe_conjElt (σ : Γ) (h : HP) : (conjElt HP σ h : Γ) = σ⁻¹ * (h : Γ) * σ := rfl

/-- **The conjugation action of `σ ∈ Γ` on `1`-cochains of `HP`**:
`(σ ⋆ c)(h) = σ c(σ⁻¹ h σ)`. Kind: definition. -/
def conjCochain (σ : Γ) (c : HP → A) : HP → A := fun h => σ • c (conjElt HP σ h)

/-- **The Kummer cocycle is equivariant** (PROVED): `κ(σ Q) = σ ⋆ κ(Q)`. -/
theorem kummer_smul (σ : Γ) (Q : A) :
    kummer HP (σ • Q) = conjCochain HP σ (kummer HP Q) := by
  funext h
  simp only [conjCochain, kummer_apply, coe_conjElt, smul_sub, smul_smul, mul_assoc,
    mul_inv_cancel_left]

/-- **The point factor `e_q = a − σ − σ⁻¹` acting on `1`-cochains of `HP`**:
`a c − σ ⋆ c − σ⁻¹ ⋆ c`. Kind: definition. -/
def normOp (a : ℤ) (σ : Γ) (c : HP → A) : HP → A :=
  a • c - conjCochain HP σ c - conjCochain HP σ⁻¹ c

/-- **The Kummer cocycle intertwines the point factor** (PROVED):
`κ(a Q − σ Q − σ⁻¹ Q) = e_q ⋆ κ(Q)`. -/
theorem kummer_pointFactor (a : ℤ) (σ : Γ) (Q : A) :
    kummer HP (a • Q - σ • Q - σ⁻¹ • Q) = normOp HP a σ (kummer HP Q) := by
  rw [normOp, ← kummer_smul, ← kummer_smul]
  simp only [kummer, map_sub, map_zsmul]

end Conj

/-! ### The norm identity at cochain level -/

section Norm

set_option linter.unusedSectionVars false

variable (HP : Subgroup Γ) [HP.Normal] (U : Subgroup HP) [U.FiniteIndex] (t : HP ⧸ U → HP)
  (ht : ∀ u : HP ⧸ U, (QuotientGroup.mk (t u) : HP ⧸ U) = u)

/-- **The retained boundary** `b = ∑ₜ t Q_R − (a Q_P − σ Q_P − σ⁻¹ Q_P)`. Kind: definition. -/
def retainedBoundary (a : ℤ) (σ : Γ) (QR QP : A) : A :=
  trNorm HP U t QR - (a • QP - σ • QP - σ⁻¹ • QP)

/-- **The retained boundary is `m`-torsion** (PROVED), given the point relation (4.1)
`∑ₜ t y_R = a y_P − σ y_P − σ⁻¹ y_P` and `m Q_R = y_R`, `m Q_P = y_P`. -/
theorem nsmul_retainedBoundary (m : ℕ) (a : ℤ) (σ : Γ) {yR yP QR QP : A}
    (hQR : m • QR = yR) (hQP : m • QP = yP)
    (hnorm : trNorm HP U t yR = a • yP - σ • yP - σ⁻¹ • yP) :
    m • retainedBoundary HP U t a σ QR QP = 0 := by
  rw [retainedBoundary, nsmul_sub, nsmul_trNorm, hQR, hnorm, nsmul_sub, nsmul_sub, smul_comm m a,
    smul_comm m σ, smul_comm m σ⁻¹, hQP, sub_self]

/-- **The actual norm identity at cochain level, with its retained boundary** (PROVED; tex
4157–4170 at a finite coefficient stage, over `HP`). From the point relation (4.1),
`∑ₜ t y_R = a y_P − σ y_P − σ⁻¹ y_P`, the corestriction of the Kummer cocycle of `y_R` is the point
factor `e_q = a − σ − σ⁻¹` applied to the Kummer cocycle of `y_P`, plus the coboundary of the
explicit `m`-torsion element `b = retainedBoundary`:
`cor κ_U(Q_R) = e_q ⋆ κ_HP(Q_P) + d⁰ b`, `m • b = 0`. -/
theorem cor_kummer_eq_normOp_add_d0 (m : ℕ) (a : ℤ) (σ : Γ) {yR yP QR QP : A}
    (hQR : m • QR = yR) (hQP : m • QP = yP)
    (hnorm : trNorm HP U t yR = a • yP - σ • yP - σ⁻¹ • yP) :
    cochainsCor1 HP A U t ht (d0 U A QR) =
        normOp HP a σ (kummer HP QP) + d0 HP A (retainedBoundary HP U t a σ QR QP) ∧
      m • retainedBoundary HP U t a σ QR QP = 0 := by
  refine ⟨?_, nsmul_retainedBoundary HP U t m a σ hQR hQP hnorm⟩
  rw [cor_kummer, ← kummer_pointFactor, kummer, kummer, ← map_add, retainedBoundary,
    add_sub_cancel]

/-- **The norm identity for any division point of the norm** (PROVED): if `Q'` is any element with
`m Q' = ∑ₜ t y_R` (e.g. the division point chosen by the Kummer map of the base field), then
`κ_HP(Q') = e_q ⋆ κ_HP(Q_P) + d⁰ b'` with `b' = Q' − (a Q_P − σ Q_P − σ⁻¹ Q_P)`, `m • b' = 0`. -/
theorem kummer_eq_normOp_add_d0_of_choice (m : ℕ) (a : ℤ) (σ : Γ) {yR yP QP Q' : A}
    (hQP : m • QP = yP) (hQ' : m • Q' = trNorm HP U t yR)
    (hnorm : trNorm HP U t yR = a • yP - σ • yP - σ⁻¹ • yP) :
    kummer HP Q' = normOp HP a σ (kummer HP QP) + d0 HP A (Q' - (a • QP - σ • QP - σ⁻¹ • QP)) ∧
      m • (Q' - (a • QP - σ • QP - σ⁻¹ • QP)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← kummer_pointFactor, kummer, kummer, ← map_add, add_sub_cancel]
  · rw [nsmul_sub, hQ', hnorm, nsmul_sub, nsmul_sub, smul_comm m a, smul_comm m σ,
      smul_comm m σ⁻¹, hQP, sub_self]

end Norm

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `cor_kummer_eq_normOp_add_d0`**: `Γ = ℤˣ` acting on `ℤ` by
multiplication, `HP = U = ⊤` with the constant transversal, `σ = 1`, `m = 2`, `a = 3`,
`y_P = y_R = 2`, `Q_P = Q_R = 1` (so `∑ₜ t y_R = 2 = 3·2 − 2 − 2`). -/
theorem nonVacuity :
    ∃ (HP : Subgroup ℤˣ) (_ : HP.Normal) (U : Subgroup HP) (_ : U.FiniteIndex)
      (t : HP ⧸ U → HP) (_ : ∀ u : HP ⧸ U, (QuotientGroup.mk (t u) : HP ⧸ U) = u)
      (yR yP QR QP : ℤ), (2 : ℕ) • QR = yR ∧ (2 : ℕ) • QP = yP ∧
      trNorm HP U t yR = (3 : ℤ) • yP - (1 : ℤˣ) • yP - (1 : ℤˣ)⁻¹ • yP := by
  have hq : ∀ u : (⊤ : Subgroup ℤˣ) ⧸ (⊤ : Subgroup (⊤ : Subgroup ℤˣ)), u = 1 := fun u => by
    induction u using QuotientGroup.induction_on with
    | H x => exact QuotientGroup.eq.mpr (Subgroup.mem_top _)
  refine ⟨⊤, inferInstance, ⊤, inferInstance, fun _ => 1, fun u => (hq u).symm ▸ rfl, 2, 2, 1, 1,
    by norm_num, by norm_num, ?_⟩
  have hcard : Fintype.card ((⊤ : Subgroup ℤˣ) ⧸ (⊤ : Subgroup (⊤ : Subgroup ℤˣ))) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨1, hq⟩
  simp only [trNorm, OneMemClass.coe_one, one_smul, Finset.sum_const, Finset.card_univ, hcard,
    inv_one]
  norm_num

end ZInQ.Contrib.CloudB3E2.NormCochain
