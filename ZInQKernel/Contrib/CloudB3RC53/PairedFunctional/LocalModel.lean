import Mathlib

/-!
# RC53 PairedFunctional: the tame local model (4.4) and its two integral contractions

Manuscript `diophantine_zq.tex`, tex L3470–3480 (the local free model (4.4) at a tame split prime)
and the proof of Proposition `ex:arith-paired-functional`, tex L3727–3765 (the Frobenius
contraction, L3731–3735, and the inertia contraction, L3762–3765).

At a tame split prime `q` the local free model is the three-term complex
`M --d⁰--> M ⊕ M --d¹--> M` with
`d⁰(v) = (Av, Cv)`, `d¹(v, w) = −Cv + Dw`, `A = Φ − 1`, `C = g − 1`, `D = Φ − N_q(g)`,
`N_q(g) = (q+1)/2 + ((q−1)/2) g`, subject to `DC = CA` (tex L3472–3476).

Here `M` is any module over any commutative ring `S` (in the manuscript `S = 𝒪[G]`, or a
height-one localization of `Λ`, and `M` the free coefficient module), `Φ` and `g` are
`S`-linear endomorphisms of `M` (Frobenius and an inertia generator). Nothing about `S` is
assumed: the contractions are *integral*, i.e. defined over `S` itself, as soon as the
indicated operators are units of `End_S M`.

Nodes (all PROVED):
* `TameModelIsComplex` (tex L3472–3476): `d¹ ∘ d⁰ = 0 ↔ DC = CA`.
* `TameCommutator` (tex L3475–3476): `DC − CA = (Φg − gΦ) − (N_q(g) − 1)(g − 1)`; in particular
  `DC = CA` when `Φ` commutes with `g` and `g² = 1` (a quadratic inertia character).
* `TameAugmentation` (tex L3477–3479): at `g = 1`, `C = 0` and `D = Φ − q`.
* `FrobeniusContraction` (tex L3731–3735): if `A, D` are units and `DC = CA`, then
  `h¹(v, w) = A⁻¹v`, `h²(u) = (0, D⁻¹u)` contract the complex.
* `InertiaContraction` (tex L3762–3765): if `C` is a unit and `DC = CA`, then
  `h¹(v, w) = C⁻¹w`, `h²(u) = (−C⁻¹u, 0)` contract the complex.
* `MatrixFrobeniusContraction` (tex L3758–3760, L5186–5187): over `M = Sⁿ`, the Frobenius
  contraction with the adjugate inverses `A⁻¹ = det(A)⁻¹ adj(A)`, `D⁻¹ = det(D)⁻¹ adj(D)` as soon as
  `det A`, `det D` are units of `S` ("at `(t)` the nonzero central Frobenius determinants give
  integral adjugate contractions").
* `ContractionAcyclic`: a contraction makes the complex acyclic in every degree (every cocycle is a
  coboundary), the use made of it in the comparison (tex L3740–3743, L3842–3849).

A "contraction" of the three-term complex means maps `h¹ : M ⊕ M → M`, `h² : M → M ⊕ M` with
`h¹ d⁰ = 1`, `d⁰ h¹ + h² d¹ = 1`, `d¹ h² = 1` (a contracting homotopy `dh + hd = 1` of the complex
`0 → M → M ⊕ M → M → 0`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open LinearMap

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-! ### The complex -/

/-- `d⁰(v) = (Av, Cv)` (tex L3472). -/
def tameD0 (A C : Module.End S M) : M →ₗ[S] M × M := LinearMap.prod A C

/-- `d¹(v, w) = −Cv + Dw` (tex L3472). -/
def tameD1 (C D : Module.End S M) : M × M →ₗ[S] M := LinearMap.coprod (-C) D

@[simp] theorem tameD0_apply (A C : Module.End S M) (v : M) : tameD0 A C v = (A v, C v) := rfl

@[simp] theorem tameD1_apply (C D : Module.End S M) (x : M × M) :
    tameD1 C D x = -C x.1 + D x.2 := by
  simp [tameD1]

/-- `N_q(g) = (q+1)/2 + ((q−1)/2) g` for an odd prime `q = 2k + 1` (tex L3475): here
`(q+1)/2 = k + 1`, `(q−1)/2 = k`. -/
def normQ (k : ℕ) (g : Module.End S M) : Module.End S M := ((k + 1 : ℕ) : Module.End S M) + (k : ℕ) • g

/-- **The local model (4.4) is a complex exactly when `DC = CA`** (tex L3472–3476).
Classification: PROVED. -/
def TameModelIsComplex : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (A C D : Module.End S M),
    tameD1 C D ∘ₗ tameD0 A C = 0 ↔ D * C = C * A

theorem tameModelIsComplex_proof : TameModelIsComplex := by
  intro S M _ _ _ A C D
  constructor
  · intro h
    ext v
    have := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply, tameD0_apply, tameD1_apply, LinearMap.zero_apply] at this
    simp only [Module.End.mul_apply]
    rw [← sub_eq_zero, ← this]; abel
  · intro h
    ext v
    simp only [LinearMap.comp_apply, tameD0_apply, tameD1_apply, LinearMap.zero_apply]
    have := LinearMap.congr_fun h v
    simp only [Module.End.mul_apply] at this
    rw [this]; abel

/-- **The commutator form of `DC = CA`** (tex L3472–3476): with `A = Φ − 1`, `C = g − 1`,
`D = Φ − N_q(g)`, one has `DC − CA = (Φg − gΦ) − (N_q(g) − 1)(g − 1)`, and
`N_q(g) − 1 = k (1 + g)` for `q = 2k + 1`. Hence `DC = CA` whenever `Φ` commutes with `g` and
`g² = 1`. Classification: PROVED. -/
def TameCommutator : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (k : ℕ) (Φ g : Module.End S M),
    ((Φ - normQ k g) * (g - 1) - (g - 1) * (Φ - 1) =
        (Φ * g - g * Φ) - (normQ k g - 1) * (g - 1)) ∧
    normQ k g - 1 = (k : ℕ) • (1 + g) ∧
    (Φ * g = g * Φ → g * g = 1 → (Φ - normQ k g) * (g - 1) = (g - 1) * (Φ - 1))

theorem tameCommutator_proof : TameCommutator := by
  intro S M _ _ _ k Φ g
  have hN : normQ k g - 1 = (k : ℕ) • (1 + g) := by
    simp only [normQ, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; noncomm_ring
  refine ⟨by noncomm_ring, hN, fun hc hg => ?_⟩
  rw [← sub_eq_zero]
  have e : (Φ - normQ k g) * (g - 1) - (g - 1) * (Φ - 1) =
      (Φ * g - g * Φ) - (normQ k g - 1) * (g - 1) := by noncomm_ring
  rw [e, hN, hc, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul, mul_assoc]
  have : (1 + g) * (g - 1) = g * g - 1 := by noncomm_ring
  rw [this, hg, sub_self, mul_zero]

/-- **Augmentation `g = 1`** (tex L3477–3479): then `C = 0` and `D = Φ − q`, so the model is the
direct sum of `[Φ − 1]` in degrees zero and one and `[Φ − q]` in degrees one and two.
Classification: PROVED. -/
def TameAugmentation : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (k : ℕ) (Φ : Module.End S M),
    ((1 : Module.End S M) - 1 = 0) ∧ Φ - normQ k 1 = Φ - ((2 * k + 1 : ℕ) : Module.End S M)

theorem tameAugmentation_proof : TameAugmentation := by
  intro S M _ _ _ k Φ
  refine ⟨sub_self _, ?_⟩
  congr 1
  simp only [normQ, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat]
  noncomm_ring

/-! ### Contractions -/

/-- A contraction of the three-term complex `M --d⁰--> N --d¹--> M'`: `h¹ d⁰ = 1`,
`d⁰ h¹ + h² d¹ = 1`, `d¹ h² = 1`. -/
structure IsContraction {M N M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module S N] [AddCommGroup M'] [Module S M'] (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M')
    (h1 : N →ₗ[S] M) (h2 : M' →ₗ[S] N) : Prop where
  deg0 : h1 ∘ₗ d0 = LinearMap.id
  deg1 : d0 ∘ₗ h1 + h2 ∘ₗ d1 = LinearMap.id
  deg2 : d1 ∘ₗ h2 = LinearMap.id

/-- The Frobenius contraction `h¹(v, w) = A⁻¹v` (tex L3733). -/
def frobH1 (A : Module.End S M) : M × M →ₗ[S] M := Ring.inverse A ∘ₗ LinearMap.fst S M M

/-- The Frobenius contraction `h²(u) = (0, D⁻¹u)` (tex L3733). -/
def frobH2 (D : Module.End S M) : M →ₗ[S] M × M := LinearMap.inr S M M ∘ₗ Ring.inverse D

/-- The inertia contraction `h¹(v, w) = C⁻¹w` (tex L3764). -/
def inertH1 (C : Module.End S M) : M × M →ₗ[S] M := Ring.inverse C ∘ₗ LinearMap.snd S M M

/-- The inertia contraction `h²(u) = (−C⁻¹u, 0)` (tex L3764). -/
def inertH2 (C : Module.End S M) : M →ₗ[S] M × M := LinearMap.inl S M M ∘ₗ (-Ring.inverse C)

/-- **The Frobenius contraction** (proof of `ex:arith-paired-functional`, tex L3730–3735): "Thus
`A, D` are invertible over `𝒪[G]`. The formulas `h¹(v, w) = A⁻¹v`, `h²(u) = (0, D⁻¹u)` contract the
complex; the identities follow from `DC = CA`." Over any commutative ring `S`.
Classification: PROVED. -/
def FrobeniusContraction : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (A C D : Module.End S M),
    IsUnit A → IsUnit D → D * C = C * A →
      IsContraction (tameD0 A C) (tameD1 C D) (frobH1 A) (frobH2 D)

theorem frobeniusContraction_proof : FrobeniusContraction := by
  intro S M _ _ _ A C D hA hD hDC
  -- `C A⁻¹ = D⁻¹ C`
  have key : C * Ring.inverse A = Ring.inverse D * C := by
    calc C * Ring.inverse A = Ring.inverse D * (D * C) * Ring.inverse A := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hD, one_mul]
      _ = Ring.inverse D * C := by
          rw [hDC, mul_assoc, mul_assoc, Ring.mul_inverse_cancel _ hA, mul_one]
  have kv : ∀ v, C (Ring.inverse A v) = Ring.inverse D (C v) := fun v =>
    LinearMap.congr_fun key v
  have iA : ∀ v, Ring.inverse A (A v) = v := fun v =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel _ hA) v
  have iD : ∀ v, Ring.inverse D (D v) = v := fun v =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel _ hD) v
  have Di : ∀ v, D (Ring.inverse D v) = v := fun v =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ hD) v
  have Ai : ∀ v, A (Ring.inverse A v) = v := fun v =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ hA) v
  refine ⟨?_, ?_, ?_⟩
  · ext v; simp [frobH1, iA]
  · apply LinearMap.ext; rintro ⟨v, w⟩
    ext <;> simp [frobH1, frobH2, Ai, kv, map_add, map_neg, iD]
  · ext u; simp [frobH2, Di]

/-- **The inertia contraction** (proof of `ex:arith-paired-functional`, tex L3755–3765): when
inertia minus one `C` is invertible ("inertia minus one is `−2`, a unit at `𝔭 ≠ (2)`", "at the
moving prime inertia minus one is invertible unless `𝔭 = (t)`"), "the maps are
`h¹(v, w) = C⁻¹w`, `h²(u) = (−C⁻¹u, 0)`". Over any commutative ring `S`.
Classification: PROVED. -/
def InertiaContraction : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (A C D : Module.End S M),
    IsUnit C → D * C = C * A →
      IsContraction (tameD0 A C) (tameD1 C D) (inertH1 C) (inertH2 C)

theorem inertiaContraction_proof : InertiaContraction := by
  intro S M _ _ _ A C D hC hDC
  -- `A C⁻¹ = C⁻¹ D`
  have key : Ring.inverse C * D = A * Ring.inverse C := by
    calc Ring.inverse C * D = Ring.inverse C * D * (C * Ring.inverse C) := by
          rw [Ring.mul_inverse_cancel _ hC, mul_one]
      _ = Ring.inverse C * (D * C) * Ring.inverse C := by simp only [mul_assoc]
      _ = A * Ring.inverse C := by
          rw [hDC, ← mul_assoc, Ring.inverse_mul_cancel _ hC, one_mul]
  have kv : ∀ v, Ring.inverse C (D v) = A (Ring.inverse C v) := fun v =>
    LinearMap.congr_fun key v
  have iC : ∀ v, Ring.inverse C (C v) = v := fun v =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel _ hC) v
  have Ci : ∀ v, C (Ring.inverse C v) = v := fun v =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ hC) v
  refine ⟨?_, ?_, ?_⟩
  · ext v; simp [inertH1, iC]
  · apply LinearMap.ext; rintro ⟨v, w⟩
    ext <;> simp [inertH1, inertH2, Ci, iC, kv, map_add, map_neg]
  · ext u; simp [inertH2, Ci]

/-- **Adjugate (determinant) form of the Frobenius contraction** (tex L3758–3760, L5186–5187):
over `M = Sⁿ` with matrices `A, C, D`, if `det A` and `det D` are units of `S` and `DC = CA`, the
maps built from the adjugate inverses `A⁻¹ = det(A)⁻¹ adj(A)`, `D⁻¹ = det(D)⁻¹ adj(D)` contract
the model. (At `𝔭 = (t)` the central Frobenius determinants are nonzero, hence units of `Λ_(t)`;
see `Lambda.lean`.) Classification: PROVED. -/
def MatrixFrobeniusContraction : Prop :=
  ∀ (S : Type) [CommRing S] (n : Type) [Fintype n] [DecidableEq n] (A C D : Matrix n n S),
    IsUnit A.det → IsUnit D.det → D * C = C * A →
      A⁻¹ = Ring.inverse A.det • A.adjugate ∧ D⁻¹ = Ring.inverse D.det • D.adjugate ∧
      IsContraction (tameD0 (Matrix.toLin' A) (Matrix.toLin' C))
        (tameD1 (Matrix.toLin' C) (Matrix.toLin' D))
        (Matrix.toLin' A⁻¹ ∘ₗ LinearMap.fst S (n → S) (n → S))
        (LinearMap.inr S (n → S) (n → S) ∘ₗ Matrix.toLin' D⁻¹)

theorem matrixFrobeniusContraction_proof : MatrixFrobeniusContraction := by
  intro S _ n _ _ A C D hA hD hDC
  refine ⟨Matrix.inv_def A, Matrix.inv_def D, ?_⟩
  have uA : IsUnit (Matrix.toLin' A) :=
    Matrix.isUnit_toLin'_iff.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hA)
  have uD : IsUnit (Matrix.toLin' D) :=
    Matrix.isUnit_toLin'_iff.mpr ((Matrix.isUnit_iff_isUnit_det D).mpr hD)
  have rA : Ring.inverse (Matrix.toLin' A) = Matrix.toLin' A⁻¹ := by
    have h1 : Matrix.toLin' A * Matrix.toLin' A⁻¹ = 1 := by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hA, Matrix.toLin'_one]; rfl
    calc Ring.inverse (Matrix.toLin' A)
        = Ring.inverse (Matrix.toLin' A) * (Matrix.toLin' A * Matrix.toLin' A⁻¹) := by
          rw [h1, mul_one]
      _ = Matrix.toLin' A⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ uA, one_mul]
  have rD : Ring.inverse (Matrix.toLin' D) = Matrix.toLin' D⁻¹ := by
    have h1 : Matrix.toLin' D * Matrix.toLin' D⁻¹ = 1 := by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hD, Matrix.toLin'_one]; rfl
    calc Ring.inverse (Matrix.toLin' D)
        = Ring.inverse (Matrix.toLin' D) * (Matrix.toLin' D * Matrix.toLin' D⁻¹) := by
          rw [h1, mul_one]
      _ = Matrix.toLin' D⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ uD, one_mul]
  have hDC' : Matrix.toLin' D * Matrix.toLin' C = Matrix.toLin' C * Matrix.toLin' A := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hDC]
  have := frobeniusContraction_proof S (n → S) (Matrix.toLin' A) (Matrix.toLin' C)
    (Matrix.toLin' D) uA uD hDC'
  simpa only [frobH1, frobH2, rA, rD] using this

/-- **A contraction makes the model acyclic** (tex L3740–3743, L3842–3849: the full local complexes
at active and moving primes are acyclic, so the comparison is a quasi-isomorphism): `d⁰` is
injective, every `1`-cocycle is a coboundary, and `d¹` is surjective. Classification: PROVED. -/
def ContractionAcyclic : Prop :=
  ∀ (S M N M' : Type) [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup M'] [Module S M'] (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M') (h1 : N →ₗ[S] M)
    (h2 : M' →ₗ[S] N), IsContraction d0 d1 h1 h2 →
      Function.Injective d0 ∧ (∀ x, d1 x = 0 → d0 (h1 x) = x) ∧ Function.Surjective d1

theorem contractionAcyclic_proof : ContractionAcyclic := by
  intro S M N M' _ _ _ _ _ _ _ d0 d1 h1 h2 hc
  refine ⟨fun a b hab => ?_, fun x hx => ?_, fun y => ⟨h2 y, ?_⟩⟩
  · have ha := LinearMap.congr_fun hc.deg0 a
    have hb := LinearMap.congr_fun hc.deg0 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  · have := LinearMap.congr_fun hc.deg1 x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hx, map_zero,
      add_zero] at this
    exact this
  · have := LinearMap.congr_fun hc.deg2 y
    simpa using this

/-- **Non-vacuity**: the inertia contraction applies to the scalar primitive constituent at an
active prime, `M = S`, `g = −1` (so `C = −2`), with `2` a unit of `S` (tex L3755–3757), for every
Frobenius `Φ`: then `DC = CA` holds (`TameCommutator`, `g² = 1`). Classification: PROVED. -/
theorem inertia_applies_scalar_primitive (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (k : ℕ)
    (Φ : Module.End S S) :
    IsContraction (tameD0 (Φ - 1) ((-1 : Module.End S S) - 1))
      (tameD1 ((-1 : Module.End S S) - 1) (Φ - normQ k (-1)))
      (inertH1 ((-1 : Module.End S S) - 1)) (inertH2 ((-1 : Module.End S S) - 1)) := by
  apply inertiaContraction_proof
  · have e : ((-1 : Module.End S S) - 1) = algebraMap S (Module.End S S) (-2) := by
      ext; simp; norm_num
    rw [e]; exact h2.neg.map _
  · exact (tameCommutator_proof S S k Φ (-1)).2.2 (LinearMap.ext fun x => by simp)
      (LinearMap.ext fun x => by simp)

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
