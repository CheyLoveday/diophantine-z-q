import ZInQKernel.Contrib.OneProof.CharPolyCharP
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

/-!
# charpoly-p: `DegPolyAt A` from four statements about the Euler characteristic

Mumford's route to the polynomiality of `deg` (§19), split at the Euler characteristic. Over the genuine tree
definitions (CW07's coherent-cohomology `Scheme.Modules.eulerChar`, AnthropicFLT's `Scheme.Modules.IsInvertible`,
Mathlib's `Scheme.Modules.pullback`, charpoly-ell's `degEnd`):

* `EulerPullbackDegAt A`: `χ(ψ^*L) = deg ψ · χ(L)` for every `ψ ∈ End A` and invertible `L`;
* `ChiPullbackPolyAt A`: for invertible `L` and a finite family `e`, `x ↦ χ((∑ xᵢ eᵢ)^*L)` is a polynomial;
* `ExistsChiNeZeroAt A`: some invertible `L` has `χ(L) ≠ 0`;
* `DegMulNAt A g`: `deg [m] = m^{2g}` for `(m : k) ≠ 0`.

`degPolyAt_of_chi` proves charpoly-p's `DegPolyAt A` (deg-det's `DegHomogPoly` at `k, A`) from them. The
homogeneity of degree `2g` comes from `deg(mψ) = m^{2g} deg ψ` for infinitely many `m`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial

noncomputable section

namespace ZInQ.Contrib.OneProof.CharPolyCharP.ChiDecomp

open ZInQ.Contrib.OneProof.CharPolyEll ZInQ.Contrib.OneProof.CharPolyCharP ZInQ.Contrib.OneProof.DegDet

/-! ## 1. Homogeneity from scaling (pure algebra) -/

/-- A rational polynomial `N` with `N(m x) = m^n N(x)` for every integer point `x` and infinitely many
`m ∈ ℕ` agrees at integer points with its homogeneous component of degree `n`. -/
theorem eval_eq_homogeneousComponent {r : ℕ} (N : MvPolynomial (Fin r) ℚ) (n : ℕ) (S : Set ℕ)
    (hS : S.Infinite)
    (h : ∀ m ∈ S, ∀ x : Fin r → ℤ, MvPolynomial.eval (fun i => ((m : ℤ) * x i : ℚ)) N =
      (m : ℚ) ^ n * MvPolynomial.eval (fun i => (x i : ℚ)) N) (x : Fin r → ℤ) :
    MvPolynomial.eval (fun i => (x i : ℚ)) N =
      MvPolynomial.eval (fun i => (x i : ℚ)) (MvPolynomial.homogeneousComponent n N) := by
  classical
  set T := max N.totalDegree n
  set c : ℕ → ℚ := fun d => MvPolynomial.eval (fun i => (x i : ℚ)) (MvPolynomial.homogeneousComponent d N)
  set U : ℚ[X] := ∑ d ∈ Finset.range (T + 1), C (c d) * X ^ d
  have hU : ∀ t : ℚ, U.eval t = MvPolynomial.eval (fun i => t * (x i : ℚ)) N := by
    intro t
    conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent N]
    rw [map_sum, eval_finsetSum]
    have hsplit : Finset.range (T + 1) = Finset.range (N.totalDegree + 1) ∪
        (Finset.range (T + 1) \ Finset.range (N.totalDegree + 1)) := by
      rw [Finset.union_sdiff_of_subset]
      exact Finset.range_subset_range.mpr (by omega)
    rw [hsplit, Finset.sum_union Finset.disjoint_sdiff]
    have hzero : ∑ d ∈ Finset.range (T + 1) \ Finset.range (N.totalDegree + 1),
        (C (c d) * X ^ d : ℚ[X]).eval t = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      have hd' : N.totalDegree < d := by
        simp only [Finset.mem_sdiff, Finset.mem_range] at hd; omega
      simp [c, MvPolynomial.homogeneousComponent_eq_zero d N hd']
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X]
    have := aeval_mul_of_isHomogeneous (S := ℚ)
      (MvPolynomial.homogeneousComponent_isHomogeneous d N) t (fun i => (x i : ℚ))
    have this' : MvPolynomial.eval (fun i => t * (x i : ℚ)) (MvPolynomial.homogeneousComponent d N) =
        t ^ d * MvPolynomial.eval (fun i => (x i : ℚ)) (MvPolynomial.homogeneousComponent d N) := this
    rw [this', mul_comm]
  set V : ℚ[X] := U - C (U.eval 1) * X ^ n
  have hV : V = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot V ?_
    refine Set.Infinite.mono ?_ (hS.image (Nat.cast_injective.injOn))
    rintro _ ⟨m, hm, rfl⟩
    change V.eval (m : ℚ) = 0
    simp only [V, eval_sub, eval_mul, eval_C, eval_pow, eval_X, hU, _root_.one_mul]
    have := h m hm x
    push_cast at this
    rw [this]; ring
  have hcoeff := congrArg (fun P : ℚ[X] => P.coeff n) hV
  simp only [V, coeff_sub, coeff_C_mul, coeff_X_pow, ite_true, _root_.mul_one, coeff_zero] at hcoeff
  have hUn : U.coeff n = c n := by
    simp only [U, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hn; simp only [Finset.mem_range] at hn; omega
  have h1 := hU 1
  simp only [_root_.one_mul] at h1
  rw [← h1]
  linarith [hUn, hcoeff]

/-- The `m ∈ ℕ` with `(m : k) ≠ 0` form an infinite set. -/
theorem infinite_natCast_ne_zero (k : Type) [Field k] : {m : ℕ | (m : k) ≠ 0}.Infinite := by
  rcases Nat.eq_zero_or_pos (ringChar k) with h0 | hp
  · haveI : CharP k 0 := by rw [← h0]; exact ringChar.charP k
    haveI : CharZero k := CharP.charP_to_charZero k
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => j + 1)
      (fun a b h => by simpa using h) fun j => ?_
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  · refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => ringChar k * j + 1)
      (fun a b h => by simpa [hp.ne'] using h) fun j => ?_
    change ((ringChar k * j + 1 : ℕ) : k) ≠ 0
    rw [Nat.cast_add, Nat.cast_mul, ringChar.Nat.cast_ringChar, zero_mul, zero_add, Nat.cast_one]
    exact one_ne_zero

/-! ## 2. The four statements -/

variable {k : Type} [Field k] [IsAlgClosed k]

/-- `χ(A, M)`, CW07's Euler characteristic over `k`. -/
def chi (A : PkgI3.AbVar k) (M : A.X.left.Modules) : ℤ :=
  letI : A.X.left.Over (Spec (CommRingCat.of k)) := ⟨A.X.hom⟩
  Scheme.Modules.eulerChar k M

/-- `ψ^*M`. -/
def pb {A : PkgI3.AbVar k} (ψ : PkgI3.AbVar.End A) (M : A.X.left.Modules) : A.X.left.Modules :=
  (Scheme.Modules.pullback ψ.hom.left).obj M

/-- **`χ(ψ^*L) = deg ψ · χ(L)`** (consequence of published theorems). D. Mumford, *Abelian varieties*
(1970), §12 (isogenies; UNVERIFIED locator) and §16 (Riemann–Roch `χ(L)² = deg φ_L`, which gives `0 = 0` for a
non-isogeny; UNVERIFIED locator). -/
def EulerPullbackDegAt (A : PkgI3.AbVar k) : Prop :=
  ∀ (ψ : PkgI3.AbVar.End A) (L : A.X.left.Modules), Scheme.Modules.IsInvertible L →
    chi A (pb ψ L) = (degEnd ψ : ℤ) * chi A L

/-- **`x ↦ χ((∑ xᵢ eᵢ)^*L)` is a polynomial** (consequence of published theorems: the theorem of the cube,
Mumford §6 Cor. 2 and §10, makes `x ↦ (∑ xᵢ eᵢ)^*L` quadratic in `Pic A`; Snapper's theorem (Kleiman 1966) or
Riemann–Roch §16 makes `χ` polynomial in the exponents; locators UNVERIFIED). The tree proves the cube for
commutative proper smooth group schemes (vendored AnthropicFLT,
`Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso`) and a one-variable Snapper polynomiality. -/
def ChiPullbackPolyAt (A : PkgI3.AbVar k) : Prop :=
  ∀ (L : A.X.left.Modules), Scheme.Modules.IsInvertible L →
    ∀ (r : ℕ) (e : Fin r → PkgI3.AbVar.End A), ∃ P : MvPolynomial (Fin r) ℚ,
      ∀ x : Fin r → ℤ, (chi A (pb (∑ i, x i • e i) L) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) P

/-- **Some invertible sheaf has `χ ≠ 0`** (consequence of published theorems: an abelian variety is
projective, Mumford §6 Application 1 / §7, and an ample `L` has `χ(L) = h⁰(L) > 0`, §16; locators UNVERIFIED).
The tree's vendored AnthropicFLT has a symmetric invertible `𝓛` whose Čech χ-polynomial has positive leading
coefficient (`RelativeGroupLaw.exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq`). -/
def ExistsChiNeZeroAt (A : PkgI3.AbVar k) : Prop :=
  ∃ L : A.X.left.Modules, Scheme.Modules.IsInvertible L ∧ chi A L ≠ 0

/-- **`deg [m] = m^{2g}` for `char k ∤ m`** (published: Mumford §4 (iv), §6 Application 2; UNVERIFIED). The
tree's vendored AnthropicFLT proves it for its `RelativeGroupLaw.endDegree`
(`endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero`). -/
def DegMulNAt (A : PkgI3.AbVar k) (g : ℕ) : Prop :=
  ∀ m : ℕ, (m : k) ≠ 0 → degEnd (m : PkgI3.AbVar.End A) = m ^ (2 * g)

/-! ## 3. The reduction -/

theorem chi_congr (A : PkgI3.AbVar k) {M N : A.X.left.Modules} (e : M ≅ N) : chi A M = chi A N := by
  letI : A.X.left.Over (Spec (CommRingCat.of k)) := ⟨A.X.hom⟩
  exact Scheme.Modules.eulerChar_congr k e

theorem pb_mul (A : PkgI3.AbVar k) (ψ χ : PkgI3.AbVar.End A) (M : A.X.left.Modules) :
    chi A (pb (ψ * χ) M) = chi A (pb χ (pb ψ M)) := by
  refine chi_congr A ?_
  have h : (ψ * χ).hom.left = χ.hom.left ≫ ψ.hom.left := rfl
  unfold pb
  rw [h]
  exact ((Scheme.Modules.pullbackComp χ.hom.left ψ.hom.left).app M).symm

theorem deg_mul_natCast (A : PkgI3.AbVar k) (g : ℕ) (hE : EulerPullbackDegAt A) (hN : DegMulNAt A g)
    {L : A.X.left.Modules} (hL : Scheme.Modules.IsInvertible L) (hχ : chi A L ≠ 0)
    (m : ℕ) (hm : (m : k) ≠ 0) (ψ : PkgI3.AbVar.End A) :
    degEnd ((m : PkgI3.AbVar.End A) * ψ) = m ^ (2 * g) * degEnd ψ := by
  have h1 := hE ((m : PkgI3.AbVar.End A) * ψ) L hL
  rw [pb_mul, hE ψ (pb (m : PkgI3.AbVar.End A) L) (Scheme.Modules.IsInvertible.pullback _ hL),
    hE _ L hL, hN m hm] at h1
  have : ((degEnd ((m : PkgI3.AbVar.End A) * ψ) : ℕ) : ℤ) = ((m ^ (2 * g) * degEnd ψ : ℕ) : ℤ) := by
    apply mul_right_cancel₀ hχ
    push_cast at h1 ⊢
    linear_combination -h1
  exact_mod_cast this

/-- **`DegPolyAt A` from the four statements.** -/
theorem degPolyAt_of_chi (A : PkgI3.AbVar k) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (hE : EulerPullbackDegAt A) (hP : ChiPullbackPolyAt A) (hL : ExistsChiNeZeroAt A)
    (hN : DegMulNAt A g) : DegPolyAt A := by
  classical
  obtain ⟨L, hLi, hχ⟩ := hL
  intro r e
  obtain ⟨P, hPx⟩ := hP L hLi r e
  have hc : (chi A L : ℚ) ≠ 0 := by exact_mod_cast hχ
  set N0 : MvPolynomial (Fin r) ℚ := MvPolynomial.C (chi A L : ℚ)⁻¹ * P
  have hdeg : ∀ x : Fin r → ℤ, ((degEnd (∑ i, x i • e i) : ℕ) : ℚ) =
      MvPolynomial.eval (fun i => (x i : ℚ)) N0 := by
    intro x
    have h := hE (∑ i, x i • e i) L hLi
    have h' : (chi A (pb (∑ i, x i • e i) L) : ℚ) =
        (degEnd (∑ i, x i • e i) : ℚ) * (chi A L : ℚ) := by
      rw [h]; push_cast; ring
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, ← hPx x, h']
    field_simp
  refine ⟨g, MvPolynomial.homogeneousComponent (2 * g) N0, hg,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun x => ?_⟩
  rw [hdeg x]
  refine eval_eq_homogeneousComponent N0 (2 * g) _ (infinite_natCast_ne_zero k) ?_ x
  intro m hm y
  rw [← hdeg y]
  have hsum : (∑ i, ((m : ℤ) * y i) • e i) = (m : PkgI3.AbVar.End A) * ∑ i, y i • e i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, _root_.mul_assoc]
  have h2 := hdeg (fun i => (m : ℤ) * y i)
  simp only [Int.cast_mul] at h2
  rw [← h2, hsum, deg_mul_natCast A g hE hN hLi hχ m hm]
  push_cast
  ring

/-- `deg [m] = m^{2 dim A}` with `dim A` a natural number (the printed form of `DegMulNAt`). -/
def DegMulNDimAt (A : PkgI3.AbVar k) : Prop :=
  ∃ g : ℕ, A.dim = (g : WithBot ℕ∞) ∧ DegMulNAt A g

/-- **The field from the four Euler-characteristic statements** (on fields with no ring homomorphism to `ℂ`;
the others by degpoly-proof). -/
theorem charPolyIndepOfEllAlgClosed_of_chi
    (hE : ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) →
      ∀ A : PkgI3.AbVar k, EulerPullbackDegAt A)
    (hP : ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) →
      ∀ A : PkgI3.AbVar k, ChiPullbackPolyAt A)
    (hL : ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) →
      ∀ A : PkgI3.AbVar k, ExistsChiNeZeroAt A)
    (hN : ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) →
      ∀ A : PkgI3.AbVar k, DegMulNDimAt A) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb' fun k _ _ he A => by
    obtain ⟨g, hg, hN'⟩ := hN k he A
    exact degPolyAt_of_chi A g hg (hE k he A) (hP k he A) (hL k he A) hN'

end ZInQ.Contrib.OneProof.CharPolyCharP.ChiDecomp


