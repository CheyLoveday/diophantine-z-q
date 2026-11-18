import ZInQKernel.Contrib.OneProof.RC.CoefModules.Conjugate

/-!
# Lane RC28 (coefficient modules), part 12: non-vacuity of `FullTorsion`

Manuscript `diophantine_zq.tex` (11/5), tex 1760–1830 (the curves `E_ℓ : y² = x(x−ℓ)(x+3ℓ)`, with
full rational `2`-torsion) and tex 2780 (`E[2]` over the field of definition).

`FullTorsion K S W N` (`|E(K_S)[N]| = N²`) is the only hypothesis of the duality statements of
this lane. It holds for `N = 2` and every curve with full rational `2`-torsion, for every `S`:

* `cubicCurve e₁ e₂ e₃`: `y² = (x − e₁)(x − e₂)(x − e₃)`; `isElliptic_cubicCurve` for distinct
  roots in characteristic zero; `fullTorsion_two_cubicCurve`: `FullTorsion K S _ 2`.
* `curveEll ℓ = cubicCurve 0 ℓ (−3ℓ)` is `E_ℓ` (`curveEll_coeffs`), `fullTorsion_two_curveEll`.
* `fullTorsion_one`: the trivial case `N = 1` (`i = 0`).
* `hasRootsOfUnity_two`: `μ_2 ⊂ K_S` from `E_1`'s full `2`-torsion (through the Weil pairing).
* `actualConj_nonempty_gaussian`: an actual complex conjugation for `K = ℚ(i)` (the fourth
  cyclotomic field) and `S` the places above `2`, restricting to the nontrivial automorphism.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain WeierstrassCurve
open scoped WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- `y² = (x − e₁)(x − e₂)(x − e₃)`. -/
def cubicCurve (e₁ e₂ e₃ : K) : WeierstrassCurve K :=
  ⟨0, -(e₁ + e₂ + e₃), 0, e₁ * e₂ + e₁ * e₃ + e₂ * e₃, -(e₁ * e₂ * e₃)⟩

theorem cubicCurve_Δ (e₁ e₂ e₃ : K) :
    (cubicCurve e₁ e₂ e₃).Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, cubicCurve]
  ring

/-- **Distinct roots give an elliptic curve** (characteristic zero). Kind: PROVED. -/
theorem isElliptic_cubicCurve {e₁ e₂ e₃ : K} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    (cubicCurve e₁ e₂ e₃).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, cubicCurve_Δ]
  refine IsUnit.mk0 _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23))))

/-- The `2`-torsion point `(e, 0)` over `K_S` for a root `e`. -/
theorem nonsingular_root {e₁ e₂ e₃ : K} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (j : Fin 3) :
    ((cubicCurve e₁ e₂ e₃).baseChange (KS K S)).toAffine.Nonsingular
      (algebraMap K (KS K S) (![e₁, e₂, e₃] j)) 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, cubicCurve,
    map_zero, map_neg, map_add, map_mul]
  have hinj := (algebraMap K (KS K S)).injective
  have d12 : algebraMap K (KS K S) e₁ - algebraMap K (KS K S) e₂ ≠ 0 :=
    sub_ne_zero.mpr fun h => h12 (hinj h)
  have d13 : algebraMap K (KS K S) e₁ - algebraMap K (KS K S) e₃ ≠ 0 :=
    sub_ne_zero.mpr fun h => h13 (hinj h)
  have d23 : algebraMap K (KS K S) e₂ - algebraMap K (KS K S) e₃ ≠ 0 :=
    sub_ne_zero.mpr fun h => h23 (hinj h)
  set f₁ := algebraMap K (KS K S) e₁
  set f₂ := algebraMap K (KS K S) e₂
  set f₃ := algebraMap K (KS K S) e₃
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    refine ⟨by ring, Or.inl ?_⟩
  · have : (0 : KS K S) * 0 - (3 * f₁ ^ 2 + 2 * -(f₁ + f₂ + f₃) * f₁ + (f₁ * f₂ + f₁ * f₃ + f₂ * f₃))
        = -((f₁ - f₂) * (f₁ - f₃)) := by ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero d12 d13)
  · have : (0 : KS K S) * 0 - (3 * f₂ ^ 2 + 2 * -(f₁ + f₂ + f₃) * f₂ + (f₁ * f₂ + f₁ * f₃ + f₂ * f₃))
        = (f₁ - f₂) * (f₂ - f₃) := by ring
    rw [this]
    exact mul_ne_zero d12 d23
  · have : (0 : KS K S) * 0 - (3 * f₃ ^ 2 + 2 * -(f₁ + f₂ + f₃) * f₃ + (f₁ * f₂ + f₁ * f₃ + f₂ * f₃))
        = -((f₁ - f₃) * (f₂ - f₃)) := by ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero d13 d23)

/-- **`FullTorsion` holds for `N = 2` for every curve with full rational `2`-torsion**, for every
`S`. Kind: PROVED (four distinct `2`-torsion points over `K`; at most four over `K̄`). -/
theorem fullTorsion_two_cubicCurve {e₁ e₂ e₃ : K} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃)
    (h23 : e₂ ≠ e₃) : FullTorsion K S (cubicCurve e₁ e₂ e₃) 2 := by
  have := isElliptic_cubicCurve h12 h13 h23
  set V := (cubicCurve e₁ e₂ e₃).baseChange (KS K S)
  -- the points `(e_j, 0)` are `2`-torsion
  have htors : ∀ j : Fin 3, (Affine.Point.some _ _ (nonsingular_root (S := S) h12 h13 h23 j) :
      V.toAffine.Point) ∈ AddSubgroup.torsionBy V.toAffine.Point ((2 : ℕ) : ℤ) := by
    intro j
    change _ ∈ Submodule.torsionBy ℤ _ _
    rw [Submodule.mem_torsionBy_iff, Nat.cast_ofNat, two_zsmul]
    have hneg : -(Affine.Point.some _ _ (nonsingular_root (S := S) h12 h13 h23 j) :
        V.toAffine.Point) = Affine.Point.some _ _ (nonsingular_root (S := S) h12 h13 h23 j) := by
      rw [Affine.Point.neg_some]
      congr 1
      simp only [Affine.negY, V, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃, cubicCurve, map_zero]
      ring
    nth_rewrite 2 [← hneg]
    exact add_neg_cancel _
  let pts : Option (Fin 3) → TorsS K S (cubicCurve e₁ e₂ e₃) ((2 : ℕ) : ℤ)
    | none => 0
    | some j => ⟨_, htors j⟩
  have hinj : Function.Injective pts := by
    have hinjK := (algebraMap K (KS K S)).injective
    rintro (_ | j) (_ | j') h <;> simp only [pts, Subtype.mk.injEq] at h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (by simp)
    · exact absurd (congrArg Subtype.val h) (by simp)
    · rw [Affine.Point.some.injEq] at h
      have h1 := hinjK h.1
      fin_cases j <;> fin_cases j' <;> simp at h1 ⊢ <;>
        first
        | exact absurd h1 h12 | exact absurd h1 h13 | exact absurd h1 h23
        | exact absurd h1.symm h12 | exact absurd h1.symm h13 | exact absurd h1.symm h23
  have hfin : Finite (TorsS K S (cubicCurve e₁ e₂ e₃) ((2 : ℕ) : ℤ)) :=
    finite_torsS (by norm_num)
  have hle := Nat.card_le_card_of_injective pts hinj
  have hge : Nat.card (TorsS K S (cubicCurve e₁ e₂ e₃) ((2 : ℕ) : ℤ)) ≤ 2 ^ 2 := by
    rw [← natCard_torsBar (cubicCurve e₁ e₂ e₃) 2]
    exact Nat.card_le_card_of_injective _ (inclTors_injective _ 2)
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hle
  unfold FullTorsion
  omega

/-- **The curve `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`** of tex 1760–1830. -/
def curveEll (ℓ : K) : WeierstrassCurve K := cubicCurve 0 ℓ (-3 * ℓ)

theorem curveEll_coeffs (ℓ : K) :
    curveEll ℓ = ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩ := by
  simp only [curveEll, cubicCurve]
  congr 1 <;> ring

/-- **`E_ℓ` has full `2`-torsion over `K_S`, for every `S`** (`ℓ ≠ 0`). Kind: PROVED. -/
theorem fullTorsion_two_curveEll {ℓ : K} (hℓ : ℓ ≠ 0) : FullTorsion K S (curveEll ℓ) 2 := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  refine fullTorsion_two_cubicCurve (Ne.symm hℓ) ?_ ?_
  · intro h
    exact hℓ (by linear_combination (1 / 3 : K) * h)
  · intro h
    exact hℓ (by linear_combination (1 / 4 : K) * h)

theorem isElliptic_curveEll {ℓ : K} (hℓ : ℓ ≠ 0) : (curveEll ℓ).IsElliptic := by
  refine isElliptic_cubicCurve (Ne.symm hℓ) ?_ ?_
  · intro h
    exact hℓ (by linear_combination (1 / 3 : K) * h)
  · intro h
    exact hℓ (by linear_combination (1 / 4 : K) * h)

/-- `FullTorsion` at `N = 1` (`i = 0`). Kind: PROVED. -/
theorem fullTorsion_one (W : WeierstrassCurve K) : FullTorsion K S W 1 := by
  unfold FullTorsion
  rw [one_pow, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun P Q => ?_⟩, ⟨0⟩⟩
  obtain ⟨x, hx⟩ := P
  obtain ⟨y, hy⟩ := Q
  have hx' : ((1 : ℕ) : ℤ) • x = 0 := (Submodule.mem_torsionBy_iff _ _).mp hx
  have hy' : ((1 : ℕ) : ℤ) • y = 0 := (Submodule.mem_torsionBy_iff _ _).mp hy
  rw [Nat.cast_one, one_zsmul] at hx' hy'
  subst hx' hy'
  rfl

/-- **Non-vacuity of `HasRootsOfUnity`** at `N = 2`, for every `K` and `S`. Kind: PROVED. -/
theorem hasRootsOfUnity_two (S : Set (HeightOneSpectrum (𝓞 K))) : HasRootsOfUnity K S 2 :=
  haveI := isElliptic_curveEll (K := K) one_ne_zero
  hasRootsOfUnity_of_fullTorsion K S (curveEll 1) 2 (fullTorsion_two_curveEll one_ne_zero)

/-- **Non-vacuity of `ActualConj`**: for `K = ℚ(i)` (the fourth cyclotomic field) and `S` the
places above `2` there is an actual complex conjugation, nontrivial on `K`. Kind: PROVED. -/
theorem actualConj_nonempty_gaussian :
    ∃ C : ActualConj (CyclotomicField 4 ℚ)
      {v : HeightOneSpectrum (𝓞 (CyclotomicField 4 ℚ)) |
        v.asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) ∈
          ({Ideal.span {(2 : ℤ)}} : Set (Ideal ℤ))}, C.κ ≠ RingEquiv.refl _ := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have : IsTotallyComplex (CyclotomicField 4 ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) _ (by norm_num)
  have h2 : Module.finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) (CyclotomicField 4 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  exact ActualConj.exists h2 (fun κ => isStable_comap_int _ κ)

end ZInQ.Manuscript.RC.CoefModules
