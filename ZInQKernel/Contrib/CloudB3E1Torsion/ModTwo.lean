import ZInQKernel.Contrib.CloudB3E1Torsion.InvariantSocle
import ZInQKernel.Contrib.CloudB3RC53.Basic

/-!
# `ModTwoTrivial` for the actual curve

Manuscript `diophantine_zq.tex`, tex 1765 (`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`), 2724–2727.

This discharges the named input `ModTwoTrivial` of `InvariantSocle.lean` for `E_ℓ` over a number
field `K`, given full `2`-power torsion over `K_S` (the tree's `HasFullTwoTorsion`).

* **`twoTorsion_fixed_ecurve`** (PROVED): `G_{K,S}` fixes `E_ℓ(K_S)[2]`. A nonzero `2`-torsion
  point `(x, y)` has `y = −y`, so `y = 0`, and `x(x − ℓ)(x + 3ℓ) = 0`; its coordinates lie in `K`.
* **`modTwoTrivial_of_fixed`** (PROVED, any curve): if `G_{K,S}` fixes `E(K_S)[2]` and
  `|E(K_S)[2^n]| = 4^n` for all `n`, then `G_{K,S}` acts trivially on `E[2^i]/2E[2^i]`. For
  `s = g t − t` one has `2^{i−1} s = 0`, since `g` fixes `2^{i−1} t ∈ E[2]`. The doubling map
  `E[2^i] → E[2^{i−1}]` is onto, because its kernel is `E[2]` and the cardinalities match.
* **`modTwoTrivial_ecurve`**, **`not_orthComparisonInverse_ecurve`** (PROVED): for `E_ℓ` with
  `HasFullTwoTorsion` over `S₀`, lane E2's `OrthComparisonInverse` on the actual `MinS`
  (`i ≥ 1`, any index `p`) is uninhabited. No named input remains.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53 (Ecurve)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-! ### The doubling map -/

theorem memT {A : Type*} [AddCommGroup A] {n : ℤ} {x : A} :
    x ∈ AddSubgroup.torsionBy A n ↔ n • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

section Doubling

variable {W : WeierstrassCurve K}

/-- `t ↦ 2t`, `E(K_S)[2^{j+1}] → E(K_S)[2^j]`. Kind: definition. -/
def dbl (j : ℕ) : TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ) →+ TorsS K S W ((2 ^ j : ℕ) : ℤ) where
  toFun t := ⟨(2 : ℤ) • t.1, by
    have h := memT.mp t.2
    refine memT.mpr ?_
    rw [smul_smul]
    convert h using 2
    push_cast
    ring⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' t t' := Subtype.ext (smul_add _ _ _)

/-- The kernel of the doubling map is `E[2]`. Kind: definition. -/
def dblKerEquiv (j : ℕ) : (dbl (K := K) (S := S) (W := W) j).ker ≃ TorsS K S W ((2 ^ 1 : ℕ) : ℤ) where
  toFun t := ⟨t.1.1, by
    have h : (2 : ℤ) • t.1.1 = 0 := congrArg Subtype.val t.2
    refine memT.mpr ?_
    convert h using 2⟩
  invFun t := ⟨⟨t.1, by
    have h : (2 : ℤ) • (t : (W.baseChange (KS K S)).toAffine.Point) = 0 := by
      convert memT.mp t.2 using 2
    refine memT.mpr ?_
    have : ((2 ^ (j + 1) : ℕ) : ℤ) = (2 ^ j : ℤ) * 2 := by push_cast; ring
    rw [this, mul_smul, h, smul_zero]⟩, by
    apply Subtype.ext
    change (2 : ℤ) • (t : (W.baseChange (KS K S)).toAffine.Point) = 0
    convert memT.mp t.2 using 2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [W.IsElliptic]

omit [NumberField K] in
/-- **The doubling map is onto** under full `2`-power torsion. Kind: PROVED. -/
theorem dbl_surjective (hfull : ∀ n : ℕ, FullTorsion K S W (2 ^ n)) (j : ℕ) :
    Function.Surjective (dbl (K := K) (S := S) (W := W) j) := by
  have hfin : ∀ n : ℕ, Finite (TorsS K S W ((2 ^ n : ℕ) : ℤ)) := fun n =>
    finite_torsS (by exact_mod_cast (pow_ne_zero n two_ne_zero : (2 : ℕ) ^ n ≠ 0))
  have hc : ∀ n : ℕ, Nat.card (TorsS K S W ((2 ^ n : ℕ) : ℤ)) = 4 ^ n := fun n => by
    rw [hfull n, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  have hker : Nat.card (dbl (K := K) (S := S) (W := W) j).ker = 4 :=
    (Nat.card_congr (dblKerEquiv j)).trans ((hc 1).trans (by norm_num))
  have htot := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (dbl (K := K) (S := S) (W := W) j).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange _).toEquiv, hker, hc (j + 1)] at htot
  have hr : Nat.card (dbl (K := K) (S := S) (W := W) j).range =
      Nat.card (TorsS K S W ((2 ^ j : ℕ) : ℤ)) := by
    rw [hc j]
    rw [pow_succ] at htot
    omega
  rw [← AddMonoidHom.range_eq_top, ← AddSubgroup.card_eq_iff_eq_top]
  exact hr

omit [NumberField K] in
/-- **Mod-`2` triviality from the triviality on `E[2]`** (PROVED). -/
theorem modTwoTrivial_of_fixed (hfull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
    (hfix : ∀ (g : GKS K S) (t : TorsS K S W ((2 ^ 1 : ℕ) : ℤ)), g • t = t) (i : ℕ) :
    ModTwoTrivial (S := S) W i := by
  intro g t
  rcases i with _ | j
  · refine ⟨0, Subtype.ext ?_⟩
    have h := memT.mp (g • t).2
    have h' := memT.mp t.2
    simp only [pow_zero, Nat.cast_one, one_smul] at h h'
    rw [smul_zero, add_zero]
    exact h.trans h'.symm
  · set s : TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ) := g • t - t with hs
    have hs2 : s.1 ∈ AddSubgroup.torsionBy ((W.baseChange (KS K S)).toAffine.Point)
        ((2 ^ j : ℕ) : ℤ) := by
      refine memT.mpr ?_
      let u : TorsS K S W ((2 ^ 1 : ℕ) : ℤ) := ⟨((2 ^ j : ℕ) : ℤ) • t.1, by
        refine memT.mpr ?_
        rw [smul_smul]
        have h := memT.mp t.2
        convert h using 2
        push_cast
        ring⟩
      have hu := congrArg Subtype.val (hfix g u)
      change Affine.Point.map (galS K S g).toAlgHom (((2 ^ j : ℕ) : ℤ) • t.1) =
        ((2 ^ j : ℕ) : ℤ) • t.1 at hu
      rw [map_zsmul] at hu
      change ((2 ^ j : ℕ) : ℤ) • ((g • t).1 - t.1) = 0
      rw [smul_sub, coe_smul_torsS, hu, sub_self]
    obtain ⟨t', ht'⟩ := dbl_surjective hfull j ⟨s.1, hs2⟩
    refine ⟨t', Subtype.ext ?_⟩
    have h1 : (2 : ℤ) • t'.1 = s.1 := congrArg Subtype.val ht'
    rw [two_zsmul] at h1
    rw [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, two_nsmul, h1, hs, AddSubgroup.coe_sub]
    abel

end Doubling

/-! ### The actual curve -/

section Ecurve

variable (ℓ : ℕ) [(Ecurve ℓ).IsElliptic]

omit [(Ecurve ℓ).IsElliptic] in
/-- **`G_{K,S}` fixes `E_ℓ(K_S)[2]`** (PROVED): the nonzero `2`-torsion points are `(0, 0)`,
`(ℓ, 0)`, `(−3ℓ, 0)`, with coordinates in `K`. -/
theorem twoTorsion_fixed_ecurve (g : GKS K S)
    (t : TorsS K S ((Ecurve ℓ).baseChange K) ((2 ^ 1 : ℕ) : ℤ)) : g • t = t := by
  obtain ⟨P, hP⟩ := t
  apply Subtype.ext
  rw [coe_smul_torsS]
  rcases P with _ | ⟨x, y, h⟩
  · exact map_zero _
  have h2 : (2 : ℤ) • (Affine.Point.some x y h :
      (((Ecurve ℓ).baseChange K).baseChange (KS K S)).toAffine.Point) = 0 := by
    convert memT.mp hP using 2
  have hneg : Affine.Point.some x y h = -(Affine.Point.some x y h :
      (((Ecurve ℓ).baseChange K).baseChange (KS K S)).toAffine.Point) :=
    eq_neg_of_add_eq_zero_left (by rw [← two_zsmul]; exact h2)
  rw [Affine.Point.neg_some, Affine.Point.some.injEq] at hneg
  have hy : y = 0 := by
    have := hneg.2
    simp [Affine.negY, Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.baseChange,
      WeierstrassCurve.map] at this
    have h2y : (2 : KS K S) * y = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2y with h | h
    · exact absurd h two_ne_zero
    · exact h
  have heq := (Affine.equation_iff x y).1 h.1
  rw [hy] at heq
  simp [Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    map_ofNat] at heq
  have hx : x * (x - (ℓ : KS K S)) * (x + 3 * (ℓ : KS K S)) = 0 := by linear_combination -heq
  rw [Affine.Point.map_some, Affine.Point.some.injEq]
  refine ⟨?_, by rw [hy, map_zero]⟩
  rcases mul_eq_zero.1 hx with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · rw [h'', map_zero]
    · rw [sub_eq_zero.1 h'', map_natCast]
  · rw [eq_neg_of_add_eq_zero_left h', map_neg, map_mul, map_ofNat, map_natCast]

/-- **`ModTwoTrivial` for `E_ℓ`** (PROVED), under full `2`-power torsion over `K_S`. -/
theorem modTwoTrivial_ecurve [hF : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S
    ((Ecurve ℓ).baseChange K)] (i : ℕ) : ModTwoTrivial (S := S) ((Ecurve ℓ).baseChange K) i :=
  modTwoTrivial_of_fixed hF.full (twoTorsion_fixed_ecurve ℓ) i

end Ecurve

/-! ### The orthogonal comparison at the actual modules, with no named input -/

section Actual

open ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3E2.DualPres
open ZInQ.Manuscript.RC.Limits (SplitInclusion)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {S₀ S' : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S') (ℓ : ℕ) [(Ecurve ℓ).IsElliptic]
  [hF : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S₀ ((Ecurve ℓ).baseChange K)]
  (i : ℕ) [NeZero i] (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
  {k : Type} [CommRing k] [TopologicalSpace k]
  [Module k (MinS hS ((Ecurve ℓ).baseChange K) i α)]
  [SMulCommClass (GKS K S') k (MinS hS ((Ecurve ℓ).baseChange K) i α)]
  {Δ' Δ'' : LocalConditions k (GKS K S') (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S' v.1) (MinS hS ((Ecurve ℓ).baseChange K) i α)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S'}
  {X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1)}
  {EU : ∀ j, SplitInclusion (genuineUq K S' k (place j) (X j))
    (genuineLq K S' k (MinS hS ((Ecurve ℓ).baseChange K) i α) (place j))}

/-- **Lane E2's `OrthComparisonInverse` is uninhabited at the actual modules of `E_ℓ`** (PROVED,
no named input; tex 3736–3753): for `i ≥ 1`, full `2`-power torsion over `K_{S₀}` (the staged
presentation's field `full`) and any index `p`. Kind: PROVED. -/
theorem not_orthComparisonInverse_ecurve (p : ι) :
    ¬ Nonempty (OrthComparisonInverse K S₀ S' k (MinS hS ((Ecurve ℓ).baseChange K) i α)
      Δ' Δ'' place X EU) :=
  not_orthComparisonInverse_actual hS _ i α (hF.full i) (modTwoTrivial_ecurve ℓ i) p

end Actual

end ZInQ.Contrib.CloudB3E1Torsion
