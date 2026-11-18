import ZInQKernel.Contrib.OneProof.SelmerTwoPower

/-!
# The Kummer sequence in rank zero: `corank_{ℤ₂} Sel_{2^∞}(A/ℚ) = 0`

Target: the GLUE input `KummerCorankZero` of the Theorem 5.3 deduction, stated in
`ZInQKernel/Contrib/OneProof/RC/Skeleton/Steps.lean` (integration branch of the Theorem 5.3 lanes,
commit 839ff728, lines 133–140), copied verbatim below as a local `def`:

```
def KummerCorankZero : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → Module.rank ℤ A.toAffine.Point = 0 →
    Finite (sha A) → Z2Corank (selmerTwoPower A) 0
```

Manuscript: `lem:forward-rank` (`diophantine_zq.tex` L1098–1104: "the ordinary Kummer sequence
`0 → A(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)[2^∞] → 0` gives the corank assertion"); Silverman,
*The Arithmetic of Elliptic Curves*, X.4.

**Proof (PROVED, standard axioms).** The only part of the Kummer sequence needed is that
`Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)` is injective when `A(ℚ)` is torsion (`A(ℚ) ⊗ ℚ₂/ℤ₂ = 0`). Then
`Sel_{2^∞}` embeds in the finite group `Ш`, so it is finite, and `M ≅ (ℚ₂/ℤ₂)^0 × M`.

Injectivity, on cocycles (`eq_zero_of_explicitCoeff1_eq_zero`): let `c` be a continuous cocycle
with values in `A[2^∞]` whose image in `H¹(G_ℚ, A(ℚˢ))` vanishes, so `c(σ) = σP − P` for some
`P ∈ A(ℚˢ)`. As `G_ℚ` is compact and `A[2^∞]` discrete, `c` has finite image, so one `2^n` kills
every value (`exists_uniform_two_pow`); hence `2^n P` is Galois-fixed, so `2^n P = Q ∈ A(ℚ)` (Tau
Ceti `mem_H0_pointCoeff_iff`). Rank zero makes `Q` torsion, say `m Q = 0` with `m = 2^a u`,
`u` odd. With `x 2^n + y u = 1`, put `R = x Q ∈ A(ℚ)`: then `2^a (Q − 2^n R) = y m Q = 0`, so
`T = P − R` satisfies `2^{n+a} T = 0`, i.e. `T ∈ A[2^∞]`, and `c(σ) = σT − T` because `R` is
rational. So `c` is a coboundary in `A[2^∞]`. Neither the finiteness of `A(ℚ)` nor Mordell–Weil
is used: only that every rational point is torsion, which is `rank_eq_zero_iff`.

The hypothesis `A.IsElliptic` is part of the copied statement and is not needed by the proof.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.KummerCorankZero

open ZInQ.Manuscript.SelmerTwoPower TauCeti TauCeti.ContCohomology

set_option linter.dupNamespace false in
/-- **The Kummer sequence in rank zero** (GLUE in the Theorem 5.3 deduction; `lem:forward-rank`,
tex L1098–1104; Silverman X.4): rank zero and finite `Ш` give `corank Sel_{2^∞} = 0`. Statement
copied verbatim from `ZInQKernel/Contrib/OneProof/RC/Skeleton/Steps.lean` @ 839ff728. -/
def KummerCorankZero : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → Module.rank ℤ A.toAffine.Point = 0 →
    Finite (sha A) → Z2Corank (selmerTwoPower A) 0

/-- Rank zero: every rational point is torsion. -/
theorem exists_nsmul_eq_zero_of_rank_eq_zero {A : WeierstrassCurve ℚ}
    (hr : Module.rank ℤ A.toAffine.Point = 0) (Q : A.toAffine.Point) :
    ∃ m : ℕ, 0 < m ∧ m • Q = 0 := by
  obtain ⟨a, ha0, ha⟩ := rank_eq_zero_iff.mp hr Q
  refine ⟨a.natAbs, Int.natAbs_pos.mpr ha0, ?_⟩
  rw [← natCast_zsmul]
  rcases Int.natAbs_eq a with h | h
  · rw [← h]; exact ha
  · rw [h, neg_smul, neg_eq_zero] at ha; exact ha

/-- A continuous cocycle with values in `A[2^∞]` is killed by one power of `2`: `G_ℚ` is compact
and `A[2^∞]` is discrete, so the cocycle has finite image. -/
theorem exists_uniform_two_pow {A : WeierstrassCurve ℚ}
    (z : Z1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff A)) :
    ∃ n : ℕ, ∀ σ : AbsoluteGaloisGroup ℚ,
      2 ^ n • (((z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A) σ : TwoPowerCoeff A) :
        A.PointCoeff) = 0 := by
  classical
  have hc : Continuous (z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A) := (mem_Z1_iff.1 z.2).1
  have hS : (Set.range (z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A)).Finite :=
    (isCompact_range hc).finite_of_discrete
  have hk : ∀ v : TwoPowerCoeff A, ∃ k : ℕ, 2 ^ k • (v : A.PointCoeff) = 0 :=
    fun v => AddCommGroup.mem_primaryComponent.mp v.2
  choose k hk using hk
  refine ⟨∑ v ∈ hS.toFinset, k v, fun σ => ?_⟩
  have hle : k ((z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A) σ) ≤ ∑ v ∈ hS.toFinset, k v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr ⟨σ, rfl⟩)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk, smul_zero]

/-- **`Sel_{2^∞} → Ш` has trivial kernel in rank zero**: a class of `H¹(G_ℚ, A[2^∞])` whose image
in `H¹(G_ℚ, A(ℚˢ))` vanishes is zero, when every point of `A(ℚ)` is torsion. -/
theorem eq_zero_of_explicitCoeff1_eq_zero {A : WeierstrassCurve ℚ}
    (hr : Module.rank ℤ A.toAffine.Point = 0)
    (c : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff A))
    (hc : explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff A) (twoPowerCoeffIncl A)
      continuous_of_discreteTopology c = 0) : c = 0 := by
  induction c using QuotientAddGroup.induction_on with
  | H z =>
    have hc' := hc
    rw [show ((z : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff A))) = (z : H1 _ _) from rfl,
      explicitCoeff1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hc'
    obtain ⟨P, hP⟩ := hc'
    have hP' : ∀ σ : AbsoluteGaloisGroup ℚ, σ • P - P =
        (((z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A) σ : TwoPowerCoeff A) : A.PointCoeff) :=
      fun σ => hP σ
    obtain ⟨n, hn⟩ := exists_uniform_two_pow z
    -- `2^n P` is Galois-fixed, hence rational
    have hfix : ∀ σ : AbsoluteGaloisGroup ℚ, σ • (2 ^ n • P) = 2 ^ n • P := by
      intro σ
      have hσ : σ • P = P + (((z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A) σ :
          TwoPowerCoeff A) : A.PointCoeff) := by rw [← hP' σ]; abel
      rw [smul_comm, hσ, smul_add, hn σ, add_zero]
    obtain ⟨Q, hQ⟩ := A.mem_H0_pointCoeff_iff.1 ((FixedPoints.mem_addSubgroup _ _ _).2 hfix)
    -- rank zero: `Q` is torsion; split off its odd part
    obtain ⟨m, hm0, hmQ⟩ := exists_nsmul_eq_zero_of_rank_eq_zero hr Q
    obtain ⟨a, u, hu, hm⟩ := Nat.exists_eq_two_pow_mul_odd hm0.ne'
    have hcop : IsCoprime ((2 ^ n : ℕ) : ℤ) (u : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hu))
    obtain ⟨x, y, hxy⟩ := hcop
    set R : A.toAffine.Point := x • Q with hR
    have hkey : 2 ^ a • (Q - 2 ^ n • R) = 0 := by
      have e : ((2 ^ a : ℕ) : ℤ) * (1 - ((2 ^ n : ℕ) : ℤ) * x) = y * (m : ℤ) := by
        rw [hm]; push_cast at hxy ⊢; linear_combination (-(2 : ℤ) ^ a) * hxy
      calc 2 ^ a • (Q - 2 ^ n • R)
          = (((2 ^ a : ℕ) : ℤ) * (1 - ((2 ^ n : ℕ) : ℤ) * x)) • Q := by
            rw [hR]; module
        _ = y • (m • Q) := by rw [e, mul_smul, natCast_zsmul]
        _ = 0 := by rw [hmQ, smul_zero]
    -- `T = P − R ∈ A[2^∞]`
    set T : A.PointCoeff := P - A.basePointCoeff R with hT
    have h1 : 2 ^ n • T = A.basePointCoeff (Q - 2 ^ n • R) := by
      rw [hT, smul_sub, ← hQ, map_sub, map_nsmul]
    have h2 : 2 ^ (n + a) • T = 0 := by
      rw [pow_add, mul_comm (2 ^ n) (2 ^ a), mul_smul, h1, ← map_nsmul, hkey, map_zero]
    let TT : TwoPowerCoeff A := ⟨T, AddCommGroup.mem_primaryComponent.mpr ⟨n + a, h2⟩⟩
    have hB : ((z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff A)) ∈
        B1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff A) := by
      rw [mem_B1_iff]
      refine ⟨TT, fun σ => Subtype.ext ?_⟩
      simp only [TT, AddSubgroup.coe_sub, coe_smul_twoPowerCoeff]
      rw [hT, smul_sub, A.smul_basePointCoeff, ← hP' σ]
      abel
    exact (H1pi_eq_zero_iff).2 hB

/-- **The Kummer sequence in rank zero** (PROVED). -/
theorem kummerCorankZero_proof : KummerCorankZero := by
  intro A _ hr hfin
  let φ : selmerTwoPower A →+ sha A :=
    { toFun := fun c => ⟨explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff A)
        (twoPowerCoeffIncl A) continuous_of_discreteTopology c, c.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact Subtype.ext (eq_zero_of_explicitCoeff1_eq_zero hr c (congrArg Subtype.val hc))
  have : Finite (selmerTwoPower A) := Finite.of_injective φ hinj
  exact ⟨selmerTwoPower A, inferInstance, inferInstance, ⟨AddEquiv.uniqueProd.symm⟩⟩

end ZInQ.Contrib.CloudB3RC53.KummerCorankZero
