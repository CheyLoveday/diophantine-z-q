import ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.PassageToLimit

/-!
# The two-power Kummer map on a free generator is injective

Manuscript `diophantine_zq.tex`, tex 1098–1104, 4005–4014 (the Kummer sequence; the input `hδ`
of `KappaGen.hκ_central`).

* `twoPowerSequence n` (definition): the coefficient sequence
  `0 → E[2ⁿ] → E[2^∞] --2ⁿ--> E[2^∞] → 0` of `G_ℚ` (`E[2^∞]` divisible), restricted to `G_K`.
* **`levelToInfinite_levelDelta_eq_zero`** (PROVED): if the finite Kummer class `δₙ(P)` of a point
  dies in `H¹(G_K, E[2^∞])`, then `P ∈ 2ⁿ E(K) + E(K)[2^∞]` (exactness at `H¹(E[2ⁿ])` of the long
  sequence of `twoPowerSequence`, naturality of `δ` into the point sequence, and the kernel of
  `δₙ`, Silverman X.4.2 at level `n`).
* **`dvd_of_kummer_eq_zero`** (PROVED): for a free generator `g` of `E(K)` modulo torsion,
  `levelToInfinite n (δₙ(a g)) = 0` forces `2ⁿ ∣ a`.
* `kummerInf P d` (definition): the `2`-primary Kummer image of `P ⊗ d` in `Sel_{2^∞}(E/K)`:
  for `d = [a/2ⁿ]` (a chosen representative), `levelToInfinite n (δₙ(a P))`;
  **`kummerInf_injective_gen`** (PROVED): `kummerInf g d = 0 → d = 0` for a free generator — the
  input `hδ` of `KappaGen.hκ_central`; `hδ_of_equiv` (PROVED): the same for `δ = kummerInf ∘ ι`
  with `ι` an identification of the points (`ι` and `hcomp` are PROVED: `kc_hcomp_central`,
  `KummerCompHcomp.lean`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.KummerInj

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Contrib.RC53Assist.DiskOrders.Limit

variable (r : SeparableClosure ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- Multiplication by `2ⁿ` on `E[2^∞]`. Kind: definition. -/
def twoPowerMul (n : ℕ) : TwoPowerCoeff E →+ TwoPowerCoeff E := nsmulAddMonoidHom (2 ^ n)

/-- **The sequence `0 → E[2ⁿ] → E[2^∞] → E[2^∞] → 0`** of `G_ℚ`. Kind: definition. -/
def twoPowerSequenceQ (n : ℕ) :
    DiscreteShortExact (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (TwoPowerCoeff E)
      (TwoPowerCoeff E) where
  incl := (torsionToTwoPower E n).toAddMonoidHom
  proj := twoPowerMul E n
  incl_equivariant g a := (torsionToTwoPower E n).map_smul g a
  proj_equivariant g b := smul_comm (2 ^ n) g b
  incl_injective a b h := Subtype.ext (congrArg (fun x : TwoPowerCoeff E => (x : E.PointCoeff)) h)
  proj_surjective b := by
    obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.1 b.2
    have hm2 : IsUnit ((2 ^ n : ℕ) : ℚ) := isUnit_iff_ne_zero.2 (by positivity)
    obtain ⟨Q, hQ⟩ := (E.kummerShortExact (2 ^ n) hm2).proj_surjective (b : E.PointCoeff)
    refine ⟨⟨Q, AddCommGroup.mem_primaryComponent.2 ⟨m + n, ?_⟩⟩, Subtype.ext hQ⟩
    rw [pow_add, mul_comm, mul_nsmul]
    rw [show (2 ^ n) • Q = (b : E.PointCoeff) from hQ]
    exact hm
  exact b := by
    constructor
    · intro hb
      refine ⟨⟨(b : E.PointCoeff), AddSubgroup.torsionBy.nsmul_iff.2 ?_⟩, Subtype.ext rfl⟩
      exact congrArg Subtype.val hb
    · rintro ⟨a, rfl⟩
      exact Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 a.2)

/-- The sequence restricted to `G_K`. Kind: definition. -/
abbrev twoPowerSequence (n : ℕ) :=
  (twoPowerSequenceQ E n).restrict (galK r)

/-- The connecting map of the restricted sequence from `H⁰(G_K, E[2^∞])`. Kind: definition. -/
abbrev deltaInf (n : ℕ) := (twoPowerSequence r E n).explicitDelta0

/-- The finite-to-infinite map is the degree-one map of the restricted sequence (PROVED). -/
theorem levelToInfinite_eq (n : ℕ) :
    levelToInfinite r E n = explicitCoeff1 (galK r) (E.TorsionCoeff (2 ^ n))
      (twoPowerSequence r E n).inclDistribMulActionHom continuous_of_discreteTopology :=
  rfl

/-- `E[2^∞] → E` on invariants. Kind: definition. -/
abbrev torsInv : H0 (galK r) (TwoPowerCoeff E) →+ pointsK r E :=
  explicitCoeff0 (galK r) (TwoPowerCoeff E) (infiniteCoeffIncl r E)

/-- **Naturality**: `δₙ ∘ (E[2^∞] → E) = δ_∞` on `H⁰(G_K, E[2^∞])` (PROVED). -/
theorem levelDelta_torsInv (n : ℕ) (t : H0 (galK r) (TwoPowerCoeff E)) :
    levelDelta r E n (torsInv r E t) = deltaInf r E n t := by
  have h := (twoPowerSequence r E n).explicitDelta0_coeffMap (levelSequence r E n)
    (DistribMulActionHom.id (galK r)) (infiniteCoeffIncl r E) (infiniteCoeffIncl r E)
    (fun a => rfl) (fun b => rfl) t
  have hid : explicitCoeff1 (galK r) (E.TorsionCoeff (2 ^ n)) (DistribMulActionHom.id (galK r))
      continuous_of_discreteTopology = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H c => rfl
  rw [hid] at h
  exact h.symm

omit [E.IsElliptic] in
/-- The image of `E(K)[2^∞]` in `E(K)` is torsion. Kind: PROVED. -/
theorem torsInv_isOfFinAddOrder (t : H0 (galK r) (TwoPowerCoeff E)) :
    IsOfFinAddOrder (torsInv r E t) := by
  obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.1 (t : TwoPowerCoeff E).2
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 ^ m, by positivity, ?_⟩
  apply Subtype.ext
  change (2 ^ m) • ((t : TwoPowerCoeff E) : E.PointCoeff) = 0
  exact hm

/-- **A finite Kummer class dying in `H¹(G_K, E[2^∞])`** (PROVED): then `P = 2ⁿ Q + t` with `t`
torsion. -/
theorem levelToInfinite_levelDelta_eq_zero (n : ℕ) (P : pointsK r E)
    (h : levelToInfinite r E n (levelDelta r E n P) = 0) :
    ∃ Q t : pointsK r E, IsOfFinAddOrder t ∧ P = (2 ^ n) • Q + t := by
  have hmem : levelDelta r E n P ∈ (deltaInf r E n).range := by
    rw [(twoPowerSequence r E n).explicitLongExact_H1A, AddMonoidHom.mem_ker]
    exact h
  obtain ⟨t, ht⟩ := hmem
  have h0 : levelDelta r E n (P - torsInv r E t) = 0 := by
    rw [map_sub, levelDelta_torsInv, ht, sub_self]
  have hk : P - torsInv r E t ∈ (levelDelta r E n).ker := h0
  rw [levelDelta_ker] at hk
  obtain ⟨Q, hQ⟩ := hk
  refine ⟨Q, torsInv r E t, torsInv_isOfFinAddOrder r E t, ?_⟩
  rw [show (nsmulAddMonoidHom (2 ^ n) : pointsK r E →+ pointsK r E) Q = (2 ^ n) • Q from rfl]
    at hQ
  rw [hQ]
  abel

/-- **On a free generator, the `2`-primary Kummer classes detect `2ⁿ ∣ a`** (PROVED). -/
theorem dvd_of_kummer_eq_zero {g : pointsK r E} (hg : ¬ IsOfFinAddOrder g)
    (hgen : ∀ P : pointsK r E, ∃ c : ℤ, IsOfFinAddOrder (P - c • g)) (n : ℕ) (a : ℤ)
    (h : levelToInfinite r E n (levelDelta r E n (a • g)) = 0) : (2 ^ n : ℤ) ∣ a := by
  obtain ⟨Q, t, ht, hQ⟩ := levelToInfinite_levelDelta_eq_zero r E n (a • g) h
  obtain ⟨c, hc⟩ := hgen Q
  -- `(a − 2ⁿ c) g = 2ⁿ (Q − c g) + t` is torsion
  have htor : IsOfFinAddOrder ((a - 2 ^ n * c) • g) := by
    have e : (a - 2 ^ n * c) • g = ((2 ^ n : ℕ) : ℤ) • (Q - c • g) + t := by
      rw [sub_smul, mul_smul, hQ, smul_sub, natCast_zsmul]
      push_cast
      abel
    rw [e]
    exact hc.zsmul.add ht
  by_contra hd
  have hne : a - 2 ^ n * c ≠ 0 := fun h0 => hd ⟨c, by linarith⟩
  obtain ⟨m, hm, hm0⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.1 htor
  exact hg (isOfFinAddOrder_iff_zsmul_eq_zero.2
    ⟨m * (a - 2 ^ n * c), mul_ne_zero hm hne, by rw [mul_smul]; exact hm0⟩)

/-! ### The `2`-primary Kummer map on `E(K) × ℚ₂/ℤ₂` -/

/-- Every element of `ℚ₂/ℤ₂` is `[a/2ⁿ]` (PROVED). -/
theorem exists_rep (d : Q2Z2) : ∃ (n : ℕ) (a : ℤ),
    (QuotientAddGroup.mk ((a : ℚ_[2]) / 2 ^ n) : Q2Z2) = d := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective d
  by_cases hq : q = 0
  · exact ⟨0, 0, by simp [hq]⟩
  set n : ℕ := (-q.valuation).toNat
  have hn : -q.valuation ≤ (n : ℤ) := Int.self_le_toNat _
  have hz : ‖(2 : ℚ_[2]) ^ n * q‖ ≤ 1 := by
    rw [norm_mul, show ((2 : ℚ_[2]) ^ n) = ((2 : ℕ) : ℚ_[2]) ^ n by norm_num, Padic.norm_p_pow,
      Padic.norm_eq_zpow_neg_valuation hq, ← zpow_add₀ (by norm_num)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  set z : ℤ_[2] := ⟨(2 : ℚ_[2]) ^ n * q, hz⟩
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  refine ⟨n, (z.appr n : ℤ), ?_⟩
  rw [QuotientAddGroup.eq]
  have hw' := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hw
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_sub, PadicInt.coe_natCast] at hw'
  have hzq : (z : ℚ_[2]) = 2 ^ n * q := rfl
  rw [hzq] at hw'
  push_cast at hw'
  have h2 : (2 : ℚ_[2]) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have e : -(((z.appr n : ℤ) : ℚ_[2]) / 2 ^ n) + q = ((w : ℤ_[2]) : ℚ_[2]) := by
    field_simp
    push_cast
    linear_combination -hw'
  change ‖-(((z.appr n : ℤ) : ℚ_[2]) / 2 ^ n) + q‖ ≤ 1
  rw [e]
  exact w.2

/-- `[a/2ⁿ] = 0` when `2ⁿ ∣ a` (PROVED). -/
theorem rep_zero {n : ℕ} {a : ℤ} (h : (2 ^ n : ℤ) ∣ a) :
    (QuotientAddGroup.mk ((a : ℚ_[2]) / 2 ^ n) : Q2Z2) = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [QuotientAddGroup.eq_zero_iff]
  have h2 : (2 : ℚ_[2]) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have e : (((2 ^ n * c : ℤ)) : ℚ_[2]) / 2 ^ n = ((c : ℤ_[2]) : ℚ_[2]) := by
    push_cast
    field_simp
  change ‖(((2 ^ n * c : ℤ)) : ℚ_[2]) / 2 ^ n‖ ≤ 1
  rw [e]
  exact PadicInt.norm_le_one _

/-- The chosen level of `d = [a/2ⁿ]`. Kind: definition. -/
def repN (d : Q2Z2) : ℕ := (exists_rep d).choose

/-- The chosen numerator of `d = [a/2ⁿ]`. Kind: definition. -/
def repA (d : Q2Z2) : ℤ := (exists_rep d).choose_spec.choose

theorem rep_spec (d : Q2Z2) :
    (QuotientAddGroup.mk ((repA d : ℚ_[2]) / 2 ^ repN d) : Q2Z2) = d :=
  (exists_rep d).choose_spec.choose_spec

/-- **The `2`-primary Kummer image of `P ⊗ d`** in `Sel_{2^∞}(E/K)`: for `d = [a/2ⁿ]` (the chosen
representative), `levelToInfinite n (δₙ(a P))`. Kind: definition. -/
def kummerInf (P : pointsK r E) (d : Q2Z2) : selmerK r E :=
  ⟨levelToInfinite r E (repN d) (levelDelta r E (repN d) (repA d • P)), by
    rw [mem_selmerK, inclK_infinite_levelDelta]
    exact zero_mem _⟩

/-- **`hδ` for a free generator** (PROVED; Silverman X.4.2 at every level and the sequence
`0 → E[2ⁿ] → E[2^∞] → E[2^∞] → 0`): `kummerInf g d = 0 → d = 0`. -/
theorem kummerInf_injective_gen {g : pointsK r E} (hg : ¬ IsOfFinAddOrder g)
    (hgen : ∀ P : pointsK r E, ∃ c : ℤ, IsOfFinAddOrder (P - c • g)) (d : Q2Z2)
    (h : kummerInf r E g d = 0) : d = 0 := by
  have h0 := congrArg Subtype.val h
  have hd := dvd_of_kummer_eq_zero r E hg hgen (repN d) (repA d) h0
  rw [← rep_spec d]
  exact rep_zero hd

/-- **`hδ` through an identification of the points** (PROVED): for an additive equivalence
`ι : V ≃ E(K)` (the identification of a model of the rational points with the fixed-geometric-point
model; `ι` and `hcomp` are PROVED, `kc_hcomp_central`) and a free generator `gen` of `V` modulo
torsion, the Kummer map `δ = kummerInf ∘ ι` satisfies `δ(gen, d) = 0 → d = 0`. -/
theorem hδ_of_equiv {V : Type} [AddCommGroup V] (ι : V ≃+ pointsK r E) {gen : V}
    (hg : ¬ IsOfFinAddOrder gen) (hgen : ∀ P : V, ∃ c : ℤ, IsOfFinAddOrder (P - c • gen))
    (d : Q2Z2) (h : kummerInf r E (ι gen) d = 0) : d = 0 := by
  refine kummerInf_injective_gen r E (fun ht => hg ?_) (fun P => ?_) d h
  · obtain ⟨m, hm, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 ht
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ι.injective ?_⟩
    rw [map_nsmul, hm0, map_zero]
  · obtain ⟨c, hc⟩ := hgen (ι.symm P)
    refine ⟨c, ?_⟩
    obtain ⟨m, hm, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hc
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
    have := congrArg ι hm0
    rwa [map_nsmul, map_sub, map_zsmul, AddEquiv.apply_symm_apply, map_zero] at this

end ZInQ.Contrib.CloudB3E2.KummerInj
