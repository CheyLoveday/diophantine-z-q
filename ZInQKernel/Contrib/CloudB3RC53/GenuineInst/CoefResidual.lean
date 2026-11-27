import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefDerivative
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity

/-!
# Genuine instantiations, part 19: the residual module of the actual `M_i` is `𝔽₂²`

Manuscript `diophantine_zq.tex`, tex 2724–2727 (`M_i = (T_2E ⊗ A_i)(α_i)`, `A_i = (ℤ/2^i)[t]/t^i`)
and tex 4479–4480 (the residual representation `W = E[2]`, trivial since `E[2]` is rational).

The residual module of `M_i` is `𝔽₂ ⊗_{A_i} M_i`, along the residue map `ε : A_i → 𝔽₂`
(`2 ↦ 0`, `t ↦ 0`). Here:

* `resEps`: the residue map (`i ≠ 0`); the units of `A_i` go to `1`, so the twist `α_i` dies;
* `resCancel`: `𝔽₂ ⊗_{A_i} (A_i ⊗_ℤ T) ≅ 𝔽₂ ⊗_ℤ T ≅ T / 2T` (`cancelBaseChange`,
  `quotTensorEquivQuotSMul`);
* `resCancel_resAct`: under `resCancel` the residual action `id ⊗ α(g)(id ⊗ g)` is the action of
  `g` on `T / 2T` (the twist dies since `ε(α(g)) = 1`);
* `halfEquiv`: `P[2m] / 2P[2m] ≅ P[2]` (multiplication by `m`) for an abelian group `P` with
  `|P[2m]| = (2m)²`, `|P[m]| = m²`, `|P[2]| = 4` (counting kernels and images);
* `residualEquiv`: for the actual `M_{j+1} = Mcoef K S W (j+1) α`,
  `𝔽₂ ⊗_{A_{j+1}} M_{j+1} ≅ E(K_S)[2]`, `G_{K,S}`-equivariantly (`residualEquiv_resAct`), given
  `FullTorsion` at `2^{j+1}`, `2^j` and `2` (RC28's Néron–Ogg–Shafarevich GLUE hypothesis);
* `torsTwoEquiv`, `residualFin2`: `E(K_S)[2] ≅ 𝔽₂²`, hence `𝔽₂ ⊗_{A_{j+1}} M_{j+1} ≅ 𝔽₂²`; with
  trivial Galois action on `E(K_S)[2]` (tex 4479–4480) the residual action is trivial in these
  coordinates (`residualFin2_resAct`); `residualLinearFin2`: the same as an `𝔽₂`-linear
  equivalence;
* `ResidualCoefModuleF2` (node, PROVED): the combined statement;
* Non-vacuity (`residualFin2_hyps_cubicCurve`): for `y² = (x − e₁)(x − e₂)(x − e₃)` with distinct
  `e_k ∈ K` the hypotheses hold at `j = 0` (`smul_torsTwo_cubicCurve`: trivial action on
  `E(K_S)[2]`).

**Classification.** Definitions and PROVED statements; the only hypotheses are `FullTorsion`
(GLUE, as in RC28) and, for `residualFin2_resAct`, the trivial action on `E(K_S)[2]`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open TensorProduct ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

section Residue

variable (i : ℕ) [NeZero i]

/-- **The residue map** `ε : A_i = (ℤ/2^i)[t]/t^i → 𝔽₂`, `2 ↦ 0`, `t ↦ 0`. -/
def resEps : Acoef i →+* ZMod 2 :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom (ZMod.castHom (dvd_pow_self 2 (NeZero.ne i)) (ZMod 2)) 0)
    (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [NeZero.ne i])

/-- `A_i → 𝔽₂` as an algebra. -/
instance algebraAcoefZModTwo : Algebra (Acoef i) (ZMod 2) := (resEps i).toAlgebra

/-- Every unit of `A_i` reduces to `1` (`𝔽₂ˣ` is trivial). -/
theorem resEps_unit (u : (Acoef i)ˣ) : resEps i u = 1 := by
  have h0 : resEps i u ≠ 0 := (u.isUnit.map _).ne_zero
  generalize resEps i u = x at h0 ⊢
  fin_cases x
  · exact absurd rfl h0
  · rfl

end Residue

section Cancel

variable (i : ℕ) [NeZero i] {G : Type} [Group G] (α : G →* (Acoef i)ˣ) (T : Type)
  [AddCommGroup T] [DistribMulAction G T]

/-- **The residual module** `𝔽₂ ⊗_{A_i} (A_i ⊗_ℤ T)(α)` of the coefficient module. -/
abbrev ResMod2 : Type := ZMod 2 ⊗[Acoef i] CoefMod (Acoef i) α T

/-- The action of `g` on the residual module: `id ⊗ (α(g) · (id ⊗ g))`. -/
def resAct (g : G) : ResMod2 i α T →ₗ[Acoef i] ResMod2 i α T :=
  LinearMap.lTensor (ZMod 2) (CoefMod.act (Acoef i) α T g)

/-- `ℤ ⧸ (2) ≅ 𝔽₂` as `ℤ`-modules. -/
def intQuotTwo : (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) ≃ₗ[ℤ] ZMod 2 :=
  (Int.quotientSpanNatEquivZMod 2).toIntAlgEquiv.toLinearEquiv

/-- **`𝔽₂ ⊗_{A_i} (A_i ⊗_ℤ T) ≅ T / 2T`** (additively). -/
def resCancel : ResMod2 i α T ≃+ T ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • (⊤ : Submodule ℤ T)) :=
  ((LinearEquiv.lTensor (ZMod 2) (CoefMod.equiv (Acoef i) α T).symm).toAddEquiv.trans
    (AlgebraTensorModule.cancelBaseChange ℤ (Acoef i) (ZMod 2) (ZMod 2) T).toAddEquiv).trans
    (((TensorProduct.congr intQuotTwo.symm (LinearEquiv.refl ℤ T)).trans
      (quotTensorEquivQuotSMul T (Ideal.span {((2 : ℕ) : ℤ)}))).toAddEquiv)

theorem intQuotTwo_symm (z : ZMod 2) :
    intQuotTwo.symm z = Ideal.Quotient.mk (Ideal.span {((2 : ℕ) : ℤ)}) (z.val : ℤ) := by
  apply intQuotTwo.injective
  rw [LinearEquiv.apply_symm_apply]
  change z = Int.quotientSpanNatEquivZMod 2 (Ideal.Quotient.mk _ (z.val : ℤ))
  change z = ((z.val : ℤ) : ZMod 2)
  simp

omit [DistribMulAction G T] in
/-- `resCancel` on a pure tensor: `c ⊗ (a ⊗ t) ↦ ε(a)c · [t]`. -/
theorem resCancel_tmul (c : ZMod 2) (a : Acoef i) (t : T) :
    resCancel i α T (c ⊗ₜ CoefMod.equiv (Acoef i) α T (a ⊗ₜ t)) =
      Submodule.Quotient.mk (((resEps i a * c).val : ℤ) • t) := by
  have h1 : (LinearEquiv.lTensor (ZMod 2) (CoefMod.equiv (Acoef i) α T).symm)
      (c ⊗ₜ CoefMod.equiv (Acoef i) α T (a ⊗ₜ t)) = c ⊗ₜ (a ⊗ₜ t) := by
    rw [LinearEquiv.lTensor_tmul, LinearEquiv.symm_apply_apply]
  change ((TensorProduct.congr intQuotTwo.symm (LinearEquiv.refl ℤ T)).trans
    (quotTensorEquivQuotSMul T (Ideal.span {((2 : ℕ) : ℤ)})))
      (AlgebraTensorModule.cancelBaseChange ℤ (Acoef i) (ZMod 2) (ZMod 2) T
        ((LinearEquiv.lTensor (ZMod 2) (CoefMod.equiv (Acoef i) α T).symm)
          (c ⊗ₜ CoefMod.equiv (Acoef i) α T (a ⊗ₜ t)))) = _
  rw [h1, AlgebraTensorModule.cancelBaseChange_tmul, LinearEquiv.trans_apply, congr_tmul,
    LinearEquiv.refl_apply, Algebra.smul_def, intQuotTwo_symm, quotTensorEquivQuotSMul_mk_tmul]
  rfl

/-- The action of `g` on `T / 2T`. -/
def actQ (g : G) : T ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • (⊤ : Submodule ℤ T)) →ₗ[ℤ]
    T ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • (⊤ : Submodule ℤ T)) :=
  Submodule.mapQ _ _ (DistribSMul.toAddMonoidHom T g).toIntLinearMap (by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [Submodule.mem_comap, AddMonoidHom.coe_toIntLinearMap, DistribSMul.toAddMonoidHom_apply,
      smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top)

/-- **The twist `α` disappears on the residual module**: `resCancel` intertwines the action
`id ⊗ α(g)(id ⊗ g)` with the action of `g` on `T / 2T`. PROVED. -/
theorem resCancel_resAct (g : G) (x : ResMod2 i α T) :
    resCancel i α T (resAct i α T g x) = actQ T g (resCancel i α T x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul c m =>
    obtain ⟨m, rfl⟩ := (CoefMod.equiv (Acoef i) α T).surjective m
    induction m using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [map_add, tmul_add, map_add, map_add, hx, hy, map_add, map_add]
    | tmul a t =>
      have h1 : resAct i α T g (c ⊗ₜ CoefMod.equiv (Acoef i) α T (a ⊗ₜ t)) =
          c ⊗ₜ CoefMod.equiv (Acoef i) α T ((((α g : (Acoef i)ˣ) : Acoef i) * a) ⊗ₜ (g • t)) := by
        rw [resAct, LinearMap.lTensor_tmul, ← CoefMod.smul_tmul]
        rfl
      rw [h1, resCancel_tmul, resCancel_tmul, map_mul, resEps_unit, one_mul]
      rw [smul_comm]
      rfl

end Cancel

section Halving

/-! ### `T / 2T ≅ T[2]` for `T = P[2m]` with full torsion -/

variable {P : Type} [AddCommGroup P] {n : ℕ} (m : ℕ)

/-- Multiplication by `m`, `P[2m] → P[2]`. -/
def halfMap (hnm : n = 2 * m) : AddSubgroup.torsionBy P (n : ℤ) →+ AddSubgroup.torsionBy P ((2 : ℕ) : ℤ) :=
  AddMonoidHom.mk' (fun x => ⟨m • (x : P), by
    rw [AddSubgroup.torsionBy.nsmul_iff, smul_smul, ← hnm]
    exact AddSubgroup.torsionBy.nsmul_iff.mp x.2⟩)
    (fun x y => Subtype.ext (by simp))

theorem coe_halfMap (hnm : n = 2 * m) (x : AddSubgroup.torsionBy P (n : ℤ)) :
    (halfMap m hnm x : P) = m • (x : P) := rfl

/-- Doubling, `P[2m] → P`. -/
def dblMap (n : ℕ) : AddSubgroup.torsionBy P (n : ℤ) →+ P :=
  AddMonoidHom.mk' (fun x => 2 • (x : P)) (fun x y => by simp)

/-- The kernel of `halfMap` is `P[m]`. -/
def kerHalfEquiv (hnm : n = 2 * m) : (halfMap (P := P) m hnm).ker ≃ AddSubgroup.torsionBy P (m : ℤ) where
  toFun x := ⟨x.1.1, by
    have h := congrArg Subtype.val (AddMonoidHom.mem_ker.mp x.2)
    exact AddSubgroup.torsionBy.nsmul_iff.mpr h⟩
  invFun y := ⟨⟨y.1, by
      rw [AddSubgroup.torsionBy.nsmul_iff, hnm, ← smul_smul,
        AddSubgroup.torsionBy.nsmul_iff.mp y.2, smul_zero]⟩,
    AddMonoidHom.mem_ker.mpr (Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp y.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The kernel of `dblMap` is `P[2]`. -/
def kerDblEquiv (hnm : n = 2 * m) : (dblMap (P := P) n).ker ≃ AddSubgroup.torsionBy P ((2 : ℕ) : ℤ) where
  toFun x := ⟨x.1.1, AddSubgroup.torsionBy.nsmul_iff.mpr (AddMonoidHom.mem_ker.mp x.2)⟩
  invFun y := ⟨⟨y.1, by
      rw [AddSubgroup.torsionBy.nsmul_iff, hnm, mul_comm, ← smul_smul,
        AddSubgroup.torsionBy.nsmul_iff.mp y.2, smul_zero]⟩,
    AddMonoidHom.mem_ker.mpr (AddSubgroup.torsionBy.nsmul_iff.mp y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {m}

theorem natCard_range_of_ker {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    {a k : ℕ} (hA : Nat.card A = a) (hk : Nat.card f.ker = k) : Nat.card f.range * k = a := by
  rw [← hA, ← hk, ← AddSubgroup.index_ker, mul_comm]
  exact AddSubgroup.card_mul_index f.ker

/-- **`halfMap` is onto `P[2]`** when `|P[2m]| = (2m)²`, `|P[m]| = m²`, `|P[2]| = 4`. PROVED. -/
theorem halfMap_surjective (hnm : n = 2 * m) (hm : m ≠ 0)
    (hT : Nat.card (AddSubgroup.torsionBy P (n : ℤ)) = n ^ 2)
    (hM : Nat.card (AddSubgroup.torsionBy P (m : ℤ)) = m ^ 2)
    (h2 : Nat.card (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) = 2 ^ 2) :
    Function.Surjective (halfMap (P := P) m hnm) := by
  have hr := natCard_range_of_ker (halfMap (P := P) m hnm) hT
    ((Nat.card_congr (kerHalfEquiv m hnm)).trans hM)
  have hm2 : 0 < m ^ 2 := by positivity
  have hcard : Nat.card (halfMap (P := P) m hnm).range =
      Nat.card (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) := by
    rw [h2]
    apply Nat.eq_of_mul_eq_mul_right hm2
    rw [hr, hnm]
    ring
  have : Finite (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) := Nat.finite_of_card_ne_zero (by omega)
  exact AddMonoidHom.range_eq_top.mp (AddSubgroup.eq_top_of_card_eq _ hcard)

/-- **`P[m] = 2·P[2m]`** under the same cardinalities. PROVED. -/
theorem exists_two_nsmul_of_mem (hnm : n = 2 * m) (hm : m ≠ 0)
    (hT : Nat.card (AddSubgroup.torsionBy P (n : ℤ)) = n ^ 2)
    (hM : Nat.card (AddSubgroup.torsionBy P (m : ℤ)) = m ^ 2)
    (h2 : Nat.card (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) = 2 ^ 2)
    {y : P} (hy : y ∈ AddSubgroup.torsionBy P (m : ℤ)) :
    ∃ x : AddSubgroup.torsionBy P (n : ℤ), 2 • (x : P) = y := by
  have hr := natCard_range_of_ker (dblMap (P := P) n) hT
    ((Nat.card_congr (kerDblEquiv m hnm)).trans h2)
  have hle : (dblMap (P := P) n).range ≤ AddSubgroup.torsionBy P (m : ℤ) := by
    rintro _ ⟨x, rfl⟩
    change 2 • (x : P) ∈ _
    rw [AddSubgroup.torsionBy.nsmul_iff, smul_smul, mul_comm, ← hnm]
    exact AddSubgroup.torsionBy.nsmul_iff.mp x.2
  have hcard : Nat.card (AddSubgroup.torsionBy P (m : ℤ)) ≤ Nat.card (dblMap (P := P) n).range := by
    rw [hM]
    apply le_of_eq
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ 2 by norm_num)
    rw [hr, hnm]
    ring
  have : Finite (AddSubgroup.torsionBy P (m : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hM]; positivity)
  have heq := AddSubgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

/-- **`ker(halfMap) = 2·P[2m]`** as `ℤ`-submodules. PROVED. -/
theorem ker_halfMap (hnm : n = 2 * m) (hm : m ≠ 0)
    (hT : Nat.card (AddSubgroup.torsionBy P (n : ℤ)) = n ^ 2)
    (hM : Nat.card (AddSubgroup.torsionBy P (m : ℤ)) = m ^ 2)
    (h2 : Nat.card (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) = 2 ^ 2) :
    LinearMap.ker (halfMap (P := P) m hnm).toIntLinearMap =
      Ideal.span {((2 : ℕ) : ℤ)} • (⊤ : Submodule ℤ (AddSubgroup.torsionBy P (n : ℤ))) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hx
    have hy : (x : P) ∈ AddSubgroup.torsionBy P (m : ℤ) :=
      AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val hx)
    obtain ⟨z, hz⟩ := exists_two_nsmul_of_mem hnm hm hT hM h2 hy
    refine ⟨z, Submodule.mem_top, Subtype.ext ?_⟩
    rw [← hz, AddSubgroup.coe_zsmul, Nat.cast_ofNat, ofNat_zsmul]
  · rintro ⟨z, -, rfl⟩
    apply Subtype.ext
    rw [coe_halfMap, AddSubgroup.coe_zsmul, Nat.cast_ofNat, ofNat_zsmul, smul_smul, mul_comm, ← hnm,
      AddSubgroup.torsionBy.nsmul_iff.mp z.2]
    rfl

/-- **`P[2m] / 2P[2m] ≅ P[2]`** (multiplication by `m`), under the cardinalities `(2m)²`, `m²`,
`4`. PROVED. -/
def halfEquiv (hnm : n = 2 * m) (hm : m ≠ 0)
    (hT : Nat.card (AddSubgroup.torsionBy P (n : ℤ)) = n ^ 2)
    (hM : Nat.card (AddSubgroup.torsionBy P (m : ℤ)) = m ^ 2)
    (h2 : Nat.card (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) = 2 ^ 2) :
    (AddSubgroup.torsionBy P (n : ℤ) ⧸
        (Ideal.span {((2 : ℕ) : ℤ)} • (⊤ : Submodule ℤ (AddSubgroup.torsionBy P (n : ℤ))))) ≃ₗ[ℤ]
      AddSubgroup.torsionBy P ((2 : ℕ) : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (ker_halfMap hnm hm hT hM h2).symm).trans
    ((halfMap (P := P) m hnm).toIntLinearMap.quotKerEquivOfSurjective (halfMap_surjective hnm hm hT hM h2))

theorem halfEquiv_mk (hnm : n = 2 * m) (hm : m ≠ 0)
    (hT : Nat.card (AddSubgroup.torsionBy P (n : ℤ)) = n ^ 2)
    (hM : Nat.card (AddSubgroup.torsionBy P (m : ℤ)) = m ^ 2)
    (h2 : Nat.card (AddSubgroup.torsionBy P ((2 : ℕ) : ℤ)) = 2 ^ 2)
    (x : AddSubgroup.torsionBy P (n : ℤ)) :
    halfEquiv hnm hm hT hM h2 (Submodule.Quotient.mk x) = halfMap m hnm x := rfl

end Halving

section Actual

/-! ### The actual `M_i`: `𝔽₂ ⊗_{A_i} M_i ≅ E[2] ≅ 𝔽₂²` -/

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

omit [NumberField K] in
/-- Multiplication by `2^j`, `E[2^{j+1}] → E[2]`, is `G_{K,S}`-equivariant. PROVED. -/
theorem halfMap_smul (j : ℕ) (σ : GKS K S) (x : TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ)) :
    halfMap (2 ^ j) (pow_succ' 2 j) (σ • x) = σ • halfMap (2 ^ j) (pow_succ' 2 j) x := by
  apply Subtype.ext
  rw [coe_halfMap, coe_smul_torsS, coe_smul_torsS, coe_halfMap, map_nsmul]

variable (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ)

/-- **The residual module of the actual `M_{j+1}` is `E[2]`**: `𝔽₂ ⊗_{A_{j+1}} M_{j+1} ≅
E(K_S)[2]`, `c ⊗ (a ⊗ t) ↦ ε(a)c · 2^j t`, given that `E[2^{j+1}]`, `E[2^j]`, `E[2]` are defined
over `K_S` (`FullTorsion`, Néron–Ogg–Shafarevich GLUE as in RC28). -/
def residualEquiv (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2) :
    ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α ≃+ TorsS K S W ((2 : ℕ) : ℤ) :=
  (resCancel (j + 1) α (TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ))).trans
    (halfEquiv (pow_succ' 2 j) (pow_ne_zero j two_ne_zero) hT hM h2).toAddEquiv

omit [NumberField K] in
/-- **`residualEquiv` is `G_{K,S}`-equivariant**: the residual action of `σ` on
`𝔽₂ ⊗ M_{j+1}` (the twist `α` disappears) is the Galois action on `E[2]`. PROVED. -/
theorem residualEquiv_resAct (hT : FullTorsion K S W (2 ^ (j + 1)))
    (hM : FullTorsion K S W (2 ^ j)) (h2 : FullTorsion K S W 2) (σ : GKS K S)
    (x : ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α) :
    residualEquiv j α hT hM h2 (resAct (j + 1) α _ σ x) = σ • residualEquiv j α hT hM h2 x := by
  change halfEquiv (pow_succ' 2 j) (pow_ne_zero j two_ne_zero) hT hM h2
      (resCancel (j + 1) α _ (resAct (j + 1) α _ σ x)) =
    σ • halfEquiv (pow_succ' 2 j) (pow_ne_zero j two_ne_zero) hT hM h2 (resCancel (j + 1) α _ x)
  rw [resCancel_resAct]
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (resCancel (j + 1) α _ x)
  rw [← ht]
  exact halfMap_smul j σ t

variable (K S W) in
/-- **`E(K_S)[2] ≅ 𝔽₂²`** when `|E(K_S)[2]| = 4`. -/
def torsTwoEquiv (h2 : FullTorsion K S W 2) : TorsS K S W ((2 : ℕ) : ℤ) ≃+ (Fin 2 → ZMod 2) :=
  letI : Module (ZMod 2) (TorsS K S W ((2 : ℕ) : ℤ)) := AddSubgroup.torsionBy.zmodModule
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (TorsS K S W ((2 : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [show Nat.card _ = 2 ^ 2 from h2]; norm_num)
  haveI : Fintype (TorsS K S W ((2 : ℕ) : ℤ)) := Fintype.ofFinite _
  (LinearEquiv.ofFinrankEq (R := ZMod 2) (TorsS K S W ((2 : ℕ) : ℤ)) (Fin 2 → ZMod 2) (by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := TorsS K S W ((2 : ℕ) : ℤ))
    rw [← Nat.card_eq_fintype_card, show Nat.card _ = 2 ^ 2 from h2, ZMod.card] at hc
    rw [Module.finrank_fin_fun]
    exact (Nat.pow_right_injective le_rfl hc).symm)).toAddEquiv

/-- **The residual module of the actual `M_{j+1}` is `𝔽₂²`**: `𝔽₂ ⊗_{A_{j+1}} M_{j+1} ≅ 𝔽₂²`
(additively), under `FullTorsion` at `2^{j+1}`, `2^j`, `2`. -/
def residualFin2 (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2) :
    ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α ≃+ (Fin 2 → ZMod 2) :=
  (residualEquiv j α hT hM h2).trans (torsTwoEquiv K S W h2)

omit [NumberField K] in
/-- **The residual representation is trivial when `E[2]` is rational** (tex 4479–4480): if
`G_{K,S}` acts trivially on `E(K_S)[2]`, the residual action of every `σ` on `𝔽₂ ⊗ M_{j+1}` is the
identity in the coordinates `residualFin2`. PROVED. -/
theorem residualFin2_resAct (hT : FullTorsion K S W (2 ^ (j + 1)))
    (hM : FullTorsion K S W (2 ^ j)) (h2 : FullTorsion K S W 2)
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P) (σ : GKS K S)
    (x : ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α) :
    residualFin2 j α hT hM h2 (resAct (j + 1) α _ σ x) = residualFin2 j α hT hM h2 x := by
  change torsTwoEquiv K S W h2 (residualEquiv j α hT hM h2 (resAct (j + 1) α _ σ x)) =
    torsTwoEquiv K S W h2 (residualEquiv j α hT hM h2 x)
  rw [residualEquiv_resAct, htriv]

/-- **`𝔽₂ ⊗_{A_{j+1}} M_{j+1} ≅ 𝔽₂²` as `𝔽₂`-vector spaces** (`residualFin2` is additive between
`𝔽₂`-modules, hence `𝔽₂`-linear). -/
def residualLinearFin2 (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2) :
    ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofBijective ((residualFin2 j α hT hM h2).toAddMonoidHom.toZModLinearMap 2)
    (residualFin2 j α hT hM h2).bijective

omit [NumberField K] in
theorem residualLinearFin2_apply (hT : FullTorsion K S W (2 ^ (j + 1)))
    (hM : FullTorsion K S W (2 ^ j)) (h2 : FullTorsion K S W 2)
    (x : ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α) :
    residualLinearFin2 j α hT hM h2 x = residualFin2 j α hT hM h2 x := rfl

end Actual

section NonVacuity

/-! ### Non-vacuity: the hypotheses of `residualFin2_resAct` hold for `y² = (x−e₁)(x−e₂)(x−e₃)` -/

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **`G_{K,S}` acts trivially on `E(K_S)[2]`** for `E : y² = (x − e₁)(x − e₂)(x − e₃)` with
`e_k ∈ K`: a `2`-torsion point is `0` or `(e_k, 0)`. PROVED. -/
theorem smul_torsTwo_cubicCurve (e₁ e₂ e₃ : K) (σ : GKS K S)
    (P : TorsS K S (cubicCurve e₁ e₂ e₃) ((2 : ℕ) : ℤ)) : σ • P = P := by
  obtain ⟨Q, hQ⟩ := P
  apply Subtype.ext
  rw [coe_smul_torsS]
  rcases Q with _ | ⟨x, y, h⟩
  · exact map_zero _
  have h2Q : (2 : ℤ) • (Affine.Point.some _ _ h :
      ((cubicCurve e₁ e₂ e₃).baseChange (KS K S)).toAffine.Point) = 0 :=
    (Submodule.mem_torsionBy_iff _ _).mp hQ
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2Q
  have hy : y = 0 := by
    have h2y := h2Q.2
    simp only [Affine.negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃, cubicCurve, map_zero, zero_mul, sub_zero] at h2y
    have h2 : (2 : KS K S) ≠ 0 := by
      rw [← map_ofNat (algebraMap K (KS K S)) 2]
      exact (map_ne_zero _).mpr two_ne_zero
    have : (2 : KS K S) * y = 0 := by linear_combination h2y
    exact (mul_eq_zero.mp this).resolve_left h2
  subst hy
  have heq := h.1
  rw [Affine.equation_iff'] at heq
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, cubicCurve,
    map_zero, map_neg, map_add, map_mul] at heq
  have hfac : (x - algebraMap K (KS K S) e₁) * (x - algebraMap K (KS K S) e₂) *
      (x - algebraMap K (KS K S) e₃) = 0 := by linear_combination -heq
  have hx : ∃ e : K, x = algebraMap K (KS K S) e := by
    rcases mul_eq_zero.mp hfac with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · exact ⟨e₁, sub_eq_zero.mp h1⟩
      · exact ⟨e₂, sub_eq_zero.mp h2⟩
    · exact ⟨e₃, sub_eq_zero.mp h3⟩
  obtain ⟨e, rfl⟩ := hx
  rw [Affine.Point.map_some, Affine.Point.some.injEq]
  exact ⟨AlgHom.commutes _ e, map_zero _⟩

/-- **Non-vacuity of the hypotheses of `residualFin2_resAct`** (at `j = 0`): for every number
field `K`, every `S` and distinct `e₁, e₂, e₃ ∈ K`, the curve `y² = (x − e₁)(x − e₂)(x − e₃)`
satisfies `FullTorsion` at `2^1`, `2^0`, `2` and has trivial Galois action on `E(K_S)[2]`.
PROVED. -/
theorem residualFin2_hyps_cubicCurve {e₁ e₂ e₃ : K} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃)
    (h23 : e₂ ≠ e₃) :
    FullTorsion K S (cubicCurve e₁ e₂ e₃) (2 ^ (0 + 1)) ∧
      FullTorsion K S (cubicCurve e₁ e₂ e₃) (2 ^ 0) ∧ FullTorsion K S (cubicCurve e₁ e₂ e₃) 2 ∧
      ∀ (σ : GKS K S) (P : TorsS K S (cubicCurve e₁ e₂ e₃) ((2 : ℕ) : ℤ)), σ • P = P :=
  ⟨fullTorsion_two_cubicCurve h12 h13 h23, fullTorsion_one _,
    fullTorsion_two_cubicCurve h12 h13 h23, smul_torsTwo_cubicCurve e₁ e₂ e₃⟩

end NonVacuity

section Node

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex

/-- **Node: the residual module of the actual coefficient module is `𝔽₂²` with trivial action.**
Manuscript tex 2724–2727 (`M_i = (T_2E ⊗ A_i)(α_i)`) and tex 4479–4480 (the residual
representation is `E[2]`, trivial since `E[2]` is rational). Claim: for every number field `K`,
`S`, Weierstrass curve `W`, `i = j + 1 ≥ 1` and character `α : G_{K,S} → A_i^×`, if `E[2^i]`,
`E[2^{i-1}]`, `E[2]` are defined over `K_S` (`FullTorsion`) and `G_{K,S}` acts trivially on
`E(K_S)[2]`, then `𝔽₂ ⊗_{A_i} M_i ≅ 𝔽₂²` as `𝔽₂`-vector spaces, and every `σ ∈ G_{K,S}` acts as
the identity on it. Kind: PROVED (`residualCoefModuleF2_proof`); non-vacuity of the hypotheses:
`residualFin2_hyps_cubicCurve`. -/
def ResidualCoefModuleF2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (W : WeierstrassCurve K) (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ),
    FullTorsion K S W (2 ^ (j + 1)) → FullTorsion K S W (2 ^ j) → FullTorsion K S W 2 →
    (∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P) →
    ∃ e : ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α ≃ₗ[ZMod 2] (Fin 2 → ZMod 2),
      ∀ (σ : GKS K S) x, e (resAct (j + 1) α _ σ x) = e x

theorem residualCoefModuleF2_proof : ResidualCoefModuleF2 := by
  intro K _ _ S W j α hT hM h2 htriv
  exact ⟨residualLinearFin2 j α hT hM h2, fun σ x => residualFin2_resAct j α hT hM h2 htriv σ x⟩

end Node

end ZInQ.Contrib.CloudB3RC53.GenuineInst
