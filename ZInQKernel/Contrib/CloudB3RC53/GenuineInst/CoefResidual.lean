import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefDerivative

/-!
# Genuine instantiations, part 19: the residual module of the actual `M_i` is `𝔽₂²`

Manuscript `diophantine_zq.tex`, tex 2724–2727 (`M_i = (T_2E ⊗ A_i)(α_i)`, `A_i = (ℤ/2^i)[t]/t^i`)
and tex 4479–4480 (the residual representation `W = E[2]`, trivial since `E[2]` is rational).

The residual module of `M_i` is `𝔽₂ ⊗_{A_i} M_i`, along the residue map `ε : A_i → 𝔽₂`
(`2 ↦ 0`, `t ↦ 0`). Here:

* `resEps`: the residue map (`i ≠ 0`); the units of `A_i` go to `1`, so the twist `α_i` dies;
* `resCancel`: `𝔽₂ ⊗_{A_i} (A_i ⊗_ℤ T) ≅ 𝔽₂ ⊗_ℤ T ≅ T / 2T` (`cancelBaseChange`,
  `quotTensorEquivQuotSMul`);
* (later stages) `T / 2T ≅ E[2]` for `T = E[2^i]` with full torsion, and `E[2] ≅ 𝔽₂²` with trivial
  action when `E[2]` is rational.
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

end ZInQ.Contrib.CloudB3RC53.GenuineInst
