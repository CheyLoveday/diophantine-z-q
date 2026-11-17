import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8

/-! h33-dict, part A (scratch test): TYZ Prop. 3.2(4) in its used form, proved from `hCM`, and the
uniformization of `ε` over the representatives `Φ`. -/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.H33Dict

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.Contrib.TYZGenus.CMBridge ZInQ.Contrib.TYZGenus.TYZ35 ZInQ.Contrib.TYZDecomp
  ZInQ.RouteK.Redei ZInQ.Literature ZInQ.Contrib.TYZGenus.TYZSplit

/-! ## §A1. The CM inputs from `hCM` -/

/-- The CM inputs of the TYZ chain (algebraicity, field of definition, Shimura reciprocity on `Pic`) from
the printed main theorem of CM `hCM` and the proved theta identity (theta-wp8, hx-used). -/
theorem cmInputs (hCM : T5Glue.ShimuraMainCM) : X0ModuliUsed.CMInputs :=
  X0ModuliUsed.cmInputs_of (X0EtaRoute.srAt_x ThetaWP8.xEtaWeierstrass hCM)
    (X0EtaRoute.srAt_y ThetaWP8.xEtaWeierstrass hCM)

/-- `Gal(H_{n,4}/H_n)` moves `z_n` only by `ℤτ(1)` (glue KER of the kernel), from the CM inputs. -/
theorem kerFix (h : X0ModuliUsed.CMInputs) : T321.KerFixesZnMod :=
  T321.kerFixesZnMod
    (ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of h.pic ZInQ.Contrib.TYZGenus.Shimura.etaModelFricke)
    (T321.tyzThm36OneFive_of h.pic h.alg T321.wNegatesI) (X0ModuliUsed.znOverH4_of_field h.field)

/-! ## §A2. Restrictions to `H_n` -/

section General

variable {K : Type} [Field K] [NumberField K]

/-- If the Artin symbol of `c ∈ Pic O` fixes the Hilbert class field, then `c ↦ 1` in `Cl(K)` (stated for a
general `K`: at `K = ℚ(√−n)` the rewrite by `restrict_ringClassArtinEquiv` times out in the kernel). -/
theorem picToMax_eq_one_of_fix (O : NumberFieldOrder K) (c : Pic O)
    (h : ∀ x : ringClassField (maximalNumberFieldOrder K),
      ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) =
        IntermediateField.inclusion (ringClassField_maximal_le O) x) :
    picToMax O c = 1 := by
  apply (ringClassArtinEquiv (maximalNumberFieldOrder K)).injective
  rw [map_one]
  ext x
  have e := h x
  rw [← restrictNormalHom_inclusion_apply, restrict_ringClassArtinEquiv] at e
  have e' := (IntermediateField.inclusion (ringClassField_maximal_le O)).injective e
  rw [e']
  rfl

end General

section Restr

variable {n : ℕ} [NeZero n]

theorem restricts_inv_mul {ρ ρ' : GalQ} {t : ClG n} (h : Restricts n ρ t) (h' : Restricts n ρ' t) :
    Restricts n (ρ'⁻¹ * ρ) 1 := by
  intro x
  rw [AlgEquiv.mul_apply, h x, ← h' x]
  simp

theorem restricts_agree {ρ ρ' : GalQ} {t : ClG n} (h : Restricts n ρ t) (h' : Restricts n ρ' t) :
    ∀ x ∈ hilbertBar n, ρ x = ρ' x := by
  intro x hx
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := h ⟨y, hy⟩
  have h2 := h' ⟨y, hy⟩
  change ρ (embed n y) = ρ' (embed n y)
  exact h1.trans h2.symm

/-- **An automorphism acting trivially on `H_n` and as `a ∈ Pic(𝒪_{n,4})` on `H_{n,4}` has `a ↦ 1` in
`Cl(K_n)`** (compatibility of the Artin maps, ring-class's `restrict_ringClassArtinEquiv`). -/
theorem picToMax_eq_one {σ : GalQ} (h1 : Restricts n σ 1) {a : Pic (O4 n)} (ha : ActsAsArtin4 σ n a) :
    picToMax (O4 n) a = 1 := by
  have hle := ringClassField_maximal_le (O4 n)
  refine picToMax_eq_one_of_fix (O4 n) a fun x => ?_
  have hc : ((IntermediateField.inclusion hle x : H4 n) : SeparableClosure (QNeg n)) =
      ((x : hilbertField n) : SeparableClosure (QNeg n)) := IntermediateField.coe_inclusion hle x
  have e1 := ha (IntermediateField.inclusion hle x)
  have e2 : σ (embed n ((x : hilbertField n) : SeparableClosure (QNeg n))) =
      embed n ((x : hilbertField n) : SeparableClosure (QNeg n)) := by
    rw [h1 x, AlgEquiv.one_apply]
  rw [hc] at e1
  apply Subtype.ext
  rw [hc]
  apply (embed n).injective
  rw [← e1, e2]

end Restr

/-! ## §A3. TYZ Proposition 3.2(4), used form -/

theorem tauG_two_eq : tauG 2 = pt00 := by
  rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul, ptT_add_self]

theorem tauG_two_tors : IsOfFinAddOrder (tauG 2) :=
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, by rw [two_nsmul, tauG_two_eq, pt00_add_self]⟩

/-- **TYZ Proposition 3.2(4), the form the uniformization of `ε` uses**: for squarefree `n ≡ 5, 7 (mod 8)`
two lifts `ρ, ρ' ∈ Gal(ℚ̄/ℚ)` of the same `t ∈ Cl_n = Gal(H_n/K_n)` move `z_n` (`TYZ35.basePt n`) to
points that differ by a torsion point. TYZ Prop. 3.2(4) (`CM point1`, arXiv:1411.4728v1 about L1261, as
quoted in tyz-split.md and in the docstring of `TYZSplit.IsPhi`: `2z_n ∈ A(H_n)`) gives it at once; here it
is proved from the CM inputs: `Gal(H_{n,4}/H_n)` moves `z_n` by `ℤτ(1)` for `n ≡ 5` (kernel glue KER, from
Shimura reciprocity, TYZ Thm 3.6(1) in Lean and `z_n ∈ A(H_{n,4})`), and `z_n ∈ A(H_n)` for `n ≡ 7`. -/
def TYZProp324Used : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) → ∀ (t : ClG n) (ρ ρ' : GalQ),
    Restricts n ρ t → Restricts n ρ' t → IsOfFinAddOrder (galPt ρ (basePt n) - galPt ρ' (basePt n))

theorem tyzProp324Used_of (h : X0ModuliUsed.CMInputs) : TYZProp324Used := by
  intro n hn0 hsq hn8 t ρ ρ' hρ hρ'
  rcases hn8 with h5 | h7
  · have hb : basePt n = tyzZn n := by simp [basePt, h5]
    rw [hb]
    have hσ := restricts_inv_mul hρ hρ'
    have hω : (ρ'⁻¹ * ρ) (T321.omegaBar n) = T321.omegaBar n :=
      restricts_fix_sqrt_negn hσ T321.omegaBar_sq
    obtain ⟨a, ha⟩ := T321.exists_acts4_of_fix hω
    have hpa := picToMax_eq_one hσ ha
    obtain ⟨j, hj⟩ := kerFix h n hn0 h5 hsq a hpa _ ha
    have hρe : ρ = ρ' * (ρ'⁻¹ * ρ) := by group
    have : galPt ρ (tyzZn n) - galPt ρ' (tyzZn n) = j • tauG 2 := by
      conv_lhs => rw [hρe, galPt_mul, hj, map_add, map_zsmul, T321.galPt_tauG_two]
      abel
    rw [this]
    exact tauG_two_tors.zsmul
  · have hb : basePt n = tyzZ7 n := by
      have : n % 8 ≠ 5 := by omega
      simp [basePt, this]
    rw [hb]
    have hz := cmFieldOfDefinition7_of h.field n h7 hsq
    rw [galPt_congr (restricts_agree hρ hρ') hz, sub_self]
    exact IsOfFinAddOrder.zero

end ZInQ.Contrib.TYZGenus.H33Dict

#print axioms ZInQ.Contrib.TYZGenus.H33Dict.tyzProp324Used_of
