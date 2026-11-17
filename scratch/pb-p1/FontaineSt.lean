import ZInQKernel.Contrib.OneProof.PanBergerPst

/-!
# pb-p1: Fontaine's `B_st = B_cris[log [p̃]]` as printed in Berger's survey, and the two leaves of `r11r12` over it

Fontaine's rings, as Berger prints them in *An introduction to the theory of p-adic representations*
(arXiv:math/0210184v1, II.2.2 p. 11, II.2.3 p. 12, II.3.1 p. 13, II.3.3 p. 14-15), inside Mathlib's `B_dR`:

* `A_cris = {Σ a_n ω^n/n! : a_n ∈ A_inf, a_n → 0}` (`AcrisOf w`, for a generator `w` of `ker θ`), and
  `B_cris^+` the `ℚ_p`-algebra it generates (`BcrisPlusOf`);
* `B_cris = B_cris^+[1/t]`, `t = log [ε]` (`BcrisOf`);
* `B_st = B_cris[log [p̃]]` with `log [p̃] = log_p(p) − Σ (1 − [p̃]/p)^n/n`, `log_p(p) = 0` (`BstFOf`), which is
  bst-construct's `logPTilde`.

Proved: `A_cris ⊆ A_max` (`acrisOf_le_amaxOf`, from `p^n/n! ∈ ℤ_p`), `A_cris` does not depend on the generator
(`acrisOf_le`, `acrisOf_eq`), `B_st^{Fontaine} ⊆ B_st^{tree}` (`bstFOf_le`), and the basis form of admissibility
passes from a subring to a larger one (`isAdmissibleT_mono`). Hence Berger's theorem over Fontaine's ring gives the
current field `bergerPrintedV` (`bergerPrintedV_of_survey`), and Pan's theorem and Berger's theorem over Fontaine's
ring give `r11r12 : PanBerger` directly (`panBerger_of_F`), with no comparison of rings.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace FontaineSt

open Module PowerSeries Ideal
open scoped TensorProduct
open BergerBst BmaxOne
open PanBergerSplit (Ainf AinfP theta)

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## §1. `p^n/n! ∈ ℤ_p` -/

theorem factorial_val_le (n v m : ℕ) (hpm : ¬ p ∣ m) (h : n.factorial = p ^ v * m) : v ≤ n := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hval : padicValNat p n.factorial = v := by
    rw [h, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hpm, add_zero]
  have h1 := sub_one_mul_padicValNat_factorial (p := p) n
  rw [hval] at h1
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : v ≤ (p - 1) * v := Nat.le_mul_of_pos_left v h2
  omega

theorem exists_dpCoeff (n : ℕ) : ∃ e : ℤ_[p], (e : ℚ_[p]) * (n.factorial : ℚ_[p]) = (p : ℚ_[p]) ^ n := by
  obtain ⟨v, m, hpm, hvm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p hp.out.ne_one
  have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  have hv : v ≤ n := factorial_val_le p n v m hpm hvm
  refine ⟨(p : ℤ_[p]) ^ (n - v) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  have hum : ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (m : ℤ_[p]) = 1 := hu.val_inv_mul
  have hum' : (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hum
    rwa [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at this
  rw [hvm]
  push_cast
  calc ((p : ℚ_[p]) ^ (n - v) * (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) *
        ((p : ℚ_[p]) ^ v * (m : ℚ_[p]))
      = (p : ℚ_[p]) ^ (n - v) * (p : ℚ_[p]) ^ v *
          ((((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p])) := by ring
    _ = (p : ℚ_[p]) ^ n := by rw [hum', mul_one, ← pow_add, Nat.sub_add_cancel hv]

/-- `p^n/n! ∈ ℤ_p`. -/
def dpCoeff (n : ℕ) : ℤ_[p] := Classical.choose (exists_dpCoeff p n)

theorem dpCoeff_spec (n : ℕ) : (dpCoeff p n : ℚ_[p]) * (n.factorial : ℚ_[p]) = (p : ℚ_[p]) ^ n :=
  Classical.choose_spec (exists_dpCoeff p n)

/-- `1/n! = (p^n/n!) · p^{−n}` in `ℚ_p`. -/
theorem inv_factorial_eq (n : ℕ) :
    ((n.factorial : ℚ_[p]))⁻¹ = (dpCoeff p n : ℚ_[p]) * ((p : ℚ_[p])⁻¹) ^ n := by
  have h1 := dpCoeff_spec p n
  have hn' : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have he : (dpCoeff p n : ℚ_[p]) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact pow_ne_zero _ hp' h1.symm
  rw [inv_pow, ← h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ he, one_mul]

/-! ## §2. `A_cris`, `B_cris^+`, `B_cris`, `B_st` (Berger 2004, II.3.1 and II.3.3) -/

theorem algebraMap_mem_ith {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    algebraMap (Ainf p) (AinfP p) w ∈ Ith p := by
  have hk : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, rfl⟩ := hk
  rw [map_mul]
  have : algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ Ith p := by
    have h := xi'_mem p
    exact h
  exact Ideal.mul_mem_left _ _ this

/-- The divided-power series `Σ a_n X^n / n!` of `Σ a_n X^n`, over `W(𝓞_ℂ_p♭)[1/p]`. -/
def dpSeries (f : (Ainf p)⟦X⟧) : (AinfP p)⟦X⟧ :=
  PowerSeries.mk fun n => algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n f) *
    qpToLoc p (((n.factorial : ℕ) : ℚ_[p]))⁻¹

/-- **`A_cris`** (Berger, *An introduction to the theory of p-adic representations*, arXiv:math/0210184v1,
II.3.1 p. 13, with `ω` any generator of `ker θ`; Fontaine's `A_cris`): the elements `Σ a_n ω^n/n!` of `B_dR^+`,
`a_n ∈ A_inf = W(𝓞_ℂ_p♭)` tending to `0` `p`-adically, the series evaluated `ker θ`-adically. -/
def AcrisOf (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Set (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  {x | ∃ f ∈ restricted p, x = evalB p (algebraMap_mem_ith p hw) (dpSeries p f)}

/-- **`B_cris^+ = A_cris[1/p]`**: the `ℚ_p`-algebra generated by `A_cris` in `B_dR` (Berger 2004 II.3.1: the
`Σ x_n ω^n/n!` with `x_n ∈ B̃^+ = A_inf[1/p]`, `x_n → 0`). -/
def BcrisPlusOf (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' AcrisOf p w hw)

/-- **`B_cris = B_cris^+[1/t]`**, `t = log [ε₀]` (Berger 2004 II.3.1, II.2.3). -/
def BcrisOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' AcrisOf p w hw ∪ {Ring.inverse (tOf p h)})

/-- **Fontaine's `B_st = B_cris[log [p̃]] ⊆ B_dR`** (Berger 2004 II.3.3 p. 14-15: `B_st = B_cris[Y]` embedded in
`B_dR` by `Y ↦ log [p̃] = log_p(p) − Σ_{n ≥ 1} (1 − [p̃]/p)^n/n`, `p̃^(0) = p`, `log_p(p) = 0`; the tree's
`logPTilde`). -/
def BstFOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' AcrisOf p w hw ∪ {Ring.inverse (tOf p h)} ∪ {toBdR p (logPTilde p)})

theorem bcrisPlusOf_le_bcrisOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : BcrisPlusOf p w hw ≤ BcrisOf p h w hw :=
  Algebra.adjoin_mono Set.subset_union_left

theorem bcrisOf_le_bstFOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : BcrisOf p h w hw ≤ BstFOf p h w hw :=
  Algebra.adjoin_mono Set.subset_union_left

/-! ## §3. `A_cris` does not depend on the generator; `A_cris ⊆ A_max` -/

theorem acrisOf_le {w w' : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hw' : WittVector.fontaineTheta 𝓞_ℂ_[p] p w' = 0) (c : Ainf p) (hc : w' = w * c) :
    AcrisOf p w' hw' ⊆ AcrisOf p w hw := by
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨PowerSeries.rescale c f, restricted_rescale p c hf, ?_⟩
  apply psEval_eq_of_terms
  intro k
  rw [dpSeries, dpSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, hc,
    map_mul, map_mul, map_pow]
  ring

/-- **`A_cris` is the same for every generator of `ker(θ : A_inf → 𝓞_ℂ_p)`** (Berger 2004 II.2.2's
`ω = ([ε] − 1)/([ε_1] − 1)`, `ξ = p − [p̃]`, …). -/
theorem acrisOf_eq {w w' : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hw' : WittVector.fontaineTheta 𝓞_ℂ_[p] p w' = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    (hgen' : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w'}) :
    AcrisOf p w hw = AcrisOf p w' hw' := by
  apply le_antisymm
  · have : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
    rw [hgen', Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact acrisOf_le p hw' hw c (by rw [← hc, mul_comm])
  · have : w' ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw'
    rw [hgen, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact acrisOf_le p hw hw' c (by rw [← hc, mul_comm])

/-- **`A_cris ⊆ A_max`**: `Σ a_n ω^n/n! = Σ (a_n p^n/n!) (ω/p)^n` and `p^n/n! ∈ ℤ_p`. -/
theorem acrisOf_le_amaxOf {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    AcrisOf p w hw ⊆ (AmaxOf p w hw : Set (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
  rintro _ ⟨f, hf, rfl⟩
  let g : (Ainf p)⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff n f * zpToW p (dpCoeff p n)
  have hg : g ∈ restricted p := fun k => by
    obtain ⟨N, hN⟩ := hf k
    refine ⟨N, fun n hn => ?_⟩
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n g
    rw [PowerSeries.coeff_mk]
    exact Dvd.dvd.mul_right (hN n hn) _
  refine ⟨g, hg, ?_⟩
  change evalB p (alg_mem_of_theta p hw) (PowerSeries.map (algebraMap (Ainf p) (AinfP p)) g) = _
  apply psEval_eq_of_terms
  intro n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, dpSeries, PowerSeries.coeff_mk]
  have hq : qpToLoc p (dpCoeff p n : ℚ_[p]) = algebraMap _ _ (zpToW p (dpCoeff p n)) :=
    qpToLoc_algebraMap p _
  rw [inv_factorial_eq p n]
  simp only [map_mul, map_pow]
  rw [← hq]
  ring

theorem acrisOf_le_amax {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) :
    AcrisOf p w hw ⊆ (Amax p : Set (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
  rw [← amaxOf_eq_amax p hw hgen]
  exact acrisOf_le_amaxOf p hw

/-- **Fontaine's `B_st` lies in the tree's `B_st = B_max^+[1/t][log [p̃]]`.** -/
theorem bstFOf_le {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) :
    BstFOf p h w hw ≤ BstOf p h := by
  rw [BstFOf, Algebra.adjoin_le_iff]
  rintro x ((⟨y, hy, rfl⟩ | hx) | hx)
  · exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨y, acrisOf_le_amax p hw hgen hy, rfl⟩))
  · exact Algebra.subset_adjoin (Or.inl (Or.inr hx))
  · exact Algebra.subset_adjoin (Or.inr hx)

/-! ## §4. The basis form of admissibility passes to a larger ring -/

section Mono

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

theorem inclT_tmul (B : Subalgebra ℚ_[p] (BdR p)) (b : B) (v : Fin n → E) :
    inclT p B (b ⊗ₜ[ℚ_[p]] v) = (b : BdR p) ⊗ₜ v := by
  rw [inclT, TensorProduct.map_tmul]
  rfl

/-- **Fontaine admissibility (basis form) over `B ⊆ B'` implies it over `B'`**: the image of a `B`-basis of
`B ⊗ V` of `H`-invariant vectors is a `B'`-basis of `B' ⊗ V` (`B' ⊗_B (B ⊗_{ℚ_p} V) ≅ B' ⊗_{ℚ_p} V`), with the same
image in `B_dR ⊗ V`. -/
theorem isAdmissibleT_mono {B B' : Subalgebra ℚ_[p] (BdR p)} (hBB' : B ≤ B') (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) (h : IsAdmissibleT p B H ρ) : IsAdmissibleT p B' H ρ := by
  obtain ⟨ι, b, hb⟩ := h
  letI : Algebra B B' := (Subalgebra.inclusion hBB').toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    rfl
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ_[p] B B' B' (Fin n → E)
  refine ⟨ι, (b.baseChange B').map e, fun i => ?_⟩
  have key : ∀ x : B ⊗[ℚ_[p]] (Fin n → E),
      inclT p B' (e ((1 : B') ⊗ₜ[B] x)) = inclT p B x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
    | tmul c v =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, inclT_tmul, inclT_tmul]
      congr 1
      change ((c • (1 : B') : B') : BdR p) = (c : BdR p)
      rw [Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add]
  rw [Basis.map_apply, Basis.baseChange_apply, key]
  exact hb i

end Mono

/-! ## §5. Potential semistability in Fontaine's sense -/

section Pst

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`V` is potentially semistable in Fontaine's sense** (Berger 2004 II.5.2 with II.3.3 and I.2.3): for some
finite `K/ℚ_p` inside `ℚ̄_p`, `V|_{G_K}` is `B_st`-admissible, `B_st = B_cris[log [p̃]]` (`BstFOf`), in the form
`B_st ⊗_{ℚ_p} V ≃ B_st^d` as `B_st[G_K]`-modules (a `B_st`-basis of `G_K`-invariant vectors). -/
def IsPstF {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissibleT p (BstFOf p h w hw) K.fixingSubgroup ρ

/-- A `ℚ̄_p`-valued `ρ` is potentially semistable in Fontaine's sense: on a model `V = E^n`. -/
def LocalIsPstF {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstF p h w hw ρE

/-- Fontaine's pst implies pst over the tree's `B_st` (basis form). -/
theorem isPstT_of_F {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    (ρ : GQp p →* GL (Fin n) E) (hF : IsPstF p h w hw ρ) : IsPstT p h ρ := by
  obtain ⟨K, hK, hadm⟩ := hF
  exact ⟨K, hK, isAdmissibleT_mono p (bstFOf_le p h hw hgen) _ ρ hadm⟩

end Pst

/-! ## §6. The generator `ξ = p − [p̃]` -/

theorem theta_xi' : WittVector.fontaineTheta 𝓞_ℂ_[p] p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  have : ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
    exact Ideal.mem_span_singleton_self _
  exact this

/-- A chosen generator `ε₀` of `ℤ_p(1)`. -/
def eps0 : PreTilt 𝓞_ℂ_[p] p := Classical.choose (exists_isGenEps p)

theorem eps0_spec : IsGenEps p (eps0 p) := Classical.choose_spec (exists_isGenEps p)

/-- Fontaine's pst at the chosen `ε₀` and `ξ`. -/
abbrev LocalIsPstF0 (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  LocalIsPstF p (eps0_spec p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) n ρ

end FontaineSt

namespace PanDict

open BmaxOne BergerBst PanBergerSplit FontaineSt

/-- **R11. Berger's theorem in the printed form of Berger's survey**: every de Rham representation is potentially
semistable, with Fontaine's `B_st` (L. Berger, *An introduction to the theory of p-adic representations*, in
*Geometric aspects of Dwork theory* (de Gruyter 2004; volume data UNVERIFIED), arXiv:math/0210184v1, IV.5.1 p. 30
(statement: "every de Rham representation is potentially semi-stable. We shall now give a proof of that
statement") and IV.5.3 p. 31 (proof), citing Berger, Invent. Math. 148 (2002), whose Théorème 0.7 is the same
theorem: §1.2 p. 11 of arXiv:math/0102179v3 prints that Berger's `B_st` gives Fontaine's functor `D_st`), at
`K = ℚ_p`, for a `p`-adic representation `V = E^n` (`E/ℚ_p` finite inside `ℚ̄_p`, `ρ_E : G_{ℚ_p} → GL_n(E)`
continuous):

* de Rham (II.2.3 p. 12): `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`);
* potentially semistable (II.5.2 p. 19): for some finite `K/ℚ_p`, `V|_{G_K}` is `B_st`-admissible (I.2.3 p. 6: "which
  is equivalent to having `B ⊗_{ℚ_p} V ≃ B^d` as `B[G_K]`-modules"), with `B_st = B_cris[log [p̃]]` (II.3.3),
  `B_cris = B_cris^+[1/t]` (II.3.1), `t = log [ε₀]` (II.2.3), `B_cris^+ = A_cris[1/p]`,
  `A_cris = {Σ a_n ω^n/n!}` (II.3.1), `log [p̃] = −Σ (1 − [p̃]/p)^n/n` (`log_p(p) = 0`, II.3.3).

Stated for every generator `ε₀` of `ℤ_p(1)` and every generator `w` of `ker θ` (Berger's `ω` is one, II.2.2;
`A_cris` does not depend on it, `acrisOf_eq`). -/
def BergerSurveyF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstF p h w hw ρE

/-- pb-pst's `BergerPrintedVT` (the tree's `B_st`, basis form) from Berger's theorem over Fontaine's `B_st`
(`B_st^{Fontaine} ⊆ B_st^{tree}`, `isPstT_of_F`; `ξ` generates `ker θ`). -/
theorem bergerPrintedVT_of_survey (hB : BergerSurveyF) : BergerPrintedVT := by
  intro p _ ε₀ h n E _ ρE hc hdr
  exact isPstT_of_F p h (theta_xi' p) ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp ρE
    (hB p ε₀ h _ (theta_xi' p) ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp n E ρE hc hdr)

/-- **The current field `bergerPrintedV` from Berger's theorem over Fontaine's `B_st`.** -/
theorem bergerPrintedV_of_survey (hB : BergerSurveyF) : BergerPrintedV :=
  bergerPrintedV_of_T (bergerPrintedVT_of_survey hB)

/-- **R12. Pan, Theorem 1.0.4, with potential semistability in the sense of Fontaine** (L. Pan, *The
Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem
1.0.4 = arXiv:1901.07166v2 Theorem 1.0.4 p. 5 with Conjecture 1.0.1 p. 2: "the restriction of ρ at the
decomposition group at p is potentially semi-stable in the sense of Fontaine"; JAMS numbering UNVERIFIED), `p ≥ 5`:
as pb-fix3's `PanPrintedP`, with "potentially semistable" over Fontaine's `B_st = B_cris[log [p̃]]` (Berger 2004
II.3.3, `BstFOf`) on a model `V = E^n`, in the basis form (`B_st ⊗ V ≃ B_st^d` equivariantly, which implies the
dimension form for every `G_{ℚ_p}`-stable `B`, `isAdmissible_of_T`), for every generator `ε₀` of `ℤ_p(1)` and every
generator `w` of `ker θ`. -/
def PanPrintedF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstF p h w hw 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

/-- `PanPrintedB` (bst-construct's form, kernel eigenform conclusion) with Fontaine's pst at `ε₀`, `ξ`:
`panPrintedB_of_printedP` verbatim with the potential-semistability hypothesis passed through. -/
theorem panPrintedB_F_of_printedF (hP : PanPrintedF) :
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstF0 p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q) := by
  intro p _ hp ιp ρ hirr hfr hpst hodd hht
  obtain ⟨N, _, k, g, ρg, ψ, ⟨S, hatt⟩, htw⟩ := hP p hp (eps0 p) (eps0_spec p) _ (theta_xi' p)
    ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp ιp ρ (isIrreducibleP_of ρ hirr) hfr hpst hodd
    ((localDistinctHTP_iff p _).mpr hht)
  obtain ⟨M, χ, g', hM, hk, hg', hcoef⟩ := exists_normalized_of_eigenform g
  refine ⟨M, k, χ, g', hM, hk, hg', ψ, S ∪ Finset.range (N + 1), fun q hq hqS v σ hv hσ => ?_⟩
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨hqS, hqN1⟩ := hqS
  have hqN : ¬ q ∣ N := fun hd => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd
    omega
  rw [trace_of_twist p htw, (hatt q hq hqN hqS).2 v σ hv hσ, hcoef q hq hqN]

/-- Berger's theorem over Fontaine's `B_st` for a continuous `ℚ̄_p`-valued `ρ` de Rham on a model. -/
theorem bergerB_F_of_survey (hB : BergerSurveyF) :
    ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
      Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstF0 p n ρ := by
  intro p _ n ρ hρ hdr
  obtain ⟨E, hE, ρE, hmod, hdrE⟩ := hdr
  exact ⟨E, hE, ρE, hmod, hB p (eps0 p) (eps0_spec p) _ (theta_xi' p)
    ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp n E ρE (continuous_model hmod hρ) hdrE⟩

/-- **`r11r12 : PanBerger` from Pan's and Berger's theorems, both over Fontaine's `B_st`**, and the current
bundle's Diamond–Shurman 9.6.5 / Deligne–Serre fields: bst-construct's `panBerger_of_printedB` verbatim with
Fontaine's pst in place of the tree's (the predicate is only passed from Berger's conclusion to Pan's hypothesis,
so no comparison of period rings is used). -/
theorem panBerger_of_F (hP : PanPrintedF) (hB : BergerSurveyF)
    (h965 : DSCoeffExt.DSThm965Printed) (hK : DSCoeffExt.EigenformCoeffFieldFinite)
    (h966 : DSThm966EV.DSThm966Printed) : PanBerger := by
  have hD : ZInQ.Contrib.HodgeSplit.DSThm965 :=
    DS965Weak.dsThm965_of_weak (DSCoeffExt.dsThm965Weak_of_printed h965 hK)
  have hDS : ZInQ.Contrib.HodgeSplit.DSThm966 := DSThm966EV.dsThm966_of_printed h966
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := bergerB_F_of_survey hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := panPrintedB_F_of_printedF hP p hp Φ.symm (dualRep ρ)
    (dualRep_isIrreducible ρ hirr) (dualRep_finitelyRamified ρ hfr) hpst'
    (dualRep_isOdd ρ hodd) hht'
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, charInv ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
  intro q hq hqS
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨⟨hqS, hqSr⟩, hqNp⟩ := hqS
  have hNp : 0 < N * p := Nat.mul_pos hN (Fact.out : p.Prime).pos
  have hqdvd : ¬ q ∣ N * p := fun h => by
    have := Nat.le_of_dvd hNp h
    omega
  refine ⟨hSr q hq hqSr, ?_⟩
  obtain ⟨α, hα⟩ := coeff_mem_range hD hDS p ιC ιL hN hk hg hq hqdvd
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have h1 := htr q hq hqS v σ hv hσ
  rw [trace_dualRep_inv] at h1
  rw [h1, charInv_apply]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

/-- **Not a leaf, and not used by the fold**: the comparison that would give the old field `panPrintedP` from
`PanPrintedF`, namely that potential semistability over the tree's `B_st = B_max[log [p̃]]` in bst-construct's
dimension form implies it over Fontaine's `B_cris[log [p̃]]` (basis form). It holds (Fontaine's `D_st` is computed by
either ring: `φ(B_max^+) ⊆ B_cris^+ ⊆ B_max^+` and the regularity of `B_st`), but no print read here states it for
`B_max[log [p̃]]`: Berger 2002 §1.2 p. 11 states it for his `B_max[log [π̄]]`, and Berger 2004 II.3.5 p. 16 for
crystalline periods. Its proof needs Frobenius on `A_max` and `A_cris` and the regularity of `B_st`, which the
tree lacks. Recorded so that the gap is explicit. -/
def BmaxStToFontaine : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E), IsPstB p ρE → IsPstF p h w hw ρE

/-- The old field `panPrintedP` from the new Pan leaf and the comparison `BmaxStToFontaine` (not used by the fold). -/
theorem panPrintedP_of_F (hP : PanPrintedF) (hC : BmaxStToFontaine) : PanPrintedP := by
  intro p _ hp ιp ρ hirr hfr hpst hodd hht
  obtain ⟨E, hE, ρE, hmod, hpstE⟩ := hpst
  haveI := hE
  exact hP p hp (eps0 p) (eps0_spec p) _ (theta_xi' p) ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp ιp ρ
    hirr hfr ⟨E, hE, ρE, hmod, hC p (eps0 p) (eps0_spec p) _ (theta_xi' p)
      ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp 2 E ρE hpstE⟩ hodd hht

end PanDict
end PkgI4
end HDec

#print axioms HDec.PkgI4.PanDict.bergerPrintedV_of_survey
#print axioms HDec.PkgI4.PanDict.panBerger_of_F
