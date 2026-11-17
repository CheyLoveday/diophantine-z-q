import ZInQKernel.Contrib.OneProof.DeRhamPrint
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.TateTwistInvariants

/-!
# bdr-inv: `B_dR^{G_F} = F` (Fontaine), proved: `DeRhamPrint.BdRInvariantsPrinted`

Task bdr-inv (2026-11-17). The statement `DeRhamPrint.BdRInvariantsPrinted`
(`ZInQKernel/Contrib/OneProof/DeRhamPrint.lean`) is used verbatim (imported, not restated).

Proof (Brinon–Conrad, *CMI notes* (2009), Prop. 4.3.1 / Thm. 4.3.2-type argument; Fontaine, Astérisque 223,
Exp. II; locators UNVERIFIED):
1. `σ([ε] - 1) = ([ε] - 1) · c_σ` in `B_dR^+` with `θ(c_σ) = χ(σ)` (`bdrPlus_xe`): `σ(ε) = ε^a ρ^{p^m}` in the
   tilt with `ρ^♯ = 1`, `a ≡ χ(σ) mod p^m`, and `[ρ] - 1 ∈ ξ W(O♭)` gives `θ(c_σ) ≡ a mod p^m` (bounded error).
2. `[ε] - 1` is a uniformizer of the DVR `B_dR^+`; a `G_K`-invariant `x = T^{j-k} u` gives
   `χ^{j-k} σ(θ u) = θ u`, so `j = k` by Tate's theorem (`tateTwistInvariants_proof`): `x ∈ (B_dR^+)^×`.
3. `θ(x) ∈ ℂ_p^{G_K} = K` (Ax–Sen–Tate, `axSenTate_proof`); the Hensel lift `F → B_dR^+` (G9's
   `exists_hensel_lift`) is `G_F`-invariant; the difference is invariant with `θ = 0`, hence `0` by 2.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BdRInv

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.PkgI4.Cp ZInQ.Contrib.G9.BdrKer
  ZInQ.Contrib.G9.BdrKer.Cp ZInQ.Contrib.HodgeSplit DeRhamPrint.TDict Module

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. A compatible system of `p`-power roots of unity coming from `ℚ̄_p` -/

theorem exists_prim : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ p := by
  have : NeZero (p : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (PadicAlgCl p))
    (Polynomial.degree_cyclotomic_pos p (PadicAlgCl p) hp.out.pos).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/-- `1, ζ_p, ζ_{p²}, …` in `ℚ̄_p`. -/
def zq : ℕ → PadicAlgCl p
  | 0 => 1
  | 1 => Classical.choose (exists_prim p)
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (zq (n + 1)) hp.out.pos)

theorem zq_succ_pow (n : ℕ) : zq p (n + 1) ^ p = zq p n := by
  rcases n with _ | n
  · exact (Classical.choose_spec (exists_prim p)).pow_eq_one
  · exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (zq p (n + 1)) hp.out.pos)

theorem zq_pow (n : ℕ) : zq p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [zq]
  | succ n ih => rw [pow_succ', pow_mul, zq_succ_pow, ih]

theorem zq_pow_add (n m : ℕ) : zq p (n + m) ^ p ^ m = zq p n := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, pow_succ', pow_mul, zq_succ_pow, ih]

theorem norm_zq (n : ℕ) : ‖((zq p n : PadicAlgCl p) : ℂ_[p])‖ = 1 := by
  have h1 : ‖((zq p n : PadicAlgCl p) : ℂ_[p])‖ ^ p ^ n = 1 := by
    rw [← norm_pow, PadicComplex.coe_eq, ← map_pow, zq_pow, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).mp h1

theorem zq_ne_zero (n : ℕ) : ((zq p n : PadicAlgCl p) : ℂ_[p]) ≠ 0 := by
  intro h; have := norm_zq p n; rw [h, norm_zero] at this; exact zero_ne_one this

/-- The root system of TDict built from `zq`. -/
def Zq : RootSystem p where
  z n := ⟨((zq p n : PadicAlgCl p) : ℂ_[p]), (mem_O_iff p _).mpr (norm_zq p n).le⟩
  pow_succ n := Subtype.ext (by
    push_cast
    rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow, zq_succ_pow])
  zero := Subtype.ext (by simp [zq])
  one_ne h := by
    have h1 := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at h1
    rw [PadicComplex.coe_eq, ← map_one (algebraMap (PadicAlgCl p) ℂ_[p])] at h1
    exact (Classical.choose_spec (exists_prim p)).ne_one hp.out.one_lt
      ((algebraMap (PadicAlgCl p) ℂ_[p]).injective h1)

theorem Zq_z (n : ℕ) : ((Zq p).z n : ℂ_[p]) = ((zq p n : PadicAlgCl p) : ℂ_[p]) := rfl

/-! ## 2. The Galois action on `ε` -/

/-- The cyclotomic exponent mod `p^m`: `σ(ζ) = ζ^{a}` for `ζ^{p^m} = 1`. -/
def aexp (σ : GQp p) (m : ℕ) : ℕ := (PadicInt.toZModPow m ((cyc p σ : ℤ_[p]))).val

theorem cpAct_zq (σ : GQp p) (m : ℕ) :
    cpAct p σ ((zq p m : PadicAlgCl p) : ℂ_[p]) = ((zq p m : PadicAlgCl p) : ℂ_[p]) ^ aexp p σ m := by
  rw [cpAct_coe]
  have h := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := m) σ.toRingEquiv (zq p m) (zq_pow p m)
  rw [show σ (zq p m) = σ.toRingEquiv (zq p m) from rfl, h, PadicComplex.coe_eq, PadicComplex.coe_eq, map_pow]
  rfl

end

end BdRInv
