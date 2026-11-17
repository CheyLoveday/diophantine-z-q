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


/-- The components of `ρ = (σ(ε) ε^{-a})^{1/p^m}`, in `ℂ_p`. -/
def rhoC (σ : GQp p) (m n : ℕ) : ℂ_[p] :=
  cpAct p σ ((zq p (n + m) : PadicAlgCl p) : ℂ_[p]) *
    (((zq p (n + m) : PadicAlgCl p) : ℂ_[p])⁻¹) ^ aexp p σ m

theorem norm_rhoC (σ : GQp p) (m n : ℕ) : ‖rhoC p σ m n‖ = 1 := by
  rw [rhoC, norm_mul, norm_pow, norm_inv, norm_cpAct, norm_zq]; simp

/-- `ρ`'s components in `𝓞_ℂ_p`. -/
def rhoO (σ : GQp p) (m n : ℕ) : (𝓞_ℂ_[p] : Type) :=
  ⟨rhoC p σ m n, (mem_O_iff p _).mpr (norm_rhoC p σ m n).le⟩

theorem coe_pow_zq (k N : ℕ) : (((zq p k : PadicAlgCl p) : ℂ_[p])) ^ N = (((zq p k ^ N : PadicAlgCl p)) : ℂ_[p]) := by
  rw [PadicComplex.coe_eq, PadicComplex.coe_eq, map_pow]

theorem inv_pow_pow (c : ℂ_[p]) (a N : ℕ) : ((c⁻¹) ^ a) ^ N = ((c ^ N)⁻¹) ^ a := by
  rw [← pow_mul, mul_comm, pow_mul, inv_pow]

theorem rhoC_pow (σ : GQp p) (m n N : ℕ) (k : ℕ) (hk : zq p (n + m) ^ N = zq p k) :
    rhoC p σ m n ^ N = cpAct p σ ((zq p k : PadicAlgCl p) : ℂ_[p]) *
      (((zq p k : PadicAlgCl p) : ℂ_[p])⁻¹) ^ aexp p σ m := by
  rw [rhoC, mul_pow, inv_pow_pow, ← map_pow, coe_pow_zq, hk]

theorem rhoO_succ (σ : GQp p) (m n : ℕ) : rhoO p σ m (n + 1) ^ p = rhoO p σ m n := by
  apply Subtype.ext
  simp only [rhoO, SubmonoidClass.coe_pow]
  rw [rhoC_pow p σ m (n + 1) p (n + m) (by rw [Nat.add_right_comm]; exact zq_succ_pow p (n + m))]
  rfl

/-- `ρ ∈ O♭`. -/
def rho (σ : GQp p) (m : ℕ) : PreTilt (𝓞_ℂ_[p] : Type) p := mkSeq p (rhoO p σ m) (rhoO_succ p σ m)

theorem untilt_rho (σ : GQp p) (m : ℕ) : (rho p σ m).untilt = 1 := by
  rw [rho, untilt_mkSeq]
  apply Subtype.ext
  simp only [rhoO, rhoC, OneMemClass.coe_one, zero_add]
  rw [cpAct_zq, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (zq_ne_zero p m))]

theorem oAct_coe (σ : GQp p) (x : (𝓞_ℂ_[p] : Type)) : ((oAct p σ x : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) = cpAct p σ (x : ℂ_[p]) := rfl

/-- **`σ(ε) = ε^a · ρ^{p^m}`** in the tilt. -/
theorem preTiltMap_eps (σ : GQp p) (m : ℕ) :
    DR.preTiltMap p (oAct p σ) (eps (Zq p)) = eps (Zq p) ^ aexp p σ m * rho p σ m ^ p ^ m := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (DR.preTiltMap p (oAct p σ) (eps (Zq p))) =
    PreTilt.coeff n (eps (Zq p) ^ aexp p σ m * rho p σ m ^ p ^ m)
  rw [map_mul, map_pow, map_pow, eps, rho, coeff_mkSeq, coeff_mkSeq, ← map_pow, ← map_pow, ← map_mul]
  change Ideal.Quotient.mk _ (oAct p σ ((Zq p).z n)) = _
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, oAct_coe, Zq_z, rhoO]
  rw [rhoC_pow p σ m n (p ^ m) n (zq_pow_add p n m), inv_pow]
  have h0 := pow_ne_zero (aexp p σ m) (zq_ne_zero p n)
  field_simp

/-! ## 3. `B_dR^+`: `θ⁺` and `σ` on Teichmüller lifts -/

theorem thetaPlusCp_plus (w : WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) :
    thetaPlusCp p (plus p w) = ((fontaineTheta (𝓞_ℂ_[p] : Type) p w : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) := by
  change awayEquivCp p (thetaPlus p (plus p w)) = _
  rw [thetaPlus_plus, AlgEquiv.commutes]
  rfl

theorem thetaPlusCp_teich (x : PreTilt (𝓞_ℂ_[p] : Type) p) :
    thetaPlusCp p (plus p (teichmuller p x)) = ((x.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) := by
  rw [thetaPlusCp_plus, fontaineTheta_teichmuller]

theorem bdrPlusMap_plus (σ : GQp p) (w : WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) :
    DR.bdrPlusMap p (oAct p σ) (plus p w) = plus p (WittVector.map (DR.preTiltMap p (oAct p σ)) w) := by
  change DR.bdrPlusMap p (oAct p σ) (ofLoc p (algebraMap _ _ w)) = ofLoc p (algebraMap _ _ _)
  rw [bdrPlusMap_ofLoc, locMap_algebraMap]

theorem bdrPlusMap_teich (σ : GQp p) (x : PreTilt (𝓞_ℂ_[p] : Type) p) :
    DR.bdrPlusMap p (oAct p σ) (plus p (teichmuller p x)) = plus p (teichmuller p (DR.preTiltMap p (oAct p σ) x)) := by
  rw [bdrPlusMap_plus, map_teichmuller]

end

end BdRInv
