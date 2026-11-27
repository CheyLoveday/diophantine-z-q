import ZInQKernel.Contrib.OneProof.RC.Even.EvenPhase
import ZInQKernel.Contrib.OneProof.RC.KSplit.Seed

/-!
# Lane RC22 (glue sweep, symbols): the (E.12) field of lane RC3's no-seed data, discharged

Lane RC3's interface `KSplit.NoSeedTraceData` (`Coefficients.lean`, tex 10319–10481) has the field
`hrec : ShellRecurrence a (η p) ψp ap p`, the good `T(p²)` formula (E.12) at `p` (tex 8156–8161,
kind PRINT: Shimura's `T(p²)` formula plus modularity), and the field
`hψ : ψp = η p * (−1/p)` (`ψ/η = χ₋₁`, tex 10361, 10457, kind ELLIOT). Lane RC11 PROVES (E.12)
from lane RC8's eigenspace condition (`Even.E12_of_eigenspace`, `RC/Even/EvenPhase.lean`), in
exactly the coefficient form of `ShellRecurrence`, for `a = hiwCoeff g` (the `q`-expansion
coefficients of a weight-`3/2` form `g` in the good-Hecke eigenspace attached to `E` and `η`) and
`ap = a_p(E)` the coefficient of Mathlib's `L(E, s)`. This file states the two field-level bridges.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Sym

open ZInQ.Manuscript.RC

/-- **(E.12) at `p`, in lane RC3's form** (tex 8156–8161; the field `hrec` of
`KSplit.NoSeedTraceData`, tex 10456–10463): for `g` in the good-Hecke eigenspace attached to `E`,
level `N` (`4 ∣ N`), characters `ψ, η` with `ψ/η = χ_{−σ}`, and a prime `p ∤ N`, the coefficients
`a = hiwCoeff g` satisfy `ShellRecurrence a (η p) (ψ p) a_p(E) p`. Kind: PROVED, from lane RC8's
eigenspace condition `IsInWaldspurgerEigenspace E N ψ η g` (PRINT-level interface) and
`ψ/η = χ_{−σ}`. Consumer: lane RC3's `ShellRecurrence` hypothesis (`hrec` of `NoSeedTraceData`,
of `shell_p_sq`, `shell_p_four`, `Bp_p`, `Bp_p_cube`, `Hp_p_cube`, `Hp_p_sq_mul`,
`Hp_p_cube_inTwoO`); discharger: lane RC11's `Even.E12_of_eigenspace`. -/
theorem shellRecurrence_of_eigenspace {E : WeierstrassCurve ℚ} {N : ℕ} (hN : 4 ∣ N)
    (ψ η : DirichletCharacter ℂ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (PrintsAnalytic.kronecker (-σ) n : ℂ))
    {g : UpperHalfPlane → ℂ} (hg : PrintsAnalytic.IsInWaldspurgerEigenspace E N ψ η g)
    {p : ℕ} [hp : Fact p.Prime] (hpN : ¬ p ∣ N) :
    KSplit.ShellRecurrence (PrintsAnalytic.hiwCoeff g) (η p) (ψ p) (E.LFunction p) p := by
  intro n
  rw [Even.E12_of_eigenspace hN ψ η hσ hψη hg hp.out hpN n, jacobiSym.legendreSym.to_jacobiSym]
  rfl

/-- **`ψ/η = χ₋₁` at `p`, in lane RC3's form** (tex 10361, 10457; the field `hψ` of
`KSplit.NoSeedTraceData`): for the positive sign `σ = 1` (`ψ/η = χ_{−1}`), level `4 ∣ N` and a
prime `p ∤ N`, `ψ(p) = η(p) (−1/p)`. Kind: PROVED, from `η = ψ χ_{−1}` on residues prime to `N`.
Consumer: lane RC3's hypothesis `hψ` (of `NoSeedTraceData`, `shell_p_sq`, `Hp_p_cube`);
discharger: lane RC11's character relation `hψη` with `σ = 1`. -/
theorem psi_eq_eta_mul_legendre {N : ℕ} (hN : 4 ∣ N) (ψ η : DirichletCharacter ℂ N)
    (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (PrintsAnalytic.kronecker (-1) n : ℂ))
    {p : ℕ} [hp : Fact p.Prime] (hpN : ¬ p ∣ N) :
    ψ p = η p * ((legendreSym p (-1) : ℤ) : ℂ) := by
  have h2p : ¬ 2 ∣ p := by
    intro h
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h).symm
    exact hpN (hp2 ▸ dvd_trans (by norm_num) hN)
  have hk : PrintsAnalytic.kronecker (-1) p = legendreSym p (-1) := by
    have hfac : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2p
    unfold PrintsAnalytic.kronecker
    rw [hfac, pow_zero, one_mul, pow_zero, Nat.div_one, jacobiSym.legendreSym.to_jacobiSym]
  have hsq : ((legendreSym p (-1) : ℤ) : ℂ) ^ 2 = 1 := by
    have h1 : (legendreSym p (-1)) ^ 2 = 1 := by
      rcases legendreSym.eq_one_or_neg_one p (a := -1)
        (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; intro h
            exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit
              (isUnit_of_dvd_one (by simpa using h))) with h | h <;> rw [h] <;> norm_num
    exact_mod_cast h1
  have hrel := hψη p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpN)
  rw [hk] at hrel
  rw [hrel, mul_assoc, ← sq, hsq, mul_one]

end ZInQ.Manuscript.RC.GlueSweep.Sym
