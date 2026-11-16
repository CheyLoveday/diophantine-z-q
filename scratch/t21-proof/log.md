# t21-proof log

Base 2880fef1. Build tree copied from ~/dzq-check2 (same commit).

## Step 1: reduction (T21Reduce.lean) — VERIFIED (compiles, 6 s)
`tyzThm21At31_of_glue : BrandtValueAt3 → LcalUnitOneThree → TYZThm21At31`.
- `torsionOrder_three : torsionOrder (QNeg 3) = 6` (Mathlib `IsCyclotomicExtension.Rat.torsionOrder_eq`).
- `classSum_eq`: Cl_3 subsingleton (pid_three), class sum = f 1 (tv_eq_of_toClassGroup_eq).
- `int_eq_pm_one_of_sq`: a ∈ ℤ, a² = z, 0 < ‖z‖ < 4 → a = ±1.
Glue left: `BrandtValueAt3` (∀ admissible τ, ∀ test vector f, f 1 = ±3), `LcalUnitOneThree`
(0 < ‖lcalSq m‖ < 4 at m = 1, 3).

## Step 2: Brandt side infrastructure (ZInQKernel/Contrib/OneProof/T21Proof/) — VERIFIED (each compiles)
- Hurwitz.lean: Hurwitz coordinates `hc`/`hur`, `mulH`/`starH`/`nrdH` (integer polynomials), `IsHur S`
  closure; `exists_oneI_mul` (even norm ⇒ divisible by 1+i, mod-2 decide), `eq_smul_unit_of_nrdH`
  (norm 4^m ⇒ 2^m · unit).
- Local.lean: `ev w : 𝔸ᶠ_ℚ →+* ℚ_[p_w]` via Mathlib `padicEquiv`; `piQ w`; components of qι γ, centre, ιAt.
- LocalPred.lean: `LocOK` (ℚ_p^× O_{B,p}^×), `InR ω` (ℤ_p + ℤ_p ω + 4O_{B,p}), `Loc2OK`; closure under
  products/inverses.
- GlobalStep.lean: `global_step` (γ ∈ ℚ_p^× O_{B,p}^× at all odd p ⇒ γ = q·n, nrd n = 2^k; content
  argument), `two_adic_step` (⇒ μβ ≡ X + Yω mod 4O_B with μ a unit; reduction ℤ_2 → ℤ/4).
- Finite.lean (decide +kernel, 11 s): 24 Hurwitz units; mod-4 obstruction for the 6 classes
  t ∉ {0, t*(s)} for all 8 sign patterns s; partner identity; sums of the test vector values.
- BaseChange.lean: `tauHat_integral` (τ̂(Ô_K) integral at every place; copy of Tau Ceti's private
  `exists_semilocalHom_sum_tmul_eq`). Pitfall: `attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion` needed (ℚ-algebra diamond).
Cross-check (classes.py, python): for each of the 8 τ, the classes in B^×H are exactly {0, t*}
(matches scratch/h29-fix/brandt.py's −3 classes).

## Step 3: BrandtValueAt3 PROVED — VERIFIED (compiles; axioms propext, Classical.choice, Quot.sound)
`ZInQ.Contrib.T21Proof.testVector_one : AdmissibleTau 3 τ → IsTestVector 3 τ f → f 1 = 3 ∨ f 1 = -3`
(ZInQKernel/Contrib/OneProof/T21Proof/BrandtValue.lean; scratch/t21-proof/AxBrandt.lean prints axioms).
Files: Tau.lean (signs of τ, 𝓞 = ℤ[ω], τ̂(Ô_K) ⊂ ℤ_p+ℤ_pω, place 2), K2.lean (centralizer of ω at 2),
Brandt.lean (subgroup Sg, H ≤ Sg, twoRep_ne for the 6 classes), Brandt2.lean (partner ∈ R̂_3^×),
BrandtValue.lean (gT = −3·[B^×H] + 1·[else] ∈ InPiZ; generator ⇒ f(1) = ±3).
Route: g defined by membership in the double coset B^×H (invariances free); sums need exactly
{0, t*} ⊂ B^×H among TYZ's 8 representatives: positive by explicit R̂_3^× element, negative by the
local invariant (global content argument + 2-adic mod-4 obstruction, decide).
