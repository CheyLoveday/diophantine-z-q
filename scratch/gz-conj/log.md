# gz-conj results log

Target: `ZInQ.GZHL3.GrossConjugationCd` (ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean),
i.e. `GrossConjugationAt (shortCurve (-(d:ℚ)^2))` for d ≡ 5 (mod 8) squarefree
(statement in ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean §2).

## Setup
- merged wip/gz-weil ad22e947 (VERIFIED: git merge, no conflicts).
- build: copied gz-weil .lake/build (reflink) and lean/.lake/build; `lake build` of Heegner, Cd, ALBasic,
  Level, FHNonvanishing.FE, HeckeAll.Provider: success (VERIFIED).

## Plan (proof outline)
1. rootNumber f = -1 for the newform of C_d: Tau Ceti FE (`completedL_newform_sub`) vs proved
   FunctionalEquation5 at level N = 32 d^2 (`level_eq_of_coeff_cd`), L(f,s) not identically 0. Kills clause eps=+1.
2. eps = -1 means frickeSign = +1: f(-1/(Nz)) = N z^2 f(z), so eichler f ∘ W_N - eichler f has derivative 0,
   value 0 at the fixed point i/sqrt N.
3. coefficients real: conj(eichler f τ) = eichler f (-conj τ) = eichler f (W_N ψ τ) = eichler f (ψ τ), ψ τ = 1/(N conj τ).
4. lattice uniqueness: g2,g3 determine the lattice (local ODE argument + identity theorem + poles), so
   conj L = L for a period lattice of E/ℚ; hence conj(weierPt z) = weierPt(conj z).
5. ψ τ_Q = τ_{Q*}, Q* = [N C, B, A/N] (residue β, same D); Q ↦ Q* permutes Γ0(N)-classes; so conj fixes heegnerC.
6. ι∘σ = conj∘ι; map ι injective ⇒ σ y = y.
