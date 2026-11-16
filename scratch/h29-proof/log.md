# h29-proof results log

Task h29-proof, started 2026-11-16 14:35 PST. Base 0caafe66 (fork main w80).
Target: hL29 = `ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3`
(`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean:455`).

## Step 0. Setting (VERIFIED by reading files)
* `~/tyz-src/Period7.tex` is NOT on this host (ls fails). All TYZ line numbers below are quoted from
  h29-split.md, h29-fix.md, h29-ne3.md, rv-tyz-inputs.md (which read it), not re-read.
* `~/pyenv` absent; Python with cypari2 run through `uv run --offline --with cypari2 python -I`.
* Genus theory is already proved in Lean in the project: `ZInQ.RouteK.Redei.chi n q :
  ClassGroup (𝓞 (QNeg n)) →* Multiplicative (ZMod 2)` (χ_q([𝔞]) = (N𝔞/q)),
  `range_sq_eq_ker_chi` (Cl² = ⋂ ker χ_q, odd squarefree n > 1), `card_ker_sq_eq`
  (#Cl[2] = 2^{t-1}), `exists_chi_eq` (image of the genus map) — RouteK/Redei/{Genus,FourRank,Dirichlet}.lean.

## Step 1. Verdict on an outright proof (analysis)
* hL29 relates Q(n) (a finite Brandt-module sum) to 𝓛(d₁)𝓛(d₂) (L-values `lcalSq`, defined from the
  continuation of Mathlib's L-series). For a prime p ≡ 3 (mod 8), p ≠ 3, it says ℓ(p)ℓ(1) = ±Q(p), i.e. an
  exact evaluation of L(E_p,1)/Ω_p for infinitely many p. No open leaf among TYZProp23Printed,
  TYZTestVectorExists, LegendreThreeSquares, JonesPallX2Y2Z16 mentions `lcalSq`; any proof needs the explicit
  Waldspurger formula (TYZ Theorem 2.1 / 4.2, from Yuan–Zhang–Zhang). Not provable here.

## Step 2. Numerical check of the fallback leaves (VERIFIED, computed)
`genus_check.py` (uses brandt.py, brandt2.py of h29-fix, copied unchanged), output `genus_check-output.txt`.
n ∈ {11,17,33,35,41,51,57,73,105,113,123,145,195,219}, 2 admissible τ each (28 runs): for every set T of
primes of n, P_T = Σ_{t∈Cl_n} χ_T(t) f_n(t), d₂ = ∏T, d₁ = n/d₂:
(V) d₁, d₂ ≢ 1 (8) ⇒ P_T = 0; (F) d₂ ≡ 1 (8) ⇒ P_T² = 4^{k-1} w_K² 𝓛(d₁)²𝓛(d₂)²;
(S) n ≡ 1 (8) ⇒ P_T = P_{T^c}; (C) n ≡ 3 (8) ⇒ χ_T = χ_{T^c}; (PQ) Σ_T P_T = 2^k Q(n). ALL OK.
