# cfext-proof results log

Target: `JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite`
(ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean:48), Stichtenoth 3.6.3(a) finite case.

## Plan (proof route, no new leaf)
- A := O ⊗[K] L (O = w.comap ι, a local ring); `Algebra.FormallyUnramified O A` (base change of the separable
  field extension L/K, char 0); for the prime p = φ⁻¹(m_w): localizing, Mathlib's
  `Algebra.FormallyUnramified.map_maximalIdeal` gives m_O A_p = m_{A_p}, so every a ∈ p has s·a = π·b, s ∉ p.
- every x ∈ FL is ι(c)·φ(a) (bijectivity of F ⊗ L → FL, c = coefficient of least valuation).
- Archimedean step: for d ∈ O, d ≠ 0, some π^m ∈ dO (π transcendental over K by the full-constant-field
  hypothesis; {π} transcendence basis since trdeg F/K = 1 from t; lowest coefficient of an algebraic relation
  of d over K[π]).
- iterate: x = ι(c)φ(a)/φ(s); if c ∈ m_O done; else a ∈ p, replace (c, a, s) by (cπ, b, s s').
