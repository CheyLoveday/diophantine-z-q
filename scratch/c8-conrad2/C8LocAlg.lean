import ZInQKernel.Contrib.OneProof.C8Conrad
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap

/-! # c8-conrad2: `LocAlgExponentEqWeight` from Tate's theorem over `\hat{K^{ur}}`

diophantine_zq.tex L763-764 ("removing its integral local Hodge–Tate weight"): the exponent of a locally
algebraic character of `G_{ℚ_p}` is its Hodge–Tate weight. Proof: a nonzero `φ ∈ H_{-w}(ψ)` (from
`HasHTWeights {w}`) gives `x = φ(v) ≠ 0` in `ℂ_p` with `σ(x) = χ(σ)^{w-n} x` for every `σ` in the inertia group of
`K = ℚ_p(ζ_{p^k})` (every such `σ` is an Artin lift of a unit `u ≡ 1 mod p^k`: Tau Ceti's
`map_artinMap_unitFiltration_zero`, `localCyclotomicCharacter_artinMap_padic`), and Tate's theorem for the complete
discretely valued field `\hat{K^{ur}}` (`TateTwistInvariantsInertia`) forces `w = n`. -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

#check @PkgI4.htMult
#check @PkgI4.cycPow
#check @PkgI4.cpAct
#check @TauCeti.inertiaSubgroup
#check @TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero
#check @TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic
#check @TauCeti.mem_unitFiltration_zero
example (p : ℕ) [Fact p.Prime] : PadicAlgCl p = AlgebraicClosure ℚ_[p] := rfl

end HDec.G0Galois.C8Conrad
