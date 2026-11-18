import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SelfInjective

/-!
# Selmer duality, part 7: finite Selmer duality over the coefficient rings `A_i`

Over `A_i = (ℤ/2^i)[t]/t^i` (tex L2725), which is self-injective (`acoef_selfInjective`), the scope
condition `TermwiseDualComputesRHom` of `FiniteSelmerDualityNode` holds for every Selmer complex,
so the termwise dual `Hom_{A_i}(C_{U⊥}, A_i)` is the `RHom` of tex L2806–2830 and finite Selmer
duality holds from the two GLUE inputs alone (`finiteSelmerDuality_acoef`).

**Classification.** PROVED (from the GLUE inputs).
-/

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Manuscript.RC.HeegnerAlgebra

/-- Over `A_i` the termwise dual of any Selmer complex computes `RHom`. -/
theorem acoef_termwiseDualComputesRHom (i : ℕ) (C : GCx (Acoef i)) :
    TermwiseDualComputesRHom (Acoef i) C :=
  Or.inl (acoef_selfInjective i)

/-- **Finite Selmer duality over `A_i`** (tex L2806–2830): for Selmer data over `A_i`, cup-product
data with an isotropy homotopy, a trace killing coboundaries and a perfect coefficient pairing,
the global duality and local orthogonality inputs give that
`C_U → Hom_{A_i}(C_{U⊥}, A_i)[−3] = RHom_{A_i}(C_{U⊥}, A_i)[−3]` is a quasi-isomorphism. -/
theorem finiteSelmerDuality_acoef (i : ℕ) (D D' : SelData (Acoef i)) (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (P : PerfectCoefficientPairing (Acoef i))
    (hG : GlobalDualityInput Q tr htr P) (hL : LocalOrthogonalityInput Q tr htr P) :
    QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)) :=
  finiteSelmerDualityNode_proof _ D D' Q tr htr P (acoef_termwiseDualComputesRHom i _) hG hL

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
