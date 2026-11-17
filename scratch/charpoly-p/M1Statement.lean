import ZInQKernel.Contrib.OneProof.CharPolyIndepOfEllAlgClosed
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

/-! charpoly-p, scratch: the missing published input M1 stated over genuine tree definitions
(CW07 coherent cohomology `Scheme.Modules.eulerChar`, AnthropicFLT `Scheme.Modules.IsInvertible`,
Mathlib `Scheme.Modules.pullback`, the tree's `PkgI3.AbVar.IsIsogenyMor`). Statement only. -/

open CategoryTheory AlgebraicGeometry

namespace CharPolyP.Scratch

/-- **M1 (consequence of a published theorem).** D. Mumford, *Abelian varieties* (1970), §16, the
Riemann–Roch theorem `χ(L)² = deg φ_L` (UNVERIFIED locator), with `φ_{ψ^*L} = ψ̂ ∘ φ_L ∘ ψ` (§8/§13,
UNVERIFIED): for an endomorphism `ψ` of an abelian variety over an algebraically closed field that is not
an isogeny, and an invertible sheaf `L`, `χ(ψ^*L) = 0`. -/
def NonIsogPullbackEulerZero : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A),
    ¬ PkgI3.AbVar.IsIsogenyMor ψ.hom → ∀ (L : A.X.left.Modules), Scheme.Modules.IsInvertible L →
      letI : A.X.left.Over (Spec (CommRingCat.of k)) := ⟨A.X.hom⟩
      Scheme.Modules.eulerChar k ((Scheme.Modules.pullback ψ.hom.left).obj L) = 0


/-- **χ(ψ^*L) = deg ψ · χ(L) for every endomorphism (consequence of published theorems).** D. Mumford,
*Abelian varieties* (1970): for an isogeny `ψ`, `χ(ψ^*L) = deg ψ · χ(L)` (§12, UNVERIFIED locator; proved
there for finite flat `ψ` from `ψ_*𝒪` locally free of rank `deg ψ`); for a non-isogeny both sides are `0`
(`NonIsogPullbackEulerZero`, from §16). `deg` is the tree's genuine `CharPolyEll.degEnd` (function-field
degree, `0` off isogenies). -/
def EulerPullbackDeg : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    (L : A.X.left.Modules), Scheme.Modules.IsInvertible L →
      letI : A.X.left.Over (Spec (CommRingCat.of k)) := ⟨A.X.hom⟩
      Scheme.Modules.eulerChar k ((Scheme.Modules.pullback ψ.hom.left).obj L) =
        (ZInQ.Contrib.OneProof.CharPolyEll.degEnd ψ : ℤ) * Scheme.Modules.eulerChar k L

end CharPolyP.Scratch

#check @CharPolyP.Scratch.NonIsogPullbackEulerZero
#check @CharPolyP.Scratch.EulerPullbackDeg
