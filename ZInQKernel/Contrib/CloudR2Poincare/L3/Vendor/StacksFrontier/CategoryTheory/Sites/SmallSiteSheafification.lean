import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Sheafification of abelian presheaves on a small site

On a small site, abelian presheaves admit a sheafification and the maps it inverts are exactly
the locally bijective ones: `AddCommGrpCat` in the universe of the site satisfies AB5 and is a
concrete category with the exactness properties the two statements need, so both are instances.

## Main results

* `CategoryTheory.smallSiteHasSheafify`: abelian presheaves on a small site admit sheafification.
* `CategoryTheory.smallSiteWEqualsLocallyBijective`: sheafification of abelian presheaves on a
  small site inverts exactly the locally bijective maps.
-/


namespace CategoryTheory
#cloudR2LocalInstances

universe w
#cloudR2Vendor smallSiteHasSheafify in

/-- Sheafification of abelian presheaves exists on a small site. -/
theorem smallSiteHasSheafify {D : Type w} [SmallCategory D] (K : GrothendieckTopology D) :
    HasSheafify K AddCommGrpCat.{w} := inferInstance
#cloudR2Vendor smallSiteWEqualsLocallyBijective in

/-- On a small site, the maps of abelian presheaves inverted by sheafification are exactly the
locally bijective ones. -/
theorem smallSiteWEqualsLocallyBijective {D : Type w} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance

end CategoryTheory


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
