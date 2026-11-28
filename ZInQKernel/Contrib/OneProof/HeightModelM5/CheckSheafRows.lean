import ZInQKernel.Contrib.OneProof.HeightModelM5.GlobalOmega

/-!
# Axiom check for the tree-facing statements

Prints the axioms of the theorems that identify the global sections of the sheaves built in this
directory with the tree's lattices. Each list is expected to lie within `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- N4: global sections of `e*Ω¹`
#print axioms ZInQ.HeightModelM5.genericGermPullOmega
#print axioms ZInQ.HeightModelM5.genericGermPullOmega_apply
#print axioms ZInQ.HeightModelM5.stalkToGeneric_injective_sheaf
#print axioms ZInQ.HeightModelM5.genericGermPullOmega_injective
#print axioms ZInQ.HeightModelM5.range_genericGermPullOmega
#print axioms ZInQ.HeightModelM5.printedOmega_eq_sheaf
