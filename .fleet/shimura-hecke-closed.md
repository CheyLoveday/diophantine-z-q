# Shimura Hecke relations, closed

`ShimuraSteps.shimuraHeckeRelations : ShimuraSteps.ShimuraHeckeRelations` is
proved with no hypothesis in `ZInQKernel/Contrib/OneProof/ShimuraHeckeClosed.lean`.
`ShimuraSteps.pointDictionary` comes from `ShimuraPointDict.existsUnique_atTau`,
and `shimuraHeckeRelations_of_pointDictionary` then closes the relations.
`shimuraThm1Af_of_printed_closed : ShimuraThm1AsPrinted → R16Thm1b.ShimuraThm1Af`
leaves only the printed form as an input.

The branch merges wip/shimura-orbits (510a7a383) and wip/shimura-point-dict
(3245d5b23); both add new files only, and the merge is clean. Lake built the new
module, and the three axiom checks report only `propext`, `Classical.choice` and
`Quot.sound`. No leaf or fold.
