# Rational open comparison results

- Base `85505928a07a41a30e0dd9cd22e17faf54a76b06`. Approved Atkin–Lehner merge `66b8d103be2f9e6d7193df3f6c4995bccf4e8d5b` succeeded.
- Bridge documentation correction `aee7b1aee8a82005b7003fe9c6ed895b217a7e2b` points to the proved vendored bijection and transitivity.
- `PairJ`: the source invariant descends to pair classes. Each class over the j-invariant of a given equation has a representative on that equation. Lake build passed, 4 standard-axiom checks.
- `RationalPoints`: the rational degree-zero quotient has the actual cyclic-pair reading, computed on any marked lift. The first j-coordinate evaluates to the source invariant. Lake build passed, 3 standard-axiom checks.
- `ShortSubgroups`: on an elliptic equation with nonexceptional j, equal pair classes on that equation have equal subgroups. Lake build passed, 3 standard-axiom checks.
- `GenericPoints`: the pinned generic j-fibre points biject with the cyclic subgroups on the actual `EjBar`, with the specified first coordinate and pair class. Lake build passed, 6 standard-axiom checks.
- `MarkedGalois`: the coefficient map of a short equation over `Qj` is fixed by every Galois automorphism, and the marked short cover lift commutes with the action on its two point coordinates. Lake build passed, 3 standard-axiom checks.
- `GenericGalois`: the actual generic j-point bijection to subgroups of `EjBar` commutes with every `Qj`-automorphism of `Kbar`. Lake build passed, 2 standard-axiom checks.
- `PairQuotientValue`: the iterated prime-kernel Vélu quotient invariant is well defined on pair classes. Lake build passed, 2 standard-axiom checks.
- `FiniteDescent`: evaluations separate elements of a finite reduced algebra. An equivariant tuple descends uniquely by the Artinian product decomposition and fixed fields. Lake build passed, 4 standard-axiom checks.
- `QuotientInvariant`: the iterated Vélu values on the pinned generic pairs descend to `Y0RationalGenericQuotientJ`, with evaluation at every geometric point. Lake build passed, 6 standard-axiom checks.
- `QuotientValue`: the vendored cyclic-quotient root bijection and transitivity apply to the pinned generic fibre. Its field has degree ψ(N), and the actual quotient invariant generates it with the specialized modular polynomial as its minimal polynomial. Lake build passed (10083 jobs), 12 standard-axiom checks.
- `FieldComparison`: the pinned generic field is isomorphic over `Qj` to the fixed modular Laurent-series field. The first invariant maps to `jq` and the actual Vélu quotient invariant maps to `jqN N`. Lake build passed (10166 jobs), 12 standard-axiom checks.
- `Geometric`: the rational quotient remains a domain over every extension of ℚ. The coefficient map to Laurent series stays injective by linear independence in a basis of the extended ground field. Lake build passed (10167 jobs), 3 standard-axiom checks.
