# RC model levels results

- Reynolds base merged into the torsion base.
- Verdict committed for the level-one boundary. The exact-order-one locus is the identity section.
- `Divisibility` passed targeted `lake build`. It proves the abscissa divisibility over algebraically closed fields and over domains by monic descent from the fraction field. Both axiom prints list only `propext`, `Classical.choice`, and `Quot.sound`.
- The initial Lake invocation scheduled uncached prerequisites concurrently. Subsequent builds serialize Lean compiler invocations with a lock inside the required systemd scope.
- `Clopen` passed targeted serial `lake build`. A surjection of étale algebras cuts out an idempotent, its complement is finite étale for a finite source, the complement commutes with scalar extension, and field-valued points detect the closed factor by vanishing. Axiom prints list only the permitted axioms.
- `AffineDivisor` and the extracted monic descent lemma in `Divisibility` passed targeted serial `lake build`. The construction preserves the two charts and gives surjective algebra maps whenever the quadratic chart division equations divide. The requisite divisibility holds over a domain with invertible level. Axiom prints list only the permitted axioms.
- `UniversalDivisibility` passed targeted serial `lake build`. The universal domain is the five-coefficient integer ring with the level times the discriminant inverted. Specialization gives both divisibility statements and the affine restriction over every elliptic coefficient ring with invertible level. Axiom prints list only the permitted axioms.
- `ExactOrder` passed targeted serial `lake build`. The product of the proper divisor idempotents cuts out their common complement. The exact-order-one algebra is the coefficient ring. The finite étale theorem and the field-valued nonfactorization criterion have only the permitted axioms.
