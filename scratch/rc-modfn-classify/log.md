# Results log

Base: `b6f83412fd4e8da6ca55c764c65b95998e1cabbc`.

| File | Checked statement or finding | Compile |
| --- | --- | --- |
| `Interior.lean` | Compact truncated fundamental domain; finite exceptional set; monic pole clearing. | Pass |
| `LevelOne.lean` | $qj$ has analytic unit germ; cancel principal part; bounded weight zero is constant; $gD(j)=P(j)$ on punctured germs. | Pass |
| `CuspGrowth.lean` | Periodicity, eventual holomorphy, and a bound after a power of $q$ imply a meromorphic cusp germ; width of the bound is immaterial. | Pass |
| `Cosets.lean` | Right cosets inject into the projective line modulo $N$; cardinality at most `dedekindPsi N`. | Pass |
| `Orbit.lean` | Invariant monic orbit polynomial; root equal to given function; coefficients meromorphic in the width-one parameter and rational in $j$. | Pass |
| `FormalOrbit.lean` | Formal equation over ℂ(j(q)); integrality and minimum polynomial degree at most `dedekindPsi N`. | Pass |
| `Compositum.lean` | Uniform bound on the degrees of $x+cy$ by the degree of $x$ implies $y∈F(x)$ for integral $x,y$ in characteristic zero. | Pass |
| `Classification.lean` | $j(Nτ)$ realizes the second formal generator and satisfies translate growth via the modular polynomial; exact generator degree; `ComplexCuspClassification N` for every positive level. | Pass |
| `PrimitivePole.lean` | Nonconstant scaled primitive; actual affine $x$ germ is polar at every lattice value. | Pass |
| `ProjectiveIdentity.lean` | Identity iff lattice value; affine sections give the two coordinates; `projectiveValue = phiAn` for all upper half-plane parameters. | Pass |
| `AtScale.lean` | Actual curve with supplied `X0Model` and rational representative of original scale; prepared values, missing values, and oriented CM values. | Pass |

- Proof sources audited by `#print axioms`; allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Remaining inputs: supplied `X0Model`; existing normalized coefficient, lattice and period data; rational representative of the fixed scale; `CMFieldOfDefinition` or oriented chart inputs for respective consumers.
- Separate: algebraic cusp specialization, quotient/Jacobian and Hecke compatibility, good reduction comparison.
- Verification: serial `lake env lean -j1 -DautoImplicit=false`; load and available memory checked before each invocation.
