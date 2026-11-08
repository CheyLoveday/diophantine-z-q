# Arithmetic bridge specification, revision 1

Profile: development. Local Lean 4.35.0 compilation, elaborated statement
inspection and transitive axiom audit; no protected comparator, export replay,
external checker or paranoid claim. Permitted axioms: `propext`,
`Quot.sound`, `Classical.choice`. No additional arithmetic axioms are admitted.

Target module: `Research.DerivativeSwitch.ArithmeticBridge`, importing the
unchanged `Research.DerivativeSwitch.BoundaryCup`. The exact target inventory
is retained in `evidence/native/Audit.lean` once implementation is frozen.

## Intended inference

1. For a representation and an additive crossed cocycle, derive the full
   conjugation formula, including its coboundary term. When the local action
   is trivial and the transporter acts by one specified integral unit,
   derive the common inverse-unit scalar. Do not assume global quadraticity.
2. At degree two against degree one, evaluate the explicit zero-parameter
   cone product on a pure local boundary. Bilinearity kills the global and
   isotropy homotopy terms. This is the elementary product calculation;
   constructing the whole Selmer complex remains outside this module.
3. Keep separate finite and singular class/orthogonal/transported carriers.
   Define the partner using the inverse orthogonal comparison and conjugate
   transport. Derive its local coordinates from commuting local maps,
   the raw conjugate transport and the actual old/new class coordinates.
4. Use a general boundary–duality adjunction and the SAME stored matrix rows,
   identified with pairing against those partners. Evaluate the concrete
   raw local cup. Derive `BoundaryCupIdentity` with opposite normalizers;
   neither the normalized adjunctions nor the desired unit comparison may
   be stored as input fields.
5. Invoke the existing integral-unit adapter for the actual `HasCoordinate`
   tensors. The coefficient subring and the determinant's integral unit
   witness remain explicit. Common trace/clearing scalars need not be units
   and can vanish in this division-free bridge.

The representation/cocycle lemma is a reusable algebraic justification for
the local-transport input. The formal interface still requires its realization
on the actual retained Galois objects. The general pure-boundary adjunction
also remains a source-level Poitou–Tate interface, justified in the ordinary
addendum rather than constructed as arithmetic cohomology in Lean.

## Boundary and fidelity checks

- No global finite/singular complex isomorphism or strict automorphism.
- No determinant-line map masquerades as a map of functional spaces.
- One coefficient `J`; raw conjugate transport has a tame minus sign.
- The common transport factor is shared, including with a nonquadratic
  global character. Independent rescaling of the rows is not permitted.
- `J²=1` and `det J=-1` derive symmetry of `area(f,J s)`; no integral
  eigenspace decomposition or division by two.
- The common trace scalar may be zero/nonunit; actual arithmetic rank-one
  arguments separately use the source's nonzero trace and local pairing.
- `CommonStrictData` supplies actual cycle/closed-row equations and the
  nonzero area/target determinant. Their arithmetic realization is explicit
  inherited work, not newly proved by this bridge.
- The separate-triangle determinant-functor proof remains ordinary
  mathematics. A matrix cofactor theorem is not a formal determinant functor.
- Required rings and limits are accounted for in the source application
  crosswalk; no Lean construction of those arithmetic localizations is claimed.

Publication authority for the incorporated argument will be the new LaTeX
addendum. The earlier reviewed `DERIVATION.md` is preserved as a frozen
research record. None of the 39-target inputs or their sources is changed.
