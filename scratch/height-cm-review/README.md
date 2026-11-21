# Symmetric theta descent and CM degree

This fork draft develops two inputs to DZQ’s height argument. The Pazuki work asks whether the **given** symmetric principal theta class descends to a finite extension of its field of definition. The CM work isolates the class-field embedding needed to bound the degree of the field containing a singular modulus. Both board fields remain open. [Pazuki board entry](https://github.com/Deicyde/diophantine-z-q/blob/fa21b10759ad132c985aca8c6ba456cb42e66f7f/docs/one-proof/OPEN.md#pazukicor13upper) · [CM board entry](https://github.com/Deicyde/diophantine-z-q/blob/fa21b10759ad132c985aca8c6ba456cb42e66f7f/docs/one-proof/OPEN.md#cmjdegreeprint)

## Pazuki

[Symmetric descent](../../ZInQKernel/Contrib/OneProof/PazukiSymmetricDescent.lean) recovers the original fixed point from a point over a finite extension once local quasi-finiteness holds at its image. [Picard inversion](../../ZInQKernel/Contrib/OneProof/PazukiPicardInvolution.lean) targets the restriction of the actual represented pullback by inversion to the open identity component. It uses the project’s existing representability and characteristic-zero identity-component hypotheses. Pulling the addition formula back along the graph of inversion identifies this restriction with group inversion.

The geometric argument translates the open identity component by a fixed point. Inside this chart the fixed equation becomes the kernel equation for multiplication by two, a finite morphism in characteristic zero. [Descent along the base change](../../ZInQKernel/Contrib/OneProof/PazukiQuasiFiniteDescent.lean) uses the project’s finite-fibre theorem on each affine open. The whole Picard fixed locus can have infinitely many components. Relating a resulting point of the parameter scheme to the given line bundle, with its ampleness and section dimension, is required for the archived descent target. [Original arithmetic target](https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/docs/research/pazuki-inputs.md)

## CM

[CM degree comparison](../../ZInQKernel/Contrib/OneProof/CMjDegreeFromRingClass.lean) uses an embedding of the ring class field of the supplied order into the quadratic field with the actual modular value adjoined. That direction supplies the Picard-cardinality lower bound. For the full equality the same value also needs a nonzero rational annihilating polynomial of degree at most the class number. Both arithmetic inputs remain explicit. [Downstream consumer](https://github.com/Deicyde/diophantine-z-q/blob/fa21b10759ad132c985aca8c6ba456cb42e66f7f/ZInQKernel/Contrib/OneProof/CMjBridgesArithmetic.lean#L36-L47)

## Formal checking

The base is Jack’s revision `fa21b10759ad132c985aca8c6ba456cb42e66f7f` with Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. odProof runs the pinned project on Modal. The focused checks apply declarations to explicit typed targets and query transitive axioms. A separate project reporter searches for matches against the bundled open hypotheses. A match with premises leaves those premises open.

The original Pazuki module built successfully on Modal. Its four axiom queries returned only `propext`, `Classical.choice` and `Quot.sound`. The first full Pazuki scratch failed on an identifier. The repaired scratch is awaiting a complete run. The first CM and project-reporter builds timed out during dependency compilation. These results cover the original two candidates. The new fixed-locus sources are research drafts pending their own focused checks. [Pazuki scratch](CheckPazuki.lean) · [CM scratch](CheckCM.lean) · [Project reporter](Discharges.lean)
