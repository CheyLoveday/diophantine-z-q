### 1) Verification target

**Accepted within the stated conditional arithmetic-bridge scope.**

The strongest contribution is the derivation of the opposite boundary–cup normalizers from the specified partner construction, shared conjugate transport and raw local cup, followed by the existing general-size integral-unit comparison on the same realized classes and rows.

Reviewer: `/root/review_core_contribution`, internal non-author model review, 2026-11-08. I inspected sources and retained evidence read-only, raised typing and identity findings, and checked the author’s corrections. I did not edit files, run Lean or finite tests, dispatch cloud work, commit or push. Shared context/model limitations remain; no human acceptance is claimed.

This decision binds:

| File | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitch/ArithmeticBridge.lean` | `2b72fc4237d45feb84973e470f0887c3ef3768cfaaedec967857a4ca01c09ef6` |
| `research/arithmetic-boundary-cup/FORMAL_SPEC.md` | `e851cce863eed11ba9b713d39d3627b4c027c17cb15386c735969cdc90cc22f9` |
| `research/arithmetic-boundary-cup/APPLICATION.md` | `a00a0ab8b0eaf014bba81cd44a8e683dbe7b3c63492529780354979303252102` |
| `research/arithmetic-boundary-cup/manuscript-insertion.tex` | `236abc7bc0f7e25baca29a428e271ffe8c9a3f5dc7cb7b6c0482631d9d9da28b` |
| `research/arithmetic-boundary-cup/evidence/native/RESULT.json` | `57bb68c3b89b728a9603b3a6bb947c23e3f4b5d34971ccd51f83985afb08c17c` |
| `research/arithmetic-boundary-cup/evidence/native/axioms-and-statements.txt` | `285a204315a36c9be24af289b2a84654fd76c986e164627f6e3920e4776858ff` |
| `manuscripts/quartic_v13.tex` | `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` |

The source checks included the actual manuscript coefficient pairing, H11–H22, paired-functional definition, derivative conditions, retained limits and consuming switch argument; the earlier scalar-ratio implementation; and Nekovář’s explicit cone and boundary-product formulas. The historical full section 9 remains unresolved in the bounded lookup.

### 2) Independent re-derivation (outline)

The cocycle formula follows by expanding \(p(a(a^{-1}xa))=p(xa)\) in two ways and applying \(\rho(a)^{-1}\). Trivial local action removes precisely the coboundary term. If the transporter acts by a specified integral unit, its inverse supplies the common inverse-unit scalar; global quadraticity is unnecessary.

The partner is defined as \(j^{-1}c(z)\). The commuting localization maps determine its local coordinates. This is a consequence of the specified inverse comparison, rather than a separately assumed partner normalization.

In the degree-\((2,1)\) cone product, a pure local boundary has zero global and local-condition components. Bilinearity kills the homotopy terms and the degree-two/degree-zero cup term, leaving the degree-one mixed cup.

With \(Q(x,y)=\operatorname{area}(x,Jy)\), involution and determinant \(-1\) imply symmetry of \(Q\), without dividing by two. Applying the raw cup to the actual local partners \((uv,0)\) and \((0,-uJv)\) gives
\[
c_F=-\kappa_0u,\qquad c_S=\kappa_0u.
\]
The two normalizers therefore differ by the explicit integral unit \(-1\). The formal theorem derives these all-vector identities and invokes the unchanged unit adapter; it does not assume the desired normalized identities or determinant comparison.

The final consumer explicitly identifies the realized actual classes with the stored cycle vectors and the stored rows with the specified paired functionals. Its `HasCoordinate` assumptions concern those realized classes.

The addendum’s separate-triangle determinant argument is sound relative to the retained arithmetic inputs. It preserves the common integral strict determinant factor, including torsion, and allows fractional complements. This remains an ordinary proof, not a formal determinant-functor construction.

### 3) Checks

- **Statement fidelity:** Inspected elaborated definitions and theorem types, including separate finite/singular carrier universes, the integral subring and unit arguments, all-vector boundary/row identities, and the class-realization equalities used by the final consumer.
- **Typing:** The degree-one mixed cup and degree-two/degree-zero cup now have separate carriers and maps.
- **Actual-object identity:** Local-coordinate agreement is supplemented by explicit realization equalities; it no longer substitutes for class identity.
- **Normalization:** The insertion retains the actual shared unit in both partners and only combines it with the trace factor during evaluation. It does not rescale either actual class.
- **Boundary cases:** The formal comparison allows zero/common-nonunit trace factors. The ordinary arithmetic rank argument separately requires the actual nonzero trace and pairing. Divisible localization vectors, characteristic two algebra, nonquadratic global characters and the stated exceptional localization scopes are treated consistently.
- **Native evidence:** The retained commands compile five modules freshly with Lean 4.35.0 and kernel checking enabled. The new module has no diagnostics. The nine selected declarations have only `propext`, `Quot.sound` and, where recorded, `Classical.choice`. I inspected the audit implementation and output; I did not rerun them.
- **Bindings:** All twelve native input hashes match current files. I independently recomputed all entries of the frozen 63-, 65- and 99-input manifests; none changed.
- **Cloud separation:** The preservation receipt reports the same 39-target generated manifest, `117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`. No result for the running cloud job is inferred.

### 4) Discrepancy report

No unresolved defect remains in the reviewed scope. The earlier draft findings—incorrectly conflated cup degrees, missing explicit class realization, and wording that suppressed the actual common transport unit—are corrected in the bound files.

The important remaining boundary is explicit: `boundary_adjoint`, conjugate-local compatibility, and the common-strict arithmetic realization are interface requirements. The module does not construct actual Galois cohomology, Heegner classes, Selmer complexes, Poitou–Tate duality or retained arithmetic limits.

### 5) Certification result

**CERTIFIED under the explicit retained-source and formal-interface assumptions.** The new module faithfully formalizes the normalization bridge and its integral-unit consumer. The native evidence and this semantic review support development-level verification of that conditional contribution.

The accurate leading claim is:

> Derived the boundary–cup normalization comparison from specified retained duality and conjugate transport data, and connected it to the general common-strict integral-unit theorem on explicitly identified classes and functionals.

This is addendum incorporation, not canonical V13 incorporation. Full arithmetic instantiation, formal determinant functors, external-kernel verification of the new module, and whole-paper acceptance remain outside this result.
