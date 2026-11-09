# Independent boundary–cup review

Reviewer: Codex agent `/root/orthogonal_attack`, 2026-11-09.
Author reviewed: separately instantiated agent `/root/boundary_cup_attack`.
This is internal model review, not an external mathematical referee or a new
whole-paper acceptance. No author proof text was modified by this reviewer.

### 1) Verification target

Verify the source-bound inference in `research/actual-boundary-cup/DERIVATION.md`
and `APPLICATION.md`: an actual opposite-plane connecting class evaluates under
the manuscript's PD functional by one local invariant cup; the actual partner's
localization then gives opposite normalizers with relative integral unit -1.
The seven new Lean roots only prove the local representative-correction and
trace consequences; they do not construct the arithmetic objects.

Reviewed source head `fb29fe2bc6968e178a6458357c437574221b5338`; V13 hash
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
Read the actual V13 local model, H22, paired-functional and inner-limit
arguments, the new Lean module and native receipt, and the complete cochain
script. Independently read the retained published Nekovar PDF text, sections
1.3.1–1.3.2 (p41) and 6.3.1–6.3.3 (pp140–142). PDF bytes hash
`61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
The actual source product and one trace square, not merely their theorem names,
were checked. Earlier source/model existence assertions are reused premises;
this review does not certify their complete arithmetic construction.

### 2) Independent re-derivation (outline)

- In the direct local quotient, lift s as `(0,s,0)`. Its cone differential has
  pure local component s with the chosen Nekovar sign. The other plane works
  identically, so an H22 sign change reverses both signs together.
- Substitute `(0,0,l)` into the general product formula of 1.3.2(i), r=0.
  First product components vanish by bilinearity, and the only surviving third
  term is `l cup i(u)`. All compatibility/isotropy terms have a zero first
  input; they vanish without choosing a normalization.
- The partner's cone cycle equation is `i(u)=loc(g)+dq`. For closed l of
  degree1, `d(l cup q)=-l cup dq`; hence the discrepancy is exactly the
  compact-support boundary `D(0,0,l cup q)`. This is stronger than asserting
  equality only after passing to an unspecified local pairing.
- Nekovar 6.3.1 constructs the PD map by adjunction from this product followed
  by rJ. Its target B3=0 and its local-invariant square are common to both
  choices of local plane. Tracing the displayed boundary yields the claimed
  actual cohomological evaluation with a common sign.
- Substitute the actual partner H1 coordinates from the independently derived
  cone comparison: `(uv,0)` and `(0,-uJv)`. Inserting J once in the coefficient
  form gives `qF=-kappa*u*epsilon*area(v,x)` and `qS=-qF`. No independent
  rescaling or finite/singular chain equivalence has entered the calculation.

### 3) Checks

Plug-back: directly expanded both B5 expressions into
`epsilon*(area(f,J s')-area(s,J f'))`; used J²=1 and detJ=-1 for the coefficient
symmetry. Setting the complement area nonzero does not by itself prove kappa
nonzero. The packet correctly separates that rank guard.

Boundary cases: zero actual class, zero functional and zero common trace factor
remain valid for the unit-normalizer algebra. A proof of rank independence from
cross evaluations must explicitly exclude the zero common factor. At two,
self-cup vanishing requires the stated adjusted local model; graded
commutativity alone is not sufficient. The text retains that requirement.

Representation and map checks: the conjugate coefficient carrier is not silently
identified with M. Orthogonal inverse preservation is on H1, enough because B3
and the trace remove representative dependence. No map from one individual H2
functional space to the other is inferred from determinant lines.

Computation: independently reran `python -B
research/actual-boundary-cup/check_cochains.py`; output matches the retained
receipt: 256 trials, all with a nonzero cochain correction; torus H1 dimension2
and alternating trace matrix [[0,9],[-9,0]]. Wrong correction sign, evaluation
not killing local boundaries, and omitted closedness each have an explicit
counterexample. These are cochain model checks and do not verify actual Galois
Selmer complexes. Native seven-root receipt reports Lean4.35 compile/axiom audit,
no paranoid or independent external replay. The Lean source has no assumption
named boundary adjunction or desired unit relation; its premises are Leibniz,
cycle closedness, cone cycle relation and trace killing differentials.

### 4) Discrepancy report (if any)

One editorial provenance mismatch was raised with the author: SOURCES.json
records exact locators and hashes rather than literal source excerpts. The
source formula itself was independently read and is not missing mathematically.
Final binding below applies to the author's corrected description.

Important scope distinction, already respected by the packet: Nekovar's trace
is a map to an injective target complex J[-3]; the cohomological invariant lies
in the coefficient ring. The new scalar chain-trace helper is not a complete
formal construction of that global map. Its use does not eliminate the source
trace/retained-diagram premise. Likewise, preservation of the enlarged finite
tuple requires that actual cup, trace and their homotopies are all retained;
a previously retained local conjugation unit alone does not suffice.

### 5) Certification result

**CERTIFIED as a bounded ordinary cochain/source inference under the explicitly
reused arithmetic constructions and retained-data premises.** The new explicit
representative correction is valid, the shared trace forces the two actual
normalizers' relative unit, and the local Lean helper/checks support exactly
that limited algebraic step. No mathematical error found in this inference.

**NOT CERTIFIED as a complete formal arithmetic switch or independent whole-proof
verification.** Actual global Galois/cup/trace objects, full retained-inner
existence/bounds and integral determinant/universal descent remain outside the
seven formal roots. The author's contract preserves these distinctions.

The author corrected both the excerpt/locator description and a reference to
ArithmeticBridge as separate follow-up code rather than frozen code. I reread
those two final sentences; neither changes the mathematics. The final native
receipt binds the amended derivation and unchanged Lean module. The final
14-root combined axiom inventory likewise contains only propext, Quot.sound
and Classical.choice; its new modules are exactly these boundary lemmas and
the orthogonal helper. This does not expand the source application coverage.

Reviewed exact-byte SHA-256 bindings:

```json
{
  "research/actual-boundary-cup/DERIVATION.md": "ce2084ecbadaa62c861ef92e443d2f78231a8d59c4f90cf3080cb78545387a28",
  "research/actual-boundary-cup/APPLICATION.md": "24400ff8ee75d99d4977df5e751e62f71484f4b66308548e6f41ddfb514ef136",
  "research/actual-boundary-cup/README.md": "07791183ad317f7249047940803d465f99e828b13fcc9898daea4ab4b017a5e7",
  "research/actual-boundary-cup/SOURCES.json": "b88a12505baf207af136f1c60cd08e48423ec34c95cfba91b2734d2662053893",
  "research/actual-boundary-cup/check_cochains.py": "ad9c45851b76cdfdb4c7d360e4a4c034ca36911647f45c8770c3635674280c60",
  "research/actual-boundary-cup/evidence/cochain-checks.json": "5626d224d85a1af8bb5d487710b595e878abc81ec512566179551f3d8a6c2a8d",
  "research/actual-boundary-cup/evidence/native-reviewed/RESULT.json": "b79c7fdda9296f6d0133657512bf2bf07ce37b1f8665c39fdaa6167007eaa76d",
  "lean/Research/DerivativeSwitch/ActualBoundaryCup.lean": "77bcdd2ae5283ffd6cc51062e452da4294fcd5b3d952940b588b2d5b52ecdd90"
}
```
