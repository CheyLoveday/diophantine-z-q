# Isogenies act on normalized period lattices

**G2an is proved without any unproved mathematical input.**

The contribution is `AnalyticTransport.lean`, in namespace
`ZInQ.Contrib.RC53Assist.IsogenyLatticeAnalytic`.

## Exact target theorem

```lean
isogenyLatticeAnalyticGlue_holds :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.IsogenyLatticeAnalyticGlue
```

The target proposition expands to:

```lean
∀ (F : Type) [Field F] (σ : F →+* ℂ) (E₁ E₂ : WeierstrassCurve F),
  E₁.IsElliptic → E₂.IsElliptic →
  ∀ (β : TauCeti.Isogeny E₁.toAffine E₂.toAffine) (α : F),
    ZInQ.Contrib.CloudB3RC53.ModularWeil.IsPullbackScalar β α →
    ∀ L₁ L₂ : PeriodPair,
      ZInQ.Contrib.CloudB3RC53.ModularWeil.IsLatticeOfEmb σ E₁ L₁ →
      ZInQ.Contrib.CloudB3RC53.ModularWeil.IsLatticeOfEmb σ E₂ L₂ →
      ∀ l ∈ L₁.lattice, σ α * l ∈ L₂.lattice
```

In particular, no nonzero-scalar assumption has been added to the target.

## Proof

1. The normalized coordinates `℘ − b₂/12` and `(℘′ − a₁x − a₃)/2` satisfy the embedded curve equation as germs at the punctured origin. The pole of `℘` makes the first coordinate transcendental, so coordinate-ring evaluation is injective.
2. Localization extends this evaluation to the function field. Every evaluated rational function has a globally meromorphic, lattice-periodic representative. Nonzero denominators give units in the germ ring.
3. Differentiation of these representatives defines a derivation. Its map on Kähler differentials sends the normalized invariant differential to `dz`. Applying it to `IsPullbackScalar` proves the analytic derivative identity with the embedded scalar.
4. The G1 local inverse of the target Weierstrass function gives a local affine lift. The meromorphic identity theorem extends its first-coordinate identity. Source periodicity produces a local target period, which the G1 local-period theorem identifies as a lattice vector.

The constant term in the local affine lift cancels. No pointed analytic lifting theorem, uniformization existence assertion, or period-inclusion print is assumed.

Mathematical locators are recorded in every declaration's docstring. The normalization is the one in Silverman, *The Arithmetic of Elliptic Curves*, VI.3; the exact target is in `ZInQKernel/Contrib/CloudB3RC53/ModularWeil/IsogenyLattice.lean`.

## Verification

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- The complete contribution compiled with the prescribed single-file command, six threads and the specified CPU affinity, with exit code 0 and no warnings.
- The G1 compiled module `ZInQKernel/Contrib/RC53Assist/NewformPeriodsG1/ParametrizationPeriods.olean` exists in the supplied build cache and is 3,491,008 bytes.
- A separate scratch audit re-elaborated the complete source and inspected all **35 theorem statements** and their transitive axiom dependencies. It also completed with exit code 0 and no warnings.
- Every theorem's dependencies are exactly `[propext, Classical.choice, Quot.sound]`. No additional axiom or unproved mathematical input occurs.
- [StatementsAndAxioms.txt](StatementsAndAxioms.txt) contains the compiler's complete exact statement and axiom output for each of the 35 theorems.
- The delivered Lean source has no proof placeholders, extra axioms, native evaluation, new notation or syntax, or inspection commands. Its heartbeat bound is 800,000.

The main theorem's transitive axiom output is:

```text
'ZInQ.Contrib.RC53Assist.IsogenyLatticeAnalytic.isogenyLatticeAnalyticGlue_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Files

All contribution files are under `ZInQKernel/Contrib/RC53Assist/IsogenyLatticeAnalytic/`.

- `AnalyticTransport.lean`: 41,766 bytes; SHA-256 `32717cc7e42f3a5bac762b7a82a63a2cdd980ba8509f1c9c7811eadc9fe4c1cf`.
- `StatementsAndAxioms.txt`: 14,261 bytes; SHA-256 `7a3590432364f25e986a88d8e18c69df905c389ac2b046cd81b3857bc9d7bf6b`.
- `SHA256SUMS` records checksums for the source, the statement/axiom output, and this report.

The inspection commands are confined to a scratch file, not the delivered Lean source.

## Remaining work

**Nothing remains mathematically for G2an.** No existing file was edited, and no commit or integration was performed. A downstream consumer still needs to import the new module and use `isogenyLatticeAnalyticGlue_holds`; that wiring is outside this read-only contribution.

This contribution does not establish the separate rational-scalar existence/nonvanishing statement G2alg. The existing deduction of the full G2 statement still uses that separate algebraic input.
