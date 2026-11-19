# Local unramified values and Frobenius

## Result

Both original GLUE propositions are proved without additional hypotheses:

```lean
theorem localUnramifiedValueGroupPrint : LocalUnramifiedValueGroupPrint
theorem localFrobeniusGenerationPrint : LocalFrobeniusGenerationPrint
```

The namespace is `ZInQ.Contrib.RC53Assist.TateCurve`.
The aggregate theorem is:

```lean
theorem localArithmeticReadings :
    LocalUnramifiedValueGroupPrint ∧ LocalFrobeniusGenerationPrint
```

**Remaining mathematical or Mathlib gap: none for either target.**
The finite inertia lifting proposition introduced in the proof is itself proved;
it is not an assumed local-field input.

All new source files are under the public repository directory
`ZInQKernel/Contrib/RC53Assist/TateCurve/LocalReadings/`.
Existing definitions and sources were not edited. No Git commands, commits,
revision changes, or dependency updates were performed.
The work used the supplied integration base `e68f39ed`.

## Exact unchanged targets

These are the original definitions in `LocalArithmetic.lean`, quoted without weakening.
The local Galois and inertia definitions are those of `GlobalTrace.CoinvariantReadings`.

```lean
def LocalUnramifiedValueGroupPrint : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
    (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
      (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
    ∀ x : (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))ˣ,
      (∀ σ ∈ localInertia w, Units.map σ.toAlgHom.toMonoidHom x = x) →
      ∃ a : ((primeIdealQ p hp).adicCompletion ℚ)ˣ,
        w (x : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) =
          w (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
            (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) (a : _))

def LocalFrobeniusGenerationPrint : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
    (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
      (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
    ∀ σ : LocalGaloisQ p hp,
      IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ →
      ∀ H : Subgroup (LocalGaloisQ p hp), IsOpen (H : Set (LocalGaloisQ p hp)) →
        localInertia w ≤ H → σ ∈ H → H = ⊤
```

In particular, the Frobenius proof does not require normality of the open subgroup.
The value-group proof allows every value-group normalization in the original target.

## Proof and bridge inventory

All items below are **PROVED**.

1. **Valuation uniqueness and integral closure.**
   The spectral unit ball is the integral closure of the base valuation ring.
   Any extending valuation ring contains it. Its dimension is at most one, so a
   nontrivial coarsening cannot be proper. Every extending valuation is therefore
   equivalent to the spectral valuation and invariant under the full local Galois group.
   Locator: Serre, *Local Fields*, II, §2; spectral values and valuation-ring coarsenings.

2. **The local residue action.**
   The residue field is algebraic over the prime field. Reduction gives a continuous
   homomorphism from the full local Galois group to its residue Galois group, with
   kernel exactly `localInertia w`. Arithmetic Frobenius reduces to the `p`-power map.
   The residue homomorphism is also proved surjective.
   Locators: Serre, *Local Fields*, I, §8 and III, §5.

3. **Frobenius generation.**
   A closed subgroup of a prime-field Galois group containing arithmetic Frobenius
   has fixed field equal to the prime field. The image of a local open subgroup is
   closed by compactness. Pulling back its full residue image and using the kernel
   proves `LocalFrobeniusGenerationPrint`.
   Locators: Serre, *Local Fields*, I, §8; infinite Galois correspondence.

4. **Finite inertia lifting.**
   Restricted integer rings in finite Galois subextensions are finite, free over the
   base DVR, and DVRs. The finite ring-theoretic inertia restriction theorem applies
   to the genuine integral-closure actions. Finite lifts are glued by compactness
   over the directed system of finite Galois subextensions. Thus every finite inertia
   automorphism lifts to absolute inertia.
   Locator: Serre, *Local Fields*, III, §5; inverse-limit Galois theory.

5. **The inertia-fixed value group.**
   An inertia-fixed algebraic element lies in a finite Galois subextension of the
   inertia-fixed field. Absolute inertia restricts onto its finite inertia, so that
   finite inertia is trivial. Its ramification index is one by the finite inertia
   cardinality theorem. The normalized valuation comparison at primes lying over
   one another supplies the required nonzero base-field element.
   Locator: Serre, *Local Fields*, III, §5.

The citations are section-level locators for mathematical readings, not claims of
verbatim printed statements or newly checked theorem numbers or pages. References
here to *Local Fields* mean Serre's Springer GTM 67 book. They do not identify that
book with the manuscript's `serrelocal` bibliography item, which is Serre's chapter
in Cassels–Fröhlich.

## Non-vacuity

`Nonvacuity.lean` proves, for every rational prime:

- an actual extending valuation and arithmetic Frobenius exist;
- the field unit represented by the rational prime is fixed by inertia and has value
  strictly less than one;
- the open-subgroup hypotheses are realized by the full subgroup;
- finite-field Frobenius is nonidentity in a quadratic finite-field extension.

## Build and axioms

The aggregate module builds with Lean **4.35.0** and Mathlib **v4.35.0**:

```sh
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=8 taskset -c 0-31 nice -n 10 \
  lake build +ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.Main
```

Result: **build completed successfully**, including both exact targets and the
aggregate theorem. `BuildReceipt.txt` records the successful build.

`AxiomAudit.txt` contains the actual axiom output for all **77** new source declarations
and the checked types of the two target proofs and aggregate theorem. The axiom union is:

```text
[propext, Classical.choice, Quot.sound]
```

Both target proofs depend only on these standard axioms. There is no additional axiom,
unfinished proof, or assumed value-group/Frobenius-generation proposition.
The standard-input audit commands are not retained in any Lean source file.

Source checks passed for all **11** Lean files: **79,653 bytes**, **1,619 lines**.
All non-import source lines are at most 100 characters, heartbeat settings are at most
800,000, and no forbidden proof shortcut, declaration, command, or private identifier
was found. Hash checks confirmed **30** preexisting source/configuration files unchanged.

## Source files, sizes, and SHA-256

- `ResidueFrobenius.lean`: 5,287 bytes; 108 lines.
  SHA-256: `db8633653ebbf391c22d520a2257f2a24ef6c40c44967ce5e22809d9690b1513`
- `ValuationExtension.lean`: 8,582 bytes; 165 lines.
  SHA-256: `f01a44bf5cf06a9e6f03b0cd1dec15e4b4f8d8b834b203b5339f2e66b4f9e659`
- `LocalResidue.lean`: 11,983 bytes; 252 lines.
  SHA-256: `c1591802cff3b42c4660355395c93b51543eae8c38554dacae00c4a03ea684f7`
- `GaloisTopology.lean`: 3,642 bytes; 80 lines.
  SHA-256: `f736e0e687bc6895d1c939fa9a9208d34d3317d5aa669785f68c577dbf745c64`
- `LocalFrobenius.lean`: 5,193 bytes; 113 lines.
  SHA-256: `2e457beb413d77b8d957bcbcb79a52a9d7c097136fe18588ad5ea2e93af11521`
- `FiniteExtensions.lean`: 11,794 bytes; 231 lines.
  SHA-256: `0d301608978e1db2085000c4f864d2a1fb4cf35bd0f95d4394de161f7deee78c`
- `FiniteTower.lean`: 11,334 bytes; 229 lines.
  SHA-256: `a2ba082cebe69efd1e62d2ad8ea3328c53e42daca34238a42ed0606aa1226606`
- `InertiaRestriction.lean`: 6,032 bytes; 124 lines.
  SHA-256: `b3771c81a288d5d573633e48a198936941348f94772c84d78793f16e4efc0edf`
- `UnramifiedValueGroup.lean`: 11,215 bytes; 218 lines.
  SHA-256: `d6644f7468d7cf29c985a6ce443b6ff7524f5f1305d5c7a743a91be98d86348d`
- `Nonvacuity.lean`: 3,693 bytes; 77 lines.
  SHA-256: `0f30f526c07be085859b67317559a7b57c072a52d6e6cb283bb482bcfd3479e0`
- `Main.lean`: 898 bytes; 22 lines.
  SHA-256: `47ce7fa89224b8dde77c065445f025c1385baa230a8450f76e49a5ad9476ba4e`

`SOURCE_MANIFEST.json` and `SHA256SUMS` provide machine-readable custody records.
