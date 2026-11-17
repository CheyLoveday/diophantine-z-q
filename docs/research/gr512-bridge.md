# gr512-bridge: González–Rotger Thm 5.12 as printed, over Tau Ceti's ring class field

Task gr512-bridge (2026-11-17). Base: wip/leaf-fold33b 75d94fe7 (TailZ67, top `sixContactMin_of_open60`;
origin/main is an ancestor). Contributor file: `ZInQKernel/Contrib/OneProof/GR512Bridge.lean` (namespace
`GR512Bridge`; imports `…OneProof.GRDict`, Tau Ceti's `…ClassFields.RingClass.Field` and
`…OneProof.EichlerBound.Order`, never `Main`; no `sorry`). Scratch: `scratch/gr512-bridge/` (log: `log.md`).
Marks: VERIFIED (compiled, or read in the tree), STANDARD (published, exact reference), SPECULATIVE, UNVERIFIED
(theorem numbers from memory; no network on this host).

## 1. Result

**The research field `gonzalezRotgerThm512X6` (strict review 11-17: GLUE, consequence, on steps S1 and S2) is
proved in Lean from one new leaf, `gonzalezRotgerThm512X6RCF`, which is González–Rotger Thm 5.12 in its printed
form: `ℚ(P) = H_R` over Tau Ceti's `ringClassField`, with `D(R)` read off the order itself.** Every consumer is
unchanged (the old field is derived exactly).

```
GR512Bridge.gonzalezRotgerThm512X6_of_rcf :
  GR512Bridge.GonzalezRotgerThm512X6RCF → GRDict.GonzalezRotgerThm512X6
```

| review item | status here |
|---|---|
| S2: degree in `CommRing.Pic R` needs CFT + a `ClassGroup ≃ CommRing.Pic` bridge; Tau Ceti's `ringClassField` unused | **closed**: the leaf now says `ℚ(x) ≃ₐ[ℚ] ringClassField O` (resp. an index-two subfield); the degree form is a Lean proof from Tau Ceti's `finrank_ringClassField` and the bridge `picEquiv : Pic O ≃* CommRing.Pic R` (VERIFIED) |
| S1: `inertCount6 k` vs GR's `D(R)N*(R) ≠ 1` (Eichler symbols) | **matched by a proof, one reading point left**: the leaf uses `grD6 R`, the product of the `p ∣ 6` with `pR` prime **in `R`** (Eichler symbol `(R/p) = −1`); `grD6 R ≠ 1 ↔ inertCount6 k ≠ 0` for conductor prime to 6 is proved (`grD6_ne_one_iff`, VERIFIED). What remains is reading GR §5's definition of `D(R)` (§4) |
| N1: maximality of `LeafQM.O` unproved | **proved**: `N1.O_maximal` (VERIFIED) |

**Count** (autofold `--dry-run`, §6): the field `gonzalezRotgerThm512X6` (GLUE) is replaced by the published leaf
`gonzalezRotgerThm512X6RCF` (flag "reading risk: …", counted LEAF): **GLUE −1** in strict and strictest, no new glue.

## 2. The new leaf (verbatim)

```lean
def GonzalezRotgerThm512X6RCF : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ O : NumberFieldOrder k, Nat.Coprime (conductor O.toSubalgebra.toSubring) 6 →
        ∀ x : fieldPt Qbar ⟶ X, GRDict.IsGRCMPoint Ψ O.toSubalgebra.toSubring x →
          (grD6 O.toSubalgebra.toSubring ≠ 1 →
            Nonempty (residueImage (X := X.left) x.left ≃ₐ[ℚ] ringClassField O)) ∧
          (grD6 O.toSubalgebra.toSubring = 1 →
            ∃ F : IntermediateField ℚ (ringClassField O),
              Module.finrank F (ringClassField O) = 2 ∧
              Nonempty (residueImage (X := X.left) x.left ≃ₐ[ℚ] F))
```

with

```lean
def grD6 (R : Subring k) : ℕ :=   -- open Classical
  (if (Ideal.span {(2 : R)}).IsPrime then 2 else 1) * (if (Ideal.span {(3 : R)}).IsPrime then 3 else 1)
```

### 2.1 Rating: printed form, yes (flag "reading risk", one reading point: GR's definition of `D(R)`)

* **The print.** González–Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58 (2006),
  Thm 5.12, p. 946, as read by the locator audit (docs/research/locators.md, row "R5: fields of definition"):
  for `P ∈ CM(R)`, `R` of conductor prime to `DN`, `ℚ(P) = H_R` if `D(R)N*(R) ≠ 1`, and otherwise `ℚ(P)` is a
  specified subfield of `H_R` of index two.
* **Clause by clause.**
  * `ℚ(P) = H_R` (subfields of `ℂ`) gives a `ℚ`-algebra isomorphism `ℚ(x) ≅ H_R`; "a specified index-two
    subfield" gives `∃ F ⊆ H_R, [H_R : F] = 2, ℚ(x) ≅ F`. Both are consequences, never stronger (the
    specification of `F` is dropped).
  * `H_R` is **Tau Ceti's `ringClassField O`**: the class field (global CFT correspondence) of the kernel of the
    idelic quotient `C_k → Pic O`, with `Pic O ≃* Gal(H_R/k)` (`ringClassArtinEquiv`). That is the ring class
    field of the order (Cox §9; Kopp–Lagarias Thm 1.1), a genuine definition, not one invented for the purpose.
  * `R` is a Tau Ceti `NumberFieldOrder`; conductor prime to 6 is the kernel's `conductor = [𝓞_k : R]`.
  * `D(R)`: the product of the `p ∣ D` with Eichler symbol `(R/p) = −1` (`grD6`). At `N = 1`, `N*(R) = 1`.
  * `CM(R)`: gr-dict's `IsGRCMPoint` (GR's own notion, transported to `ℚ̄`-points); the "every witness" form and
    `ℚ(x) = ℚ(σQ ∘ x)` are as gr-dict §3.3 argued, unchanged.
  * `𝒪 = LeafQM.O` is a maximal order (now a theorem, §5), so `X₀(6,1)` is GR's curve at `(D, N) = (6, 1)`.
* **The reading point (S1, precise).** GR define `D(R)` through Eichler symbols (review: GR §§2, 5, p. 946;
  UNVERIFIED on this host). The Eichler symbol of a quadratic order `R` at `p` is `(k/p)` (Kronecker) for
  `p ∤ f(R)` and `1` for `p ∣ f(R)` (STANDARD: Vignéras, LNM 800, Ch. II §3; Voight, *Quaternion Algebras*,
  §30.5, numbers UNVERIFIED). In both cases `(R/p) = −1` iff `R/pR` is a field iff `pR` is a prime ideal of `R`
  (for `p ∣ f`, `R/pR ≅ 𝔽_p[ε]/(ε²)`). So the leaf reads GR's `D(R)` as `grD6`; the identification
  `grD6 R ≠ 1 ↔ inertCount6 k ≠ 0` for `(f, 6) = 1` is a Lean proof. **What a statement check should confirm**:
  that GR's `D(R)` is `∏_{p ∣ D, (R/p) = −1} p` with the standard Eichler symbol (and not, e.g., a definition
  that also counts ramified primes). The consistency checks of gr-dict §2.3 (`#CM(R) = 2, 2, 2, 4` at
  discriminants `−4, −3, −24, −19`) agree with this reading.

## 3. The bridge and the derivation (all VERIFIED, standard axioms)

* `toOrder R hR hf : NumberFieldOrder k` — the Tau Ceti order of a subring `R ⊆ 𝓞_k` of finite index
  (`f = [𝓞_k : R] ≠ 0`; finiteness over `ℤ` from `𝓞_k`, full rank from `f𝓞_k ⊆ R`);
  `toOrder_toSubring : (toOrder R hR hf).toSubalgebra.toSubring = R` (by `Iff.rfl`).
* **Bridge.** Mathlib 4.35 already has `ClassGroup.equivPic (R) [CommRing R] [IsDomain R] : ClassGroup R ≃* Pic R`
  (`Mathlib/RingTheory/PicardGroup.lean` L876) for every domain, in particular non-maximal orders (Mathlib's
  `ClassGroup` is invertible fractional ideals modulo principal ones). Tau Ceti's `Pic O` is
  `ClassGroup O.toSubalgebra`. So
  `picEquiv O : Pic O ≃* CommRing.Pic O.toSubalgebra.toSubring` is `ClassGroup.equivPic` followed by
  `picCongr` (functoriality of `CommRing.Pic` along the identity ring isomorphism), and
  `finrank_ringClassField_eq_card_pic : finrank k (ringClassField O) = Nat.card (CommRing.Pic O.toSubalgebra.toSubring)`.
* **D(R).** `isPrime_span_iff R hR p (hp : (conductor R).Coprime p) : (span {p} : Ideal R).IsPrime ↔
  (span {p} : Ideal (𝓞 k)).IsPrime` (the map `R → 𝓞_k/p𝓞_k` is onto with kernel `pR`, by Bezout
  `af + bp = 1` and `f𝓞_k ⊆ R`); `grD6_ne_one_iff : (conductor R).Coprime 6 → (grD6 R ≠ 1 ↔ inertCount6 k ≠ 0)`.
* **Derivation.** `gonzalezRotgerThm512X6_of_rcf`: with `O = toOrder R …`, `[H_R : ℚ] = [k : ℚ][H_R : k] =
  2·#CommRing.Pic R`; if `inertCount6 k ≠ 0` then `D(R) ≠ 1`, `ℚ(x) ≅ H_R` gives the degree `2h(R)` and
  `k → H_R ≅ ℚ(x)` the embedding; otherwise `D(R) = 1`, `ℚ(x) ≅ F` with `[F : ℚ]·2 = 2h(R)`.

## 4. S1 in one line

Remaining reading point: **GR's `D(R)` = product of the `p ∣ D` with Eichler symbol `(R/p) = −1`** (GR §5,
UNVERIFIED here). Everything downstream of that reading is a Lean proof.

## 5. N1: `LeafQM.O` is a maximal order (VERIFIED)

```
GR512Bridge.N1.O_maximal (O' : Subring B) (hle : LeafQM.O ≤ O') (hint : ∀ x ∈ O', IsIntegral ℤ x) :
  O' = LeafQM.O
```

* `int_of_isIntegral`: `x ∈ B` integral over `ℤ` has `trd x, nrd x ∈ ℤ` (if `x ∈ ℚ`, `ℤ` is integrally closed;
  otherwise `minpoly ℚ x = X² − trd(x) X + nrd(x)` divides a monic integer polynomial, and Gauss's lemma
  `IsIntegrally­Closed.eq_map_mul_C_of_dvd` makes its coefficients integers).
* `mem_O_of_int`: `trd(x e) ∈ ℤ` for `e = 1, i, (1+j)/2, (i+k)/2` and `nrd(x) ∈ ℤ` imply `x ∈ 𝒪`: with
  `A = 2r, B = 4s, C = r − 3t, D = 2s + 6u` one has `36A² − 18B² + 12(A−2C)² − 6(2D−B)² = 144·nrd(x)`, and
  the congruence mod 144 (576 residues, `decide`) gives `2t, 2u, r − t, s − u ∈ ℤ`. A Python scan (2304 points of
  the trace dual `𝒪^#` in a window) found no `x ∈ 𝒪^# ∖ 𝒪` with `nrd(x) ∈ ℤ` (VERIFIED, computed).

## 6. `#discharges` and the autofold dry-run

(filled in below)

## 7. What remains

* The statement check of `gonzalezRotgerThm512X6RCF` against GR's p. 946, in particular the definition of `D(R)`
  (§4) — the only reading point.
* Thm 5.12 itself (Shimura reciprocity on `X₀(6,1)`) is not formalized; nor is the existence of the canonical
  model (`x6CoarseModuli`, unchanged).

## 8. Files

* `ZInQKernel/Contrib/OneProof/GR512Bridge.lean`: the leaf, the bridge, the derivation, N1.
* `scratch/gr512-bridge/GR512Bridge.lean`, `N1Maximal.lean` (development copies, with `#print axioms`),
  `Discharges.lean`, `discharges.txt`, `autofold.json`, `autofold-dryrun.txt`, `FoldCheck.lean`, `log.md`,
  build logs.
