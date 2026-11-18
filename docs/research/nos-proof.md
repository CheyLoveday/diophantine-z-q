# nos-proof: `r7a` (Néron–Ogg–Shafarevich) — half proved, discharged from a strictly weaker printed leaf

Task nos-proof, 2026-11-16, base origin/main `0caafe66` (leaf-fold31, `sixContactMin_of_open35`). Log:
`scratch/nos-proof/log.md`.

## Verdict

* **The field `r7a : PkgI2.NeronOggShafarevich.{0}` is proved in Lean from one new leaf, `NOSProof.NOSConverseSep`,**
  which is only the direction (c) ⇒ (a) of Serre–Tate 1968 Thm 1, stated over a separable closure as printed.
  The directions (a) ⇒ (b) and (b) ⇒ (c) are proved outright, from Mathlib and what the tree already proves.
  No `sorry`. The axioms are `propext`, `Classical.choice` and `Quot.sound` (VERIFIED).
* **The target (−1 with no new leaf) is not reached.** The count is unchanged: the autofold dry run reports
  `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`. One published leaf is replaced by a
  strictly weaker published leaf: the forward half of NOS is no longer assumed.
* **The converse is really consumed.** No open field gives it, so it cannot be dropped (§3). Getting it from the open
  fields would still need at least one leaf that is not in the bundles: "if the special fibre of `N⁰` is an abelian
  variety then `N⁰` is an abelian scheme". It would also need several large Lean developments that are absent today (§4).

`#discharges` (`scratch/nos-proof/Discharges.lean`; the output is in `Discharges-output.txt`; VERIFIED; the lines
for other contributions that the import pulls in are omitted):

```
DISCHARGES [OpenResearchLeaves26.r7a] by NOSProof.neronOggShafarevich_of_converse
  still assumes: [NOSProof.NOSConverseSep]
  axioms: [propext, Classical.choice, Quot.sound]
```

Deliverable: `ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean` (namespace `NOSProof`; it imports
`ZInQKernel.Contrib.OneProof.UnipotentForward` and `...MulEtale`, not `OneProof.Main`; `lake build` takes 16 s).
The autofold spec is `scratch/nos-proof/autofold.json`. Its dry run, `scratch/nos-proof/AutofoldDry.lean`, compiles
and gives `HDec.HSyn.sixContactMin_of_open36` with the standard axioms (VERIFIED).

## 1. The statement

`r7a` (verbatim in `scratch/nos-proof/OldStatements.lean`, `Iff.rfl` to the original): for a field `K` with a DVR
`O`, a valuation ring `w` of `K̄ = AlgebraicClosure K` over `O`, and `A/K` an abelian variety:

* (a) `HasGoodReduction A O` ⟺ (b) `∀ m > 0`, `IsUnit (m : O) → InertiaTrivialOn A w m`;
* (a) ⟺ (c) `{m | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite`.

The statement was checked and is not false, vacuous or inert. `HasGoodReduction` is Serre–Tate's definition: an
abelian scheme over `O` (proper, smooth, geometrically connected fibres) whose generic fibre is isomorphic to `A`.
`IsInertia` is Mathlib's inertia subgroup of the decomposition group of `w`. "`m` prime to the residue
characteristic" is `IsUnit (m : O)`. Every hypothesis can be met.

## 2. What is proved (all in `ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean`)

| theorem | content | inputs |
| --- | --- | --- |
| `inertiaTrivialOn_of_goodReduction` | (a) ⇒ (b) over `K̄` | the proved row `PkgI2.ReductionTorsionBijective` (`AvSplit.T4.reductionTorsionBijective_of_mulEtale` with fork PR #19's `mulEtaleAbelianScheme_proof`) |
| `inertiaTrivialOn_of_goodReduction_any` | (a) ⇒ (b) over **any** field `Ω ⊇ K` and any valuation ring `w ⊆ Ω` over `O` | av-split's injectivity of reduction (TailQ §3–§5) copied with `K̄` replaced by `Ω`; `AvSplit.T4.unramifiedSectionsEq`, `mulEtaleAbelianScheme_proof`, Mathlib's valuative criteria |
| `infinite_natCast_isUnit` | infinitely many `m ≥ 1` are units of `O`, which gives (b) ⇒ (c) | Mathlib (`m = (N+1)·char κ + 1`, or `N + 1` when `char κ = 0`) |
| `isInertia_extend` and the lemmas before it | an extension to `K̄` of an inertia element of `w ∩ K^s` is inertia at `w` | dict-galois's proof (wip/dict-galois `81d1f67f`), copied verbatim |
| `inertiaTrivialOn_sep_of` | triviality on `A(K̄)[m]` implies triviality on `A(K^s)[m]` | `isInertia_extend`, `ZInQ.Contrib.AbVarBC.extPt` (Galois-equivariant, injective) |
| `neronOggShafarevich_of_converse` | **`NOSConverseSep → PkgI2.NeronOggShafarevich.{0}`** | the above, with the leaf at `K^s = separableClosure K K̄` and `w ∩ K^s` |

Proof of (a) ⇒ (b), which is Serre–Tate's own argument. Let `𝒜/O` be the abelian scheme, `σ` an element of
inertia at `w` and `x ∈ A(Ω)[m]`. By the valuative criterion `x` lifts to `x̃ : Spec w → 𝒜`, and
`Spec(σ|_w) ≫ x̃` lifts `σx`. Both lifts are `m`-torsion, by uniqueness of lifts. Since `σ` acts trivially on
`κ(w)`, the two lifts have the same reduction `Spec κ(w) → 𝒜`. The morphism `[m]` is étale and separated, so two
`m`-torsion points of `𝒜(w)` with the same reduction are equal (`UnramifiedSectionsEq`, proved in TailQ). Hence
`σx = x`.

`scratch/nos-proof/SepCompat.lean` proves dict-galois's leaf `NOSSepDict.NeronOggShafarevichSep` (a verbatim copy;
`diff` against wip/dict-galois reports IDENTICAL) from `NOSConverseSep` (compiled, standard axioms). The proof uses
`inertiaTrivialOn_of_goodReduction_any` at `Ω = Ks`.

## 3. Consumers: both directions are live

Closure scan from `ZInQ.OneProof.frozenTarget` (`scratch/nos-proof/Uses.lean`, 116,234 constants, output in
`uses.txt`; VERIFIED). Eighteen non-bundle constants take `PkgI2.NeronOggShafarevich` as a hypothesis. The uses
were read by hand:

* **(a) ⇒ (b)** (`.1.mp`): TailC l. 5244 (`G4WeilRes.point_fixed` → `inertiaFixesHomsMon`, `kernelField_of_model`)
  and TailF l. 3731 (`GoodRedG3Bridge`). Both are now covered by the proved half.
* **(c) ⇒ (a)** (`.2.mpr`): only LPrefix l. 856, `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg`
  (`[NumberField K]`, a QM abelian surface for `(2,−3)` with `A[3]` rational, `m = 3^(k+1)`). It is reached through
  `LeafQM.AV.QML3.goodReduction` from `HSyn.LinkedTate.qmModelG3_of` (TailF, through `GoodRedG3Bridge`) and
  `G0ModField.KernelField.good_of_QML3` (TailC).

The QML3 consumer makes a round trip. It shows that inertia is trivial on `A[3^∞]` (r6's unipotence plus
`QuatUnipotentTrivial`), applies the converse to get good reduction, and then applies the forward direction for
every `ℓ ≠ p` to get `G3Out`. What the round trip uses is the independence of `ℓ`. It cannot be bypassed:
`QuatUnipotentTrivial` kills `N = σ − 1` only where `B ⊗ ℚ_ℓ` is a division algebra (`ℓ = 2, 3`). For `ℓ ∤ 6`, the
algebra `B_ℓ ≅ M₂(ℚ_ℓ)` has nonzero square-zero elements, so triviality at `ℓ` needs the toric rank of the Néron
model to be zero, which is exactly the content of the converse.

**Narrowing.** The converse is consumed only at number fields, for these QM surfaces. A leaf restricted to number
fields, or the (d) form "`T_3` unramified ⇒ good reduction", would serve that one consumer after a reroute.
Neither can prove `r7a` as stated: (c) does not follow from (d), since infinitely many `m` need not include all
powers of one prime. The proof of the converse is also the same over any DVR. I therefore kept the general form,
which is the printed one.

## 4. Why the converse is not obtained from the open fields (missing inputs, rated)

The classical proof of (c) ⇒ (a) is Serre–Tate §2, with Grothendieck's SGA 7 IX for the semistable case. Mapped
onto the open fields:

1. Pass to `O^sh`. Inertia-trivial torsion is rational over `K^sh`, so `raynaudSemistableSH` with the proved
   `StrictHenselizationPair` gives semistable Néron models (open fields; usable).
2. `A(K^sh)[m] = N(O^sh)[m] ↪ N_s(k^s)[m]`. This follows from the Néron mapping property and unramified sections
   (GLUE, provable along the lines of TailQ). It needs `[m]` étale on a *smooth commutative group scheme*; PR #19
   proves this only for abelian schemes (BLR 7.3 Lemma 2 in general; locator UNVERIFIED).
3. `#N_s(k̄)[m] ≤ #Φ · m^{2a+r}`, with `a + r = g`. Here `mumfordTorsionAlgClosed` gives the abelian part and roots
   of unity give the torus part. The component group must be finite (Noetherian topology), and the dimension
   formula for the extension and constancy of fibre dimension are needed (GLUE; large; partly in infra-smooth-dim
   and `groupSchemeEquidim`). With infinitely many `m`, this forces `r = 0`.
4. **`N⁰_s` an abelian variety ⇒ `N⁰` an abelian scheme.** This is a properness criterion for smooth group schemes
   over a DVR (SGA 7 IX §2 / BLR 7.4; numbers UNVERIFIED; also EGA IV 15.7.10-type criteria). It is **not** an open
   field and is not in Mathlib: it would be a new **LEAF**.
5. Descent of good reduction from `O^sh` to `O`, using `neronBaseChangeStrictHenselization` and fpqc descent of
   properness (GLUE). Mathlib 4.35's `Morphisms/FlatDescent.lean` has fpqc descent of universal closedness
   (l. 49), open immersions and isomorphisms, and `LocalFlatDescent.lean` has descent of local finite type
   (VERIFIED by reading). Descent of separatedness and the group structure on `N⁰` were not checked.

So even a full Lean development of steps 1–3 and 5 (weeks of work) would replace `NOSConverseSep` by the leaf in
step 4, which is again −1 + 1. **The smallest missing input is `NOSConverseSep` itself.** Rating: **printed form**.
It is one implication of the equivalence printed as Serre–Tate Thm 1, over a separable closure `K_s` as in the
print, with Serre–Tate's definition of good reduction and the print's "infinitely many `m` prime to `p`". It is
a consequence of the print, never stronger, and over genuine definitions (Mathlib's inertia subgroup and schemes,
the chain's `HasGoodReduction`). Locator: Serre, Tate, *Good reduction of abelian varieties*, Ann. of Math. 88
(1968), 492–517, §1 Thm 1 (from memory, UNVERIFIED; no source on this host). If the print lists only (a), (b) and
the `T_ℓ` form (d), then (c) ⇒ (a) is still in its proof (Serre–Tate §2 uses one `m` large compared with the
component group). In that case the leaf should be flagged "pending reading: (c) may be in the proof rather than
the display". The same reading question applies to the old `r7a` and to dict-galois's leaf.

## 5. For the integrator

* Fold: `python3 scripts/one_proof/autofold.py scratch/nos-proof/autofold.json`. The leaf row is
  `nosConverseSep` (kind `published`, no flag, so autofold adds "unread: new printed leaf"). The dry run compiles.
* **Fold order with dict-galois.** dict-galois replaces `r7a` by `NOSSepDict.NeronOggShafarevichSep`, which is both
  directions. Folding nos-proof instead for that row gives a strictly weaker leaf. If dict-galois's fold lands
  first, `scratch/nos-proof/SepCompat.lean`'s `neronOggShafarevichSep_of_converse` discharges its field from
  `NOSConverseSep` (move it into a Contrib file next to dict-galois's and drop the `Copy` def).
* Proposed `docs/research/locators.md` row: `NOSProof.NOSConverseSep | Serre–Tate, Ann. of Math. 88 (1968) §1
  Thm 1, (c) ⇒ (a), over K_s | UNVERIFIED (no source on host) | (a) ⇒ (b) ⇒ (c) proved in Lean (nos-proof)`.
* Name hygiene: the copied dict-galois lemmas live in `NOSProof` (no clash with `NOSSepDict`), and the copied
  av-split lemmas carry an `Ω` suffix (`iotaΩ`, `rhoΩ_inj`, …) in `NOSProof`.

## 6. Files

* `ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean`: the contribution (about 26 KB).
* `scratch/nos-proof/`: `log.md`; `OldStatements.lean` (verbatim `r7a`, compiles); `T1.lean`–`T3.lean` (the build
  stages); `Uses.lean` and `uses.txt` (consumer scan); `Discharges.lean` and `Discharges-output.txt`;
  `autofold.json`, `autofold-dryrun.txt` and `AutofoldDry.lean`; `SepCompat.lean`.
