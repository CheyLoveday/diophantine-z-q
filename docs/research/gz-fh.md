# gz-fh: `FHNonvanishing` split into Friedberg–Hoffstein Theorem B, the twisted root number, and proved glue

Status: research note (task gz-fh, 2026-11-15). Branch `wip/gz-fh` (base `wip/w72` 24f97774).
Lean: `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` (new file, the deliverable),
`scratch/gz-fh/FH.lean` (the same content as a scratch check), `scratch/gz-fh/Discharges.lean`
(the `#discharges` run). Results log: `scratch/gz-fh/log.md`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
theorem with its reference. **SPECULATIVE**: an assessment. No copy of Friedberg–Hoffstein,
Atkin–Li or Iwaniec–Kowalski is on this host and there is no network: **every literature locator
in this note is UNVERIFIED**, and the statement of Friedberg–Hoffstein's theorem is recalled from
memory.

---

## 0. Main result

COMPILE_STATUS_PLACEHOLDER

```lean
theorem ZInQ.GZFH.fhNonvanishing_of_printed
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB) (hTw : ZInQ.GZFH.TwistNewformRootNumber) :
    ZInQ.GZDecomp.FHNonvanishing
```

`FHNonvanishing` (hypothesis `hL2` of `ZInQ.OneProof.frozenTarget`, rated composite) now rests on
two printed leaves over genuine definitions, and everything else is proved:

| Name (`ZInQ.GZFH.`) | Kind | Source (UNVERIFIED locators) | Printed form? |
| --- | --- | --- | --- |
| `FriedbergHoffsteinB` | LEAF (research) | Friedberg–Hoffstein, Ann. of Math. (2) 142 (1995) 385–423, Theorem B | specialization of the printed theorem (`F = ℚ`, `π = π_f` weight 2 trivial central character, `χ₀` unramified at the finite places of `S`, `S ∋ 2`), with the local conditions `χ_v = χ₀,v` written as `D/D₀ ∈ (ℚ_v^×)²` (Mathlib's `ℚ_[p]`) and `ε(½, π ⊗ χ₀) = 1` written as Tau Ceti's root number of the twisted newform. Not literal: the idelic language is translated by a standard dictionary (§2). Flag: unread. |
| `TwistNewformRootNumber` | LEAF (textbook) | Iwaniec–Kowalski, *Analytic Number Theory* (2004), Prop. 14.20; Atkin–Li, Invent. Math. 48 (1978) 221–243, Thm 3.1; Shimura 1971 Prop. 3.64 | consequence of the printed proposition: specialized to `k = 2`, trivial nebentypus, `χ = χ_D` with `D` odd fundamental, and the Gauss sum evaluated (`τ(χ_D)² = χ_D(−1)|D|`). Flag: unread. |
| `fhNonvanishing_of_printed` and helpers | GLUE, proved | Dirichlet's theorem (Mathlib), gz-statements' `heegnerHyp_iff_split`, `jacobiSym_neg_level`, `coprime_of_heegnerHyp`, reduction `ℤ_p → ℤ/p`, `ℤ_2 → ℤ/8` | — |

The root-number computation the proof needs is proved in Lean: for the auxiliary discriminant
`D₀ = −q` (`q ≡ −1 mod 8N` prime, from Dirichlet's theorem in Mathlib)
`χ_{D₀}(−N) = −1`, so `rootNumber(f ⊗ χ_{D₀}) = χ_{D₀}(−N)·(−1) = +1`, which is Friedberg–Hoffstein's
compatibility hypothesis. What cannot be proved from Mathlib or Tau Ceti today is the *formula*
`ε(f ⊗ χ) = χ(−N) ε(f)` itself together with the newform property of the twist (Tau Ceti has
`CuspForm.twist` and its `q`-expansion, but neither newness of twists nor the twisted Fricke
eigenvalue; VERIFIED by reading `Contrib/TauCeti/NumberTheory/ModularForms/Twist/Basic.lean`), so
it is the separate leaf `TwistNewformRootNumber`.

REST_PLACEHOLDER
