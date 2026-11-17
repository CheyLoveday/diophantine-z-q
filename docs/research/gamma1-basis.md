# gamma1-basis: Shimura's integral basis as the leaf, basis ⇒ span as proved glue

Task gamma1-basis (2026-11-17). Branch wip/gamma1-basis (base wip/leaf-fold33b 4ce18aa42, a descendant of
8ba86099; origin/main ee33f2143 merged, CI files only). Scratch: `scratch/gamma1-basis/`.

## 1. Result

The open research field `gamma1IntegralSpan : CoeffFieldFinite.Gamma1IntegralSpan` (bundle
`HDec.HSyn.OpenResearchLeaves41`, rated LEAF strict / GLUE strictest by the queue10 verdict of 11-17, because
"basis ⇒ span" sat inside the statement) is now proved from a new leaf in the printed form:

```lean
/-- Shimura 1971, §3.5, Thm 3.52 (printed form, number UNVERIFIED) -/
def Gamma1Basis.Gamma1IntegralBasis : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ), 2 ≤ k →
    ∃ (ι : Type) (b : Module.Basis ι ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      ∀ (i : ι) (n : ℕ), ∃ z : ℤ, (qExpansion 1 (b i)).coeff n = z

theorem Gamma1Basis.gamma1IntegralSpan_of_basis (h : Gamma1IntegralBasis) :
    CoeffFieldFinite.Gamma1IntegralSpan                 -- the field's proof (glue: Basis.span_eq + span_mono)
theorem Gamma1Basis.old_of_basis (h : Gamma1IntegralBasis) :
    CoeffFieldFinite.Gamma1IntegralSpan                 -- the same, under the task's name
theorem Gamma1Basis.gamma1IntegralBasis_of_span (h : CoeffFieldFinite.Gamma1IntegralSpan) :
    Gamma1IntegralBasis                                 -- the converse (exists_linearIndependent + Basis.mk)
theorem Gamma1Basis.gamma1IntegralBasis_iff_span :
    Gamma1IntegralBasis ↔ CoeffFieldFinite.Gamma1IntegralSpan
```

File: `ZInQKernel/Contrib/OneProof/Gamma1IntegralBasis.lean` (imports
`ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFinite`, the module that declares the statement; not
`OneProof.Main`). Statement of `Gamma1IntegralSpan` unchanged; every consumer unchanged (the fold fills the old
field by `gamma1IntegralSpan_of_basis`).

Counts (autofold dry run, VERIFIED): strict 12/23 on 35 → 12/23 on 35; **strictest 11/24 → 12/23** (GLUE −1),
no new glue (the bridge is proved).

Compile status: all of it compiles with only `propext`, `Classical.choice`, `Quot.sound` (section 4, VERIFIED).

## 2. Checks asked for

* **Γ₁(N) vs Γ¹(N)** (VERIFIED, read): Mathlib's `CongruenceSubgroup.Gamma1 N` is
  `{A ∈ SL₂(ℤ) | A₀₀ ≡ 1, A₁₁ ≡ 1, A₁₀ ≡ 0 mod N}` (`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean:136`,
  `Gamma1_mem`), i.e. `c ≡ 0`, `a ≡ d ≡ 1`: the group `Γ₁(N)` of Shimura, Diamond–Im and Diamond–Shurman (all three
  use this convention; from memory, UNVERIFIED for Shimura's book), not `Γ¹(N)` (`b ≡ 0`). It contains
  `T = (1 1; 0 1)`, so the `q`-expansion at `∞` is in `q = e^{2πiz}`, period `1`: `qExpansion 1`, as in the leaf.
  Tau Ceti's `CF N k` (`ZInQKernel/Contrib/G9/I4Layer.lean:1234`) is the same type.
* **All k ≥ 2 needed** (VERIFIED, read): the only consumer is
  `CoeffRational.eigenformCoeffFieldFinite_of_heckePrime` (TailZ56/57/65), whose target
  `DSCoeffExt.EigenformCoeffFieldFinite` (`DSCoeffExt.lean:460`) quantifies over every `k ≥ 2` and every Dirichlet
  character `χ` mod `N`, and the field types are fixed by the bundles. Restricting the leaf to even `k` would not
  prove the old field, and odd weights are not vacuous for `N ≥ 3` (e.g. `η(z)³η(7z)³ ∈ S₃(Γ₀(7), (−7/·))`, STANDARD,
  from memory). The printed theorem covers every `k ≥ 2`, so no restriction is needed.

## 3. The leaf rated against the print

| leaf | printed form? | reason |
| --- | --- | --- |
| `Gamma1Basis.Gamma1IntegralBasis` | **yes (printed form)**, locator UNVERIFIED | Shimura 1971 Thm 3.52 (number from memory, UNVERIFIED; cross-check Diamond–Im 1995 §12.3, `S_k(Γ₁(N), ℤ) ⊗ ℂ = S_k(Γ₁(N))`): "`S_k(Γ₁(N))` has a basis consisting of forms with rational integral Fourier coefficients". The Lean statement is exactly that, for every `N ≥ 1`, every `k ≥ 2`, over Mathlib's genuine `CuspForm` on `Gamma1 N` and Mathlib's `qExpansion`; the index type of the basis is left free (`ι : Type`), which is weaker than or equal to "a finite basis" (any basis of the finite-dimensional space is finite). Since the converse `gamma1IntegralBasis_of_span` is proved, the leaf is also a consequence of the print if the print instead says "is spanned by" such forms: either wording gives it. |

Rating: **LEAF strict, LEAF strictest**, flagged unread (locator UNVERIFIED) like every new printed leaf. Reading
checks for the statement check: (i) the theorem number and whether Shimura states it for `Γ₁(N)` in the
`c ≡ 0, a ≡ d ≡ 1` convention (if the print were for `Γ¹(N)`, conjugation by `diag(N,1)` changes the expansion
variable to `q^{1/N}`, and the leaf would need the Diamond–Im form instead); (ii) the weight range (`k ≥ 2` in the
leaf; a print for all `k ≥ 1` or for `k ≥ 2` both imply it); (iii) the weight-`k` action
`(f|γ)(z) = (cz+d)^{-k} f(γz)` on `SL₂(ℤ)` (Mathlib's slash action agrees on `SL₂`).

Proposed `docs/research/locators.md` row (for the integrator; not edited here): "gamma1IntegralBasis | Shimura,
*Introduction to the arithmetic theory of automorphic functions* (1971), §3.5 Thm 3.52; Diamond–Im (1995) §12.3 |
unread | printed form: basis of `S_k(Γ₁(N))` with rational integral Fourier coefficients, `k ≥ 2`; locator
UNVERIFIED".

## 4. Lean (compile record)

All VERIFIED (compiled on this host, 11-17):

* `lake build +ZInQKernel.Contrib.OneProof.Gamma1IntegralBasis +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`:
  success, 16,070 jobs; `ZInQ.OneProof.frozenTarget` standard axioms (`scratch/gamma1-basis/build.log`).
* `#discharges` (`scratch/gamma1-basis/Discharges.lean`, output `scratch/gamma1-basis/discharges-output.txt`):

  ```
  DISCHARGES [OpenResearchLeaves41.gamma1IntegralSpan] by Gamma1Basis.gamma1IntegralSpan_of_basis
    still assumes: [Gamma1Basis.Gamma1IntegralBasis]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves41.gamma1IntegralSpan] by Gamma1Basis.old_of_basis
    still assumes: [Gamma1Basis.Gamma1IntegralBasis]
    axioms: [propext, Classical.choice, Quot.sound]
  ```

  `#print axioms` of `gamma1IntegralBasis_of_span` and `gamma1IntegralBasis_iff_span`: the same three. No `sorry`.
* Autofold spec `scratch/gamma1-basis/autofold.json` (field `gamma1IntegralSpan`, proof
  `_root_.Gamma1Basis.gamma1IntegralSpan_of_basis {n}.gamma1IntegralBasis`, one leaf `gamma1IntegralBasis`, kind
  published, flag "unread: new printed leaf (...); locator UNVERIFIED"). `autofold.py --dry-run` (tree untouched):
  `strict count: 12/23 on 35 -> 12/23 on 35; strictest 11/24 -> 12/23`. The generated module
  (`scratch/gamma1-basis/FoldDryRun.lean`, line 1 stripped; raw output `FoldDryRun.lean.txt`) compiles against
  TailZ66: `OpenResearchLeaves42`, `openResearchLeaves41_of_OpenResearchLeaves42` and `sixContactMin_of_open60`,
  all with standard axioms (`scratch/gamma1-basis/foldrun-output.txt`).

## 5. What remains

Nothing in Lean for this field. The leaf needs a human statement check against the print (section 3).
