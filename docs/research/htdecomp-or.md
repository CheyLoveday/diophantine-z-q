# htdecomp-or: `hodgeTateDecompExists` from an or-form leaf (tensor form OR Hom form)

Task htdecomp-or, 2026-11-17. Base `origin/wip/leaf-fold33b` at d911d55cf (8ba86099 is an ancestor), with
`origin/main` (ee33f2143) merged. Log: `scratch/htdecomp-or/log.md`.

## Verdict

The research field `hodgeTateDecompExists` (`ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists`,
`ZInQKernel/Contrib/OneProof/HodgeTatePairingDecomp.lean` l. 44; strict leaf review 2026-11-17, queue10: GLUE/GLUE,
"Fontaine 1982's form is unread. A Hom-form print needs a `C_p`-dualization Lean does not prove") is **proved in Lean
from one new leaf**, the disjunction of the two printed shapes of the Hodge–Tate decomposition:

```
def HodgeTateDecompOr : Prop := HodgeTateDecompExists ∨ HodgeTateDecompHom

theorem ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or (h : HodgeTateDecompOr) : HodgeTateDecompExists
theorem ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_hom (h : HodgeTateDecompHom) : HodgeTateDecompExists
```

The **`ℂ_p`-dualization the review asked for is proved** (`dualEquiv`, `dualEquiv_map`, §2): an equivariant
`Hom_{ℚ_p}(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b` gives an equivariant `ℂ_p ⊗ V ≅ ℂ_p(1)^b ⊕ ℂ_p^a`, for any
`ℚ_p`-representation `V` of `G_F`, with no finiteness assumption on `V` (the Hom form forces it). No new glue: the
proof uses only Mathlib and pkg-I4/TailS definitions and lemmas (`cpAct_inv_apply`, `cpAct_algebraMap`).
`#print axioms`: `[propext, Classical.choice, Quot.sound]` for both theorems (VERIFIED, §5).

Result for the fold (`autofold.py --dry-run`, §6): `hodgeTateDecompExists` (GLUE, pending reading) replaced by
`hodgeTateDecompOr` (LEAF, unread, locator UNVERIFIED): **GLUE −1 in both columns, no new glue.**

In addition (helper `HodgeTateDecompOrH1.lean`, not part of the leaf): a third printed shape, the `H¹_ét` form
`ℂ_p ⊗ V_p(A)^∨ ≅ ℂ_p^a ⊕ ℂ_p(−1)^b` (Faltings 1988), implies the Hom form (`hom_of_h1`); and the tensor form implies
the Hom form (`hom_of_tensor`), so **the two disjuncts are equivalent and the or-leaf is equivalent to the field it
replaces** (`or_iff_field`). The leaf is therefore neither stronger nor weaker than the old field as a
proposition. What changes is the rating: whichever of the three shapes Fontaine (or Tate, or Faltings) prints, the
leaf follows from that print by a Lean proof with no glue. The review rated the field GLUE only because a Hom-form
print would have needed a dualization that Lean did not prove. That dualization is now proved.

## 1. Statements (VERIFIED: compiled)

The field, verbatim (unchanged; `scratch/htdecomp-or/Statement.lean` copies it and checks `Iff.rfl` against the tree):

```
def HodgeTateDecompExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))
```

The Hom form (`ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom`, `ZInQKernel/Contrib/OneProof/HodgeTateDecompOr.lean`):

```
def HodgeTateDecompHom : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : (A.V p →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (f : A.V p →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ A.galRep p σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))

def HodgeTateDecompOr : Prop := HodgeTateDecompExists ∨ HodgeTateDecompHom
```

Conventions: `G_F` acts on `Hom` by `(σf)(x) = σ(f(σ⁻¹x))` (Tate's action), on `ℂ_p(−1)` by `c ↦ χ(σ)⁻¹σ(c)`.
Factor order: Tate's `t_{G'}(C) ⊕ t_G^*(C)(−1)`, so the untwisted factor comes first. The objects are the field's:
pkg-I4's abelian variety, `V_p(A)`, `galRep`, `cpAct`, `cycPow` and `gfToGqp`.

Why `Hom_{ℚ_p}(V_p(A), ℂ_p)` and not `Hom_{ℤ_p}(T_p(A), ℂ_p)`: the tree has no `Module ℤ_[p] ℂ_[p]` instance (VERIFIED by
`#synth`), so the `ℤ_p` form cannot be stated without an instance written for the purpose. The two are canonically
equal: `V_p(A) = ℚ_p ⊗_{ℤ_p} T_p(A)` and `ℂ_p` is a `ℚ_p`-space (extension of scalars, Mathlib's
`LinearMap.liftBaseChangeEquiv`). This is STANDARD.

## 2. The dualization (the step the review said Lean did not prove)

`HodgeTateDecompOr.lean` §2, for any `ℚ_p`-representation `ρ` of `G_F` on any `ℚ_p`-space `V`, with
`e : Hom_{ℚ_p}(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b`:

1. `ev f : ℂ_p ⊗ V → ℂ_p`, `c ⊗ v ↦ c f(v)` (Mathlib's `liftBaseChangeEquiv`, `ℂ_p`-linear in `f`).
2. `eq_zero_of_ev`: if `ev f w = 0` for all `f`, then `w = 0`. Proof: the coordinates of `w` in the base-changed
   basis are `ev (ι ∘ b.coord i) w`, for any basis `b` of `V`. No finiteness is needed.
3. `dualMap w = (⟨e⁻¹(0, ε_k), w⟩_k, ⟨e⁻¹(ε_k, 0), w⟩_k)`. It is injective, by step 2 and because `u ↦ ⟨e⁻¹u, w⟩` vanishes on
   the standard basis.
4. `finiteDimensional_of_dual`: since `dualMap` is injective into a finite-dimensional space, `ℂ_p ⊗ V` is finite, so the basis
   of `V` is finite. `finrank_eq_of_dual`: `dim ℂ_p ⊗ V = dim V = dim Dual(ℂ_p ⊗ V) = dim Hom(V, ℂ_p) = a + b`.
   So `dualEquiv : ℂ_p ⊗ V ≅ ℂ_p^b × ℂ_p^a`.
5. `ev_map`: `⟨f, σw⟩ = σ⟨σ⁻¹f, w⟩`. With `e(σ⁻¹ f_k) = f_k` on the untwisted part and
   `e(σ⁻¹ f_k) = χ(σ) e(f_k)` on the `ℂ_p(−1)` part (`cycPow_inv_neg_one : χ(σ⁻¹)^{−1} = χ(σ)`, from Mathlib's
   cyclotomic character being a homomorphism), `dualEquiv_map` gives exactly the field's equivariance, with
   `ℂ_p(1)^b` first and `ℂ_p^a` second.

`hodgeTateDecompExists_of_hom` takes `⟨b, a, dualEquiv p e, dualEquiv_map …⟩`.

## 3. The new leaf and its rating

**`hodgeTateDecompOr` (`ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr`): LEAF (published, flag unread, locator
UNVERIFIED) in both columns.** Each disjunct is a printed shape with bases chosen and both exponents left unnamed:

* the tensor disjunct is Fontaine 1982's isomorphism `ℂ_p ⊗ V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t*_{A'})`, if it is
  printed in that form (hodgetate-from-dr §3);
* the Hom disjunct is `Hom_{ℤ_p}(T_p(A), ℂ_p) ≅ (ℂ_p ⊗_F t_{A'}) ⊕ (ℂ_p(−1) ⊗_F t_A^*)`, the shape of Tate 1967 §4
  (the corollary to the theorem on `Hom(T(G), C)`, for `G = A[p^∞]` of an abelian scheme, i.e. good reduction) and
  of Fontaine 1982 if Fontaine prints the Hom form; written over `V_p` as in §1;
* a third shape, `ℂ_p ⊗ H¹_ét ≅ (ℂ_p ⊗ H¹(A, 𝒪)) ⊕ (ℂ_p(−1) ⊗ H⁰(A, Ω¹))` (Faltings, JAMS 1 (1988)), implies the Hom
  disjunct in Lean (`hom_of_h1`).

All locators and the exact printed wording are UNVERIFIED (no network). Tate's corollary covers only good reduction,
so for every `A` the Hom disjunct needs Fontaine 1982 (or Faltings 1988). The leaf asserts the conclusion for every
`A`, as the field does.

**Not stronger than either print.** If the print is the tensor form, the leaf follows by `or_of_tensor`. If it is
the Hom form, it follows by `or_of_hom`. If it is the `H¹` form, it follows by `or_of_h1`, whose proof is in Lean. The only translation in
each case is choosing bases of `t_A`, `t_{A'}` (the tangent spaces and the dual abelian variety are not in Mathlib)
and replacing `T_p` by `V_p` in the Hom form, as in the field. The leaf asserts neither exponent, so the
dictionary objection to the old `HodgeTateDecompAbVar` (that the exponent `g` needs the dual abelian variety) does not
apply.

**Why this meets the review's condition without a reading.** The review rated the field GLUE because a Hom-form
print would need a `ℂ_p`-dualization that Lean did not prove. That dualization is now proved (§2), with the converse
(`hom_of_tensor`) and the `H¹` shape as well. The reading can only decide which disjunct is the literal print, and
either one implies the leaf.

Proposed `locators.md` row (not added, since `locators.md` is not this task's file): *Fontaine 1982 Théorème principal / Tate
1967 §4 corollary on `Hom(T(G), C)`: tensor OR Hom form with bases chosen, both exponents unnamed
(`HodgeTateOr.HodgeTateDecompOr`); Hom ⇒ tensor proved in Lean (htdecomp-or); locator UNVERIFIED.*

## 4. What compiles (VERIFIED)

| file | imports | content |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/HodgeTateDecompOr.lean` (14.5 KB) | `HodgeTatePairingDecomp` (defines the field) | `HodgeTateDecompHom`, `HodgeTateDecompOr`, the dualization, `hodgeTateDecompExists_of_hom`, `hodgeTateDecompExists_of_or` |
| `ZInQKernel/Contrib/OneProof/HodgeTateDecompOrH1.lean` (15.3 KB, helper) | `HodgeTateDecompOr` | `HodgeTateDecompH1`, `hom_of_h1`, `or_of_h1`, `hodgeTateDecompExists_of_h1`; `hom_of_tensor`, `hom_iff_tensor`, `or_iff_field` |

`lake build ZInQKernel.Contrib.OneProof.HodgeTateDecompOr +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`
succeeded (16070 jobs), and `lake build ZInQKernel.Contrib.OneProof.HodgeTateDecompOrH1` succeeded too. Neither file has `#eval`, `run_cmd`, notation,
macros or `sorry`, and neither imports `ZInQKernel.OneProof.Main`. Every theorem depends only on `[propext, Classical.choice, Quot.sound]`.

## 5. `#discharges` (`scratch/htdecomp-or/Discharges.lean`, full output `Discharges-output.txt`)

```
DISCHARGES [OpenResearchLeaves41.hodgeTateDecompExists] by ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_h1
  still assumes: [ZInQ.Contrib.HodgeTateOr.HodgeTateDecompH1]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves41.hodgeTateDecompExists] by ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_hom
  still assumes: [ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves41.hodgeTateDecompExists] by ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or
  still assumes: [ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr]
  axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.HodgeTateOr.hom_iff_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.HodgeTateOr.or_iff_field' depends on axioms: [propext, Classical.choice, Quot.sound]
#discharges: 40 open hypotheses, 13321 theorems checked, 28 discharge one
```

## 6. Autofold spec and dry-run fold

`scratch/htdecomp-or/autofold.json` discharges the field `hodgeTateDecompExists` with the proof
`_root_.ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or {n}.hodgeTateDecompOr`. Its one new leaf is
`hodgeTateDecompOr`, of kind published, with the flag "unread: or-form leaf (…); locator UNVERIFIED" (flag_class
`unread,unverified-locator`). `python3 scripts/one_proof/autofold.py scratch/htdecomp-or/autofold.json --dry-run`
(VERIFIED) printed:

```
strict count: 12/23 on 35 -> 13/22 on 35; strictest 11/24 -> 12/23
```

That is GLUE 23 → 22 (strict) and 24 → 23 (strictest), LEAF +1 in each column, with no new glue. The dry-run module
(`scratch/htdecomp-or/AutofoldDry.lean`, the output without its first line) builds the generation
`OpenResearchLeaves42` and `HDec.HSyn.sixContactMin_of_open60` on top of TailZ66 and compiles, and
`sixContactMin_of_open60` depends on `[propext, Classical.choice, Quot.sound]` (VERIFIED). The dry run wrote nothing to the tree.

## 7. What remains

* A reading of Fontaine 1982 (Théorème principal, pp. 379–381 per the review) and of Tate 1967 §4, to record which
  disjunct is the literal print and the locator. With the or-form this is bookkeeping: it cannot change the rating.
* The integrator's fold (autofold with the spec above), then OPEN.md regeneration and the `locators.md` row.
