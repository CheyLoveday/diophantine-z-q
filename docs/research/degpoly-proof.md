# degpoly-proof: `DegHomogPoly` proved over every algebraically closed field that embeds into `ℂ`; the field `charPolyIndepOfEllAlgClosed` needs no degree theory there; the characteristic-`p` case is consumed, so "−1, no new leaf" is out of reach

Task degpoly-proof, 2026-11-16. Base: wip/deg-det `ecf7da39`, merged with origin/main `e41a7169` (STATUS.md only)
and origin/wip/homfree-proof `a0570509` (homfree-proof's lattice representation; only its ideas are reused, and
the contributions below do not import its file). Scratch: `scratch/degpoly-proof/` (results log `log.md`).

Marks: VERIFIED = read in a source, computed or compiled; STANDARD = published, exact reference; SPECULATIVE =
unchecked. No network: every theorem number recalled from memory is UNVERIFIED.

## 1. Verdict

1. **`DegHomogPoly` cannot be proved outright from the tree, and no narrowing removes the need for it in
   characteristic `p` (finding, VERIFIED).** The statement quantifies over every algebraically closed field, and
   the consumers of the field it serves use the characteristic-`p` case. The field `charPolyIndepOfEllAlgClosed`
   reaches the proof only through T7 (`PkgI3.CharPolyIndepOfEll`). One of T7's two consumer chains,
   `linkedTateData_of_local → g14TraceCompat_of_link → common_trace → trace_T_of_frobCompare`, applies T7 to the
   reduction mod `p` of an abelian variety over a number field: `FrobTraceLink` supplies
   `∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : End Ab) …`, and `common_trace` calls
   `trace_T_of_frobCompare hM Ab α` at that `k` (§5). So the target "−1, no new leaf" cannot be reached by
   narrowing to fields that embed into `ℂ`, which is the route homfree-proof used.

2. **Over every algebraically closed field `k` with a ring homomorphism `k → ℂ`, `DegHomogPoly` is proved.**
   This is VERIFIED: it compiles, and the axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof uses
   only the bundle's open fields `uniformizationLeafAll` and `mumfordTorsionAlgClosed`, deg-det's `KerDvd`, and
   the tree. The key identity is

   ```
   deg ψ = det_ℤ(M_ψ|_Λ)   for every ψ ∈ End(A)        (DegPolyC.degEnd_eq_det)
   ```

   Here `Λ` is the period lattice and `M_ψ` the linear lift of `ψ`. So `x ↦ deg(∑ xᵢ eᵢ)` equals
   `det(∑ xᵢ U(eᵢ))`, a homogeneous polynomial of degree `rank Λ = 2g`. This follows the task's suggested route
   (1)–(3), with every step in Lean (§3). As a by-product, Mumford §19 Thm 4 holds over these fields
   (`degEqDetTateC`: `det V_ℓ(ψ) = deg ψ`).

3. **The field itself has a shorter proof over these fields, with no degree at all.** The characteristic
   polynomial of `V_ℓ(φ)` equals `charpoly_ℤ(M_φ|_Λ)` (`CharPolyLattice.charpoly_V_eq`, §2). This covers T7 over
   every field with a ring homomorphism to `ℂ`, algebraically closed or not.

4. **Two count-neutral discharges of the field.** Both are VERIFIED by `#discharges` and by an autofold dry run
   whose module compiles. Each replaces the field by one strictly weaker published leaf; the strict count goes
   from 34/11 on 45 to 34/11 on 45.

   | spec | discharge theorem | still assumes | new leaf |
   | --- | --- | --- | --- |
   | `autofold.json` (recommended) | `CharPolyLattice.charPolyIndepOfEllAlgClosed_of_noEmb` | `uniformizationLeafAll`, `mumfordTorsionAlgClosed` | `CharPolyIndepOfEllAlgClosedNoEmb` |
   | `autofold-degpoly.json` | `DegPolyC.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb` | the same two, plus `homFreeFiniteAlgClosed` | `DegHomogPolyNoEmb` |

   - `CharPolyIndepOfEllAlgClosedNoEmb` is §19 Thm 4 restricted to fields with no ring homomorphism to `ℂ`.
   - `DegHomogPolyNoEmb` is deg-det's `DegHomogPoly` restricted to the same fields.
   - If deg-det's fold lands first, `autofold-after-degdet.json` (UNCHECKED, since its field does not exist on this
     base) turns deg-det's leaf `degHomogPoly` into `degHomogPolyNoEmb`, with no other input.

## 2. The field over fields that embed into `ℂ` (`ZInQKernel/Contrib/OneProof/CharPolyLattice.lean`, 14 KB)

Imports only `OneProof.H.TailE`, `TailQ`, `LF4T5` and `Contrib.AVB1.AlgClosed`, the module that declares the field.
It does not depend on deg-det's or homfree-proof's unmerged files. Namespace `ZInQ.Contrib.OneProof.CharPolyLattice`.

Setup: let `K` be a field with `emb : K̄ → ℂ`, and `σ = emb ∘ (K → K̄)`. Then:
- T35 (`AvSplit.Final.h38 HL HT`) gives `Φ : ℂ^g → A(ℂ)_σ` with kernel the lattice `Λ`;
- the linear lift `M_φ` comes from `homLinearLift_of_analyticHomLift` (from `HL`), and preserves `Λ`
  (`lift_mem_lattice`);
- conj-twist's `tateLatticeInj_of_T5` (from `HT`) gives an injective `α : ℤ_ℓ ⊗ Λ → T_ℓ(A)`, natural by
  `homT_tateLattice`.

The proof of `charpoly_V_eq`:
1. `α ∘ (X ⊗ ℤ_ℓ) = T_ℓ(φ) ∘ α`, where `X = M_φ|_Λ` (`latEnd`).
2. `T_ℓ` is free of rank `2g`, by `mumfordTorsionAlgClosed` and t5-torsion's `tate_linearEquiv`.
3. `β = α ⊗ ℚ_ℓ` is injective, because `ℚ_ℓ` is flat over `ℤ_ℓ` (`IsLocalization.flat`). Both sides have rank `2g`
   (`finrank_lattice`), so `β` is an isomorphism (`linearEquivOfInjective`).
4. `β` conjugates `(X ⊗ ℤ_ℓ) ⊗ ℚ_ℓ` to `V_ℓ(φ)`. So `charpoly V_ℓ(φ) = charpoly_ℤ(X)` mapped to `ℚ_ℓ`
   (`LinearEquiv.charpoly_conj`, `LinearMap.charpoly_baseChange`).

Theorems, all with standard axioms (VERIFIED):

```lean
theorem charPolyIndep_of_emb (HL : UniformizationLeafAll) (HT : MumfordTorsionAlgClosed)
    (emb : AlgebraicClosure K →+* ℂ) (A) (φ) : ∃ P : ℤ[X], P.Monic ∧ ∀ ℓ …   -- body of T7
theorem charPolyIndepOfEllC (HL) (HT) : CharPolyIndepOfEllC            -- T7 over k with σ : k →+* ℂ
theorem charPolyIndepOfEllAlgClosedC (HL) (HT) : CharPolyIndepOfEllAlgClosedC
theorem charPolyIndepOfEllAlgQ (HL) (HT) : CharPolyIndepOfEllAlgQ      -- k algebraic over ℚ
theorem charPolyIndepOfEllAlgClosed_of_noEmb (HL) (HT) (HR : CharPolyIndepOfEllAlgClosedNoEmb) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
```

## 3. `DegHomogPoly` over fields that embed into `ℂ` (`ZInQKernel/Contrib/OneProof/DegHomogPolyC.lean`, 40 KB)

Imports `CharPolyLattice` and deg-det's `DegEqDetTate`, which declares `DegDet.DegHomogPoly` and `KerDvd`.
Namespace `ZInQ.Contrib.OneProof.DegPolyC`. Throughout, `k` is algebraically closed.

**A. Kernel points over any field `L ⊇ k` correspond to the fibre `ψ⁻¹(e₀)`** (`card_ker_eq`, for `ψ` finite).
1. An `L`-point through a closed point `x` is determined by its composite to `Spec k` (`eq_of_closed`). The proof
   writes the point as `Spec(κ(x) → L) ≫ fromSpecResidueField x` (Mathlib's
   `descResidueField_stalkClosedPointTo_fromSpecResidueField`), and `κ(x) ≅ k` by `residueFieldIsoBase`.
2. `e₀`, the image of the identity, is closed (`pointEquivClosedPoint`).
3. The points of `ψ⁻¹(e₀)` are closed, because the fibre is discrete (`isDiscrete_preimage_singleton`) and finite
   (`finite_preimage_singleton`).
4. Kernel points therefore inject into the fibre. Every fibre point gives an `L`-point through
   `pointOfClosedPoint`, and that point lies in the kernel, again by step 1.

So `#ker ψ(L) = #ψ⁻¹(e₀)` for every field `L` with `Algebra k L`. This covers `k̄`, `ℂ` and `\overline{K(A)}` alike.

**B. In characteristic `0`, `deg ψ = #ψ⁻¹(e₀)` for an isogeny** (`degEnd_le_card_fibre`, `degEnd_ne_zero`,
`degEnd_eq_card_fibre`).
1. Let `Ω = AlgebraicClosure K(A)`. Each `ψ^*K(A)`-embedding `τ : K(A) → Ω` gives
   `P_τ = Spec τ ≫ fromSpecStalk η`, an `Ω`-point.
2. Give `Ω` the `k`-structure read off one composite (`Spec.preimage`). Then every `P_τ` is a `k`-point, and
   `ψ ∘ P_τ` does not depend on `τ` (`SpecMap_stalkMap_fromSpecStalk`).
3. So `τ ↦ P_τ P_{τ₀}⁻¹` maps into `ker ψ(Ω)`. It is injective, because `fromSpecStalk` is a monomorphism.
4. There are `deg ψ` embeddings: `AlgHom.card`, with separability from characteristic `0`.
5. Hence `deg ψ ≤ #ker ψ(Ω) = #ψ⁻¹(e₀)`.
6. `deg ψ ≠ 0` for an isogeny: `ψ` is quasi-finite at the generic point (`Scheme.Hom.quasiFiniteAt`), and a
   quasi-finite algebra over a field is finite (`Module.Finite.of_quasiFinite`).
7. deg-det's `KerDvd.kerDvdDeg` gives `#ker ψ(k̄) ∣ deg ψ`.

**C. `#ker ψ(ℂ) = det_ℤ(M_ψ|_Λ) > 0` when the kernel is finite** (`card_ker_eq_det`).
1. `M_ψ` is injective. If `M_ψ z = 0`, then `Φ(tz)` is a kernel point for every `t`, so `N·tz ∈ Λ` for every real
   `t`, where `N` is the order of the kernel. Hence `z = 0` (`eq_zero_of_real_smul_mem`).
2. `μ ↦ Φ(M_ψ⁻¹ μ)` is a surjection `Λ → ker ψ(ℂ)` with kernel `M_ψ Λ`. So
   `#ker ψ(ℂ) = [Λ : M_ψ Λ] = |det_ℤ|` (`Submodule.natAbs_det_equiv`).
3. The sign: `det_ℤ = det_ℝ(M_ψ) = normSq(det_ℂ M_ψ) ≥ 0` (`Basis.ofZLatticeBasis_repr_apply`,
   `LinearMap.det_restrictScalars`, `Algebra.norm_complex_apply`).

**D. `det_ℤ(M_ψ|_Λ) ≠ 0` implies that `ψ` is an isogeny** (`latRep`, `latRep_injective`,
`isIsogeny_of_det_ne_zero`).
1. `latRep : End(A) →+* End_ℤ(Λ)` is an injective ring homomorphism, by uniqueness of lifts. homfree-proof's
   `lift_unique` and `hom_eq_zero_of_cpts` are copied into this file.
2. By Cayley–Hamilton, `χ(ψ) = 0` with `χ(0) = det`. So `ψ q(ψ) = q(ψ) ψ = [n]` with `n = −det ≠ 0`.
3. `[n]` is an isogeny in characteristic `0` (`HSyn.mulIsogeny_proved`). So `ψ` is surjective, and finite by
   `IsFinite.of_comp`.

**E. Assembly.** `degEnd_eq_det` combines the cases:
- isogenies: `deg = #ψ⁻¹(e₀) = #ker ψ(ℂ) = det` (B, A, C);
- non-isogenies: `deg = 0 = det` (D).

`degHomogPolyC` then takes `N = det(∑ᵢ Xᵢ · C(Cᵢ))`, where `Cᵢ` is the matrix of `latRep eᵢ` in a `ℤ`-basis of
`Λ`. `N` is homogeneous of degree `#basis = 2g` (`det_isHomogeneous`).

```lean
def DegHomogPolyC : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (_ : k →+* ℂ) (A) (r) (e), …  -- DegHomogPoly + σ
theorem degHomogPolyC (HL) (HT) : DegHomogPolyC
theorem degHomogPoly_of_noEmb (HL) (HT) (HR : DegHomogPolyNoEmb) : DegDet.DegHomogPoly
theorem charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb (HL) (HT) (HR) (HH : HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
theorem degEqDetTateC (HL) (HT) : DegEqDetTateC   -- deg ψ = det V_ℓ(ψ), k ⊂→ ℂ
```

## 4. The new leaves and their ratings

The two leaves are alternatives: the integrator picks one spec.

- **`CharPolyLattice.CharPolyIndepOfEllAlgClosedNoEmb`**, the leaf of the recommended spec.
  - Statement: the field's statement with the extra hypothesis `IsEmpty (k →+* ℂ)`, over the same objects
    (`PkgI3.AbVar`, `homT`, `V_ℓ`).
  - Rating: **LEAF, published, not the printed form.** It is Mumford, *Abelian varieties* (1970), §19 Thm 4 (locator
    UNVERIFIED, the same citation as the field), specialized by a ∀-instance. So it is a consequence of the print and
    never stronger. It is not the printed form because the print has no hypothesis on embeddings.
  - By Steinitz, the fields covered are those of characteristic `p`, and those of characteristic `0` with
    transcendence degree above the continuum (STANDARD).
  - It is live: the characteristic-`p` case is used (§5).
  - Proposed kinds.tsv row: kind `published`, flag "specialization (forall-instance) … the characteristic-p case IS
    used". This is the same precedent as homfree-proof's `HomFreeFiniteAlgClosedNoEmb`.
  - Proposed locators.md row: Mumford §19 Thm 4, restricted to fields with no ring homomorphism to `ℂ`, unread.
- **`DegPolyC.DegHomogPolyNoEmb`**, the leaf of the second spec.
  - Statement: deg-det's `DegHomogPoly` restricted to the same fields.
  - Rating: **LEAF, published, not the printed form.** It is a ∀-instance of deg-det's printed-form leaf (Mumford §19,
    `deg` a homogeneous polynomial function of degree `2g`; locator UNVERIFIED).
  - It is the deeper input: the theorem of the cube and Riemann–Roch in characteristic `p`. With deg-det's Lean
    proof, everything else of Thm 4 is done.
  - It needs the open field `homFreeFiniteAlgClosed` in addition.

Recommendation: fold `autofold.json`. It has the fewest inputs and no dependence on unmerged contributions, and its
leaf is a direct specialization of a numbered theorem. Use `autofold-degpoly.json` or `autofold-after-degdet.json`
if the project prefers the crowdsourcing target to be polynomiality rather than Thm 4.

No statement problem was found. `DegHomogPoly` and the field are true (Mumford §19; STANDARD), non-vacuous, and
consistent with the proofs above. For `dim A = 0`, both sides are `1`.

## 5. Consumers (closure scan, VERIFIED; `scratch/degpoly-proof/Closure.lean`, output `closure_out.txt`)

The scan covers `frozenTarget`'s closure, 259,568 constants. The non-bundle constants whose type mentions T7 or the
field:
- `t7_of_algClosed5`, `charPolyIndepOfEll_of_algClosed`;
- `PkgI3.trace_indep_of_ell`, `GlueC10Link.trace_endE_indep`, `trace_T_of_frobCompare`;
- `G14Trace.common_trace`, `g14TraceCompat_of_link`, `G0AssembleMod.linkedTateData_of_local`;
- `R16Split.trace_endV_rat`, `rank_two_of_dim`, `r16_of_coreY`, `r16_of_printed`.

Two chains reach these:

1. **`gluePieces_of_open4` uses `OpenTextbookLeaves4.t7` only through `linkedTateData_of_local`.** The chain
   continues `→ g14TraceCompat_of_link → common_trace → trace_T_of_frobCompare → trace_endE_indep →
   trace_indep_of_ell`.
   - `common_trace` (TailC L8718) applies T7 at `Ab : PkgI3.AbVar k`.
   - The field `k` comes from `FrobTraceLink` (`Contrib/FrobChain/LinkedStatement.lean` L43–49). It has
     **`CharP k p`**: `Ab` is the reduction mod `p`, and `α` its Frobenius.
   - This is the characteristic-`p` use.
2. **`openResearchLeaves21_of_OpenResearchLeaves22` uses the field through `r16_of_printed → … →
   trace_endV_rat`,** with `A : AbVar ℚ`. `CharPolyIndepOfEllC` covers this chain.

So the characteristic-`p` case of Mumford §19 Thm 4 is genuinely consumed, through `ℓ`-independence of the trace of
Frobenius on the reduction. No reroute onto ℂ-embeddable fields can remove it. Removing the field outright would need
either a proof in characteristic `p` or a different source for the Frobenius trace in `common_trace` (another leaf).
`mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed` and the other open fields do not supply the characteristic-`p`
polynomiality (deg-det §4).

## 6. Compile record (all VERIFIED, Lean 4.35.0, Mathlib v4.35.0)

- `lake build ZInQKernel.Contrib.OneProof.CharPolyLattice`: OK (11,761 jobs).
- `lake build ZInQKernel.Contrib.OneProof.DegHomogPolyC`: OK (11,768 jobs).
- `scratch/degpoly-proof/CheckAxioms.lean` (output in `CheckAxioms-output.txt`):
  - all 17 listed theorems have axioms `[propext, Classical.choice, Quot.sound]`;
  - two `example`s check the exact types of `charPolyIndepOfEllAlgClosed_of_noEmb` and `degHomogPoly_of_noEmb`.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +…CharPolyLattice +…DegHomogPolyC`: OK
  (13,706 jobs), and `frozenTarget` has standard axioms.
- `#discharges` (`scratch/degpoly-proof/Discharges.lean`, output in `Discharges-output.txt`):

  ```
  DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.CharPolyLattice.charPolyIndepOfEllAlgClosed_of_noEmb
    still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll,
   AvSplit.MumfordTorsionAlgClosed,
   ZInQ.Contrib.OneProof.CharPolyLattice.CharPolyIndepOfEllAlgClosedNoEmb]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.DegPolyC.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb
    still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll,
   AvSplit.MumfordTorsionAlgClosed,
   ZInQ.Contrib.OneProof.DegPolyC.DegHomogPolyNoEmb,
   ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 56 open hypotheses, 3095 theorems checked, 13 discharge one
  ```

  The output also lists deg-det's discharges, which are on this base.
- Autofold dry runs (`python3 scripts/one_proof/autofold.py <spec> --dry-run`):
  - both `autofold.json` and `autofold-degpoly.json` print
    `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`;
  - the generated modules `FoldDryRun.lean` and `FoldDryRun-degpoly.lean` (line 1 stripped) compile, and
    `HDec.HSyn.sixContactMin_of_open36` has standard axioms.
- Neither contribution contains `#eval`, `run_cmd`, notation, macros or `sorry`. `Closure.lean` uses `run_cmd`, but
  it is a scratch file.

## 7. What remains

- The characteristic-`p` case: either `CharPolyIndepOfEllAlgClosedNoEmb` or `DegHomogPolyNoEmb`, depending on the
  spec.
- Integration notes:
  - `DegHomogPolyC.lean` imports deg-det's `DegEqDetTate` (unmerged). `CharPolyLattice.lean` imports only main.
  - homfree-proof's `HomFreeFiniteAlgClosed.lean` is not needed by either file. If both folds land, the T6 and T7
    branches use the same pair of open fields (`uniformizationLeafAll`, `mumfordTorsionAlgClosed`) for their
    ℂ-embeddable parts.
