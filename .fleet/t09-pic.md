# t09-pic: summary

**Verdict.** The field `t09SymmIsogenyExists` (`HDec.WeilPairing.T09_SymmIsogenyExists`) is **proved from four printed
leaves**, all stated over genuine definitions:
- L1 `PicRepresentableAbVar`: `Pic_{A/K}` is representable (Murre–Oort; FGA 232; Kleiman 9.4.8);
- L2 `PicZeroAbVar`: `Pic⁰` is an abelian variety (Mumford §13; Kleiman 9.5);
- L3 `PhiAmpleIsogeny`: `φ_L` is an isogeny for ample `L` (Mumford §6, §8);
- L4 `WeilPairingMumford`: Mumford's `ē_n` at `Pic⁰`, with its properties (Mumford §§20, 23).

L4 is also split into six one-property leaves, L4a–f (nine leaves in all). One GLUE (c) field becomes four LEAF
fields. All locators are UNVERIFIED (no network).

**What is new and genuine.** Every definition is built over the vendored Jacobian-Challenge Picard library and
Mathlib:
- the Mumford bundle `Λ(L)` and `φ_L : A → Pic_{A/K}` (Yoneda);
- the identity component, and "`(B, ι)` is `Pic⁰`";
- the dual `f^∨` (sheafified pull-back of families);
- `IsAmple` (Stacks 01PS) and `IsVeryAmple` (`i^*𝒪(1)`);
- `t_x` and `n_A` on `A_K̄`;
- **Mumford's `ē_n` itself** (`weilScalar`, the descent scalar `t_x^*ψ ∘ ψ⁻¹ ∈ Γ(A_K̄, 𝒪)`).

So every object in Mumford's statements now exists in Lean, and c-to-printed2's list of missing pieces is done.

**Glue proved.**
- **Very ample ⇒ ample** (EGA II 4.5.10), so the old leaf L0 is a theorem. The key step: the nonvanishing locus of
  `i^*X_k` is `i⁻¹D₊(X_k)`.
- Every abelian variety over every field has a very ample class.
- `φ_L(0) = 0`.
- `φ_L` factors through `Pic⁰` by a homomorphism (connectedness and rigidity).
- `f^∨` restricts to `End(Pic⁰)`.
- `n_A ∘ t_x = n_A` on `A[n]`.
- `weilScalar_spec`: no default branch on `A[n] × Pic⁰[n]`, given L6.

**What compiles.**
- `scratch/t09-pic/Pic.lean` (imports `TailB` and the vendored modules): 0 errors; all 13 `#print axioms` lines are
  `[propext, Classical.choice, Quot.sound]`.
- `scratch/t09-pic/FoldCheck.lean` (on `TailZ19`): `HDec.HSyn.sixContactMin_of_open15_t09pic` gives
  `ZInQ.SixContactMin` from leaf-fold12's bundles, with the field replaced by the four leaves (16-field
  `OpenAddedLeaves11T09Pic`). Standard axioms.
- `scratch/t09-pic/Ample.lean`: the ampleness proof, on vendored imports only.

**Review.** Two independent model reviews found no mathematical error. Their citation cautions are applied.

**What remains.** The four leaves are textbook theorems. Formalizing them is the crowdsourcing target: FGA-level
representability, `Pic⁰` smooth and proper, the theorem of the square / `K(L)` finite, and Mumford §20 duality.
Locators to check against the books: Mumford §§6, 8, 13, 20, 23; Kleiman 9.2.5, 9.4.8, 9.5; Milne 16.2(c).

Report: `docs/research/t09-pic.md` (fold recipe in §6). Log: `scratch/t09-pic/log.md`.
