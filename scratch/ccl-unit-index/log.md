# CCL unit index: sizing and verification log

Base: `e2c1297914384566331b965e22e95a3bb6512475`.

**VERIFIED (tree and manuscript).** The manuscript already excludes both exceptional fields
(tex 2720–2722, 2836–2844) and explicitly invokes that exclusion before dropping the factor
(tex 2914–2929). The Lean interface drops it without encoding the exclusion. No error was
found in these manuscript lines.

At the base, `ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean` has precisely these
CCL statements (using `T(d,q) := ∑ τ ∈ D.relGal d q, Affine.Point.map τ.toAlgHom (D.y (d*q))`
and `F(d,q) := D.frob d q` to fit the display):

- L138–140: `D.Admissible d q := 0 < d ∧ Nat.Coprime d (2 * D.N * D.DK.natAbs) ∧ q.Prime ∧
  ¬ q ∣ 6 * d * D.N * D.DK.natAbs`. This permits `d = 1`.
- L145–153: `D.NormRelations` is the conjunction of
  `∀ d ℓ, D.Admissible d ℓ → jacobiSym D.DK ℓ = -1 →
  T(d,ℓ) = (E.LFunction ℓ : ℤ) • D.y d` and
  `∀ d q, D.Admissible d q → jacobiSym D.DK q = 1 →
  T(d,q) = (E.LFunction q : ℤ) • D.y d -
    Affine.Point.map (F(d,q)).toAlgHom (D.y d) -
    Affine.Point.map (F(d,q))⁻¹.toAlgHom (D.y d)`.
- L156–159: `HeegnerPointData.zero_normRelations` supplies these relations for every
  `DK, N, H, relGal, frob` if the point system is zero.
- L176–177: `CCLThm2_15Applied E Anchor := ∃ D : HeegnerPointData E,
  D.NormRelations ∧ Anchor D`. There is no unit hypothesis on either clause or on the anchor.

The exact reference and applied formula were cross-checked against the existing reading-desk
audit: Cai–Chen–Liu, Trans. Amer. Math. Soc. 370 (2018), Thm 2.15, p. 3730
(read: AI reading of the journal page). The independently visible manuscript citation is at
tex 2918. The print puts `u_m` on the trace, with `u_m = 1` for `m ≠ 1` and
`u_1 = [𝒪_K^× : ℤ^×]` in the recorded wording. No journal page was re-read in this pass.

**VERIFIED (consumer search).** See [consumers.md](consumers.md) for the semantic uses,
the available premises and the comment-only references. The build graph at the base gives
two immediate importers of `Heegner` and 461 importers in the reverse transitive closure.

**VERIFIED (Lean).** The proposed mod-8 argument excludes −3 only: `2² = −4` in
`ZMod 8`. The Heegner form hypothesis at `4 ∣ N` gives the congruence modulo 16,
where neither −3 nor −4 is a square. At generic level the numerical inputs to the
split transport can hold with `(d,N,D_K,q) = (1,37,−4,5)` and Heegner form
`[37,12,1]`. The linear algebra of transport alone does not remove a unit
factor. The staged conductor bound follows from the prime divisor and positivity.

**VERIFIED (build).** Built `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`
and `Mathlib.Data.ZMod.Basic` separately with `lake build`. Then
`lake env lean scratch/ccl-unit-index/Check.lean` passed. See
[axioms.txt](axioms.txt) for all six declarations. No project module was changed.

**Stop rule.** The generic transport exports unweighted equalities at arbitrary
admissible `d`, with arbitrary `Anchor` in its print wrappers. Neither the level
nor conductor discharge is available in those premises. Keeping the generic
unweighted claims over a corrected leaf would require an extra premise, so the
Lean leaf and all consumer statements and proofs were left unchanged. The staged
conductor calculation alone does not settle the independent scope question of
using `m = d` instead of the manuscript audit's `c = d, m = 1` specialization.
