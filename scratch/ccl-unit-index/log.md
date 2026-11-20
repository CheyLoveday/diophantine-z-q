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
