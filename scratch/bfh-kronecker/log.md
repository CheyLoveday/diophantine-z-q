# bfh-kronecker results log

Task: restate bfh-leaf's `BFHClauseII` over the Kronecker symbol `(D/n)` (BFH's χ_D), prove the bridge to
fh-printed's `idelicChar`, rebuild the hFH discharge + fold check using only B = 4.

## 11-16 05:50 setup
- Build tree: copied (reflink) ~/dzq-wt/fh-printed/.lake/build and lean/.lake/build (fh-printed HEAD 8d0b9b64 differs
  from this base only in new files + OneProof/Main.lean).

## Kronecker symbol (Mathlib + FHPrinted/LocalNorm only) — VERIFIED (compiled, no warnings)
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Kronecker.lean`:
  `kroneckerPrime D p := if p = 2 then χ₈ (D : ZMod 8) else jacobiSym D p`;
  `kroneckerSym D n := if n = 0 then (if |D| = 1 then 1 else 0) else ∏_{p^k ∥ n} kroneckerPrime D p ^ k`.
- Proved: kroneckerSym_one, kroneckerSym_mul (m,n ≠ 0), kroneckerSym_of_prime, kroneckerSym_prime (= legendreSym p D,
  p odd), kroneckerSym_two (= χ₈ D), kroneckerSym_two_of_one_mod_four; charAtPrime_odd (p odd, p² ∤ d: charAtPrime d p
  = legendreSym p d), charAtPrime_two_of_one_mod_four (= χ₈ d), charAtPrime_four_mul (square class), 
  charAtPrime_eq_kroneckerPrime (every fundamental d, every prime p), idelicChar_eq_kroneckerSym (every fundamental d,
  n ≠ 0), kroneckerSym_eq_jacobiSym (d ≡ 1 mod 4 squarefree, n ≠ 0).
- Pitfall: in this toolchain `if_pos`/`if_neg` are deprecated (use `ite_eq_left`/`ite_eq_right` with the condition);
  `simp only [key]` under `∀ u : ℤ_[p], … (u : ℚ_[p])` fails (subring coercion motive): rewrite with a funext'd
  equality of predicates instead.
