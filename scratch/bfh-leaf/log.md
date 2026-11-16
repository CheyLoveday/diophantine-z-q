# bfh-leaf results log

Task: replace top hypothesis `hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` of `ZInQ.OneProof.frozenTarget` by a printed
leaf for Bump–Friedberg–Hoffstein 1990, opening theorem clause (ii), and prove `ZInQ.GZDecomp.FHNonvanishing` from it.

## 11-15 23:00 setup
- Merged origin/wip/fh-printed (8d0b9b64), clean. Build tree copied from ~/dzq-wt/unif-printed (.lake/build, lean/.lake/build).
- `lake build ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE`: OK (VERIFIED).

## Split primes (Mathlib only) — VERIFIED (compiled)
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Split.lean` (= scratch/bfh-leaf/Split.lean): `SplitsIn K p` := two distinct
  primes of `𝓞 K` in `(Ideal.span {(p:ℤ)}).primesOver (𝓞 K)`. Proved: `ef_eq_one` (fundamental identity
  `Ideal.sum_ramification_inertia_eq_finrank`), `exists_int_sub_mem` (f = 1), `natCast_not_mem_sq` (e = 1, via
  `ramificationIdx'_eq_ramificationIdx`), `zmod_isSquare_of_splitsIn` (p² ∤ d, √d ∈ K, p split ⇒ d nonzero square mod p),
  `mod_eight_of_splitsIn_two` (d fundamental discriminant, √d ∈ K, 2 split ⇒ d ≡ 1 mod 8). No deprecated API.
