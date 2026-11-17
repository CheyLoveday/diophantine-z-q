# hp23-proof results log

Target: `H29Split.TYZProp23Printed` (hP23), `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L488.
Base: wip/hfx-proof 779d0d7d + merge origin/main (c1e4ed1b) = ee2f8a65.
Build tree: reflink copy of ~/dzq-wt/neron-flt/.lake/build (same Main.lean), then
`lake build ZInQKernel.Contrib.OneProof.TYZTestVectorExists` (scratch/hp23-proof/build1.txt).

## Plan (route of hfx-proof report §7)
1. `tv_eq_sign`: every test vector is `±F` on the double coset `DC(twoRep t)` (from the partition data of
   hfx-proof's `testVector_of_partition`; `fOf F ∈ π_ℤ^{U_n}` + generation + rank one).
2. n ≡ 3: F ∈ {−3, 1}, odd.
3. n ≡ 1: F ∈ {1, −1} off the classes with t.2.2 = 1; `h²` lies in a class with t.2.2 = 0 by the invariant
   `nrd ∈ 2^ℤ(1 + 4ℤ₂)` at 2 (`Good`), with even valuations of `nrd γ` at odd primes.
