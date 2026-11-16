# hfx-proof results log

Target: `H29Split.TYZTestVectorExists` (hfx), `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L421.
Base: origin/main 0caafe66 + merged origin/wip/t21-proof f597c34c (T21Proof helpers) + origin/proof/hp23-hurwitz-ab-20261116 84a9f2e6 (fork PR #39, Hurwitz approximation).

## Computations (VERIFIED, python `scratch/hfx-proof/orbits.py`)
- Right action of `K_{n,2}^×` on TYZ's 8 classes `O_B^× \ (O_B/4)^× / {±1}`, for every residue of
  `τ(√−n) = ai+bj+ck` (mod 8) allowed by `AdmissibleTau`:
  - n ≡ 3 (mod 8) (a,b,c odd; 64 residues): orbits of sizes (2,6). The 2-orbit depends on the residue
    and need not contain the class of 1 (e.g. (3,1,1): 2-orbit {(1,0,0),(0,0,1)}).
  - n ≡ 1 (mod 8) (4|c, one of a,b odd, the other ≡ 0 mod 4; 32 residues): orbits {000,010}, {110,100},
    {101,111,001,011} for every residue, using the uniformizer 1+τ(√−n); without it (2,2,2,2).
  - Hence `π^{U_n}` is 1-dim in all cases; generator `−3/1` (n≡3), `1/−1/0` (n≡1).

## Lean (compiled with `lake env lean`)
- `HfxProof/Assembly.lean`: `testVector_of_partition` — hfx for (n,τ) from surjectivity onto the 8 double
  cosets, a function F on {0,1}³ whose level sets are the classes, and rank-one linear algebra. COMPILES.
- `HfxProof/Euclid.lean`: `euclid_prime` (βO_B + pO_B = γO_B, nrd γ = p). COMPILES.
- `HfxProof/ClassOne.lean`: `exists_global_mul_unit` (B̂^× = B^× Ô_B^×, Ô_B read place by place). COMPILES.
