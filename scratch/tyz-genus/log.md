# tyz-genus results log

Task tyz-genus (2026-11-16). Base wip/leaf-fold33b 4da8d4f3; merged origin/main (up to date),
origin/wip/h29-proof, origin/wip/h11-reduce (clean merges). Build tree reflink-copied from ~/dzq-wt/leaf-fold33b
(identical Main.lean); `lake build TYZLemma29Genus TYZThm11Integral TYZProp23Printed` OK.

TYZ source ~/tyz-src/Period7.tex: NOT on this host (ls fails). TYZ line numbers below are quoted from earlier notes.

## Step 0: findings before Lean (VERIFIED by reading the files)

* F0.1 `TYZThm21Pairs` (TYZLemma29Genus.lean:91) quantifies over integer sign choices `ℓ : ℕ → ℤ` with
  `IsLcalSign ℓ` (`(ℓ m)^2 = lcalSq m` for every squarefree m ≡ 1,3 mod 8). As h11-reduce §1 found for
  `TYZLemma29PrintedNe3`, such a leaf is vacuous unless TYZ Thm 1.1 (= h11) holds, so h11 cannot be derived from
  `TYZThm21Pairs` (item (3) of the task is impossible in that form).
* F0.2 `TYZThm21Pairs` requires `1 < n`; the values L(1)^2 needs an instance with d1 d2 = 1, i.e. n = 1, which
  the leaf excludes; at n = 3, pair (3,1) only gives 𝓛(3)^2 𝓛(1)^2 = (Q(3)/3)^2 (product, not each factor).
