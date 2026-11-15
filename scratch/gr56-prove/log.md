# gr56-prove results log

Base 43513d87 (leaf-fold25). Target: research field `gonzalezRotgerProp56X6` (`GRCountX6.GonzalezRotgerProp56X6`).

## Findings
- VERIFIED (scratch/gr56-prove/Reach.lean, reach.txt; closure of `ZInQ.OneProof.frozenTarget`, 97682 constants):
  the only live consumer of the count (`R5fpCount`, reached from the field through
  `gonzalezRotgerCountX6Ab_of_printed` (TailZ27) and `ShimuraSplit.r5fpCount_of_points` (TailZ8/9)) is
  `HDec.FS5NoCM.nocm_on_witness` (TailC L1371), via `fibreComTrivialOwn_of`, `fibreComTrivialFull_of`,
  `fibreComTrivialFull_of_leaves'`, `fibreComTrivialFull_of_leaves''` (TailC), called from TailK L294
  (`gluePieces_of_open4`, `r.r5count`). LPrefix's `subsingleton_of_bundle` (pi0 route) is not live.
- VERIFIED (reading TailC L1371-1452): `nocm_on_witness` uses the count only as an upper bound
  (`#CM(R) ≤ 2` against four distinct CM points), for arbitrary `R`.
- Assessment: the field (exact count for every order of conductor prime to 6) needs (a) Eichler's
  optimal-embedding count (local quaternion orders at 2, 3; not in Mathlib) and (b) the existence of QM
  surfaces over ℚ̄ with prescribed CM (Shimura; no kernel input). Neither is in reach; plan: prove the
  injection CM(R) ↪ optimal embeddings mod 𝒪^× from the textbook fields (lattice model), giving the
  upper bound from `GRCountX6.EichlerOptEmbCount6`, and reroute the single consumer.

## Compile log
- Probe1.lean: names checked (VERIFIED).
- GR56Lattice.lean §1-§2 (LatData, exists_latData, ρn, realize, qmIso_of_scalar): compiles after cancel fix.
- GR56Lattice.lean §3-§10 compile (VERIFIED, `lake env lean`, 0 errors); `#print axioms` of
  `GR56.exists_injective_optEmb`, `GR56.card_cmSet_le`, `GR56.emb_opt`, `GR56.qmIso_descend`:
  [propext, Classical.choice, Quot.sound].
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GR56Lattice`:
  OK (12995 jobs). `#discharges` (scratch/gr56-prove/discharges.txt): 63 open hypotheses, 1899 theorems checked,
  7 discharge one, none from GR56 (expected: R5fpCountLe is weaker than the field; manual fold).

## Statements proved (GR56Lattice.lean)
- `GR56.exists_injective_optEmb hU hG hM k hk R hR hc : ∃ F : CMSet R → Quot (GRCountX6.ConjRel R), Injective F`
- `GR56.card_cmSet_le … (hfin : Finite (Quot (ConjRel R))) : Finite (CMSet R) ∧ card (CMSet R) ≤ card (Quot …)`
- `GR56.R5fpCountLe` (def), `GR56.r5fpCountLe_of_r5fpCount : R5fpCount → R5fpCountLe`,
  `GR56.r5fpCountLe_of_eichler : EichlerOptEmbCount6 → hU → hG → hM → R5fpCountLe`
- `HDec.FS5NoCM.nocm_on_witness_le`, `fibreComTrivialOwn_of_le`, `fibreComTrivialFull_of_le`,
  `fibreComTrivialFull_of_leaves'_le`, `fibreComTrivialFull_of_leaves''_le` (consumer chain with R5fpCountLe).
