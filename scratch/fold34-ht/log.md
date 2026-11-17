# fold34-ht log

Base wip/leaf-fold33b c0f3d085c (= origin/main; not moved). Render_open count at base: 35 open (29 H, strictest 11/18,
6 others) (leaf-fold33 log step 17).

1. Merged origin/wip/hodgetate-from-dr (7320b450) without conflicts (its merge base 5e235a40a is an ancestor of the
   base). Count unchanged (35 open): the merge adds only Contrib modules and scratch files, not imported by Main.
2. New Contrib modules (fold34-ht), separate from the fold:
   * `ZInQKernel/Contrib/OneProof/HodgeTatePairingWeil0.lean` (imports TailK): `tatePairingZl_field0`,
     `tateGSp_field0` = hodgetate-from-dr's `HodgeTatePairingWeil.lean` verbatim with T9 in the type of
     `PicZeroChar0.T09_SymmIsogenyExists0` (written out) and `[CharZero K]` added.
   * `ZInQKernel/Contrib/OneProof/HodgeTatePairingCore0.lean`: `hodgeTateDecompAbVar_of_leaves0` = Core verbatim with the
     characteristic-0 T9 (F is finite over Q_p, CharZero F is derived in the proof already).
   * `ZInQKernel/Contrib/OneProof/HodgeTatePairingCharZero.lean`: `t09SymmIsogenyExists0_of_open` (from
     picRepresentableAbVar, kleimanPicZeroProper, mumfordTorsionAlgClosed via picZeroAbVar0_of_leaves with
     picLocFinType_proof and identityComponentLFT_proof, phisurj's characteristic-0 theorems) and
     `hodgeTateDecompAbVar_of_open (hHT : HodgeTateDecompExists) (hM : MumfordTorsionAlgClosed)
     (h1 : PicRepresentableAbVar) (hK : KleimanPicZeroProper) : HodgeSplit.HodgeTateDecompAbVar`.
   Build oleans copied (reflink) from ~/dzq-wt/lcal-one (byte-identical Main.lean, ZInQKernel differs only by its own
   Contrib files).
