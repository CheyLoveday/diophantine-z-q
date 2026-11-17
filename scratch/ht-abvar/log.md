# ht-abvar results log

## 2026-11-17 setup
- Base: bfcab3800 (derham-scholze); merged origin/main (d973b8e8d) and origin/wip/c8-conrad2 (6d7cee6e2) for the
  C8/Poincare dry-run inputs. Build tree: reflink copy of ~/dzq-wt/cm-branch/.lake/build (+ lean/.lake/build),
  whose Main.lean is byte-identical.

## (1) The field and its Picard route (VERIFIED by reading the tree)
- Field: `hodgeTateDecompAbVar : ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (TailS.lean L347): for every
  finite F/Q_p, A : PkgI4.I3.AbVar F, g with A.dim = g: G_F-equivariant C_p (x) V_p(A) ~ C_p(1)^g x C_p^g.
- Filled at TailZ74 L381 (`openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf`):
  `hodgeTateDecompAbVar_of_open_k954 n.hodgeTateDecompExists t.mumfordTorsionAlgClosed l.picRepresentableAbVar
  l.kleimanPicZeroProper954` (TailZ69 L55): (a,b) from HodgeTateDecompExists, a=b from the Weil pairing of a
  symmetric isogeny A -> A^vee (t09SymmIsogenyExists0_of_open_k954, the Picard rows), a+b=2g.
- `n.hodgeTateDecompExists` comes from the open field `hodgeTateDecompOr` (TailZ79:
  `hodgeTateDecompExists_of_or n.hodgeTateDecompOr`); its only reader is the line above.
