# dcy3-used results log

Base 43513d87 (leaf-fold25). Build tree copied from ~/dzq-check2 (bc90deac, same Lean tree).

## Step 1: consumers (VERIFIED, read)

* `HDec.HSyn.OpenAddedLeaves17.deligneComponentsY3PrintedAb` is copied unchanged through the added bundles
  (TailZ34 -> Z31 -> Z30 -> Z26 -> Z24) to `OpenAddedLeaves12`; `TailZ23.addedLeaves9_of_open14` turns it into
  `deligneComponentsY3Printed` (non-Ab) by `deligneComponentsY3Printed_iff_ab_gl (qmFamilyGroupLaw_of_groupLaw
  r.mumfordGroupLaw)`; `TailZ13.addedLeaves8_of_open9` uses it once:
  `y3Connected := y3Connected_of_deligne (deligneComponentsY3_of_printed l.deligneComponentsY3Printed)`.
* `y3Connected : TSHecke.Y3Connected` (TailG l.8352: `∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left`) is used only
  as `hconn` in `propTSAll_of_pieces3` (TailK l.317) -> `coverModelOfHecke_of_heckeRest` ->
  `heckeIrreducible_of_connected` (TailG l.8380): every fine witness is irreducible.
* So the field is used only through "some fine witness Y3 is connected over Q". Neither the bijection
  pi0 = Q>0\Af^x/nrd(K3) nor the Galois action is used beyond that.

## Step 2: weakest used form

`Y3ConnectedAb : ∃ Y Φ, R1fpPropsAb Y Φ ∧ ConnectedSpace Y.left` (abelian-scheme clause list, as the field).
