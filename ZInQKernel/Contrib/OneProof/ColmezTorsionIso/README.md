# ColmezTorsionIso: `A[p^n](F̄) ≅ A[p^n](C_p)`, `G_F`-equivariantly

The lead's LEAF path for the open hypothesis `colmez1992DeRhamAbVar`
(`HDec.HSyn.OpenAddedLeaves30.colmez1992DeRhamAbVar`, statement
`DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar` in `TatePrints/Rows.lean`), from the row ruling in
`docs/one-proof/kinds.tsv`: "a named Lean theorem identifying A[p^n](F̄) with A[p^n](C_p),
G_F-equivariantly, with the model step ruled". This is the readers' non-blocking point (1) in
`docs/research/tate-prints-adversarial-readings.md`, now a Lean theorem.

Add-only. Imports: `G9/Galois.lean`, `AbVarBC/Main.lean` (`Basic`, `Shape`), and
`TatePrints/Rows.lean` (`Row` only). No new hypothesis; every theorem uses only `propext`,
`Classical.choice`, `Quot.sound`.

## The setting in the tree

* The row's abelian variety is `A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F` (`G9/I4Layer.lean`): a
  commutative group scheme over `Spec F`, proper, smooth, geometrically integral, for an abstract
  finite extension `F/ℚ_p`. There is no integral model.
* `A.T p = Tate.T p (Additive (A.Pt (AlgebraicClosure F)))` (`G9/I4Layer.lean`, `AbVar.T`): the
  inverse limit of the `p^n`-torsion of the `F̄`-points, `F̄ = AlgebraicClosure F`; `A.V p` is
  `ℚ_p ⊗ A.T p`, and `A.galRep p` lets `σ ∈ G_F` act on coordinates.
* `G_F` acts on `B_dR` through `gfToGqp p F : G_F → G_{ℚ_p}`, restriction along the isomorphism
  `embF : ℚ̄_p ≃ F̄` (`G9.embF_gfToGqp`, `G9.embF_bijective`); `phiF : F → ℚ̄_p` and
  `F' = fieldF p F` are the corresponding copy of `F` in `ℚ̄_p`.

## The model step, ruled

* Colmez's `K` is `F` and his `X` is `A`. His identification `𝒳(O_{C_p}) = X(C_p)` for a proper
  model `𝒳` over `O_K` (p. 638, "Par construction") is taken as given: the statement of
  Théorème 5.2 uses only the group `X(C_p)` and its Galois action, both read off `A` over `F`. The
  model enters Colmez's construction of the periods, not the statement (and the periods do not
  depend on it, p. 640).
* `C_p` is an `F`-algebra through `F → ℚ̄_p ⊂ C_p`, `y ↦ phiF y` (`algCp`, a local instance only),
  whose image is the tree's `F'`. The embedding `F̄ → C_p` is `x ↦ embF⁻¹ x` (`iotaFbar`), the
  same isomorphism `ℚ̄_p ≃ F̄` that defines `gfToGqp`; it is an `F`-algebra map.
* `σ ∈ G_F` acts on `C_p` by `cpAct (gfToGqp σ)` (`cpGal`), the continuous extension of `σ`, which
  is the action the row uses on `B_dR` (`bdrAct (gfToGqp σ)`); `iotaFbar` is `G_F`-equivariant
  (`iotaFbar_galF`). On points, `G_F` acts on coordinates (`galAct`).

## Statements (namespace `ZInQ.Contrib.ColmezTorsionIso`)

`Basic.lean`:

* `exists_extPt_eq_of_pow`: for a kernel abelian variety `B` over a field `K` of characteristic
  `0`, a `K`-embedding `κ : Ω → Ω₂` with `Ω` algebraically closed, and `N ≠ 0`, every `q ∈ B(Ω₂)`
  with `q ^ N = 1` is `extPt κ x` for some `x ∈ B(Ω)`. Proof: `[N]` is finite (the tree's proved
  `AbVarBC.mulIsogeny`), so `q` is a point of the finite `K`-scheme `B[N]`, whose `Ω₂`-points have
  coordinates integral over `K`, hence in `κ(Ω)` (`AbVarBC.exists_lift_of_isFinite`).
* `extCp p A : A.Pt (AlgebraicClosure F) →* A.Pt ℂ_[p]`, the natural map `P ↦ P ∘ Spec(ι)`;
  `extCp_injective` (any field extension), `extCp_surj_torsion` (on `N`-torsion, `N ≠ 0`),
  `extCp_galAct` (`extCp (σ • x) = cpGal σ • extCp x`).
* `torsCp p A N hN : tors (Additive A(F̄)) N ≃+ tors (Additive A(ℂ_p)) N`, with `torsCp_apply`
  (it is `extCp`) and `torsCp_galAct` (`G_F`-equivariance).
* **`torsion_iso`**: for `N ≠ 0`, the natural map `A[N](F̄) → A[N](ℂ_p)` is bijective, additive,
  and commutes with `G_F`; `torsion_iso_pow` is the case `N = p^n`.
* `TCp p A = Tate.T p (Additive A(ℂ_p))`, `VCp p A = ℚ_p ⊗ TCp p A`, `galRepCp p A` (Colmez's
  `T_p(X)`, `V_p(X)` and Galois action); `tateCp p A : A.T p ≃ₗ[ℤ_p] TCp p A` with `tateCp_galT`;
  `vCp p A : A.V p ≃ₗ[ℚ_p] VCp p A` with **`vCp_galRep`**:
  `vCp (A.galRep p σ v) = galRepCp p A σ (vCp v)`.

`Shape.lean`: `ColmezShape p F Q ρ` (the row's conclusion for a representation `ρ`, with `B_dR⁺`
abstracted as `Q`), `colmezShape_transfer` (invariance under a `G_F`-equivariant linear
isomorphism), `colmezShape_iff_cp`.

`Row.lean` (namespace `DeRhamScholze.TatePrints.ColmezCp`):

* `Colmez1992DeRhamAbVarCp : Prop`: the row word for word, with `A.V p`, `A.galRep p` replaced by
  `VCp p A`, `galRepCp p A` (`T_p` from the `C_p`-points, as printed on pp. 638-639).
* **`colmez1992DeRhamAbVar_iff_cp : Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarCp`**, and
  `colmez1992DeRhamAbVar_of_cp : Colmez1992DeRhamAbVarCp → Colmez1992DeRhamAbVar`.

## What remains for the lead

* The identification of the two Tate modules is now a Lean theorem, so the reading step of the
  ruling is gone: `Colmez1992DeRhamAbVarCp` states Théorème 5.2 (i)-(ii) with Colmez's own
  `T_p(X)`, and the row follows from it by `colmez1992DeRhamAbVar_of_cp`. If the lead accepts
  this, the row can be re-rated against `Colmez1992DeRhamAbVarCp` (a fidelity reading of the new
  statement against p. 639 is needed; it differs from the read row only in `T_p` and its action).
* Not formalized, ruled as above: Colmez's `𝒳(O_{C_p}) = X(C_p)` for a proper model over `O_K`
  (valuative criterion; the tree has no integral model). The statement in Colmez's terms is about
  `X(C_p)`, so no model enters it.
* The readers' non-blocking points (2) (`ℤ_p`-linearity in `u`) and (3) (dropped clauses) are
  unchanged.
* The ledgers (`kinds.tsv`, `reviews.tsv`, the open list) are not edited here (add-only).
