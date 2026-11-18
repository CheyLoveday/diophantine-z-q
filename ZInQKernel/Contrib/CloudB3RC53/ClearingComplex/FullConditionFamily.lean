import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionTame

/-!
# The new places of the full-condition identification are the primes of the family

Manuscript `diophantine_zq.tex`, the triangle (5.6) (tex 5234–5238:
`C_old → (C_b)₀ → ⊕_{q ∈ Q} Q_q → C_old[1]`, one singular quotient per prime `q` of the family,
at the chosen place over `q`), tex 5394–5403 ("after augmentation the representation is unramified
at `Q`").

`Identification3Q K S S' hS F dK hK cE tK` extends `Identification3` (unchanged) by the
identification of its new places with the family's primes `F.Q`:

* `eQ : NewPlaces K S S' ≃ F.Q` — one new place per prime of the family;
* `lies : ∀ v, (eQ v : ℕ) ∈ v` — the new place `v` lies over the prime `eQ v`;
* `hqq : ∀ v, qq v = eQ v` — the residue cardinality of the tame model at `v` is that prime (the
  primes of `Q` split in `K`, `Family.Admissible`).

Consequences (PROVED): `isEmpty_newPlaces_iff` (no new places iff `Q = ∅`), `card_newPlaces`
(`#(S' − S) = #Q`), `eNQ` (the singular summands are indexed by `ι × Q`), and
`tame_singular_quasiIso_Q`: for every `q ∈ Q` the genuine singular quotient at the place over `q`
is quasi-isomorphic to `[M₀ --(Φ − q)--> M₀]` in degrees one and two, with this `q`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

variable (K : Type) [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K)))
  (hS : S ⊆ S')

/-- **The full-condition identification with its new places identified with the family's primes**
(GLUE, additive over `Identification3`). -/
structure Identification3Q [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    (F : Family) (dK hK cE tK : ℕ) extends Identification3 K S S' hS F.b dK hK cE tK where
  /-- one new place per prime of the family -/
  eQ : NewPlaces K S S' ≃ F.Q
  /-- the new place `v` lies over the prime `eQ v` -/
  lies : ∀ v : NewPlaces K S S', (((eQ v : ℕ) : ℤ) : 𝓞 K) ∈ v.1.asIdeal
  /-- the residue cardinality of the tame model at `v` is the prime `eQ v` -/
  hqq : ∀ v : NewPlaces K S S', qq v = (eQ v : ℕ)

namespace Identification3Q

variable {K S S' hS} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {F : Family}
  {dK hK cE tK : ℕ} (M : Identification3Q K S S' hS F dK hK cE tK)

include M in
/-- **No new places iff the family has no primes** (`Q = ∅`). -/
theorem isEmpty_newPlaces_iff : IsEmpty (NewPlaces K S S') ↔ F.Q = ∅ := by
  rw [Equiv.isEmpty_congr M.eQ, Finset.isEmpty_coe_sort]

include M in
/-- **The number of new places is the number of primes of the family.** -/
theorem card_newPlaces : Fintype.card (NewPlaces K S S') = F.Q.card := by
  rw [Fintype.card_congr M.eQ, Fintype.card_coe]

/-- **The singular summands are indexed by `ι × Q`.** -/
def eNQ : M.C.N ≃ M.ιn × F.Q :=
  M.eN.trans (Equiv.prodCongr (Equiv.refl _) M.eQ)

/-- **For every prime `q ∈ Q`, the genuine singular quotient at the new place over `q` is the tame
`[M₀ --(Φ − q)--> M₀]` in degrees one and two**, with the residue cardinality equal to `q`
(PROVED from `tame_singular_quasiIso` and `hqq`). -/
theorem tame_singular_quasiIso_Q (q : F.Q) :
    M.qq (M.eQ.symm q) = (q : ℕ) ∧
      QuasiIso (tameQuotMap (M.tame (M.eQ.symm q))) := by
  refine ⟨?_, M.toIdentification3.tame_singular_quasiIso (M.eQ.symm q)⟩
  rw [M.hqq, Equiv.apply_symm_apply]

end Identification3Q

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
