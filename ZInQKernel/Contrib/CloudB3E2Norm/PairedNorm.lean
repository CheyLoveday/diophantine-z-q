import ZInQKernel.Contrib.CloudB3E2Norm.TransferNorm
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange

/-!
# The paired twin of the norm identity, and its reading in Selmer-cone coordinates

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4166–4170):

> The generic paired strict lift satisfies `j z_S = e_q^c z_{P⊥}`. Conjugation sends `z` to `z⁻¹`,
> so `e_q^c = e_q`.

Here `j : C_S → C_{P⊥}` is the paired strict-to-primitive map (at `q`: from the zero condition to
the unramified condition). The consumer is lane RC30's `hlamR_of_genuine`
(`RC/Wiring/RetentionGenuineFunctionals.lean`), whose hypothesis is
`hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b`.

* **`paired_transfer_kummer_norm_of_transversal`** (PROVED): the transfer-level identity on the
  paired side, in the form of `transfer_kummer_norm_of_transversal`: for paired coefficient
  characters `θ'P`, `θ'R` (compatible, `hθ'`) whose Frobenius value is the inverse one,
  `θ'P(σ) = θP(σ)⁻¹` (`hconj`, "conjugation sends `z` to `z⁻¹`"), the twisted transfers
  `z'_T = 𝒯_{θ'}(κ(Q'_T))` of the paired Kummer cocycles satisfy
  `z'_S(g) = e_q z'_{P⊥}(g) + (R'(g) b' − b')` with the SAME point factor
  `e_q = pointFactor a z z⁻¹` (`eq_conj`: `e_q^c = e_q`), the retained boundary `b'` explicit and
  `k`-torsion, and `M[k]`-valued cochains.
* **`hlift_of_components`** (PROVED): exactly what identifies such a global identity with `hlift`.
  In the Selmer cone `C^n = G^n ⊕ U^n ⊕ L^{n−1}` (`selCx`, differential
  `d(a, u, x) = (da, du, res a − ι u − dx)`) and with `j = changeMap DPp fS`
  (`(a, u', x) ↦ (a, f_S u', x)`), `hlift` with boundary `b = (b₀, b_u, b_x)` holds as soon as
  1. (global) `a_S = e a_P + d b₀` — the transfer-level identity above, read in the global
     cochains `G^1`;
  2. (local condition) `f_S u_S = e u_P + d b_u` in `U^1`;
  3. (homotopy) `x_S = e x_P + (res b₀ − ι b_u − d b_x)` in `L^0`.
  `hlift_of_components_iff` (PROVED): conversely `hlift` with boundary `(b₀, b_u, b_x)` is
  equivalent to these three component identities.
* Non-vacuity: `nonVacuity_paired`, `nonVacuity_components`.

**What remains** to supply `hlift` for the genuine paired complexes: the global component (1)
needs the identification of `G^1` (continuous cochains of `G_{K,S}` with finite coefficients) with
the cochains of this file and the paired points `y'_T`; components (2) and (3) are local: the local
Kummer cocycles of the paired points lie in the local conditions (the Kummer condition at the old
places, zero/unramified at `q`), with the homotopy component read off from those local identities.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Central (pointFactor)

/-! ### The paired transfer identity -/

section Paired

variable {G : Type*} [Group G] {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M)
  (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : G) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

omit [Fintype (G ⧸ HP)] in
/-- **`e_q^c = e_q`** (PROVED): if the paired character takes the inverse Frobenius value,
`θ'(σ) = θ(σ)⁻¹`, its point factor `a − z⁻¹ − z` is the point factor `a − z − z⁻¹` of `θ`. -/
theorem eq_conj (θP θ'P : G ⧸ HP →* Aˣ) (a : ℤ) (σ : G)
    (hconj : θ'P (σ : G ⧸ HP) = (θP (σ : G ⧸ HP))⁻¹) :
    eq_ HP θ'P a σ = eq_ HP θP a σ := by
  simp only [eq_, frobValue, frobValueInv, hconj, inv_inv, pointFactor]
  ring

set_option linter.unusedSectionVars false in
include hrP hrR hU ht in
/-- **The generic paired strict lift satisfies `j z_S = e_q^c z_{P⊥}`, with its retained boundary,
at the level of the twisted transfer** (PROVED; tex 4166–4170 at a finite coefficient stage). For
paired characters `θ'P`, `θ'R` (`θ'R` inflated from `θ'P`) with `θ'P(σ) = θP(σ)⁻¹`, paired points
`y'_P` (support `P⊥`, fixed by `HP`) and `y'_R` (support `S`, fixed by `HR`) satisfying (4.1),
`∑_τ ρ(t_τ) y'_R = a y'_P − σ y'_P − σ⁻¹ y'_P`, and division points `k Q'_T = y'_T`:
`z'_S(g) = e_q z'_{P⊥}(g) + (R'(g) b' − b')` for every `g`, with `e_q = eq_ HP θP a σ` the point
factor of the ORIGINAL character, `b'` explicit and `k`-torsion, and `z'_S`, `z'_{P⊥}`
`M[k]`-valued. -/
theorem paired_transfer_kummer_norm_of_transversal (hle : HR ≤ HP)
    (θP θ'P : G ⧸ HP →* Aˣ) (θ'R : G ⧸ HR →* Aˣ)
    (hθ' : ∀ x : G, ((θ'R (x : G ⧸ HR) : Aˣ) : A) = θ'P (x : G ⧸ HP))
    (k a : ℤ) (σ : G) (hconj : θ'P (σ : G ⧸ HP) = (θP (σ : G ⧸ HP))⁻¹)
    {yR yP QR QP : M}
    (hQR : k • QR = yR) (hQP : k • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : G) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP) :
    (∀ g : Fin 1 → G, T HR rR hrR ρ θ'R 1 (kummerCochain ρ HR QR) g =
        eq_ HP θP a σ • T HP rP hrP ρ θ'P 1 (kummerCochain ρ HP QP) g +
          (R HR ρ θ'R (g 0) (retainedBoundaryT ρ HP HR rP rR θ'P θ'R a σ QR QP) -
            retainedBoundaryT ρ HP HR rP rR θ'P θ'R a σ QR QP)) ∧
      k • retainedBoundaryT ρ HP HR rP rR θ'P θ'R a σ QR QP = 0 ∧
      (∀ g : Fin 1 → G, k • T HR rR hrR ρ θ'R 1 (kummerCochain ρ HR QR) g = 0) ∧
      (∀ g : Fin 1 → G, k • T HP rP hrP ρ θ'P 1 (kummerCochain ρ HP QP) g = 0) := by
  rw [← eq_conj HP θP θ'P a σ hconj]
  exact transfer_kummer_norm_of_transversal ρ HP HR rP hrP rR hrR θ'P θ'R U hU t ht hle hθ' k a σ
    hQR hQP hfixR hfixP hnorm

end Paired

/-! ### Reading the identity in Selmer-cone coordinates -/

section Cone

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {S : Type u} [CommRing S] (D : SelData S) {U' : GCx S} (f : GHom U' D.U)

/-- **`hlift` is equivalent to its three components** (PROVED): for `j = changeMap D f`
(`(a, u', x) ↦ (a, f u', x)`) and the Selmer-cone differential `d(a, u, x) = (da, du,
res a − ι u − dx)`, the identity `j z_S = e z_P + d (b₀, b_u, b_x)` holds iff its global, local
condition and homotopy components hold. -/
theorem hlift_of_components_iff (zS : (selCx (restrictData D f)).X 1) (zP : (selCx D).X 1)
    (e : S) (b₀ : D.G.X 0) (bu : D.U.X 0) (bx : D.L.X (0 - 1)) :
    (changeMap D f).f 1 1 rfl zS = e • zP + (selCx D).d 0 1 rfl ((b₀, bu, bx) : selT D 0) ↔
      ((zS : selT (restrictData D f) 1).1 = e • (zP : selT D 1).1 + D.G.d 0 1 rfl b₀ ∧
        f.f 1 1 rfl (zS : selT (restrictData D f) 1).2.1 =
          e • (zP : selT D 1).2.1 + D.U.d 0 1 rfl bu ∧
        (zS : selT (restrictData D f) 1).2.2 = e • (zP : selT D 1).2.2 +
          (D.res.f 0 (1 - 1) (by omega) b₀ - D.ι.f 0 (1 - 1) (by omega) bu -
            D.L.d (0 - 1) (1 - 1) (by omega) bx)) := by
  constructor
  · intro h
    exact ⟨congrArg (fun c : selT D 1 => c.1) h, congrArg (fun c : selT D 1 => c.2.1) h,
      congrArg (fun c : selT D 1 => c.2.2) h⟩
  · rintro ⟨hG, hU, hL⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact hG
    · exact hU
    · exact hL

/-- **`hlift` from its three components** (PROVED; the direction used by the consumer). -/
theorem hlift_of_components (zS : (selCx (restrictData D f)).X 1) (zP : (selCx D).X 1)
    (e : S) (b₀ : D.G.X 0) (bu : D.U.X 0) (bx : D.L.X (0 - 1))
    (hG : (zS : selT (restrictData D f) 1).1 = e • (zP : selT D 1).1 + D.G.d 0 1 rfl b₀)
    (hU : f.f 1 1 rfl (zS : selT (restrictData D f) 1).2.1 =
      e • (zP : selT D 1).2.1 + D.U.d 0 1 rfl bu)
    (hL : (zS : selT (restrictData D f) 1).2.2 = e • (zP : selT D 1).2.2 +
      (D.res.f 0 (1 - 1) (by omega) b₀ - D.ι.f 0 (1 - 1) (by omega) bu -
        D.L.d (0 - 1) (1 - 1) (by omega) bx)) :
    ∃ b : (selCx D).X 0, (changeMap D f).f 1 1 rfl zS = e • zP + (selCx D).d 0 1 rfl b :=
  ⟨((b₀, bu, bx) : selT D 0), (hlift_of_components_iff D f zS zP e b₀ bu bx).mpr ⟨hG, hU, hL⟩⟩

end Cone

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `paired_transfer_kummer_norm_of_transversal`**: the trivial
group acting trivially on `ℤ`, `HP = HR = U = ⊤`, trivial characters (so `θ'P(σ) = 1 = θP(σ)⁻¹`),
sections and transversal, `k = 2`, `a = 3`, `y'_P = y'_R = 2`, `Q'_P = Q'_R = 1`. -/
theorem nonVacuity_paired :
    ∃ (ρ : Unit →* Module.End ℤ ℤ) (HP HR : Subgroup Unit) (_ : HP.Normal) (_ : HR.Normal)
      (_ : Fintype (Unit ⧸ HP)) (_ : Fintype (Unit ⧸ HR)) (rP : Unit ⧸ HP → Unit)
      (rR : Unit ⧸ HR → Unit) (θP θ'P : Unit ⧸ HP →* ℤˣ) (θ'R : Unit ⧸ HR →* ℤˣ)
      (U : Subgroup HP) (_ : Fintype (HP ⧸ U)) (t : HP ⧸ U → HP) (yR yP QR QP : ℤ),
      (∀ δ, ((rP δ : Unit) : Unit ⧸ HP) = δ) ∧ (∀ δ, ((rR δ : Unit) : Unit ⧸ HR) = δ) ∧
      (∀ h : HP, h ∈ U ↔ (h : Unit) ∈ HR) ∧
      (∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ) ∧ HR ≤ HP ∧
      (∀ x : Unit, ((θ'R (x : Unit ⧸ HR) : ℤˣ) : ℤ) = θ'P (x : Unit ⧸ HP)) ∧
      θ'P ((() : Unit) : Unit ⧸ HP) = (θP ((() : Unit) : Unit ⧸ HP))⁻¹ ∧
      (2 : ℤ) • QR = yR ∧ (2 : ℤ) • QP = yP ∧ (∀ h ∈ HR, ρ h yR = yR) ∧
      (∀ h ∈ HP, ρ h yP = yP) ∧
      ∑ τ : HP ⧸ U, ρ (t τ : Unit) yR = (3 : ℤ) • yP - ρ () yP - ρ ()⁻¹ yP := by
  have hq : ∀ τ : (⊤ : Subgroup Unit) ⧸ (⊤ : Subgroup (⊤ : Subgroup Unit)), τ = 1 := fun τ => by
    induction τ using QuotientGroup.induction_on with
    | H x => exact QuotientGroup.eq.mpr (Subgroup.mem_top _)
  let _ : Fintype ((⊤ : Subgroup Unit) ⧸ (⊤ : Subgroup (⊤ : Subgroup Unit))) :=
    ⟨{1}, fun τ => by simp [hq τ]⟩
  refine ⟨1, ⊤, ⊤, inferInstance, inferInstance, Fintype.ofFinite _, Fintype.ofFinite _,
    fun _ => (), fun _ => (), 1, 1, 1, ⊤, inferInstance, fun _ => 1, 2, 2, 1, 1,
    fun δ => Subsingleton.elim _ _, fun δ => Subsingleton.elim _ _, fun h => by simp,
    fun τ => (hq τ).symm ▸ rfl, le_rfl, fun _ => rfl, by simp, by norm_num, by norm_num,
    fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  have hcard : (Finset.univ : Finset ((⊤ : Subgroup Unit) ⧸ (⊤ : Subgroup (⊤ : Subgroup Unit)))) =
      {1} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun τ _ => hq τ⟩
  rw [hcard, Finset.sum_singleton]
  norm_num

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality in
/-- **Non-vacuity of the hypotheses of `hlift_of_components`**: any Selmer data, any change of
condition, the zero classes and the zero boundary. -/
theorem nonVacuity_components {S : Type} [CommRing S] (D : SelData S) {U' : GCx S}
    (f : GHom U' D.U) (e : S) :
    ∃ (zS : (selCx (restrictData D f)).X 1) (zP : (selCx D).X 1) (b₀ : D.G.X 0) (bu : D.U.X 0)
      (bx : D.L.X (0 - 1)),
      (zS : selT (restrictData D f) 1).1 = e • (zP : selT D 1).1 + D.G.d 0 1 rfl b₀ ∧
      f.f 1 1 rfl (zS : selT (restrictData D f) 1).2.1 =
        e • (zP : selT D 1).2.1 + D.U.d 0 1 rfl bu ∧
      (zS : selT (restrictData D f) 1).2.2 = e • (zP : selT D 1).2.2 +
        (D.res.f 0 (1 - 1) (by omega) b₀ - D.ι.f 0 (1 - 1) (by omega) bu -
          D.L.d (0 - 1) (1 - 1) (by omega) bx) :=
  ⟨((0, 0, 0) : selT (restrictData D f) 1), ((0, 0, 0) : selT D 1), 0, 0, 0,
    by simp; rfl, by simp; exact (f.f 1 1 rfl).map_zero, by simp; rfl⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
