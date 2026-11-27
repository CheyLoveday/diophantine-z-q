import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Transfer

/-!
# Lane RC10 (Heegner algebra), part 10: the Shapiro/transfer input and (4.2) assembled

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 7, tex lines 3202–3280.

* `ShapiroTransferInput` records the printed input (Nekovář, *Selmer complexes*, Sections
  8.1.1–8.1.6): on cohomology, the explicit transfer (H21) computes Shapiro's isomorphism followed
  by the equivariant coefficient map (H20).  It is stated for one chosen section; that the same
  holds for every section ("changing sections gives the integral homotopy in Section 8.1.4") is
  then `PROVED` from the degree-one homotopy `T1_change_section`.
* `eq42_assembled` combines the transported local relations (H19) with the weights of (H21) into
  (4.2): `f(P_{I∪ℓ,m}) = 0`, `s(P_{I∪ℓ,m}) = J f(P_{I,m})` in the common coordinates (`PROVED`).
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Finset

section Shapiro

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The `1`-cocycles of `H` with values in `M` (action `ρ`): `b(xy) = b(x) + x b(y)`. -/
def cocyclesH (ρ : G →* Module.End A M) : AddSubgroup (H → M) where
  carrier := {b | ∀ x y : H, b (x * y) = b x + ρ x (b y)}
  zero_mem' := by intro x y; simp
  add_mem' {b b'} hb hb' x y := by
    simp only [Pi.add_apply, hb x y, hb' x y, map_add]; abel
  neg_mem' {b} hb x y := by
    simp only [Pi.neg_apply, hb x y, map_neg]; abel

/-- The `1`-cocycles of `G` with values in `M(θ)` (action `R = θ ρ`): `c(gk) = c(g) + R(g) c(k)`. -/
def cocyclesG (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) : AddSubgroup (G → M) where
  carrier := {c | ∀ g k : G, c (g * k) = c g + Rtw H ρ θ g (c k)}
  zero_mem' := by intro g k; simp
  add_mem' {c c'} hc hc' g k := by
    simp only [Pi.add_apply, hc g k, hc' g k, map_add]; abel
  neg_mem' {c} hc g k := by
    simp only [Pi.neg_apply, hc g k, map_neg]; abel

omit [Fintype (G ⧸ H)] in
/-- Coboundaries `g ↦ R(g) w - w` are cocycles. -/
theorem coboundary_mem_cocyclesG (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (w : M) :
    (fun g => Rtw H ρ θ g w - w) ∈ cocyclesG H ρ θ := by
  intro g k
  simp only [Rtw_mul, Module.End.mul_apply, map_sub]
  abel

/-- The transfer (H21) of a cocycle is a cocycle (`H21_cocycle`). -/
theorem T1_mem_cocyclesG (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (r : G ⧸ H → G)
    (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (b : H → M) (hb : b ∈ cocyclesH H ρ) :
    T1 H ρ θ r hr b ∈ cocyclesG H ρ θ :=
  fun g k => H21_cocycle H ρ θ r hr b hb g k

/-- `PRINT` (Nekovář, *Selmer complexes*, Astérisque 310, Sections 8.1.1–8.1.6, pp. 189–194,
read and confirmed; Nekovář writes the corestriction on cochains with right cosets `U\G`, the
manuscript with the mirror left-coset convention, as it says), tex 3202–3249.  `G = G_K`,
`H = G_{H_f}` (normal, `Δ_f = G/H`), `M = E[2^m] ⊗ A` with the Tate action `ρ`, `θ` a character of
`Δ_f`.  `clsH` and `clsG` send `1`-cocycles of `H` (coefficients `M`) and of `G` (coefficients
`M(θ)`, action `R = θ ρ`) to their classes in abstract groups `H1H = H¹(H_f, M)` and
`H1G = H¹(K, M(θ))`; `clsG` is additive (on cocycles) and kills coboundaries; `shapiro` is
Shapiro's isomorphism followed by the coefficient map (H20).  The printed input: for one chosen
section `r₀`, the explicit transfer (H21) of a cocycle represents `shapiro` of its class.  The
class maps are defined on cocycles only, so that genuine `H¹ = Z¹/B¹` can be used (this input is
constructed from the explicit Shapiro map in
`ZInQKernel/Contrib/CloudB3RC53/HeegnerCohomology/ShapiroInput.lean`). -/
structure ShapiroTransferInput (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (H1H H1G : Type*)
    [AddCommGroup H1H] [AddCommGroup H1G] where
  clsH : cocyclesH H ρ → H1H
  clsG : cocyclesG H ρ θ →+ H1G
  shapiro : H1H →+ H1G
  clsG_cob : ∀ w : M, clsG ⟨_, coboundary_mem_cocyclesG H ρ θ w⟩ = 0
  r₀ : G ⧸ H → G
  hr₀ : ∀ δ, (QuotientGroup.mk (r₀ δ) : G ⧸ H) = δ
  computes : ∀ b : cocyclesH H ρ,
    clsG ⟨T1 H ρ θ r₀ hr₀ b, T1_mem_cocyclesG H ρ θ r₀ hr₀ b b.2⟩ = shapiro (clsH b)

/-- tex 3247–3249, `PROVED` from `ShapiroTransferInput` and `T1_change_section`: the explicit
transfer computes the same class for every choice of sections (the integral homotopy of
Nekovář 8.1.4 in degree one); no averaging factor occurs in (H21). -/
theorem ShapiroTransferInput.computes_any {ρ : G →* Module.End A M} {θ : G ⧸ H →* Aˣ}
    {H1H H1G : Type*} [AddCommGroup H1H] [AddCommGroup H1G]
    (S : ShapiroTransferInput H ρ θ H1H H1G) (r : G ⧸ H → G)
    (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (b : cocyclesH H ρ) :
    S.clsG ⟨T1 H ρ θ r hr b, T1_mem_cocyclesG H ρ θ r hr b b.2⟩ = S.shapiro (S.clsH b) := by
  obtain ⟨w, hw⟩ := T1_change_section H ρ θ S.r₀ S.hr₀ r hr b b.2
  have : (⟨T1 H ρ θ r hr b, T1_mem_cocyclesG H ρ θ r hr b b.2⟩ : cocyclesG H ρ θ) =
      ⟨T1 H ρ θ S.r₀ S.hr₀ b, T1_mem_cocyclesG H ρ θ S.r₀ S.hr₀ b b.2⟩ +
        ⟨_, coboundary_mem_cocyclesG H ρ θ w⟩ := by
    apply Subtype.ext; funext g; exact hw g
  rw [this, map_add, S.clsG_cob, add_zero, S.computes b]

end Shapiro

/-- (4.2), tex 3268–3277, `PROVED`: at a derivative prime the Mackey terms use the transported
places `r_δ⁻¹ λ`; if each transported new finite coordinate vanishes (H19) and each transported
singular coordinate is `s'_δ = ρ(r_δ)⁻¹ J ρ(r_δ) f'_δ` (H19 in transported coordinates), then the
weighted sums of (H21) satisfy `f(P_{I∪ℓ,m}) = 0` and `s(P_{I∪ℓ,m}) = J f(P_{I,m})`, where
`f(P_{I,m}) = ∑_δ θ(δ) ρ(r_δ) f'_δ`. -/
theorem eq42_assembled {Δ A M : Type*} [Fintype Δ] [CommRing A] [AddCommGroup M] [Module A M]
    (θ : Δ → A) (ρr : Δ → (M ≃ₗ[A] M)) (J : M →ₗ[A] M) (fnew' s' f' : Δ → M)
    (hf : ∀ δ, fnew' δ = 0) (hs : ∀ δ, s' δ = (ρr δ).symm (J (ρr δ (f' δ)))) :
    ∑ δ, θ δ • ρr δ (fnew' δ) = 0 ∧
      ∑ δ, θ δ • ρr δ (s' δ) = J (∑ δ, θ δ • ρr δ (f' δ)) := by
  refine ⟨by simp [hf], ?_⟩
  simp_rw [hs]
  exact weights_42 θ ρr J f'

end ZInQ.Manuscript.RC.HeegnerAlgebra
