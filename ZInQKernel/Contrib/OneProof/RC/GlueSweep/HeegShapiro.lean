import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.ShapiroInput

/-!
# Lane RC22 (glue sweep), share Heeg: the Shapiro/transfer input, genuine

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 7, tex 3202–3249.

Lane RC10 records as a `PRINT` input (Nekovář, *Selmer complexes*, Astérisque 310, 8.1.1–8.1.6,
pp. 189–194) the interface `ZInQ.Manuscript.RC.HeegnerAlgebra.ShapiroTransferInput`: on classes,
the explicit degree-one transfer (H21) for one chosen section computes Shapiro's map followed by
the coefficient map (H20); and it proves `ShapiroTransferInput.computes_any` (the same for every
section, from the degree-one homotopy of a change of sections).  The `CloudB3RC53` layer
constructs the interface with genuine `H¹ = Z¹/B¹`
(`TwistedTransfer.shapiroTransferInputGenuine`), so the print is not needed.  Here RC10's theorem is
restated for that construction, and its content in plain terms:
the class of the transferred cocycle does not depend on the section.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Heeg

open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)

/-- **The explicit transfer computes Shapiro then (H20), for every section, genuine**,
tex 3202–3249.  Kind: `PROVED`, with no remaining hypothesis beyond the data (a group `G`, a normal
subgroup `H` of finite index (for `G_{H_f} ⊆ G_K`), a module `M` over a commutative ring `A` with
action `ρ` (for `E[2^m] ⊗ A`), a character `θ` of `G ⧸ H`, and a base section `r` used to define
the Shapiro map): for every other section `r'` and every `1`-cocycle `b` of `H`, the class in
`H¹(G, M(θ)) = Z¹/B¹` of the transfer `𝒯_{r'} b` (H21) equals the Shapiro-then-(H20) image of the
class of `b` in `H¹(H, M) = Z¹/B¹` (the class maps `clsG`, `clsH` of the construction are the
quotient maps, `clsG_genuine_apply`, `clsH_genuine_apply`).

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.ShapiroTransferInput.computes_any` (lane RC10, its
`ShapiroTransferInput` hypothesis, `PRINT` Nekovář 8.1.1–8.1.6).  Discharger:
`ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer.shapiroTransferInputGenuine`. -/
theorem computes_any_genuine (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
    (r' : G ⧸ H → G) (hr' : ∀ δ, ((r' δ : G) : G ⧸ H) = δ) (b : cocyclesH H ρ) :
    (shapiroTransferInputGenuine H ρ θ r hr).clsG
        ⟨T1 H ρ θ r' hr' b, T1_mem_cocyclesG H ρ θ r' hr' b b.2⟩ =
      (shapiroTransferInputGenuine H ρ θ r hr).shapiro
        ((shapiroTransferInputGenuine H ρ θ r hr).clsH b) :=
  ShapiroTransferInput.computes_any H (shapiroTransferInputGenuine H ρ θ r hr) r' hr' b

/-- The class map `clsG` of the genuine Shapiro input is the quotient map `Z¹ → Z¹/B¹`
(definitional), `PROVED`. -/
theorem clsG_genuine_apply (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
    (c : cocyclesG H ρ θ) :
    (shapiroTransferInputGenuine H ρ θ r hr).clsG c = (QuotientAddGroup.mk' _ c : H1G H ρ θ) :=
  rfl

/-- The class map `clsH` of the genuine Shapiro input is the quotient map `Z¹ → Z¹/B¹`
(definitional), `PROVED`. -/
theorem clsH_genuine_apply (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
    (b : cocyclesH H ρ) :
    (shapiroTransferInputGenuine H ρ θ r hr).clsH b = (QuotientAddGroup.mk b : H1H H ρ) :=
  rfl

/-- **Independence of the section on classes, genuine**, tex 3245–3249 ("changing sections gives
the integral homotopy in Section 8.1.4"; no averaging factor).  Kind: `PROVED`, no remaining
hypothesis: for any two sections `r, r'` and any `1`-cocycle `b` of `H`, the transfers `𝒯_r b` and
`𝒯_{r'} b` (H21) have the same class in `H¹(G, M(θ)) = Z¹/B¹`.

Consumer: `ZInQ.Manuscript.RC.HeegnerAlgebra.ShapiroTransferInput.computes_any` (lane RC10).
Discharger: `ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer.shapiroTransferInputGenuine`
(its field `computes` for the base section `r`). -/
theorem transfer_class_indep_section (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
    (r' : G ⧸ H → G) (hr' : ∀ δ, ((r' δ : G) : G ⧸ H) = δ) (b : cocyclesH H ρ) :
    (QuotientAddGroup.mk' _ ⟨T1 H ρ θ r' hr' b, T1_mem_cocyclesG H ρ θ r' hr' b b.2⟩ :
        H1G H ρ θ) =
      QuotientAddGroup.mk' _ ⟨T1 H ρ θ r hr b, T1_mem_cocyclesG H ρ θ r hr b b.2⟩ := by
  rw [← clsG_genuine_apply H ρ θ r hr, ← clsG_genuine_apply H ρ θ r hr,
    computes_any_genuine H ρ θ r hr r' hr' b, computes_any_genuine H ρ θ r hr r hr b]

end ZInQ.Manuscript.RC.GlueSweep.Heeg
