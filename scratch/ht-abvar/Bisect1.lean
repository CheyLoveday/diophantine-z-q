import ZInQKernel.Contrib.OneProof.DeRhamScholzeT

/-!
# ht-abvar: the field `hodgeTateDecompAbVar` from the manuscript's route (`lem:de-rham-descent`, L10993-10996)

Task ht-abvar (2026-11-17; report `docs/research/ht-abvar.md`).

The H-bundle field `hodgeTateDecompAbVar` (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`, `TailS.lean`) asks for the
Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g` of an abelian variety of dimension `g` over a finite
`F/ℚ_p`. On the current route the multiplicities `(g, g)` come from the Weil pairing of a symmetric isogeny
`A → A^∨`, i.e. from the Picard rows (`hodgeTateDecompAbVar_of_open_k954`, TailZ69).

The manuscript reads the multiplicities off the Hodge numbers instead (diophantine_zq.tex L10993-10994: the two
Hodge numbers of `H¹_dR(A/F)` are `2, 2`, "consequently" the weights are `0,0,−1,−1`), through Scholze's filtered
comparison `D_dR(H¹_ét) ≅ H¹_dR(A/F)` (Cor. 1.8, cited at L736-737 and used in the lemma's first paragraph).
derham-scholze's leaves give de Rham with Hodge jumps in `[0, 1]` but no dimension of a graded piece, so one leaf
is added:

* `HodgeNumberH1AbVar` (LEAF, consequence): `dim_{ℚ_p} Fil¹ D_dR(H¹_ét(A_{F̄}, ℚ_p)) = [F:ℚ_p] · g`.

The rest is proved here: Fontaine's `gr D_dR ≅ D_HT` with dimensions (`hodgeTate01_dims`: `gr¹ D_dR ↪
Hom_{G_F}(V, ℂ_p(1))`, `gr⁰ D_dR ↪ Hom_{G_F}(V, ℂ_p)`, and Tate–Sen, derham-scholze's maps), Milne's
identification to move `Fil¹` from `H¹_ét` to `V_p(A)^∨`, `dim V_p(A) = 2g`, and the `ℂ_p`-dualization from the Hom
form to the tensor form (htdecomp-or's `dualEquiv`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTAbVar

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-! ## §1. The leaf -/

/-- **LEAF (consequence; the manuscript's Hodge numbers through Scholze's filtered comparison).**
diophantine_zq.tex `lem:de-rham-descent`, L10993: "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`" (abelian surface;
no citation, ELLIOT), carried to `D_dR(H¹_ét)` by the filtered isomorphism `D_dR(H¹_ét(A_{F̄}, ℚ_p)) ≅ H¹_dR(A/F)` of
Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with Thms 9.1, 9.3 (cited at L736-737; applied in the lemma's first
paragraph, L10953-10965). For an abelian variety of dimension `g` the Hodge filtration of `H¹_dR(A/F)` has
`Fil¹ = H⁰(A, Ω¹)` of dimension `g` (Hodge–de Rham degeneration; `Ω¹_A` free of rank `g`; standard, e.g. Mumford,
*Abelian varieties*, §4; locator UNVERIFIED), so `dim_F Fil¹ D_dR(H¹_ét) = g`.

Lean form, over the objects of `DeRhamScholze.ScholzeDeRhamAlg`: `H¹_ét(A_{F̄}, ℚ_p) = ℚ_p ⊗ H¹(A_{F̄}, ℤ_p)` with
Mathlib's pro-étale `ℓ`-adic cohomology (`HQ`, `rhoH`), `Fil^j D_dR = D_dR ∩ (t^j B_dR^+ ⊗ W)` (`filD`), dimension
over `ℚ_p` (`= [F:ℚ_p] · dim_F`). Not printed form: `H_dR` is not in Mathlib, so the Hodge number is stated on the
étale side of the comparison. -/
def HodgeNumberH1AbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g

/-! ## §2. Fontaine's `gr D_dR ≅ D_HT` with dimensions (jumps in `[0, 1]`) -/

section Dims

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- **De Rham with Hodge jumps in `[0, 1]` and `dim Fil¹ D_dR = [F:ℚ_p] h` gives the Hom-form Hodge–Tate
decomposition with multiplicities `(dim V − h, h)`.** derham-scholze's `deRhamHodgeTate01_of_fontaineT` with the
dimension count: `Fil¹ D_dR(V^∨) ↪ Hom_{G_F}(V, ℂ_p(1))` by `gr¹` (`Fil² = 0`), so `h ≤ b`; `gr⁰` has kernel in
`Fil¹`, so `dim V ≤ a + h`; Tate–Sen gives `a + b ≤ dim V`. -/
set_option maxHeartbeats 2000000 in
theorem hodgeTate01_dims (hF : FontaineTwistT) (h1 : IsDeRhamFam p (fun σ => ρ.dual σ))
    (h2 : HodgeRange p (fun σ => ρ.dual σ) 1) (h : ℕ)
    (hfil1 : finrank ℚ_[p] (filD p (fun σ => ρ.dual σ) 1) = finrank ℚ_[p] F * h) :
    ∃ (a b : ℕ) (e : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      (∀ (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))) ∧
      a + h = finrank ℚ_[p] V ∧ b = h := by
  obtain ⟨t, ht, hσ⟩ := hF p
  obtain ⟨-, hrank⟩ := h1
  have hT := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  have hA := ZInQ.Contrib.CloudB3W11.axSenTate_proof
  have hD : finrank ℚ_[p] (ddrSpaceOver p ρ) = finrank ℚ_[p] F * finrank ℚ_[p] V := by
    rw [← map_ddrFam_dual ρ, LinearEquiv.finrank_map_eq, hrank, Subspace.dual_finrank_eq]
  have hfil : ∀ j, Submodule.map (tensorDualEquiv p).toLinearMap (filD p (fun σ => ρ.dual σ) j) =
      ddrSpaceOver p ρ ⊓ filH p j := by
    intro j
    rw [filD, Submodule.map_inf _ (tensorDualEquiv p).injective, map_ddrFam_dual, map_filRange_dual]
  obtain ⟨hf0, hf2⟩ := h2
  have h0 : ddrSpaceOver p ρ ≤ filH p 0 := by
    have := hfil 0
    rw [hf0, map_ddrFam_dual] at this
    exact inf_eq_left.mp this.symm
  have h2' : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥ := by
    rw [← hfil 2]
    exact (congrArg _ hf2).trans (Submodule.map_bot _)
  have hF1 : finrank ℚ_[p] (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) =
      finrank ℚ_[p] F * h := by
    rw [← hfil 1, LinearEquiv.finrank_map_eq, hfil1]
  -- the `F'`-dimensions `a`, `b`
  obtain ⟨hfa, -⟩ := fd_htF0 ρ hT hA
  obtain ⟨hfb, -⟩ := fd_htF1 ρ hT hA
  have := hfa
  have := hfb
  haveI := fd_htSpaceOver ρ (0 : ℤ)
  haveI := fd_htSpaceOver ρ (1 : ℤ)
  haveI := fd_hom (p := p) (V := V)
  set a := finrank (fieldF p F) (htF ρ 0)
  set b := finrank (fieldF p F) (htF ρ 1)
  let bx := Module.finBasis (fieldF p F) (htF ρ 0)
  let by' := Module.finBasis (fieldF p F) (htF ρ 1)
  have hz := linIndep_two ρ hT hA (fun i => bx i) (fun i => by' i) bx.linearIndependent by'.linearIndependent
  -- Tate–Sen: `a + b ≤ dim V`
  have hab : a + b ≤ finrank ℚ_[p] V := by
    have := hz.fintype_card_le_finrank
    rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_hom] at this
  -- `Fil¹ D_dR ↪ Hom_{G_F}(V, ℂ_p(1))` by `gr¹`: `h ≤ b`
  have hle1 : (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) ≤ filH p 1 := inf_le_right
  letI : AddCommGroup (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) :=
    Module.addCommMonoidToAddCommGroup ℚ_[p]
  let G1 : (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] htSpaceOver p ρ 1 :=
    LinearMap.codRestrict _ (gr1 ht ∘ₗ Submodule.inclusion hle1)
      (fun φ => gr1_mem ρ ht hσ _ (Submodule.mem_inf.mp φ.2).1)
  have hG1 : Function.Injective G1 := by
    refine (injective_iff_map_eq_zero G1).mpr fun φ hφ => ?_
    have h3 : gr1 ht (Submodule.inclusion hle1 φ) = 0 := congrArg Subtype.val hφ
    have h4 : φ.1 ∈ ddrSpaceOver p ρ ⊓ filH p 2 :=
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp φ.2).1, mem_filH2_of_gr1 ht _ h3⟩
    rw [h2', Submodule.mem_bot] at h4
    exact Subtype.ext h4
  haveI : FiniteDimensional ℚ_[p] (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) :=
    Module.Finite.of_injective G1 hG1
  have hhb : h ≤ b := by
    have := LinearMap.finrank_le_finrank_of_injective hG1
    rw [hF1, finrank_htSpaceOver_eq] at this
    exact Nat.le_of_mul_le_mul_left this Module.finrank_pos
  sorry

end Dims

/-! ## §3. The field -/

/-- `Fil¹` of `D_dR(V_p(A)^∨)` has the dimension of `Fil¹ D_dR(H¹_ét)` (Milne's identification, `milneE`). -/
theorem finrank_filD_dual (hT : T10Etale.T10_TateDuality) (hH : HodgeNumberH1AbVar) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) :
    finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = finrank ℚ_[p] F * g := by
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfree, hfin, -⟩ := DeRhamPrint.tateModuleFree_of_mumford hM F (DeRhamPrint.toKer A) p hp
  obtain ⟨φ, hφ⟩ := hT F (DeRhamPrint.toKer A) p hp
  rw [← map_filD p (milneE p A φ) (milneE_comm p A φ hφ) 1, LinearEquiv.finrank_map_eq]
  exact hH p F A g hg

/-- **The H-bundle field `hodgeTateDecompAbVar` from the manuscript's route**: Scholze's comparison
(`ScholzeDeRhamAlg`), Milne's identification (`T10_TateDuality`) and the Hodge numbers (`HodgeNumberH1AbVar`).
No Picard scheme, no dual abelian variety, no Weil pairing. -/
theorem hodgeTateDecompAbVar_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hH : HodgeNumberH1AbVar) : HodgeTateDecompAbVar := by
  intro p _ F _ _ _ A g hg
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfdV, hdimV⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford hM) hp A g hg
  obtain ⟨h1, h2⟩ := dual_deRham_of_scholze p hS hT hM F A
  obtain ⟨a, b, e, he, hab, hb⟩ :=
    hodgeTate01_dims (A.galRep p) DeRhamScholze.TT.fontaineTwistT h1 h2 g (finrank_filD_dual hT hH p F A g hg)
  rw [hdimV] at hab
  obtain rfl : a = g := by omega
  subst hb
  exact ⟨ZInQ.Contrib.HodgeTateOr.dualEquiv p e, ZInQ.Contrib.HodgeTateOr.dualEquiv_map p (A.galRep p) e he⟩

end

end DeRhamScholze.HTAbVar
