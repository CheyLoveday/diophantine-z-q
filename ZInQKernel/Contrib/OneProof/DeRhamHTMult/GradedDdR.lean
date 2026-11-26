import ZInQKernel.Contrib.OneProof.ModularHTCoeff
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.Periods
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.BdRFiltration

/-! # De Rham representations: graded pieces of `D_dR` give the Hodge–Tate multiplicities

For a finite extension `E/ℚ_p` and a representation `ρ : G_{ℚ_p} → GL_n(E)` on `V = E^n`:

* `filBdR p i = ξ^i B_dR^+` is the de Rham filtration of `B_dR` (`ξ` any generator of `ker θ`;
  equivalently `t^i B_dR^+`, `t = log [ε]`);
* `filDdR p ρ i = D_dR(V) ∩ (Fil^i B_dR ⊗_{ℚ_p} V)`, with `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}`
  (the tree's `ddrU`), and `grDdR p ρ i = Fil^i D_dR / Fil^{i+1} D_dR`.

**Main results** (`V` de Rham in the tree's sense `IsDeRhamU`):

* `finrank_grDdR_eq_finrank_htU`: `dim_{ℚ_p} gr^i D_dR(V) = dim_{ℚ_p} (ℂ_p(i) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`
  (the tree's `htU`);
* `printHTMult_eq_finrank_grDdR`: `dim_{ℚ_p} gr^i D_dR(V) = [E : ℚ_p] · PrintHTMult p E ρ i`, where
  `PrintHTMult p E ρ i = dim_E (V ⊗_{ℚ_p} ℂ_p(i))^{G_{ℚ_p}}` is the print-side Hodge–Tate
  multiplicity of `ModularHTCoeff.lean` (cyclotomic character of weight `−1`);
* `printHasHTWeights_of_grDdR`: graded dimensions `[E : ℚ_p] · S.count i` give
  `PrintHasHTWeights p E ρ S`.

Proof: `gr^i B_dR ≅ ℂ_p(i)` through `t^i y ↦ θ(y)` (`t` a uniformizer with
`σ(t) = χ(σ) t`, `Periods`), so `gr^i D_dR` embeds in `(ℂ_p(i) ⊗ V)^G` (flatness of `V`,
`Graded`); the Tate–Sen bound `Σ_i dim (ℂ_p(i) ⊗ V)^G ≤ dim V` (from Tate's two theorems
over `ℚ_p`, `TateSenCp`) and
`Σ_i dim gr^i D_dR = dim D_dR = dim V` force equality in every degree.

`KatoDeRhamCoeff` states Kato's de Rham form (Astérisque 295 (2004), 9.4 with 14.10.3, geometric
Frobenius) over a finite coefficient field, and `modularHTCoeff_of_kato` derives the tree's
`HTNewAssembly.ModularHTCoeff` from it through `printHasHTWeights_of_grDdR`. This leaf is in
Kato's filtered form, which is stronger than the row it implies.
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open HDec.PkgI4.PanBergerSplit (tensorInv bdrLin htLin vAct ddrU htU IsDeRhamU cpLin homInv
  dualHom)
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## The de Rham filtration of `B_dR` -/

/-- Fontaine's generator `ξ` of `ker θ`, in `B_dR^+`. -/
abbrev xiPlus : BDeRhamPlus 𝓞_ℂ_[p] p := BdrKer.ofPlus 𝓞_ℂ_[p] p (BdrKer.Cp.xi' p)

theorem xiPlus_irreducible : Irreducible (xiPlus p) := by
  haveI := BdrKer.Cp.isDiscreteValuationRing_BDeRhamPlus p
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (BdrKer.Cp.maximalIdeal_BDeRhamPlus p)

theorem toBdR_xiPlus_ne_zero :
    algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (xiPlus p) ≠ 0 := fun h0 =>
  (xiPlus_irreducible p).ne_zero
    ((HDec.PkgI4.BergerBst.toBdR_injective p) (h0.trans (map_zero _).symm))

/-- `ξ` as a unit of the field `B_dR`. -/
def xiUnit : (BdR p)ˣ :=
  Units.mkOfMulEqOne _ _
    (Classical.choose_spec ((BdrKer.Cp.isField_BDeRham p).mul_inv_cancel (toBdR_xiPlus_ne_zero p)))

theorem xiUnit_val : (xiUnit p : BdR p) = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (xiPlus p) :=
  rfl

/-- **`Fil^i B_dR = ξ^i B_dR^+`**, `i ∈ ℤ`. -/
def filBdR (i : ℤ) : Submodule ℚ_[p] (BdR p) := filBdRU p (xiUnit p) i

/-- The filtration does not depend on the uniformizer: `ξ^i B_dR^+ = t^i B_dR^+`. -/
theorem filBdR_eq_tUnit {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) :
    filBdR p = filBdRU p (tUnit p h) := by
  haveI := BdrKer.Cp.isDiscreteValuationRing_BDeRhamPlus p
  funext i
  exact filU_eq_of_associated (qpToPlus p) (hkappa p) (xiUnit_val p) (tUnit_val p h)
    (IsDiscreteValuationRing.associated_of_irreducible _ (xiPlus_irreducible p)
      (logTeich_irreducible p h)) i

/-! ## The filtration of `D_dR` and its graded pieces -/

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`Fil^i D_dR(V) = D_dR(V) ∩ (Fil^i B_dR ⊗_{ℚ_p} V)`**. -/
def filDdR (ρ : GQp p →* GL (Fin n) E) (i : ℤ) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  filD (filBdR p) (bdrLin p) (vAct p ρ) i

/-- **`gr^i D_dR(V) = Fil^i D_dR / Fil^{i+1} D_dR`**. -/
abbrev grDdR (ρ : GQp p →* GL (Fin n) E) (i : ℤ) : Type _ :=
  grD (filBdR p) (bdrLin p) (vAct p ρ) i

theorem filDdR_le (ρ : GQp p →* GL (Fin n) E) (i : ℤ) : filDdR p ρ i ≤ ddrU p ρ := by
  intro x hx σ _
  exact hx.1 σ

theorem invT_eq_tensorInv {B : Type*} [AddCommGroup B] [Module ℚ_[p] B]
    (act : GQp p → B →ₗ[ℚ_[p]] B) (ρ : GQp p →* GL (Fin n) E) :
    invT act (vAct p ρ) = tensorInv p act ⊤ ρ :=
  Submodule.ext fun _ => ⟨fun hx σ _ => hx σ, fun hx σ => hx σ (Subgroup.mem_top σ)⟩

/-! ## Tate's theorems over `ℚ_p` -/

theorem tate_qp (i : ℤ) (hi : i ≠ 0) (x : ℂ_[p])
    (hx : ∀ σ : GQp p, cycPow p σ i • cpAct p σ x = x) : x = 0 :=
  EigenformHTPrinted.tate p ⊥ i hi x fun σ _ => hx σ

theorem axSen_qp (x : ℂ_[p]) (hx : ∀ σ : GQp p, cpAct p σ x = x) :
    ∃ a : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] a := by
  obtain ⟨y, hy⟩ := EigenformHTPrinted.axSen p ⊥ x fun σ _ => hx σ
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp y.2
  refine ⟨a, ?_⟩
  rw [hy, ← ha, PadicComplex.coe_eq, ← IsScalarTower.algebraMap_apply]

theorem htLin_map (ρ : GQp p →* GL (Fin n) E) (i : ℤ) (σ : GQp p)
    (y : ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (htLin p i σ) (vAct p ρ σ) y =
      cycPow p σ i • TensorProduct.map (cpL p σ) (vAct p ρ σ) y := by
  rw [show htLin p i σ = cycPow p σ i • cpL p σ from LinearMap.ext fun _ => rfl,
    TensorProduct.map_smul_left, LinearMap.smul_apply]

theorem htU_twisted (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    ∀ y ∈ invT (htLin p i) (vAct p ρ), ∀ σ,
      cycPow p σ i • TensorProduct.map (cpL p σ) (vAct p ρ σ) y = y := fun y hy σ => by
  rw [← htLin_map]; exact hy σ

/-! ## The main theorem -/

/-- **`dim gr^i D_dR(V) = dim (ℂ_p(i) ⊗ V)^{G_{ℚ_p}}`** for `V` de Rham. -/
theorem finrank_grDdR_eq_finrank_htU (ρ : GQp p →* GL (Fin n) E) (hdR : IsDeRhamU p ρ)
    (i : ℤ) : finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] (htU p ρ i) := by
  obtain ⟨ε, h⟩ := HDec.PkgI4.BmaxOne.exists_isGenEps p
  have hdR' : finrank ℚ_[p] (invT (bdrLin p) (vAct p ρ)) = finrank ℚ_[p] (Fin n → E) := by
    rw [invT_eq_tensorInv]; exact hdR
  have key := finrank_grD_bdR p (logTeich_irreducible p h) (tUnit p h) (tUnit_val p h)
    (fun σ => bdrAct_tOf p h σ) (bdrLin p) (fun _ _ => rfl) (htLin p)
    (fun _ _ _ => rfl) (vAct p ρ)
    (fun j => finiteDimensional_twisted_cp p (vAct p ρ) (fun j => invT (htLin p j) (vAct p ρ))
      (tate_qp p) (axSen_qp p) (htU_twisted p ρ) j)
    (fun J => sum_finrank_twisted_le p (vAct p ρ) (fun j => invT (htLin p j) (vAct p ρ))
      (tate_qp p) (axSen_qp p) (htU_twisted p ρ) J) hdR' i
  have e : htU p ρ i = invT (htLin p i) (vAct p ρ) := (invT_eq_tensorInv p _ ρ).symm
  rw [e, grDdR, filBdR_eq_tUnit p h]
  exact key

/-! ## The print-side multiplicity `PrintHTMult` -/

section PrintSide

variable {F : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] F]

attribute [local instance] HTNewAssembly.smulCommClassE HTNewAssembly.moduleE
  HTNewAssembly.isScalarTowerE

theorem dualHom_dualE (ρ : GQp p →* GL (Fin n) F) : dualHom (HTNewAssembly.dualE ρ) = ρ :=
  MonoidHom.ext fun σ => Units.ext (by
    rw [HDec.PkgI4.PanBergerSplit.dualHom_val, HTNewAssembly.dualE_val, inv_inv,
      Matrix.transpose_transpose])

/-- `dim_{ℚ_p} (ℂ_p(i) ⊗ V)^G = [F : ℚ_p] · PrintHTMult`. -/
theorem finrank_htU_eq (ρ : GQp p →* GL (Fin n) F) (i : ℤ) :
    finrank ℚ_[p] (htU p ρ i) = finrank ℚ_[p] F * HTNewAssembly.PrintHTMult p F ρ i := by
  have h0 : finrank ℚ_[p] (htU p ρ i) = finrank ℚ_[p] (htSpace p (HTNewAssembly.dualE ρ) i) := by
    conv_lhs => rw [← dualHom_dualE p ρ]
    rw [HDec.PkgI4.PanBergerSplit.htU, HDec.PkgI4.PanBergerSplit.finrank_tensorInv_dualHom,
      HDec.PkgI4.PanBergerSplit.homInv_ht]
  have hmap : ((HTNewAssembly.PrintHTSpace p F ρ i).restrictScalars ℚ_[p]).map
      (HTNewAssembly.psi p F (n := n)).toLinearMap = htSpace p (HTNewAssembly.dualE ρ) i := by
    ext φ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (HTNewAssembly.psi_mem_iff p F ρ i t).2 ht
    · intro hφ
      refine ⟨(HTNewAssembly.psi p F).symm φ, ?_, by simp⟩
      show (HTNewAssembly.psi p F).symm φ ∈ HTNewAssembly.PrintHTSpace p F ρ i
      rw [← HTNewAssembly.psi_mem_iff, LinearEquiv.apply_symm_apply]
      exact hφ
  have h1 : finrank ℚ_[p] ((HTNewAssembly.PrintHTSpace p F ρ i).restrictScalars ℚ_[p]) =
      finrank ℚ_[p] (htSpace p (HTNewAssembly.dualE ρ) i) := by
    rw [← hmap, LinearEquiv.finrank_map_eq]
  have h2 : finrank ℚ_[p] F * finrank F (HTNewAssembly.PrintHTSpace p F ρ i) =
      finrank ℚ_[p] ((HTNewAssembly.PrintHTSpace p F ρ i).restrictScalars ℚ_[p]) := by
    have : Module.Free F (HTNewAssembly.PrintHTSpace p F ρ i) :=
      Module.Free.of_divisionRing F (HTNewAssembly.PrintHTSpace p F ρ i)
    exact Module.finrank_mul_finrank ℚ_[p] F (HTNewAssembly.PrintHTSpace p F ρ i)
  rw [h0, ← h1, ← h2]
  rfl

/-- **The identification** (de Rham ⇒ Hodge–Tate on the print's side):
`dim_{ℚ_p} gr^i D_dR(V) = [F : ℚ_p] · dim_F (V ⊗_{ℚ_p} ℂ_p(i))^{G_{ℚ_p}}`. -/
theorem printHTMult_eq_finrank_grDdR (ρ : GQp p →* GL (Fin n) F) (hdR : IsDeRhamU p ρ)
    (i : ℤ) :
    finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] F * HTNewAssembly.PrintHTMult p F ρ i := by
  rw [finrank_grDdR_eq_finrank_htU p ρ hdR, finrank_htU_eq]

/-- The same, as a quotient: `PrintHTMult p F ρ i = dim_{ℚ_p} gr^i D_dR(V) / [F : ℚ_p]`. -/
theorem printHTMult_eq_div (ρ : GQp p →* GL (Fin n) F) (hdR : IsDeRhamU p ρ) (i : ℤ) :
    HTNewAssembly.PrintHTMult p F ρ i = finrank ℚ_[p] (grDdR p ρ i) / finrank ℚ_[p] F := by
  rw [printHTMult_eq_finrank_grDdR p ρ hdR, Nat.mul_div_cancel_left _ Module.finrank_pos]

/-- **Graded dimensions give the Hodge–Tate weights** (cyclotomic character of weight `−1`). -/
theorem printHasHTWeights_of_grDdR (ρ : GQp p →* GL (Fin n) F) (hdR : IsDeRhamU p ρ)
    (S : Multiset ℤ) (hS : ∀ i, finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] F * S.count i) :
    HTNewAssembly.PrintHasHTWeights p F ρ S := fun i =>
  Nat.eq_of_mul_eq_mul_left Module.finrank_pos
    ((printHTMult_eq_finrank_grDdR p ρ hdR i).symm.trans (hS i))

end PrintSide

end

/-! ## Kato's de Rham form and `ModularHTCoeff` -/

/-- **Kato's de Rham form of the modular Galois representation** (K. Kato, *p-adic Hodge theory
and values of zeta functions of modular forms*, Astérisque 295 (2004), 117–290: 9.4, p. 188, with
the representation of 8.3, pp. 181–182, and the Frobenius polynomial recalled in 14.10.3, p. 240;
geometric Frobenius normalization), over a finite coefficient field `E ⊆ ℚ̄_ℓ`: for a newform `f`
of weight `k ≥ 2` there are a finite `E/ℚ_ℓ` inside `ℚ̄_ℓ` and a continuous
`ρ : G_ℚ → GL₂(E)`, unramified at `p ∤ Nℓ`, with geometric Frobenius traces `a_p(f)`, such that
`ρ|_{G_{ℚ_ℓ}}` is de Rham (`IsDeRhamU`) and its de Rham filtration has graded pieces of
`E`-dimension one in degrees `0` and `k − 1` and zero otherwise (in `ℚ_ℓ`-dimensions:
`[E : ℚ_ℓ] · {0, k − 1}.count i`). Reading against the print: locators as in the research notes;
no human reading recorded. -/
def KatoDeRhamCoeff : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρ : GQ →* GL (Fin 2) E), Continuous ρ ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ v : ValuationSubring Qbar, LiesOver v p →
        ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (((ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
      IsDeRhamU ℓ (ρ.comp (decomp ℓ)) ∧
      ∀ i : ℤ, finrank ℚ_[ℓ] (grDdR ℓ (ρ.comp (decomp ℓ)) i) =
        finrank ℚ_[ℓ] E * ({0, k - 1} : Multiset ℤ).count i

/-- **`ModularHTCoeff` from Kato's de Rham form**, through `printHasHTWeights_of_grDdR` (the
geometric disjunct). -/
theorem modularHTCoeff_of_kato (h : KatoDeRhamCoeff) : HTNewAssembly.ModularHTCoeff := by
  intro ℓ _ ιC ιL N _ k f hk
  obtain ⟨E, hE, ρ, hc, hun, hfr, hdR, hgr⟩ := h ℓ ιC ιL N k f hk
  haveI := hE
  exact ⟨E, hE, ρ, hc, hun,
    Or.inr ⟨hfr, printHasHTWeights_of_grDdR ℓ (ρ.comp (decomp ℓ)) hdR _ hgr⟩⟩

end DeRhamHTMult
