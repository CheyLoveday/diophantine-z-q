import ZInQKernel.Contrib.OneProof.HodgeTateDecompOr

/-!
# The Hodge–Tate decomposition: the `H¹_ét` shape implies the Hom shape

Task htdecomp-or (2026-11-17; report `docs/research/htdecomp-or.md`). A third shape in which the Hodge–Tate
decomposition is printed (Faltings, JAMS 1 (1988), for `H¹_ét`): `ℂ_p ⊗_{ℚ_p} H¹_ét(A_{F̄}, ℚ_p) ≅
(ℂ_p ⊗_F H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗_F H⁰(A, Ω¹))`, with `H¹_ét = V_p(A)^∨`. It implies the Hom form
`HodgeTateOr.HodgeTateDecompHom` (`ℂ_p ⊗ V^∨ = Hom_{ℚ_p}(V, ℂ_p)` once `V` is finite-dimensional, which the
`H¹` shape itself forces), hence the or-leaf `HodgeTateOr.HodgeTateDecompOr`. Not part of the leaf: it shows
that the or-leaf is also a consequence of an `H¹`-shaped print.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateOr

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open ZInQ.Contrib.HodgeTateFromPairing
open scoped TensorProduct

noncomputable section

/-- **Hodge–Tate decomposition, `H¹_ét` shape, bases chosen, dimensions not specified.** Faltings, *p-adic
Hodge theory*, J. Amer. Math. Soc. 1 (1988), 255–299 (Hodge–Tate decomposition of `H^n_ét`, `n = 1`), and
for abelian varieties Fontaine 1982; locators UNVERIFIED. Printed shape: `ℂ_p ⊗_{ℚ_p} H¹_ét(A_{F̄}, ℚ_p) ≅
(ℂ_p ⊗_F H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗_F H⁰(A, Ω¹_A))`, `G_F`-equivariant. Lean form: `H¹_ét = V_p(A)^∨ =
Module.Dual ℚ_p (V_p A)` with the contragredient action `φ ↦ φ ∘ ρ(σ⁻¹)`; bases of the two `F`-spaces chosen,
dimensions `a`, `b` unnamed. -/
def HodgeTateDecompH1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] (A.V p) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] (A.V p)),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ⁻¹).dualMap x) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e x).2 k)))

variable (p : ℕ) [Fact p.Prime]

section H1

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `c ⊗ φ ↦ (v ↦ c φ(v))`, `ℂ_p ⊗ V^∨ → Hom_{ℚ_p}(V, ℂ_p)`. -/
def theta : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V →ₗ[ℂ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  LinearMap.liftBaseChange ℂ_[p] (LinearMap.llcomp ℚ_[p] V ℚ_[p] ℂ_[p] (Algebra.linearMap ℚ_[p] ℂ_[p]))

theorem theta_tmul (c : ℂ_[p]) (φ : Module.Dual ℚ_[p] V) (v : V) :
    theta p (c ⊗ₜ φ) v = c * algebraMap ℚ_[p] ℂ_[p] (φ v) := by
  simp [theta, LinearMap.liftBaseChange_tmul]

theorem theta_injective [FiniteDimensional ℚ_[p] V] : Function.Injective (theta p (V := V)) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  rw [Submodule.mem_bot]
  let b := Basis.ofVectorSpace ℚ_[p] V
  let bD := b.dualBasis
  let bDC := bD.baseChange ℂ_[p]
  apply bDC.repr.injective
  ext i
  have hi : ∀ w' : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V, bDC.repr w' i = theta p w' (b i) := by
    intro w'
    induction w' using TensorProduct.inductionOn with
    | tmul c φ =>
      rw [theta_tmul, Basis.baseChange_repr_tmul, Basis.dualBasis_repr]
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, map_add, LinearMap.add_apply]
  rw [hi, hw]
  simp

theorem finrank_theta [FiniteDimensional ℚ_[p] V] :
    finrank ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) = finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) := by
  classical
  let b := Basis.ofVectorSpace ℚ_[p] V
  rw [Module.finrank_baseChange, Subspace.dual_finrank_eq, ← (b.constr ℂ_[p]).finrank_eq,
    Module.finrank_pi, Module.finrank_eq_card_basis b]

/-- `ℂ_p ⊗ V^∨ ≅ Hom_{ℚ_p}(V, ℂ_p)` for finite-dimensional `V`. -/
def thetaEquiv [FiniteDimensional ℚ_[p] V] :
    ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V ≃ₗ[ℂ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  have : FiniteDimensional ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
    LinearEquiv.finiteDimensional ((Basis.ofVectorSpace ℚ_[p] V).constr ℂ_[p])
  LinearEquiv.ofBijective (theta p)
    ⟨theta_injective p,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_theta p)).mp (theta_injective p)⟩

theorem thetaEquiv_apply [FiniteDimensional ℚ_[p] V] (w : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) :
    thetaEquiv p w = theta p w := rfl

/-- `θ` is equivariant: `θ(σ ⊗ ρ^∨(σ)) = σ ∘ θ(·) ∘ ρ(σ)⁻¹`. -/
theorem theta_map (σ : Field.absoluteGaloisGroup F) (w : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) :
    theta p (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ⁻¹).dualMap w) =
      cpLin p (gfToGqp p F σ) ∘ₗ theta p w ∘ₗ ρ σ⁻¹ := by
  induction w using TensorProduct.inductionOn with
  | tmul c φ =>
    ext v
    rw [TensorProduct.map_tmul, theta_tmul, LinearMap.comp_apply, LinearMap.comp_apply, theta_tmul,
      cpLin_apply, cpLin_apply, map_mul, cpAct_algebraMap, LinearMap.dualMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp, LinearMap.comp_add]

/-- The `H¹` shape forces `V` to be finite-dimensional. -/
theorem finiteDimensional_of_h1 {a b : ℕ}
    (e : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :
    FiniteDimensional ℚ_[p] V := by
  classical
  have : Module.Finite ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) := Module.Finite.equiv e.symm
  let bD := Basis.ofVectorSpace ℚ_[p] (Module.Dual ℚ_[p] V)
  have : Finite (Basis.ofVectorSpaceIndex ℚ_[p] (Module.Dual ℚ_[p] V)) :=
    Module.Finite.finite_basis (bD.baseChange ℂ_[p])
  have : Module.Finite ℚ_[p] (Module.Dual ℚ_[p] V) := Module.Finite.of_basis bD
  exact (Module.finite_dual_iff ℚ_[p]).mp this

end H1

/-- **The `H¹` shape implies the Hom shape.** -/
theorem hom_of_h1 (h : HodgeTateDecompH1) : HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨a, b, e, he⟩ := h p F A
  have := finiteDimensional_of_h1 p e
  refine ⟨a, b, (thetaEquiv p).symm.trans e, fun σ f => ?_⟩
  obtain ⟨w, rfl⟩ := (thetaEquiv p).surjective f
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [thetaEquiv_apply, ← theta_map p (A.galRep p), ← thetaEquiv_apply, LinearEquiv.symm_apply_apply, he]

/-- The or-leaf (and so the field) from an `H¹`-shaped print. -/
theorem or_of_h1 (h : HodgeTateDecompH1) : HodgeTateDecompOr := or_of_hom (hom_of_h1 h)

theorem hodgeTateDecompExists_of_h1 (h : HodgeTateDecompH1) : HodgeTateDecompExists :=
  hodgeTateDecompExists_of_hom (hom_of_h1 h)

end

end ZInQ.Contrib.HodgeTateOr
