import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaT
import ZInQKernel.Contrib.OneProof.RC.Uniform.UniformLowerBound
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.BaseZeroBridge

/-!
# Lane RC22 (glue sweep): Lemma `ex:arith-base-zero` over the genuine `A = Λ_(t)` — the two-term
# model from the actual complex, and `ũ₀ ∈ Λ[1/2]` from height-one regularity

Manuscript (`diophantine_zq.tex`, 11/5 version), Lemma `ex:arith-base-zero`, tex 4330–4374:
* tex 4341–4342: "Put `A = Λ_(t)`, with residue field `ℚ₂` and fraction field `F`";
* tex 4350–4360: "Full Selmer corank one gives central dimensions `(1,1)` in degrees one and two and
  zero in every other degree. [...] Over the DVR `A`, a bounded finite free complex decomposes, by
  successive Smith reductions, into free zero-differential summands and two-term disks";
* tex 4369–4373: the corrected coordinate `ũ₀ = ε₀ u_{prim,0}` is regular and zero at the centre;
* tex 5196–5199 (with 5190–5194, 5703–5704): height-one regularity applies at the unknown base,
  so `u_{prim,0}` and `ũ₀` lie in `Λ[1/2]`.

Lane RC20's `ZInQ.Manuscript.RC.Rings.baseZero_node_genuine` is lane RC15's node
`ZInQ.Manuscript.RC.Central.baseZero_node` over the genuine `A = Λ_(t)` (residue map `rhoT`), with
`hρ` and the GLUE `hcoef` discharged; it still takes RC15's two-term model `D` with `hcentral`, and
RC20's replacement of `hcoef`: `ũ₀ = wHalf ∈ Λ[1/2]` (`hwHalf`) with `C.u 0 0 = wHalf(0)` (`hC`).
This file discharges these by theorems of the tree:
* `baseZero_node_genuine_of_complex_rings`: `D` and `hcentral` produced from the actual complex by
  the minimal-complex reduction `ZInQ.Contrib.CloudB3RC53.MinimalComplexes.centralTwoTermModelAt_proof`
  (any residue map killing the maximal ideal, here `rhoT`);
* `baseZero_node_genuine_of_regularity_rings`: `wHalf`, `hwHalf` produced from lane RC16's
  height-one regularity input at the base by RC16's `mem_lambdaHalf_of_regularity`;
* `complex_hyps_nonvacuous_rings`: the complex hypotheses are satisfiable.

Every theorem here is `PROVED` (from the remaining hypotheses named in its docstring).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.MinimalComplexes Matrix

open ZInQ.Manuscript.RC.Uniform (Lambda LambdaHalf lambdaHalfToFrac centralSpecialization
  RegularitySwitchProcess RegularAtPrime mem_lambdaHalf_of_regularity)
open ZInQ.Manuscript.RC.Rings (LambdaT rhoT rhoT_maximalIdeal)

/-- **Lemma `ex:arith-base-zero` (`BaseZero`) over `A = Λ_(t)` from the actual complex** (tex
4330–4374; the minimal-complex reduction and the central dimensions: tex 4350–4360; `A = Λ_(t)`:
tex 4341–4342).

Kind: `PROVED` from the remaining hypotheses. Consumer: lane RC20's
`ZInQ.Manuscript.RC.Rings.baseZero_node_genuine` (RC15's `baseZero_node` over `Λ_(t)` with `hρ` and
`hcoef` discharged). Discharger of its model `D` and of `hcentral` (RC15's ELLIOT input "full Selmer
corank one gives central dimensions `(1,1)`", on the two-term model):
`ZInQ.Contrib.CloudB3RC53.MinimalComplexes.centralTwoTermModelAt_proof`, applied to the residue map
`rhoT` (which kills the maximal ideal, `ZInQ.Manuscript.RC.Rings.rhoT_maximalIdeal`).

Remaining hypotheses: the actual complex `(I, deg, d)` of finite free `Λ_(t)`-modules
(`hg : IsGradedDiff deg d`, `hd : d * d = 0`) with `ρ`-central cohomology of dimension one in
degrees one and two and zero elsewhere (`h0`, `h1`, `h2`; the content of RC15's `hcentral`, now
stated on the actual complex); the print and its application (`hCST`, `hheight`, as in RC15; lane
RC19's `ZInQ.Manuscript.RC.Height.hheight_of_CST` supplies `hheight` for `CSTThm11Split`); and, for
the produced model `D = (δ)` (`m = 0`), RC15's remaining inputs (`z`, `w`, `hz`, `uprim`, `hu`, `κ`,
`Lm`, `h45`, `ε₀`, `utilde0`, `h47`) and RC20's replacement of `hcoef` (`wHalf`, `hwHalf`, `hC`).
These come after the model in the statement because they are stated on it. Non-vacuity of the
complex hypotheses: `complex_hyps_nonvacuous_rings` (the complex `[Λ_(t) --0--> Λ_(t)]` in degrees
one and two). -/
theorem baseZero_node_genuine_of_complex_rings {E : WeierstrassCurve ℚ} {k : ℚ} {b : ℕ}
    (C : CoordData b) (K : Type*) [Field K] [DecidableEq K] [Algebra ℚ K]
    (P : (E.baseChange K).toAffine.Point) (CSTThm11 : Prop) (hCST : CSTThm11)
    (hheight : CSTThm11 → ProductOrderGeTwo E k → IsOfFinAddOrder P)
    {I : Type*} [Fintype I] [DecidableEq I] (deg : I → ℤ) (d : Matrix I I LambdaT)
    (hg : IsGradedDiff deg d) (hd : d * d = 0)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → resDimAt rhoT deg d n = 0) (h1 : resDimAt rhoT deg d 1 = 1)
    (h2 : resDimAt rhoT deg d 2 = 1) :
    ∃ (Pb Qb : Matrix I I LambdaT) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
      Pb * Qb = 1 ∧ Qb * Pb = 1 ∧ IsDegPreserving deg Pb ∧ IsDegPreserving deg Qb ∧
      SplitForm (Pb * d * Qb) kind partner ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
      (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
      let D : Matrix (Fin (0 + 1)) (Fin (0 + 1)) LambdaT := Matrix.of fun _ _ => (Pb * d * Qb) s₂ s₁
      (D.map rhoT).rank = 0 ∧
      ∀ (z w : Fin (0 + 1) → LambdaT), D *ᵥ z = 0 → ∀ uprim : FractionRing Lambda,
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
          (D.map (algebraMap LambdaT (FractionRing Lambda)))
          (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
          (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim →
        ∀ (κ : (E.baseChange K).toAffine.Point →+ (Fin (0 + 1) → ℚ_[2])) (Lm : ℤ),
          (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • κ P →
        ∀ (ε₀ : LambdaT) (utilde0 : FractionRing Lambda),
          utilde0 = algebraMap LambdaT (FractionRing Lambda) ε₀ * uprim →
        ∀ wHalf : LambdaHalf, lambdaHalfToFrac wHalf = utilde0 →
          C.u 0 0 = centralSpecialization wHalf → BaseZero E k C := by
  obtain ⟨Pb, Qb, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, -, -, hs₁, hs₂, hmin, -, hc⟩ :=
    centralTwoTermModelAt_proof LambdaT ℚ_[2] rhoT rhoT_maximalIdeal I deg d hg hd h0 h1 h2
  refine ⟨Pb, Qb, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, hs₁, hs₂, hmin, hc, ?_⟩
  intro z w hz uprim hu κ Lm h45 ε₀ utilde0 h47 wHalf hwHalf hC
  exact ZInQ.Manuscript.RC.Rings.baseZero_node_genuine C K P CSTThm11 hCST hheight _ hc z w hz uprim
    hu κ Lm h45 ε₀ utilde0 h47 wHalf hwHalf hC

/-- **Lemma `ex:arith-base-zero` (`BaseZero`) over `A = Λ_(t)` with `ũ₀ ∈ Λ[1/2]` from height-one
regularity at the base** (tex 4330–4374; regularity at the unknown base: tex 5196–5199, with the
intersection formula 5190–5194 and "Both `ũ_x` and `ũ₀` lie in `Λ[1/2]`", 5703–5704; (4.7) at the
base, `ũ₀ = ε₀ u_{prim,0}` with `ε₀ ∈ Λ`: tex 4369–4373).

Kind: `PROVED` from the remaining hypotheses. Consumer: lane RC20's
`ZInQ.Manuscript.RC.Rings.baseZero_node_genuine`, whose inputs `wHalf`, `hwHalf` (`ũ₀ ∈ Λ[1/2]`,
RC20's replacement of RC15's GLUE `hcoef`) are discharged by lane RC16's
`ZInQ.Manuscript.RC.Uniform.mem_lambdaHalf_of_regularity` (descent along the switching processes at
every height-one prime `𝔭 ≠ (2)` and the intersection formula `Λ[1/2] = ⋂ Λ_𝔭`), applied to
`u_{prim,0}`, and by `ε₀ ∈ Λ`.

Remaining hypotheses: RC15's inputs of `baseZero_node_genuine` (`hCST`, `hheight`, `D`, `hcentral`,
`z`, `w`, `hz`, `uprim`, `hu`, `κ`, `Lm`, `h45`, `utilde0`), with `ε₀` given as the image of
`e₀ ∈ Λ` (the `Λ`-unit of (4.7); only `e₀ ∈ Λ` is used) in `h47`; RC16's regularity input at the base,
`hreg` (the hypothesis `regular` of RC16's `exLimitsUniformLowerBound`, ELLIOT: the switching
processes; the tree's refined form `ZInQ.Manuscript.RC.Wiring.RegularityInputs` gives it through
`RegularityInputs.rc16`); and the top layer's convention `C.u 0 0 = ũ₀(0)` for the (unique)
representative of `ũ₀` in `Λ[1/2]` (`hC`). Non-vacuity: `hreg` and `hC` are satisfiable (e.g.
`uprim = 0`, `utilde0 = 0` and `C.u 0 0 = 0`); `hC` determines `C.u 0 0` because `Λ[1/2] → Frac Λ`
is injective. -/
theorem baseZero_node_genuine_of_regularity_rings {E : WeierstrassCurve ℚ} {k : ℚ} {b : ℕ}
    (C : CoordData b) (K : Type*) [Field K] [DecidableEq K] [Algebra ℚ K]
    (P : (E.baseChange K).toAffine.Point) (CSTThm11 : Prop) (hCST : CSTThm11)
    (hheight : CSTThm11 → ProductOrderGeTwo E k → IsOfFinAddOrder P) {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) LambdaT) (hcentral : (D.map rhoT).rank = m)
    (z w : Fin (m + 1) → LambdaT) (hz : D *ᵥ z = 0) (uprim : FractionRing Lambda)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
      (D.map (algebraMap LambdaT (FractionRing Lambda)))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim)
    (κ : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • κ P)
    (e₀ : Lambda) (utilde0 : FractionRing Lambda)
    (h47 : utilde0 =
      algebraMap LambdaT (FractionRing Lambda) (algebraMap Lambda LambdaT e₀) * uprim)
    (hreg : uprim = 0 ∨ ∀ (Q : Ideal Lambda) [Q.IsPrime], Q.height = 1 → Q ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime Q)) (S₀ : Pr.Stage), Pr.coord S₀ = uprim)
    (hC : ∀ uh : LambdaHalf, lambdaHalfToFrac uh = utilde0 →
      C.u 0 0 = centralSpecialization uh) :
    BaseZero E k C := by
  obtain ⟨uh, huh⟩ := mem_lambdaHalf_of_regularity uprim hreg
  have huh' : lambdaHalfToFrac uh = uprim := huh
  have hw : lambdaHalfToFrac (algebraMap Lambda LambdaHalf e₀ * uh) = utilde0 := by
    rw [map_mul, huh', h47, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply Lambda LambdaT (FractionRing Lambda)]
  exact ZInQ.Manuscript.RC.Rings.baseZero_node_genuine C K P CSTThm11 hCST hheight D hcentral z w
    hz uprim hu κ Lm h45 (algebraMap Lambda LambdaT e₀) utilde0 h47 _ hw (hC _ hw)

/-- **Non-vacuity of the complex hypotheses** of `baseZero_node_genuine_of_complex_rings` (tex
4350–4360). PROVED: the complex `[Λ_(t) --0--> Λ_(t)]` in degrees one and two (`I = Fin 2`,
`deg = (1, 2)`, `d = 0`) is graded, squares to zero, and has `ρ`-central cohomology of dimension one
in degrees one and two and zero elsewhere. -/
theorem complex_hyps_nonvacuous_rings :
    IsGradedDiff (![1, 2] : Fin 2 → ℤ) (0 : Matrix (Fin 2) (Fin 2) LambdaT) ∧
      (0 : Matrix (Fin 2) (Fin 2) LambdaT) * 0 = 0 ∧
      (∀ n, n ≠ 1 → n ≠ 2 → resDimAt rhoT (![1, 2] : Fin 2 → ℤ) 0 n = 0) ∧
      resDimAt rhoT (![1, 2] : Fin 2 → ℤ) (0 : Matrix (Fin 2) (Fin 2) LambdaT) 1 = 1 ∧
      resDimAt rhoT (![1, 2] : Fin 2 → ℤ) (0 : Matrix (Fin 2) (Fin 2) LambdaT) 2 = 1 := by
  have hcols : ∀ n, resColsAt rhoT (![1, 2] : Fin 2 → ℤ) (0 : Matrix (Fin 2) (Fin 2) LambdaT) n = 0 := by
    intro n
    ext i j
    simp [resColsAt]
  have hcard : ∀ n : ℤ, Fintype.card {a : Fin 2 // (![1, 2] : Fin 2 → ℤ) a = n} =
      (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) := by
    intro n
    rw [Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_two]
    by_cases h1 : n = 1
    · subst h1; simp
    · by_cases h2 : n = 2
      · subst h2; simp
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · intro a b h
    simp at h
  · intro n h1 h2
    simp only [resDimAt, hcols, Matrix.rank_zero, hcard]
    simp [h1, h2]
  · simp only [resDimAt, hcols, Matrix.rank_zero, hcard]
    simp
  · simp only [resDimAt, hcols, Matrix.rank_zero, hcard]
    simp

end ZInQ.Manuscript.RC.GlueSweep.Lim
