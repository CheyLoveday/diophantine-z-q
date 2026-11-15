import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.H.TailZ35
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.OneProof.FHNonvanishing

/-!
# hx-used: the top hypothesis `hX = T5Glue.X0ModuliGalois` replaced by the form its consumers use

Task hx-used (2026-11-15). Report: `docs/research/hx-used.md`; log: `scratch/hx-used/log.md`.

`hX : T5Glue.X0ModuliGalois` (the canonical model of `X₀(N)` over `ℚ`, for every level `N` and every `g ∈ ℚ(X₀(N))`
regular on `ℍ`) enters `ZInQ.OneProof.frozenTarget` only through `T5Glue.shimuraReciprocityModFn_of_printed hCM hX`,
and the consumers of the resulting `Shimura.ShimuraReciprocityModFn` evaluate it only at level `32` and at x0-32's two
coordinate functions `ZInQ.Contrib.TYZGenus.X0.xC`, `ZInQ.Contrib.TYZGenus.X0.yC` (see the report for file and line of every instance). Through
`T5Glue.x0RatStructure_of` the canonical model is applied only at Heegner points `τ_Q`, `τ_{Q'}` of level `32` and the
same discriminant. This file

* states that used form, `X0ModuliGaloisX0_32` (the canonical model of `X₀(32)` for `x` and `y` at Heegner points);
* proves it from `hX` (`x0ModuliGaloisX0_32_of`), so it is never stronger than the field it replaces;
* proves the TYZ side from it and `hCM` (`tyzThm35ReadingA_of_used`), re-proving the consumers of
  `ShimuraReciprocityModFn` with the restricted statement;
* proves `ZInQ.FrozenTarget` with `hX` replaced by the used form (`frozenTarget_of_used`), which is the manual fold.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 20000

namespace X0ModuliUsed

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura

open T5Glue (pp modCoord IsConjModel)

/-! ## §1. The used form of `X0ModuliGalois` -/

/-- **`X0ModuliGalois` for one level `N` and one function `g`, at Heegner points.** The statement of
`T5Glue.X0ModuliGalois` with `N`, `g` fixed, without the hypothesis `IsRatModFn N g`, and with `τ = τ_Q`,
`τ' = τ_{Q'}` for Heegner forms `Q, Q'` of level `N` and the same discriminant `D`: if the point `(E_{τ_Q}, ⟨1/N⟩)`
of `Y₀(N)` is algebraic and `σ ∈ Aut(ℂ)` carries it to `(E_{τ_{Q'}}, ⟨k/N⟩)` (Weierstrass coordinates, as in
`X0ModuliGalois`), then `σ(g(τ_Q)) = g(τ_{Q'})`. -/
def X0ModuliGaloisHeegnerAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (D : ℤ) (Q Q' : HeegnerForm N D) (μ : ℂ),
    (∀ i < N, ∃ a : Qbar, ιC a = modCoord N Q.tauH i) →
    IsConjModel (σ : ℂ →+* ℂ) (pp Q.tauH) (pp Q'.tauH) μ →
    (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
      σ ((pp Q.tauH).weierstrassP (1 / N)) = μ ^ 2 * (pp Q'.tauH).weierstrassP (k / N) ∧
      σ ((pp Q.tauH).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp Q'.tauH).derivWeierstrassP (k / N)) →
    σ (g Q.tauH) = g Q'.tauH

/-- **CANONICAL MODEL OF `X₀(32)` AT HEEGNER POINTS, for x0-32's coordinates `x`, `y`** (the used form of
`T5Glue.X0ModuliGalois`; kind: consequence, GLUE, not a print). `X0ModuliGaloisHeegnerAt 32 g` for `g = ZInQ.Contrib.TYZGenus.X0.xC` and
`g = ZInQ.Contrib.TYZGenus.X0.yC`, the eta quotients `x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2`, `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)` of x0-32
(`ZInQKernel/Contrib/TYZGenus/X0.lean`). Content: `x, y ∈ ℚ(X₀(32))` (proved: `Shimura.isRatModFn_xC_of`,
`Shimura.isRatModFn_yC_of`) and `X₀(32)_ℚ` is the coarse moduli space of pairs `(E, C)` compatibly with `Aut(ℂ)`
(Shimura 1971, §6.7; Deligne–Rapoport, LNM 349, VI–VII; Diamond–Shurman §7.5–7.7; theorem numbers UNVERIFIED),
applied at the CM points `τ_Q` of `X₀(32)`. Implied by `T5Glue.X0ModuliGalois` (`x0ModuliGaloisX0_32_of`). -/
def X0ModuliGaloisX0_32 : Prop :=
  X0ModuliGaloisHeegnerAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ) ∧ X0ModuliGaloisHeegnerAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)

/-- `x` is a rational modular function of level `32` (proved in the kernel). -/
theorem isRatModFn_x : IsRatModFn 32 fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ :=
  isRatModFn_xC_of etaModelInvariant etaCuspGrowth xQExpRational

/-- `y` is a rational modular function of level `32` (proved in the kernel). -/
theorem isRatModFn_y : IsRatModFn 32 fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ :=
  isRatModFn_yC_of etaModelInvariant etaCuspGrowth yQExpRational

/-- `X0ModuliGalois` gives its restriction to one `(N, g)` with `IsRatModFn N g`. -/
theorem x0ModuliGaloisHeegnerAt_of (h : T5Glue.X0ModuliGalois) {N : ℕ} {g : UpperHalfPlane → ℂ}
    (hg : IsRatModFn N g) : X0ModuliGaloisHeegnerAt N g :=
  fun σ _ Q Q' μ h1 h2 h3 => h N (T5Glue.heegnerForm_level_pos Q) g hg σ Q.tauH Q'.tauH μ h1 h2 h3

/-- **The used form is implied by the field it replaces.** -/
theorem x0ModuliGaloisX0_32_of (h : T5Glue.X0ModuliGalois) : X0ModuliGaloisX0_32 :=
  ⟨x0ModuliGaloisHeegnerAt_of h isRatModFn_x, x0ModuliGaloisHeegnerAt_of h isRatModFn_y⟩

/-! ## §2. `X0RatStructure` and `ShimuraReciprocityModFn` for one `(N, g)` -/

/-- `T5Glue.X0RatStructure` for one `(N, g)`, at Heegner points of level `N`. -/
def X0RatStructureAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (D : ℤ) (Q Q' : HeegnerForm N D) (ρ : GalQ) (x : ℕ → Qbar),
    (∀ i < N, ιC (x i) = modCoord N Q.tauH i) → (∀ i < N, ιC (ρ (x i)) = modCoord N Q'.tauH i) →
    ∃ b b' : Qbar, ιC b = g Q.tauH ∧ ιC b' = g Q'.tauH ∧ ρ b = b'

/-- `T5Glue.x0RatStructure_of`, for one `(N, g)` (the same proof). -/
theorem x0RatStructureAt_of {N : ℕ} {g : UpperHalfPlane → ℂ} (hL : X0ModuliGaloisHeegnerAt N g) :
    X0RatStructureAt N g := by
  intro D Q Q' ρ x hx hx'
  have hN := T5Glue.heegnerForm_level_pos Q
  have hD := T5Glue.discNeZero
  obtain ⟨b, hb⟩ := T5Glue.fixedAlgebraic (g Q.tauH) fun σ₀ hσ₀ => by
    have h : ∀ i < N, (σ₀ : ℂ →+* ℂ) (modCoord N Q.tauH i) = modCoord N Q.tauH i := fun i hi => by
      rw [← hx i hi]; exact hσ₀ (x i)
    obtain ⟨μ, hμ, hk⟩ := T5Glue.moduli_transport hD (σ₀ : ℂ →+* ℂ) hN h
    exact hL σ₀ D Q Q μ (fun i hi => ⟨x i, hx i hi⟩) hμ hk
  obtain ⟨σ, hσ⟩ := T5Glue.autExtends ρ
  have h : ∀ i < N, (σ : ℂ →+* ℂ) (modCoord N Q.tauH i) = modCoord N Q'.tauH i := fun i hi => by
    rw [← hx i hi, ← hx' i hi]; exact hσ (x i)
  obtain ⟨μ, hμ, hk⟩ := T5Glue.moduli_transport hD (σ : ℂ →+* ℂ) hN h
  refine ⟨b, ρ b, hb, ?_, rfl⟩
  rw [← hσ, hb]
  exact hL σ D Q Q' μ (fun i hi => ⟨x i, hx i hi⟩) hμ hk

/-- The conclusion of `Shimura.ShimuraReciprocityModFn` for one `(N, g)` (verbatim body,
`ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean:76`, with `N`, `g` fixed). -/
def ShimuraReciprocityModFnAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'

/-- `ShimuraReciprocityModFn` is `ShimuraReciprocityModFnAt` for all `(N, g)` with `IsRatModFn N g`. -/
theorem shimuraReciprocityModFn_iff :
    ShimuraReciprocityModFn ↔ ∀ N g, IsRatModFn N g → ShimuraReciprocityModFnAt N g :=
  Iff.rfl

/-- `T5Glue.shimuraReciprocityModFn_of_split`, for one `(N, g)` (the same proof). -/
theorem shimuraReciprocityModFnAt_of_split {N : ℕ} {g : UpperHalfPlane → ℂ} (hCM : T5Glue.CMModuli)
    (hX : X0RatStructureAt N g) : ShimuraReciprocityModFnAt N g := by
  intro m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  have hN := T5Glue.heegnerForm_level_pos Q
  obtain ⟨x, hx, hx'⟩ := hCM N hN m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  exact hX D Q Q' ρ x hx hx'

/-- `T5Glue.CMModuli` from the printed main theorem of CM (t5-glue and gt-ringclass, proved). -/
theorem cmModuli_of (hCM : T5Glue.ShimuraMainCM) : T5Glue.CMModuli :=
  T5Glue.cmModuli_of_t5 hCM (T5Glue.ideleLatticeScale_of T5Glue.ringClassLattice T5Glue.invertibleColon)

/-- **`ShimuraReciprocityModFn` at level `32` for `x` and `y`**, from `hCM` and the used form. -/
theorem shimuraReciprocityModFnAt_x_y (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisX0_32) :
    ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ) ∧ ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) :=
  ⟨shimuraReciprocityModFnAt_of_split (cmModuli_of hCM) (x0RatStructureAt_of hX.1),
    shimuraReciprocityModFnAt_of_split (cmModuli_of hCM) (x0RatStructureAt_of hX.2)⟩

/-! ## §3. The consumers of `ShimuraReciprocityModFn`, from the level-32 instances -/

/-- `Shimura.shimuraReciprocityPic_of` (ShimuraModFn.lean:122), from the two instances it uses. -/
theorem shimuraReciprocityPic_of_at (hx : ShimuraReciprocityModFnAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ)
    (hy : ShimuraReciprocityModFnAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) : ShimuraReciprocityPic := by
  intro m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  obtain ⟨a, a', ha, ha', haa⟩ := hx m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  obtain ⟨b, b', hb, hb', hbb⟩ := hy m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  rw [heegnerPt_of_alg Q ha hb, heegnerPt_of_alg Q' ha' hb', ← haa, ← hbb]
  by_cases h : curveAbar.toAffine.Nonsingular a b
  · have h' : curveAbar.toAffine.Nonsingular (ρ a) (ρ b) := (nonsingular_iff_gal ρ).2 h
    simp only [h, h', ↓reduceDIte]
    rfl
  · have h' : ¬ curveAbar.toAffine.Nonsingular (ρ a) (ρ b) := fun h'' =>
      h ((nonsingular_iff_gal ρ).1 h'')
    simp only [h, h', ↓reduceDIte, map_zero]

/-- `Shimura.CMValueRingClass` for one `(N, g)`. -/
def CMValueRingClassAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm N D), ∃ a ∈ ringClassFieldD D, ιC a = g Q.tauH

/-- `Shimura.cmValueRingClass_of_modFn` (ShimuraMain.lean:131), for one `(N, g)` (the same proof). -/
theorem cmValueRingClassAt_of {N : ℕ} {g : UpperHalfPlane → ℂ} (hS : ShimuraReciprocityModFnAt N g) :
    CMValueRingClassAt N g := by
  intro D Q
  have hDneg := Q.D_neg
  have h4 := disc_mod_four Q
  obtain ⟨b, hb, hsq⟩ := sqfPart_spec D.natAbs
  have hspec := condD_spec h4 hDneg
  have hDa : (D.natAbs : ℤ) = -D := by omega
  have hm0 : sqfPart D.natAbs ≠ 0 := fun h => by rw [h, mul_zero] at hb; omega
  have hf0 : condD D ≠ 0 := by
    intro h; rw [h] at hspec; split_ifs at hspec <;> simp at hspec <;> omega
  have : NeZero (sqfPart D.natAbs) := ⟨hm0⟩
  have : NeZero (condD D) := ⟨hf0⟩
  set m := sqfPart D.natAbs with hm
  set f := condD D with hf
  have hD : D = discOf m f := by
    unfold discOf
    split_ifs at hspec ⊢ with h3
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
  have hK : ringClassFieldD D = ringClassFieldBar m f := by rw [ringClassFieldD, if_pos hDneg]
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  set J1 : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus := 1 with hJ1
  have hone : (J1 : Ideal (𝓞 (QNeg m))) = ⊤ := by
    rw [hJ1, OneMemClass.coe_one, Ideal.one_eq_top]
  have hmul : LinearMap.mulLeft ℤ (1 : ℂ) = LinearMap.id := by ext; simp
  have hL : idealLat m f J1 * Q.lat = Q.lat.map (LinearMap.mulLeft ℤ 1) := by
    rw [hone, hmul, Submodule.map_id]
    exact idealLat_top_mul (fun o ho => kappa_mul_mem_lat hsq hD Q ho)
  have hLN : idealLat m f J1 * Q.latN = Q.latN.map (LinearMap.mulLeft ℤ 1) := by
    rw [hone, hmul, Submodule.map_id]
    exact idealLat_top_mul (fun o ho => kappa_mul_mem_latN_gen hsq hD Q ho)
  have hρe : ∀ ρ ∈ (ringClassFieldD D).fixingSubgroup,
      ∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J1) x) := by
    intro ρ hρ x
    rw [hJ1, map_one, map_one, AlgEquiv.one_apply]
    have hx : e x ∈ ringClassFieldD D := by
      rw [hK, ← ringClassFieldBar_eq_map m f e]
      exact ⟨x, x.2, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ _ hx
  obtain ⟨a, -, ha, -, -⟩ := hS m f hsq e he J1 1 (hρe 1 (Subgroup.one_mem _)) D hD Q Q 1
    hL hLN
  refine ⟨a, ?_, ha⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (ringClassFieldD D)]
  intro ρ
  obtain ⟨a1, a2, h1, h2, h12⟩ := hS m f hsq e he J1 ρ (hρe ρ.1 ρ.2) D hD Q Q 1 hL hLN
  have e1 : a1 = a := ιCA.injective (h1.trans ha.symm)
  have e2 : a2 = a := ιCA.injective (h2.trans ha.symm)
  rw [← e1]
  conv_rhs => rw [e1, ← e2]
  exact h12

/-- `Shimura.cmFieldOfDefinition_of_cmValue` (ShimuraMain.lean:55), from the two instances it uses. -/
theorem cmFieldOfDefinition_of_at (hx : CMValueRingClassAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ)
    (hy : CMValueRingClassAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) : CMFieldOfDefinition ringClassFieldD := by
  intro D Q
  obtain ⟨a, haH, ha⟩ := hx D Q
  obtain ⟨b, hbH, hb⟩ := hy D Q
  rw [heegnerPt_of_alg Q ha hb]
  split_ifs with h
  · rw [mem_ptsOver_iff]
    exact ⟨haH, hbH⟩
  · exact AddSubgroup.zero_mem _

open WeierstrassCurve.Affine in
/-- `CMBridge.cmAlgebraic_of_cmValue` (Bridge.lean:3102), from the two instances it uses. -/
theorem cmAlgebraic_of_at (hx : CMValueRingClassAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ)
    (hy : CMValueRingClassAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) : CMAlgebraic := by
  classical
  intro D Q
  obtain ⟨a, -, ha⟩ := hx D Q
  obtain ⟨b, -, hb⟩ := hy D Q
  dsimp only at ha hb
  by_cases h : curveAbar.toAffine.Nonsingular a b
  · refine ⟨.some a b h, ?_⟩
    have h' : ZInQ.Contrib.TYZGenus.X0.curveAC.toAffine.Nonsingular (ZInQ.Contrib.TYZGenus.X0.xC Q.tauH) (ZInQ.Contrib.TYZGenus.X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact nonsingular_iff_C.2 h
    simp only [toC, ZInQ.Contrib.TYZGenus.X0.phiC, h', ↓reduceDIte]
    simp only [Point.map_some, Point.some.injEq]
    exact ⟨ha, hb⟩
  · refine ⟨0, ?_⟩
    have h' : ¬ ZInQ.Contrib.TYZGenus.X0.curveAC.toAffine.Nonsingular (ZInQ.Contrib.TYZGenus.X0.xC Q.tauH) (ZInQ.Contrib.TYZGenus.X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact fun h'' => h (nonsingular_iff_C.1 h'')
    simp only [ZInQ.Contrib.TYZGenus.X0.phiC, h', ↓reduceDIte, map_zero]

end X0ModuliUsed

/-! ## §4. The TYZ chain from the level-32 instances -/

namespace X0ModuliUsed

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.CMBridge ZInQ.PropN NumberField
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.RingClassBridge ZInQ.Contrib.TYZGenus.T321

/-- The four CM inputs of the TYZ chain, from `ShimuraReciprocityModFn` at level `32` for `x` and `y`. -/
structure CMInputs : Prop where
  pic : ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityPic
  field : CMFieldOfDefinition ringClassFieldD
  alg : CMAlgebraic

theorem cmInputs_of (hx : ShimuraReciprocityModFnAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ)
    (hy : ShimuraReciprocityModFnAt 32 fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) : CMInputs :=
  ⟨shimuraReciprocityPic_of_at hx hy,
    cmFieldOfDefinition_of_at (cmValueRingClassAt_of hx) (cmValueRingClassAt_of hy),
    cmAlgebraic_of_at (cmValueRingClassAt_of hx) (cmValueRingClassAt_of hy)⟩

/-- `T321.znOverH4_of` (L321.lean:1988), from the field of definition. -/
theorem znOverH4_of_field (hcm : CMFieldOfDefinition ringClassFieldD) : ZnOverH4 := by
  intro n hn hsq
  have h1 := cmFieldTYZ_of_ringClassD hcm n hn hsq
  have hi := iInH4 n hn hsq
  exact sub_mem h1 (iPt_mem hi h1)

/-- `T321.lemma321Five_of_shimuraModFn_betaOneLift hS betaOneLiftExists'` (L321.lean:2123, :2149), from the CM
inputs. -/
theorem lemma321Five_of_cmInputs (h : CMInputs) : Lemma321Five :=
  lemma321Five_of betaOneLiftExists' (znOverH4_of_field h.field)
    (tyzThm36ConjFive_of h.alg)
    (tyzThm36OneFive_of h.pic h.alg wNegatesI)
    (kerFixesZnMod
      (ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of h.pic ZInQ.Contrib.TYZGenus.Shimura.etaModelFricke)
      (tyzThm36OneFive_of h.pic h.alg wNegatesI)
      (znOverH4_of_field h.field))
    betaOnGenus5

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A from the three `𝓛`-leaves, the CM inputs at level `32` and the pinned Theorem 3.3**: the chain
`TYZChain.tyzThm35ReadingA_of_leaves` (TYZChain/Main.lean:56) → L321.lean:2156 → :2137 → Bridge.lean:3134 → :3071,
with every use of `ShimuraReciprocityModFn` replaced by the CM inputs. -/
theorem tyzThm35ReadingA_of_cmInputs (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (h : CMInputs)
    (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → ZInQ.Contrib.TYZGenus.TYZ35.TYZThm33Pinned ℓ) :
    ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura h11
    (ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves h11 h29) h29 h.field
    (ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of h.pic ZInQ.Contrib.TYZGenus.Shimura.etaModelFricke)
    ZInQ.Contrib.TYZChain.package_lemma318Literal_HHprime
    (ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33 h33) (lemma321Five_of_cmInputs h)
    h.pic ZInQ.Contrib.TYZGenus.Shimura.etaModelFricke h.alg

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A with `hX` replaced by its used form**: `TYZChain.tyzThm35ReadingA_of_leaves h11 h29
(T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (tyzThm33Pinned_of_tyzThm33 h33)` with `hX` replaced by
`X0ModuliGaloisX0_32`. -/
theorem tyzThm35ReadingA_of_used (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : T5Glue.ShimuraMainCM) (hXU : X0ModuliGaloisX0_32)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmInputs h11 h29
    (cmInputs_of (shimuraReciprocityModFnAt_x_y hCM hXU).1 (shimuraReciprocityModFnAt_x_y hCM hXU).2)
    (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33)

/-- **Theorem 1.1 with `hX` replaced by its used form `X0ModuliGaloisX0_32`** (the manual fold of `hX`): the term of
`ZInQ.OneProof.frozenTarget` (OneProof/Main.lean:62-72) with `tyzThm35ReadingA_of_leaves h11 h29
(shimuraReciprocityModFn_of_printed hCM hX) (tyzThm33Pinned_of_tyzThm33 h33)` replaced by
`tyzThm35ReadingA_of_used h11 h29 hCM hXU h33`. -/
theorem frozenTarget_of_used
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : ZInQ.Contrib.TYZDecomp.TYZThm11Integral) (h29 : ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hXU : X0ModuliGaloisX0_32)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open29 r t l g)
    (tyzThm35ReadingA_of_used h11 h29 hCM hXU h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end X0ModuliUsed

#print axioms X0ModuliUsed.x0ModuliGaloisX0_32_of
#print axioms X0ModuliUsed.tyzThm35ReadingA_of_used
#print axioms X0ModuliUsed.frozenTarget_of_used
