import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.QuadWiring
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchDuality
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Orthogonality

/-!
# RC53 SwitchInputs: non-vacuity of `DualityFromSelmer`

LESSON 2 for GenuineSteps' model structure `DualityFromSelmer R` (the inputs of the Selmer-complex
lane's `switchAdjunctionFromDuality_proof`, tex L5068–5075): a genuine instance over `ℚ` with
`σ = 1`, for every `ε ≠ 0` and every involution `J` (`J * J = 1`), so that QuadWiring's
`hU_of_dualityFromSelmer` applies.

The data (all complexes have the same module in every degree and zero differential):
* global complex `G = ℚ²`, local complex `L = F ⊕ S = ℚ² × ℚ²`, restriction `a ↦ (a, 0)` (image `F`);
* relaxed local condition `U_rel = L` (`ι = id`), strict local condition `U_str = 0`;
* local cup product `L × L → ℚ`, `x ∪ y = −switchPairing ε 1 J (x, y)`, global cup product `0`,
  target cone `Cone(0 → ℚ)[−1]`, trace the second projection, isotropy homotopy `0`;
* switch quotient `W_rel = L` (identity), coordinates `constCxH1`.

The Selmer duality quasi-isomorphism `hγ` is PROVED through `finiteSelmerDualityNode_proof`: the
local duality map and the global duality map both have acyclic cones (`quasiIso_of_coneCx_acyclic`),
by the perfectness of the switch pairing and of the cross pairing; the coordinate identity `hsw` is a
direct computation (symmetry of the switch pairing at `σ = 1`). A degreewise-isomorphic duality map
is impossible here (it would force `W_rel = 0`), so `hγ` is a genuine quasi-isomorphism statement.

Consumers: the relaxed image is the finite plane (`ndR_U`), `hU_of_dualityFromSelmer` gives that `F`
is self-annihilating for `localPair ε J` (`ndHU`, `ndHU_finPlane`), and the instance fills the
duality/detection fields of `QuasiNonquadStep.ofSelmerDuality` (`ndNonquadStep`) and the
`DualityFromSelmer` argument of `quasiMixedStep_of_genuine` (`ndMixedStep`; `ndJ₀_spec` exhibits an
involution with eigenvectors of both signs). Classification: PROVED (non-vacuity).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

/-- `ℚ²`. -/
abbrev NV2 : Type := Fin 2 → ℚ
/-- `F ⊕ S = ℚ² × ℚ²`. -/
abbrev NV4 : Type := NV2 × NV2

/-- The complex with `V` in every degree and zero differential (reducible, so that its terms are
`V` syntactically up to reducible unfolding). -/
@[reducible] def ndConst (V : Type) [AddCommGroup V] [Module ℚ V] : GCx ℚ where
  X _ := ModuleCat.of ℚ V
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The global complex `ℚ²` (every degree, zero differential). -/
abbrev ndG : GCx ℚ := ndConst NV2
/-- The local complex `F ⊕ S` (every degree, zero differential). -/
abbrev ndL : GCx ℚ := ndConst NV4

/-- Restriction `a ↦ (a, 0)`, onto the finite plane. -/
def ndRes : GHom ndG ndL where
  f _ _ _ := LinearMap.inl ℚ NV2 NV2
  comm _ _ _ _ _ _ _ _ x := by
    rfl

/-- The relaxed Selmer data: `U_rel = L`, `ι = id`. -/
abbrev ndRel : SelData ℚ := ⟨ndG, ndL, ndL, ndRes, idGHom ndL⟩

/-- The strict local condition `0 → U_rel`. -/
def ndStr0 : GHom (ndConst PUnit) ndRel.U := zeroGHom _ _

/-- The relaxed localization with switch quotient `W_rel = L` (identity) and coordinates
`constCxH1`. -/
abbrev ndW : GCx ℚ := constCx (k := ℚ) NV4

/-- The switch quotient map `L → W_rel`, the identity. -/
def ndGR : GHom ndRel.U ndW where
  f _ _ _ := LinearMap.id
  comm _ _ _ _ _ _ _ _ _ := rfl

def ndR : QuasiRelaxedLocalization ℚ := ⟨ndRel, ndW, ndGR, constCxH1 (k := ℚ) NV4⟩

variable (ε : ℚ) (J : Matrix (Fin 2) (Fin 2) ℚ)

/-- The local cup product `x ∪ y = −switchPairing(x, y)` (`σ = 1`). -/
def ndBeta : NV4 →ₗ[ℚ] NV4 →ₗ[ℚ] ℚ := -(switchPairing ε 1 J)

theorem ndBeta_apply (x y : NV4) :
    ndBeta ε J x y = -(crossPairing ε J x.1 y.2 + crossPairing ε J y.1 x.2) := by
  simp [ndBeta, switchPairing, planePairing_apply]

theorem ndL_d (a b : ℤ) (h : a + 1 = b) (x : ndL.X a) : ndL.d a b h x = 0 := rfl
theorem ndG_d (a b : ℤ) (h : a + 1 = b) (x : ndG.X a) : ndG.d a b h x = 0 := rfl

/-- The global target `0`. -/
abbrev ndE : GCx ℚ := ndConst PUnit
/-- The local target `ℚ` (every degree, zero differential). -/
abbrev ndEL : GCx ℚ := ndConst ℚ

theorem ndEL_d (a b : ℤ) (h : a + 1 = b) (x : ndEL.X a) : ndEL.d a b h x = 0 := rfl

/-- The global cup product `0`. -/
def ndCupG : GPair ndG ndG ndE where
  P _ _ _ _ := 0
  leib _ _ _ _ _ _ _ _ _ _ _ _ := rfl

/-- The local cup product. -/
def ndCupL : GPair ndL ndL ndEL where
  P _ _ _ _ := (ndBeta ε J)
  leib _ _ _ _ _ _ _ _ _ _ x y := by
    rw [ndL_d, ndL_d, ndEL_d]
    erw [map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]

/-- The Selmer pairing data between the strict and the relaxed Selmer data. -/
def ndQ : SelPairData (restrictData ndRel ndStr0) ndRel where
  E := ndE
  EL := ndEL
  resE := zeroGHom _ _
  cupG := ndCupG
  cupL := (ndCupL ε J)
  compat _ _ _ _ _ _ _ _ _ _ _ a b := by
    change (0 : ℚ) = (ndBeta ε J) (a, 0) (b, 0)
    rw [ndBeta_apply]
    simp
  hU _ _ _ _ := 0
  isotropy _ _ _ _ _ _ _ _ _ _ u v := by
    have key : ∀ (s : ℤ) (w : NV4), (0 : ℚ) + 0 + s • (0 : ℚ) = (ndBeta ε J) 0 w := by
      intro s w; rw [ndBeta_apply]; simp
    exact key _ _

/-- The trace: the second projection of `Cone(0 → ℚ)[−1]` in degree three. -/
def ndTr : (coneCx (ndQ ε J).resE).X 3 →ₗ[ℚ] ℚ := LinearMap.snd ℚ PUnit ℚ

theorem ndTr_htr : ∀ z, (ndTr ε J) ((coneCx (ndQ ε J).resE).d 2 3 rfl z) = 0 := by
  intro z
  change (0 : ℚ) - 0 = 0
  simp

/-! ### The local duality map -/

/-- The strict Selmer data. -/
abbrev ndStr : SelData ℚ := restrictData ndRel ndStr0

theorem ndBeta_zero_right (x : NV4) : (ndBeta ε J) x 0 = 0 := by
  rw [ndBeta_apply]; simp

/-- The local duality map is the switch pairing: `(u, x) ↦ (v ↦ x ∪ v)`. -/
theorem ndLoc_apply (i j : ℤ) (h : i = j) (c : (locCx ndStr).X i) (v : NV4) :
    asDual ((localDualityMap (ndQ ε J) (ndTr ε J) (ndTr_htr ε J)).f i j h c) v = (ndBeta ε J) c.2 v := by
  have key : ∀ (s : ℤ) (x v : NV4) (a : NV4), (ndBeta ε J) x v + s • (ndBeta ε J) a 0 + 0 = (ndBeta ε J) x v := by
    intro s x v a; rw [ndBeta_zero_right]; simp
  subst h
  dsimp only [localDualityMap, ghomOfInj, locComposite, ghomComp, selmerDualityMap, adjHom, adjFun,
    inclLoc, secU, asDual, LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.compr₂_apply,
    LinearMap.inr_apply, LinearMap.inl_apply, selPair, selCup, LinearMap.mk₂_apply, selCupFun]
  erw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact key (sgn i) c.2 v 0

/-- The switch pairing with `ε = σ = 1`, `J = 1`. -/
abbrev ndSP : LinearMap.BilinForm ℚ NV4 := switchPairing ε 1 J

theorem ndSP_nd (hε : ε ≠ 0) (hJ : J * J = 1) : (ndSP ε J).Nondegenerate :=
  switchPairing_nondegenerate hε one_ne_zero hJ

theorem ndBeta_eq (x v : NV4) : (ndBeta ε J) x v = -((ndSP ε J) x v) := by
  simp [ndBeta]

theorem ndBeta_inj (hε : ε ≠ 0) (hJ : J * J = 1) (x : NV4) (h : ∀ v, (ndBeta ε J) x v = 0) : x = 0 :=
  (ndSP_nd ε J hε hJ).1 x fun v => by have := h v; rw [ndBeta_eq] at this; linarith

theorem ndBeta_surj (hε : ε ≠ 0) (hJ : J * J = 1) (ψ : Module.Dual ℚ NV4) : ∃ x, ∀ v, (ndBeta ε J) x v = ψ v :=
  ⟨-(LinearMap.BilinForm.toDual (ndSP ε J) (ndSP_nd ε J hε hJ)).symm ψ, fun v => by
    rw [ndBeta_eq, map_neg, LinearMap.neg_apply, neg_neg, ← LinearMap.BilinForm.toDual_def (ndSP_nd ε J hε hJ),
      LinearEquiv.apply_symm_apply]⟩

/-- A functional on a term of `U_rel` read as a functional on `F ⊕ S`. -/
def ndDual {n : ℤ} (φ : Module.Dual ℚ (ndRel.U.X n)) : Module.Dual ℚ NV4 where
  toFun v := φ v
  map_add' v w := φ.map_add v w
  map_smul' r v := φ.map_smul r v

theorem ndUd (a b : ℤ) (h : a + 1 = b) (v : ndRel.U.X a) : ndRel.U.d a b h v = 0 := rfl

/-- The local duality map, as a map of graded complexes. -/
abbrev ndLocF : GHom (locCx ndStr) (dualCx ndRel.U 3) := localDualityMap (ndQ ε J) (ndTr ε J) (ndTr_htr ε J)

theorem ndDualD_zero (a b : ℤ) (h : a + 1 = b) (φ : (dualCx ndRel.U 3).X a) :
    (dualCx ndRel.U 3).d a b h φ = 0 := by
  refine dualCx_ext fun v => ?_
  rw [dualCx_d_apply]
  change (-(sgn a)) • asDual φ 0 = 0
  rw [map_zero, smul_zero]

theorem ndCone_snd (a b : ℤ) (h : a + 1 = b) (y : (coneCx (ndLocF ε J)).X a) :
    ((coneCx (ndLocF ε J)).d a b h y).2 = (ndLocF ε J).f a (b - 1) (by omega) y.1 := by
  change (ndLocF ε J).f a (b - 1) (by omega) y.1 -
    (dualCx ndRel.U 3).d (a - 1) (b - 1) (by omega) y.2 = _
  rw [ndDualD_zero, sub_zero]

theorem ndCone_fst2 (a b : ℤ) (h : a + 1 = b) (y : (coneCx (ndLocF ε J)).X a) :
    ((coneCx (ndLocF ε J)).d a b h y).1.2 = 0 := by
  change (negι ndStr).f a (b - 1) (by omega) y.1.1 - ndStr.L.d (a - 1) (b - 1) (by omega) y.1.2 = 0
  have e1 : y.1.1 = 0 := rfl
  have e2 : ndStr.L.d (a - 1) (b - 1) (by omega) y.1.2 = 0 := rfl
  rw [e1, e2, map_zero, sub_zero]

/-- **The local duality map has an acyclic cone** (`U_str = 0`, `U_rel = L`: the switch pairing is
perfect). PROVED. -/
theorem ndLoc_acyclic (hε : ε ≠ 0) (hJ : J * J = 1) : GAcyclic (coneCx (ndLocF ε J)) := by
  intro i j k hij hjk x hx
  have hb2 : (ndLocF ε J).f j (k - 1) (by omega) x.1 = 0 :=
    (ndCone_snd ε J j k hjk x).symm.trans (congrArg Prod.snd hx)
  have hxl : x.1.2 = 0 := by
    apply ndBeta_inj ε J hε hJ
    intro v
    have h1 := ndLoc_apply ε J j (k - 1) (by omega) x.1 v
    rw [hb2] at h1
    exact h1.symm
  obtain ⟨x', hx'⟩ := ndBeta_surj ε J hε hJ (ndDual (asDual x.2))
  refine ⟨((PUnit.unit, x'), 0), ?_⟩
  refine Prod.ext (Prod.ext rfl ((ndCone_fst2 ε J i j hij _).trans hxl.symm)) ?_
  refine (ndCone_snd ε J i j hij _).trans (dualCx_ext fun v => ?_)
  exact (ndLoc_apply ε J i (j - 1) (by omega) _ v).trans (hx' v)

/-! ### The global duality map -/

/-- The global duality map, as a map of graded complexes. -/
abbrev ndGlobF : GHom ndStr.G (dualCx (compactCx ndRel) 3) := globalDualityMap (ndQ ε J) (ndTr ε J) (ndTr_htr ε J)

/-- The global duality map is `a ↦ ((b, y) ↦ (−1)^i res a ∪ y)`. -/
theorem ndGlob_apply (i j : ℤ) (h : i = j) (a : ndStr.G.X i) (c : (compactCx ndRel).X (3 - j)) :
    asDual ((ndGlobF ε J).f i j h a) c = sgn i • (ndBeta ε J) (a, 0) c.2 := by
  have key : ∀ (s : ℤ) (a : NV2) (y z : NV4),
      (ndBeta ε J) 0 z + s • (ndBeta ε J) (a, 0) y + 0 = s • (ndBeta ε J) (a, 0) y := by
    intro s a y z; rw [ndBeta_apply ε J 0]; simp
  subst h
  exact key (sgn i) a c.2 0

/-- A functional on a term of `G'_c = Cone(G → L)[−1]` read as a functional on `ℚ² × (F ⊕ S)`. -/
def ndCD {n : ℤ} (φ : Module.Dual ℚ ((compactCx ndRel).X n)) : Module.Dual ℚ (NV2 × NV4) where
  toFun c := φ c
  map_add' v w := φ.map_add v w
  map_smul' r v := φ.map_smul r v

/-- A functional on `ℚ² × (F ⊕ S)` as a term of `Hom(G'_c, ℚ)[−3]`. -/
def ndCU (n : ℤ) (χ : Module.Dual ℚ (NV2 × NV4)) : (dualCx (compactCx ndRel) 3).X n :=
  show Module.Dual ℚ ((compactCx ndRel).X (3 - n)) from
  { toFun := fun c => χ c
    map_add' := fun v w => χ.map_add v w
    map_smul' := fun r v => χ.map_smul r v }

/-- A term of `G'_c`. -/
def ndCX (n : ℤ) (b : NV2) (y : NV4) : (compactCx ndRel).X n := (b, y)

theorem ndCompD (p q : ℤ) (h : p + 1 = q) (c : (compactCx ndRel).X p)
    (φ : Module.Dual ℚ ((compactCx ndRel).X q)) :
    φ ((compactCx ndRel).d p q h c) = ndCD φ (0, (c.1, 0)) := by
  change φ ((0 : NV2), LinearMap.inl ℚ NV2 NV2 c.1 - (0 : NV4)) = _
  rw [sub_zero]
  rfl

theorem ndGCone_fst (a b : ℤ) (h : a + 1 = b) (y : (coneCx (ndGlobF ε J)).X a) :
    ((coneCx (ndGlobF ε J)).d a b h y).1 = 0 := rfl

theorem ndGCone_apply (a b : ℤ) (h : a + 1 = b) (y : (coneCx (ndGlobF ε J)).X a)
    (c : (compactCx ndRel).X (3 - (b - 1))) :
    asDual (((coneCx (ndGlobF ε J)).d a b h y).2) c =
      sgn a • (ndBeta ε J) (y.1, 0) c.2 + sgn (a - 1) • ndCD (asDual y.2) (0, (c.1, 0)) := by
  change asDual ((ndGlobF ε J).f a (b - 1) (by omega) y.1) c -
    asDual ((dualCx (compactCx ndRel) 3).d (a - 1) (b - 1) (by omega) y.2) c = _
  rw [ndGlob_apply, dualCx_d_apply, ndCompD, neg_smul, sub_neg_eq_add]

theorem ndBeta_fst (a : NV2) (v : NV4) : (ndBeta ε J) (a, 0) v = (ndBeta ε J) (a, 0) (0, v.2) := by
  rw [ndBeta_apply, ndBeta_apply]; simp

theorem ndSgn_cancel (s : ℤ) (hs : s * s = 1) (z : ℚ) : s • s • z = z := by
  rw [smul_smul, hs, one_smul]

theorem ndGlob_key (φ : Module.Dual ℚ (NV2 × NV4)) (s t : ℤ) (hs : s * s = 1) (ht : t * t = 1)
    (h0 : ∀ b : NV2, φ (0, (b, 0)) = 0) (x' : NV4)
    (hx' : ∀ v, (ndBeta ε J) x' v = (s • (φ ∘ₗ (LinearMap.inr ℚ NV2 NV4 ∘ₗ LinearMap.inr ℚ NV2 NV2 ∘ₗ
      LinearMap.snd ℚ NV2 NV2))) v) (c : NV2 × NV4) :
    s • (ndBeta ε J) (x'.1, 0) c.2 + t • (t • φ (c.1, 0)) = φ c := by
  have e1 : (ndBeta ε J) (x'.1, 0) c.2 = (ndBeta ε J) x' (0, c.2.2) := by
    rw [ndBeta_apply, ndBeta_apply]; simp
  have e2 : φ c = φ (c.1, 0) + φ (0, (c.2.1, 0)) + φ (0, (0, c.2.2)) := by
    rw [← map_add, ← map_add]; congr 1; ext <;> simp
  rw [e1, hx', e2, h0, ndSgn_cancel t ht]
  change s • s • φ (0, (0, c.2.2)) + φ (c.1, 0) = φ (c.1, 0) + 0 + φ (0, (0, c.2.2))
  rw [ndSgn_cancel s hs]
  ring

/-- **The global duality map has an acyclic cone** (the cross pairing `ℚ² × ℚ² → ℚ` is perfect).
PROVED. -/
theorem ndGlob_acyclic (hε : ε ≠ 0) (hJ : J * J = 1) : GAcyclic (coneCx (ndGlobF ε J)) := by
  intro i j k hij hjk x hx
  have hcyc : ∀ c : (compactCx ndRel).X (3 - (k - 1)),
      sgn j • (ndBeta ε J) (x.1, 0) c.2 + sgn (j - 1) • ndCD (asDual x.2) (0, (c.1, 0)) = 0 := by
    intro c
    rw [← ndGCone_apply ε J j k hjk x c, hx]
    rfl
  have hx1 : x.1 = 0 := by
    have hb : ((x.1 : NV2), (0 : NV2)) = 0 := by
      apply ndBeta_inj ε J hε hJ
      intro v
      have h := hcyc (ndCX _ 0 (0, v.2))
      change sgn j • (ndBeta ε J) (x.1, 0) (0, v.2) + sgn (j - 1) • ndCD (asDual x.2) (0, (0, 0)) = 0 at h
      rw [Prod.mk_zero_zero, Prod.mk_zero_zero, map_zero, smul_zero, add_zero] at h
      have h' := congrArg (sgn j • ·) h
      simp only [ndSgn_cancel _ (sgn_mul_self j), smul_zero] at h'
      exact (ndBeta_fst ε J _ v).trans h'
    exact congrArg Prod.fst hb
  have h0 : ∀ b : NV2, ndCD (asDual x.2) (0, (b, 0)) = 0 := by
    intro b
    have h := hcyc (ndCX _ b 0)
    change sgn j • (ndBeta ε J) (x.1, 0) 0 + sgn (j - 1) • ndCD (asDual x.2) (0, (b, 0)) = 0 at h
    rw [ndBeta_zero_right, smul_zero, zero_add] at h
    have h' := congrArg (sgn (j - 1) • ·) h
    simp only [ndSgn_cancel _ (sgn_mul_self (j - 1)), smul_zero] at h'
    exact h'
  obtain ⟨x', hx'⟩ := ndBeta_surj ε J hε hJ (sgn i • (ndCD (asDual x.2) ∘ₗ
    (LinearMap.inr ℚ NV2 NV4 ∘ₗ LinearMap.inr ℚ NV2 NV2 ∘ₗ LinearMap.snd ℚ NV2 NV2)))
  refine ⟨(x'.1, ndCU (i - 1) (sgn (i - 1) • (ndCD (asDual x.2) ∘ₗ
    (LinearMap.inl ℚ NV2 NV4 ∘ₗ LinearMap.fst ℚ NV2 NV2 ∘ₗ LinearMap.snd ℚ NV2 NV4)))), ?_⟩
  refine Prod.ext ((ndGCone_fst ε J i j hij _).trans hx1.symm) ?_
  refine dualCx_ext fun c => (ndGCone_apply ε J i j hij _ c).trans ?_
  have hij' : i = j - 1 := by omega
  subst hij'
  exact ndGlob_key ε J (ndCD (asDual x.2)) (sgn (j - 1)) (sgn (j - 1 - 1)) (sgn_mul_self _)
    (sgn_mul_self _) h0 x' hx' (c.1, c.2)

/-! ### The coordinate identity and the instance -/

/-- `constCxH1` reads off the cochain of a cocycle. -/
theorem constCxH1_cls1 {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V]
    (c : LinearMap.ker ((constCx (k := k) V).d 1 2 rfl)) :
    constCxH1 (k := k) V (cls1 (constCx (k := k) V) c) = c.1 := by
  rw [cls1_eq_clsAt, ← iCycles_clsAt (constCx (k := k) V) 1 2 rfl c]
  unfold constCxH1 clsAt
  refine (Iso.toLinearEquiv_apply _ _).trans ?_
  simp only [Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.iCyclesIso_hom]
  congr 1
  rw [← HomologicalComplex.isoHomologyπ_hom (constCx (k := k) V).toCC 0 1 (by simp)
    (constCx_toCC_d V 0 1)]
  exact Iso.hom_inv_id_apply _ _

theorem ndSP_symm (t u : NV4) : (ndSP ε J) u t = (ndSP ε J) t u := by
  simp only [ndSP, switchPairing, planePairing_apply, one_mul]
  ring

theorem ndSw_key (z : ℤ) (t u : NV4) :
    (ndBeta ε J) (-u) t + z • (ndBeta ε J) (LinearMap.inl ℚ NV2 NV2 0) 0 + 0 = (ndSP ε J) t u := by
  rw [ndBeta_zero_right, smul_zero, add_zero, add_zero, ndBeta_eq, map_neg, LinearMap.neg_apply,
    neg_neg, ndSP_symm]

/-- The coefficient pairing `ℚ × ℚ → ℚ`, multiplication. -/
def ndP : PerfectCoefficientPairing ℚ where
  M := ModuleCat.of ℚ ℚ
  M' := ModuleCat.of ℚ ℚ
  pair := LinearMap.mul ℚ ℚ
  perfect_left := by
    refine ⟨fun a b h => ?_, fun φ => ⟨φ 1, LinearMap.ext fun x => ?_⟩⟩
    · have := congrArg (fun φ => φ (1 : ℚ)) h
      simpa using this
    · change φ 1 * x = φ x
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  perfect_right := by
    refine ⟨fun a b h => ?_, fun φ => ⟨φ 1, LinearMap.ext fun x => ?_⟩⟩
    · have := congrArg (fun φ => φ (1 : ℚ)) h
      simpa using this
    · change x * φ 1 = φ x
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- **The Selmer duality quasi-isomorphism** for the small data, through
`finiteSelmerDualityNode_proof` (both inputs PROVED by cone acyclicity). -/
theorem ndHγ (hε : ε ≠ 0) (hJ : J * J = 1) : QuasiIso (GHom.toCC (selmerDualityMap (ndQ ε J) (ndTr ε J) (ndTr_htr ε J))) :=
  finiteSelmerDualityNode_proof ℚ ndStr ndRel (ndQ ε J) (ndTr ε J) (ndTr_htr ε J) ndP
    (Or.inl (Module.injective_of_isSemisimpleRing ℚ ℚ))
    (quasiIso_of_coneCx_acyclic _ (ndGlob_acyclic ε J hε hJ))
    (quasiIso_of_coneCx_acyclic _ (ndLoc_acyclic ε J hε hJ))

/-- **A genuine instance of `DualityFromSelmer`** over `ℚ`, with `ε = σ = 1`, `J = 1`. -/
def ndDuality (hε : ε ≠ 0) (hJ : J * J = 1) : DualityFromSelmer ndR where
  Ustr := ndConst PUnit
  f := ndStr0
  hfg _ _ := rfl
  hf _ _ _ _ := rfl
  hg _ y := ⟨y, rfl⟩
  hex _ _ h := ⟨PUnit.unit, h.symm⟩
  Q := (ndQ ε J)
  tr := (ndTr ε J)
  htr := (ndTr_htr ε J)
  ε := ε
  σ := 1
  J := J
  hε := hε
  hσ := one_ne_zero
  hJ2 := hJ
  hγ := ndHγ ε J hε hJ
  hsw := by
    intro t u s _ _ ct cu hct hcu
    have e1 : constCxH1 (k := ℚ) NV4 (cls1 ndW ct) = t := (constCxH1_cls1 NV4 ct).trans hct
    have e2 : constCxH1 (k := ℚ) NV4 (cls1 ndW cu) = u := (constCxH1_cls1 NV4 cu).trans hcu
    refine (ndSw_key ε J (sgn 2) t u).trans ?_
    change (ndSP ε J) t u = (ndSP ε J) (constCxH1 (k := ℚ) NV4 (cls1 ndW ct)) (constCxH1 (k := ℚ) NV4 (cls1 ndW cu))
    rw [e1, e2]

/-! ### The relaxed image and the consumers -/

/-- **The relaxed image of the instance is the finite plane**: a degree-one cocycle `(a, u, x)` of
`C_rel` has `u = res a = (a, 0)`, and every `(a, 0)` occurs. PROVED. -/
theorem ndR_U : ndR.U = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  ext w
  rw [mem_finPlane]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    obtain ⟨z, rfl⟩ := clsAt_surjective (selCx ndRel) 1 2 rfl v
    have hq := homologyMap_clsAt (quotMap ndRel ndGR) 1 2 rfl z (LinearMap.mem_ker.2 rfl)
    change (constCxH1 (k := ℚ) NV4 ((HomologicalComplex.homologyMap
      (GHom.toCC (quotMap ndRel ndGR)) 1).hom (clsAt (selCx ndRel) 1 2 rfl z))).2 = 0
    rw [hq, ← cls1_eq_clsAt, constCxH1_cls1]
    have hz : (selCx ndRel).d 1 2 rfl z.1 = 0 := z.2
    have h3 := congrArg (fun c : selT ndRel 2 => c.2.2) hz
    change LinearMap.inl ℚ NV2 NV2 z.1.1 - z.1.2.1 - 0 = (0 : NV4) at h3
    rw [sub_zero, sub_eq_zero] at h3
    change (z.1.2.1 : NV4).2 = 0
    rw [← h3]
    rfl
  · intro hw
    let z : LinearMap.ker ((selCx ndRel).d 1 2 rfl) :=
      ⟨show selT ndRel 1 from ((w.1 : NV2), (w : NV4), (0 : NV4)), by
        refine LinearMap.mem_ker.2 (Prod.ext rfl (Prod.ext rfl ?_))
        change LinearMap.inl ℚ NV2 NV2 w.1 - w - 0 = (0 : NV4)
        rw [sub_zero, sub_eq_zero]
        exact Prod.ext rfl hw.symm⟩
    have hq := homologyMap_clsAt (quotMap ndRel ndGR) 1 2 rfl z (LinearMap.mem_ker.2 rfl)
    refine ⟨_, ⟨clsAt (selCx ndRel) 1 2 rfl z, rfl⟩, ?_⟩
    change constCxH1 (k := ℚ) NV4 ((HomologicalComplex.homologyMap
      (GHom.toCC (quotMap ndRel ndGR)) 1).hom (clsAt (selCx ndRel) 1 2 rfl z)) = w
    rw [hq, ← cls1_eq_clsAt, constCxH1_cls1]
    rfl

/-- **QuadWiring's `hU_of_dualityFromSelmer` applied to the instance** (`σ = 1`). PROVED. -/
theorem ndHU (hε : ε ≠ 0) (hJ : J * J = 1) :
    ∀ u, u ∈ ndR.U ↔
      ∀ w ∈ ndR.U, ZInQ.Manuscript.RC.Uniform.QuadraticCase.localPair ε (Matrix.toLin' J) u w = 0 :=
  hU_of_dualityFromSelmer (ndDuality ε J hε hJ) rfl

/-- The conclusion made explicit: the finite plane `F` is self-annihilating for the local pairing
`localPair ε J`. PROVED. -/
theorem ndHU_finPlane (hε : ε ≠ 0) (hJ : J * J = 1) :
    ∀ u, u ∈ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) ↔ ∀ w ∈ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ),
      ZInQ.Manuscript.RC.Uniform.QuadraticCase.localPair ε (Matrix.toLin' J) u w = 0 := by
  rw [← ndR_U]
  exact ndHU ε J hε hJ

section Steps

open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Manuscript.RC.Uniform.QuadraticCase

variable {A F : Type} [CommRing A] [Field F]

/-- **`QuasiNonquadStep.ofSelmerDuality` applied to the instance**: over the relaxed localization
`ndR`, the duality field comes from `ndDuality` and the detection field `F ≤ U` from `ndR_U`; only
the side, strict-dimension and stage-fibre data remain as arguments. PROVED. -/
def ndNonquadStep {ι : A →+* F} {ρ : A →+* ℚ} {S S' : TwoTermStage ι} (hε : ε ≠ 0) (hJ : J * J = 1)
    (SF : QuasiSwitchSide ndR (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)))
    (SS : QuasiSwitchSide ndR (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)))
    (hk0 : finrank ℚ ((selCx SF.Dstr).toCC.homology 1) = finrank ℚ ((selCx SS.Dstr).toCC.homology 1))
    (φ : (selCx SF.Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 ρ S)
    (φ' : (selCx SS.Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 ρ S') : QuasiNonquadStep ρ S S' :=
  QuasiNonquadStep.ofSelmerDuality ndR SF SS hk0 (ndDuality ε J hε hJ) ndR_U.ge φ φ'

/-- The instance transported along an equality of relaxed localizations. -/
def ndTransport (hε : ε ≠ 0) (hJ : J * J = 1) (R : QuasiRelaxedLocalization ℚ) (h : ndR = R) :
    DualityFromSelmer R :=
  h ▸ ndDuality ε J hε hJ

theorem ndTransport_ε (hε : ε ≠ 0) (hJ : J * J = 1) (R : QuasiRelaxedLocalization ℚ) (h : ndR = R) :
    (ndTransport ε J hε hJ R h).ε = ε := by
  subst h; rfl

theorem ndTransport_σ (hε : ε ≠ 0) (hJ : J * J = 1) (R : QuasiRelaxedLocalization ℚ) (h : ndR = R) :
    (ndTransport ε J hε hJ R h).σ = 1 := by
  subst h; rfl

theorem ndTransport_J (hε : ε ≠ 0) (hJ : J * J = 1) (R : QuasiRelaxedLocalization ℚ) (h : ndR = R) :
    (ndTransport ε J hε hJ R h).J = J := by
  subst h; rfl

/-- **`quasiMixedStep_of_genuine` applied to the instance**: for candidate switch data whose relaxed
localization is `ndR`, the `DualityFromSelmer` argument (with `ε`, `σ = 1`, `J`) is supplied by
`ndDuality`. PROVED. -/
theorem ndMixedStep {ι : A →+* F} {ρ : A →+* ℚ} {S : TwoTermStage ι}
    {σS : fiberH1 ρ S →ₗ[ℚ] fiberH1 ρ S} {P : Type} {S' : P → TwoTermStage ι}
    {σS' : ∀ q, fiberH1 ρ (S' q) →ₗ[ℚ] fiberH1 ρ (S' q)} (hε : ε ≠ 0) (hJ : J * J = 1)
    (ep em : Fin 2 → ℚ) (hp : Matrix.toLin' J ep = ep) (hm : Matrix.toLin' J em = -em)
    (he : e₂ ep em ≠ 0) (X : P → QuasiQuadSwitch ℚ (Matrix.toLin' J)) (hR : ∀ q, ndR = (X q).R)
    (φ : ∀ q, (selCx (X q).SF.Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 ρ S)
    (hφ : ∀ q, (φ q).toLinearMap ∘ₗ (X q).σV = σS ∘ₗ (φ q).toLinearMap)
    (φ' : ∀ q, (selCx (X q).SS.Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 ρ (S' q))
    (hφ' : ∀ q, (φ' q).toLinearMap ∘ₗ (X q).σV' = σS' q ∘ₗ (φ' q).toLinearMap)
    (cp cm : fiberH1 ρ S) (hp0 : cp ≠ 0) (hm0 : cm ≠ 0) (hcp : σS cp = cp) (hcm : σS cm = -cm)
    (hex : DetectingPrimeExists σS (fun q => (X q).R.lamQ ∘ₗ H1 (changeMap (X q).R.D (X q).SF.f₁) ∘ₗ
      (φ q).symm.toLinearMap) cp cm) :
    ∃ q, Nonempty (QuasiMixedStep ρ S (S' q) σS (σS' q)) :=
  quasiMixedStep_of_genuine two_ne_zero ε hε (Matrix.toLin' J)
    (by rw [← Matrix.toLin'_mul, hJ, Matrix.toLin'_one]) ep em hp hm he X
    (fun q => ndTransport ε J hε hJ _ (hR q)) (fun q => ndTransport_ε ε J hε hJ _ (hR q))
    (fun q => ndTransport_σ ε J hε hJ _ (hR q)) (fun q => by rw [ndTransport_J])
    φ hφ φ' hφ' cp cm hp0 hm0 hcp hcm hex

/-- The sign involution `J₀ = diag(1, −1)`. -/
def ndJ₀ : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- `J₀` meets the involution and eigenvector hypotheses of the mixed step: `J₀² = 1`,
`J₀ e₁ = e₁`, `J₀ e₂ = −e₂`, `e₂(e₁, e₂) ≠ 0`. PROVED. -/
theorem ndJ₀_spec : ndJ₀ * ndJ₀ = 1 ∧ Matrix.toLin' ndJ₀ ![1, 0] = ![1, 0] ∧
    Matrix.toLin' ndJ₀ ![0, 1] = -![0, 1] ∧ e₂ (![1, 0] : Fin 2 → ℚ) ![0, 1] ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ndJ₀, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i
    fin_cases i <;> simp [ndJ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i
    fin_cases i <;> simp [ndJ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [e₂, Matrix.det_fin_two_of]

end Steps

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
