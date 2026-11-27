import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.TruncIsotropy
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints

/-!
# Traces on the full and on the truncated cone

Nekovář, *Selmer complexes*, Astérisque 310, 5.4.1 (the global trace `H³_c ≅ R`) and 6.3 (the cup
product on Selmer complexes needs the isotropy null-homotopy only after the canonical truncation
`τ≥2` of the local target); manuscript tex 3455–3467.

For truncated Selmer pairing data `Q` write `C = Cone(E → E_L)[−1]` (the full cone) and
`C' = Cone(E → τ≥2 E_L)[−1]` (the truncated cone). The projection `E_L → τ≥2 E_L` induces a
chain map `C → C'`. In degree three it is `(a, b) ↦ (a, b mod d(E_L¹))`, and in degree four it is
injective, because `τ≥2 E_L` agrees with `E_L` in degree three. Consequently degree-three traces
on `C` killing coboundaries and on `C'` killing coboundaries correspond bijectively
(`trT_trOfTrunc`, `trOfTrunc_trT`), and one of them induces `H³ ≅ R` iff the other does
(`inducesIsoH3_trT_iff`, `inducesIsoH3_trOfTrunc_iff`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs

variable {R : Type} [CommRing R] {D D' : SelData R}

/-- The chain map from the full cone `Cone(E → E_L)[−1]` to the truncated cone
`Cone(E → τ≥2 E_L)[−1]` in degree `n`: `(a, b) ↦ (a, b mod truncSub E_L (n − 1))`, induced by the
projection `E_L → τ≥2 E_L` (Nekovář, *Selmer complexes*, 6.3; tex 3455–3467). -/
def coneProj (Q : SelPairDataTrunc D D') (n : ℤ) :
    (coneCx Q.resE).X n →ₗ[R] (coneCx Q.toSelPairData.resE).X n :=
  LinearMap.prodMap (LinearMap.id : Q.E.X n →ₗ[R] Q.E.X n) (truncSub Q.EL (n - 1)).mkQ

/-- The cone projection on a pair: `(a, b) ↦ (a, b mod truncSub E_L (n − 1))`. -/
theorem coneProj_mk (Q : SelPairDataTrunc D D') (n : ℤ) (a : Q.E.X n) (b : Q.EL.X (n - 1)) :
    coneProj Q n ((a, b) : coneT Q.resE n) =
      ((a, (truncSub Q.EL (n - 1)).mkQ b) : coneT Q.toSelPairData.resE n) :=
  rfl

/-- The cone projection is a chain map `Cone(E → E_L)[−1] → Cone(E → τ≥2 E_L)[−1]`: it commutes
with the cone differentials `d(a, b) = (d a, res a − d b)` (Nekovář, *Selmer complexes*, 6.3). -/
theorem coneProj_d (Q : SelPairDataTrunc D D') (i j : ℤ) (h : i + 1 = j)
    (y : (coneCx Q.resE).X i) :
    coneProj Q j ((coneCx Q.resE).d i j h y) =
      (coneCx Q.toSelPairData.resE).d i j h (coneProj Q i y) := by
  obtain ⟨a, b⟩ := y
  change ((Q.E.d i j h a, (truncSub Q.EL (j - 1)).mkQ
      (Q.resE.f i (j - 1) (by omega) a - Q.EL.d (i - 1) (j - 1) (by omega) b)) :
      coneT Q.toSelPairData.resE j) =
    ((Q.E.d i j h a, (truncSub Q.EL (j - 1)).mkQ (Q.resE.f i (j - 1) (by omega) a) -
      (truncSub Q.EL (j - 1)).mkQ (Q.EL.d (i - 1) (j - 1) (by omega) b)) :
      coneT Q.toSelPairData.resE j)
  rw [map_sub]

/-- The cone projection is surjective in every degree (the quotient map `E_L → τ≥2 E_L` is). -/
theorem coneProj_surjective (Q : SelPairDataTrunc D D') (n : ℤ) :
    Function.Surjective (coneProj Q n) := by
  rintro ⟨a, q⟩
  obtain ⟨b, rfl⟩ := (truncSub Q.EL (n - 1)).mkQ_surjective q
  exact ⟨((a, b) : coneT Q.resE n), rfl⟩

/-- The cone projection is injective in degrees `n` with `n − 1 ≥ 3`, where `τ≥2 E_L` agrees with
`E_L` (`truncSub E_L (n − 1) = ⊥`). -/
theorem coneProj_injective (Q : SelPairDataTrunc D D') {n : ℤ} (hn : 3 ≤ n - 1) :
    Function.Injective (coneProj Q n) := by
  refine (injective_iff_map_eq_zero (coneProj Q n)).mpr ?_
  rintro ⟨a, b⟩ h
  have h1 : a = 0 := congrArg Prod.fst h
  have h2 : (truncSub Q.EL (n - 1)).mkQ b = 0 := congrArg Prod.snd h
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_ge Q.EL hn,
    Submodule.mem_bot] at h2
  subst h1 h2
  rfl

/-- **Degree-three cocycles agree**: `(a, b mod d(E_L¹))` is a cocycle of the truncated cone iff
`(a, b)` is a cocycle of the full cone (since `truncSub E_L (4 − 1) = ⊥`). -/
theorem coneProj3_cocycle_iff (Q : SelPairDataTrunc D D') (z : (coneCx Q.resE).X 3) :
    (coneCx Q.toSelPairData.resE).d 3 4 rfl (coneProj Q 3 z) = 0 ↔
      (coneCx Q.resE).d 3 4 rfl z = 0 := by
  rw [← coneProj_d]
  exact map_eq_zero_iff _ (coneProj_injective Q (by norm_num))

/-- The kernel of the degree-three cone projection consists of coboundaries of the full cone:
`(0, d w) = d(0, −w)` for `w ∈ E_L¹`, as `truncSub E_L (3 − 1) = d(E_L¹)`. -/
theorem exists_d_of_coneProj3_eq_zero (Q : SelPairDataTrunc D D') (x : (coneCx Q.resE).X 3)
    (hx : coneProj Q 3 x = 0) : ∃ y, (coneCx Q.resE).d 2 3 rfl y = x := by
  obtain ⟨a, b⟩ := x
  have ha : a = 0 := congrArg Prod.fst hx
  have hb : (truncSub Q.EL (3 - 1)).mkQ b = 0 := congrArg Prod.snd hx
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq Q.EL (by norm_num)] at hb
  obtain ⟨w, hw⟩ := Submodule.neg_mem _ hb
  subst ha
  refine ⟨((0 : Q.E.X 2), w), ?_⟩
  change ((Q.E.d 2 3 rfl 0, Q.resE.f 2 (3 - 1) (by norm_num) 0 -
      Q.EL.d (2 - 1) (3 - 1) (by norm_num) w) : coneT Q.resE 3) = ((0 : Q.E.X 3), b)
  rw [map_zero, map_zero, zero_sub,
    show Q.EL.d (2 - 1) (3 - 1) (by norm_num) w = -b from hw, neg_neg]

/-- **Degree-three coboundaries agree**: `(a, b mod d(E_L¹))` is a coboundary of the truncated cone
iff `(a, b)` is a coboundary of the full cone (Nekovář, *Selmer complexes*, 6.3; tex 3455–3467). -/
theorem coneProj3_coboundary_iff (Q : SelPairDataTrunc D D') (z : (coneCx Q.resE).X 3) :
    (∃ y, (coneCx Q.toSelPairData.resE).d 2 3 rfl y = coneProj Q 3 z) ↔
      ∃ y, (coneCx Q.resE).d 2 3 rfl y = z := by
  constructor
  · rintro ⟨y', hy'⟩
    obtain ⟨y₀, rfl⟩ := coneProj_surjective Q 2 y'
    rw [← coneProj_d, ← sub_eq_zero, ← map_sub] at hy'
    obtain ⟨y₁, hy₁⟩ := exists_d_of_coneProj3_eq_zero Q _ hy'
    refine ⟨y₀ - y₁, ?_⟩
    rw [map_sub, hy₁, sub_sub_cancel]
  · rintro ⟨y, rfl⟩
    exact ⟨coneProj Q 2 y, (coneProj_d Q 2 3 rfl y).symm⟩

/-- **The degree-three cone projection** `Cone(E → E_L)[−1]³ → Cone(E → τ≥2 E_L)[−1]³`,
`(a, b) ↦ (a, b mod d(E_L¹))` (Nekovář, *Selmer complexes*, 6.3; tex 3455–3467). -/
abbrev coneProj3 (Q : SelPairDataTrunc D D') :
    (coneCx Q.resE).X 3 →ₗ[R] (coneCx Q.toSelPairData.resE).X 3 :=
  coneProj Q 3

/-- **The degree-two cone projection** `Cone(E → E_L)[−1]² → Cone(E → τ≥2 E_L)[−1]²`,
`(a, b) ↦ (a, b mod E_L¹) = (a, 0)` (`τ≥2 E_L` vanishes in degree one). -/
abbrev coneProj2 (Q : SelPairDataTrunc D D') :
    (coneCx Q.resE).X 2 →ₗ[R] (coneCx Q.toSelPairData.resE).X 2 :=
  coneProj Q 2

/-- The cone projections commute with the differential `C² → C³`. -/
theorem coneProj3_d (Q : SelPairDataTrunc D D') (y : (coneCx Q.resE).X 2) :
    coneProj3 Q ((coneCx Q.resE).d 2 3 rfl y) =
      (coneCx Q.toSelPairData.resE).d 2 3 rfl (coneProj2 Q y) :=
  coneProj_d Q 2 3 rfl y

/-- **The trace on the full cone attached to a trace on the truncated cone**: `tr ∘ coneProj3`
(Nekovář, *Selmer complexes*, 5.4.1 and 6.3; tex 3455–3467). -/
def trOfTrunc (Q : SelPairDataTrunc D D') (tr : (coneCx Q.toSelPairData.resE).X 3 →ₗ[R] R) :
    (coneCx Q.resE).X 3 →ₗ[R] R :=
  tr ∘ₗ coneProj3 Q

/-- The pulled-back trace on a pair: `trOfTrunc tr (a, b) = tr (a, b mod d(E_L¹))`. -/
theorem trOfTrunc_apply (Q : SelPairDataTrunc D D')
    (tr : (coneCx Q.toSelPairData.resE).X 3 →ₗ[R] R) (z : (coneCx Q.resE).X 3) :
    trOfTrunc Q tr z = tr (coneProj3 Q z) :=
  rfl

/-- If `tr` kills the coboundaries of the truncated cone, the pulled-back trace kills the
coboundaries of the full cone (Nekovář, *Selmer complexes*, 5.4.1 and 6.3; tex 3455–3467). -/
theorem trOfTrunc_kills (Q : SelPairDataTrunc D D')
    (tr : (coneCx Q.toSelPairData.resE).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((coneCx Q.toSelPairData.resE).d 2 3 rfl z) = 0) :
    ∀ z, trOfTrunc Q tr ((coneCx Q.resE).d 2 3 rfl z) = 0 := fun z => by
  rw [trOfTrunc_apply, coneProj3_d]
  exact htr _

/-- The descended trace `trT` (Nekovář, *Selmer complexes*, 6.3) is computed by the cone
projection: `trT tr0 (coneProj3 z) = tr0 z`. -/
theorem trT_coneProj3 (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[R] R)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) (z : (coneCx Q.resE).X 3) :
    Q.trT tr0 htr0 (coneProj3 Q z) = tr0 z := by
  obtain ⟨a, b⟩ := z
  exact Q.trT_mk tr0 htr0 a b

/-- **Descending the pulled-back trace returns the original trace** (Nekovář, *Selmer complexes*,
5.4.1 and 6.3; tex 3455–3467): for a trace `tr` on the truncated cone killing coboundaries,
`trT (tr ∘ coneProj3) = tr`. -/
theorem trT_trOfTrunc (Q : SelPairDataTrunc D D')
    (tr : (coneCx Q.toSelPairData.resE).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((coneCx Q.toSelPairData.resE).d 2 3 rfl z) = 0) :
    Q.trT (trOfTrunc Q tr) (trOfTrunc_kills Q tr htr) = tr := by
  refine LinearMap.ext fun z' => ?_
  obtain ⟨z, rfl⟩ := coneProj_surjective Q 3 z'
  exact trT_coneProj3 Q _ _ z

/-- **Pulling back the descended trace returns the original trace** (Nekovář, *Selmer complexes*,
5.4.1 and 6.3; tex 3455–3467): for a trace `tr0` on the full cone killing coboundaries,
`trT tr0 ∘ coneProj3 = tr0`. -/
theorem trOfTrunc_trT (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[R] R)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    trOfTrunc Q (Q.trT tr0 htr0) = tr0 :=
  LinearMap.ext fun z => trT_coneProj3 Q tr0 htr0 z

/-- **The pulled-back trace induces `H³ ≅ R` iff the trace does** (Nekovář, *Selmer complexes*,
5.4.1 and 6.3; tex 3455–3467): the cone projection identifies the degree-three cocycles
(`coneProj3_cocycle_iff`) and coboundaries (`coneProj3_coboundary_iff`) of the full and the
truncated cone, and is surjective. No coboundary-killing hypothesis on `tr` is needed. -/
theorem inducesIsoH3_trOfTrunc_iff (Q : SelPairDataTrunc D D')
    (tr : (coneCx Q.toSelPairData.resE).X 3 →ₗ[R] R) :
    InducesIsoH3 (trOfTrunc Q tr) ↔ InducesIsoH3 tr := by
  constructor
  · rintro ⟨h1, z, hz, htz⟩
    refine ⟨fun z' hz' htz' => ?_, coneProj3 Q z, (coneProj3_cocycle_iff Q z).mpr hz, htz⟩
    obtain ⟨z₀, rfl⟩ := coneProj_surjective Q 3 z'
    exact (coneProj3_coboundary_iff Q z₀).mpr
      (h1 z₀ ((coneProj3_cocycle_iff Q z₀).mp hz') htz')
  · rintro ⟨h1, z', hz', htz'⟩
    obtain ⟨z, rfl⟩ := coneProj_surjective Q 3 z'
    refine ⟨fun z₀ hz₀ htz₀ => ?_, z, (coneProj3_cocycle_iff Q z).mp hz', htz'⟩
    exact (coneProj3_coboundary_iff Q z₀).mp
      (h1 (coneProj3 Q z₀) ((coneProj3_cocycle_iff Q z₀).mpr hz₀) htz₀)

/-- **The descended trace induces `H³ ≅ R` iff the original trace does** (Nekovář, *Selmer
complexes*, 5.4.1 and 6.3; tex 3455–3467): for a trace `tr0` on `Cone(E → E_L)[−1]` killing
coboundaries, its descent `trT tr0` to `Cone(E → τ≥2 E_L)[−1]` induces `H³ ≅ R` iff `tr0` does. -/
theorem inducesIsoH3_trT_iff (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[R] R)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    InducesIsoH3 (Q.trT tr0 htr0) ↔ InducesIsoH3 tr0 := by
  rw [← inducesIsoH3_trOfTrunc_iff Q (Q.trT tr0 htr0), trOfTrunc_trT]

end ZInQ.Manuscript.RC.SelmerComplex
