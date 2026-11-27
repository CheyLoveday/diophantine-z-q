import Mathlib

/-!
# RC53 PairedFunctional: the cup-product pairing on Selmer complexes (the retained duality `PD`)

Proposition `ex:arith-paired-functional` of `diophantine_zq.tex` pairs a class with the transported
orthogonal class by "the retained duality" (tex L3752–3758) and states (tex L3826–3836): "The global
cup-product and trace maps are integral as well. The hypotheses of Selmer duality here are a
perfect coefficient pairing and the actual orthogonal local diagrams with their isotropy homotopies
[Nekovář, Sections 6.2.5–6.2.8 and Theorem 6.3.4]". This file **reproves the construction cited as
Nekovář 6.2.5–6.2.8 (locator UNVERIFIED)**: the cup product on Selmer complexes built from
compatible global and local pairings and an isotropy homotopy of the local conditions, over an
arbitrary commutative ring `S` (no denominators: every map is `S`-linear). It then extracts the
components `PD₁, PD₂, PD₃` of total degree three in exactly the shape of the hypotheses of
`IntegralClosedLift` and `PairedFunctionalWellDefined` (`ConeInverse.lean`).

## Conventions
* `GCx S`: a cochain complex of `S`-modules with relation-indexed differentials
  `d i j : X i → X j` for `i + 1 = j`; `GHom`: a chain map with relation-indexed components
  `f i j : A i → B j` for `i = j`. `GCx.toCC` turns a `GCx` into Mathlib's
  `CochainComplex (ModuleCat S) ℤ` with the same objects and differentials.
  `DEPARTURE` (form only): relation indexing avoids casts between `X (n + 1 - 1)` and `X n`.
* `GPair A B T`: bilinear maps `P i j k : A^i × B^j → T^k` (`i + j = k`) with the Leibniz rule
  `d(x ∪ y) = dx ∪ y + (−1)^i x ∪ dy`.
* Selmer complex of `G --res--> L <--ι-- U` (a cone shifted by `−1`):
  `C^n = G^n ⊕ U^n ⊕ L^{n−1}`, `d(a, u, x) = (da, du, res a − ι u − dx)`.
* Target: `K^n = E^n ⊕ E_L^{n−1}`, `d(e, z) = (de, res_E e − dz)` (the cone of `res_E : E → E_L`
  shifted by `−1`).
* Isotropy homotopy `h : U^i × U'^j → E_L^{i+j−1}`:
  `d h(u, v) + h(du, v) + (−1)^i h(u, dv) = ι u ∪_L ι' v`.
* The pairing (Nekovář's `∪_{res, h}`):
  `(a, u, x) ∪ (b, v, y) = (a ∪_G b, x ∪_L ι' v + (−1)^i res a ∪_L y + h(u, v))`.

## Nodes
* `SelmerCupLeibniz` (tex L3826–3836; PROVED): the formula above is a pairing of complexes
  `C_U × C_{U'} → K` (Leibniz rule), given `res_E (a ∪_G b) = res a ∪_L res' b` and the isotropy
  homotopy.
* `TraceComponentsLeibniz` (tex L3752–3754, L3858–3861; PROVED): for any pairing `C_U × C' → T` and
  any trace `tr : T^3 → S` vanishing on coboundaries, the components `PD_i = tr ∘ P_{i, 3−i}` satisfy
  `PD₂(dw, y) = 1 · PD₁(w, dy)` and `PD₂(w, dy) = (−1) · PD₃(dw, y)`, in the exact form of the
  hypotheses of `IntegralClosedLift` and `PairedFunctionalWellDefined`.
* `SelmerDualityComponents` (GLUE of the two): the Selmer cup product followed by a trace yields
  such components on the Selmer complexes.
* `selmerDuality_nonvacuous` (PROVED): an example in which all hypotheses hold and `PD₁ ≠ 0`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory

universe u

/-- The sign `(−1)^i` for `i : ℤ`. -/
def sgn (i : ℤ) : ℤ := (i.negOnePow : ℤ)

theorem sgn_succ (i : ℤ) : sgn (i + 1) = -sgn i := by
  simp [sgn, Int.negOnePow_succ]

theorem sgn_pred (i : ℤ) : sgn (i - 1) = -sgn i := by
  have := sgn_succ (i - 1)
  rw [sub_add_cancel] at this
  rw [this, neg_neg]

theorem sgn_mul_self (i : ℤ) : sgn i * sgn i = 1 := by
  rw [sgn, ← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem sgn_one : sgn 1 = -1 := by simp [sgn, Int.negOnePow_one]

theorem sgn_two : sgn 2 = 1 := by
  simp [sgn, Int.negOnePow_even 2 even_two]

/-- A cochain complex of `S`-modules with relation-indexed differentials. -/
structure GCx (S : Type u) [CommRing S] where
  /-- The modules. -/
  X : ℤ → ModuleCat.{u} S
  /-- The differentials `d i j`, `i + 1 = j`. -/
  d : ∀ i j : ℤ, i + 1 = j → X i →ₗ[S] X j
  d_d : ∀ (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) (x : X i), d j k hjk (d i j hij x) = 0

variable {S : Type u} [CommRing S]

/-- A chain map with relation-indexed components. -/
structure GHom (A B : GCx S) where
  /-- The components `f i j`, `i = j`. -/
  f : ∀ i j : ℤ, i = j → A.X i →ₗ[S] B.X j
  comm : ∀ (i i₁ j j₁ : ℤ) (hij : i = j) (h₁ : i + 1 = i₁) (h₂ : j + 1 = j₁) (hj : i₁ = j₁)
    (x : A.X i), f i₁ j₁ hj (A.d i i₁ h₁ x) = B.d j j₁ h₂ (f i j hij x)

/-- A pairing of complexes `A × B → T`: `P i j k : A^i × B^j → T^k` (`i + j = k`) with the Leibniz
rule `d(x ∪ y) = dx ∪ y + (−1)^i x ∪ dy`. -/
structure GPair (A B T : GCx S) where
  /-- The bilinear components. -/
  P : ∀ i j k : ℤ, i + j = k → A.X i →ₗ[S] B.X j →ₗ[S] T.X k
  leib : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : A.X i) (y : B.X j),
    T.d k k₁ hk (P i j k h x y) =
      P i₁ j k₁ (by omega) (A.d i i₁ hi x) y + sgn i • P i j₁ k₁ (by omega) x (B.d j j₁ hj y)

/-- Index congruence: a pairing evaluated on index-varying families does not depend on the index
expressions. -/
theorem GPair.congr {A B T : GCx S} (P : GPair A B T) {X Y : Type*} [AddCommGroup X]
    [Module S X] [AddCommGroup Y] [Module S Y] {i j k : ℤ}
    (f : ∀ n, i = n → X →ₗ[S] A.X n) (g : ∀ m, j = m → Y →ₗ[S] B.X m)
    (n n' m m' : ℤ) (hn : i = n) (hn' : i = n') (hm : j = m) (hm' : j = m') (h : n + m = k)
    (h' : n' + m' = k) (x : X) (y : Y) :
    P.P n m k h (f n hn x) (g m hm y) = P.P n' m' k h' (f n' hn' x) (g m' hm' y) := by
  subst hn hn' hm hm'
  rfl

/-! ### Mathlib bridge -/

/-- The Mathlib cochain complex with the same objects and differentials. -/
def GCx.toCC (A : GCx S) : CochainComplex (ModuleCat.{u} S) ℤ where
  X := A.X
  d i j := if h : i + 1 = j then ModuleCat.ofHom (A.d i j h) else 0
  shape i j h := dif_neg h
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    rw [dif_pos hij', dif_pos hjk']
    ext x
    exact A.d_d i j k hij' hjk' x

theorem GCx.toCC_d_hom (A : GCx S) (i j : ℤ) (h : i + 1 = j) (x : A.X i) :
    ((A.toCC).d i j).hom x = A.d i j h x := by
  change (if h' : i + 1 = j then ModuleCat.ofHom (A.d i j h') else 0).hom x = _
  rw [dif_pos h]
  rfl

/-! ### Selmer complexes -/

/-- Local-condition data `G --res--> L <--ι-- U`. -/
structure SelData (S : Type u) [CommRing S] where
  /-- Global complex. -/
  G : GCx S
  /-- Local condition. -/
  U : GCx S
  /-- Full local complex. -/
  L : GCx S
  /-- Restriction. -/
  res : GHom G L
  /-- The local condition map. -/
  ι : GHom U L

/-- The underlying type `G^n × U^n × L^{n−1}`. -/
abbrev selT (D : SelData S) (n : ℤ) : Type u := D.G.X n × D.U.X n × D.L.X (n - 1)

/-- `C^n = G^n ⊕ U^n ⊕ L^{n−1}`. -/
def selX (D : SelData S) (n : ℤ) : ModuleCat.{u} S := ModuleCat.of S (selT D n)

/-- `d(a, u, x) = (da, du, res a − ι u − dx)`. -/
def selD (D : SelData S) (i j : ℤ) (h : i + 1 = j) : selT D i →ₗ[S] selT D j where
  toFun c := (D.G.d i j h c.1, D.U.d i j h c.2.1,
    D.res.f i (j - 1) (by omega) c.1 - D.ι.f i (j - 1) (by omega) c.2.1 -
      D.L.d (i - 1) (j - 1) (by omega) c.2.2)
  map_add' c c' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [map_add, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' r c := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_sub]

/-- The Selmer complex `Cone(G ⊕ U → L)[−1]`. -/
def selCx (D : SelData S) : GCx S where
  X := selX D
  d := selD D
  d_d i j k hij hjk c := by
    obtain ⟨a, u, x⟩ := c
    have e1 := D.res.comm i j (j - 1) (k - 1) (by omega) hij (by omega) (by omega) a
    have e2 := D.ι.comm i j (j - 1) (k - 1) (by omega) hij (by omega) (by omega) u
    have e3 := D.L.d_d (i - 1) (j - 1) (k - 1) (by omega) (by omega) x
    change (D.G.d j k hjk (D.G.d i j hij a), D.U.d j k hjk (D.U.d i j hij u),
      D.res.f j (k - 1) _ (D.G.d i j hij a) - D.ι.f j (k - 1) _ (D.U.d i j hij u) -
        D.L.d (j - 1) (k - 1) _ (D.res.f i (j - 1) _ a - D.ι.f i (j - 1) _ u -
          D.L.d (i - 1) (j - 1) _ x)) = 0
    rw [D.G.d_d, D.U.d_d, e1, e2, map_sub, map_sub, e3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-- The underlying type `E^n × E_L^{n−1}`. -/
abbrev coneT {E EL : GCx S} (_f : GHom E EL) (n : ℤ) : Type u := E.X n × EL.X (n - 1)

/-- `K^n = E^n ⊕ E_L^{n−1}`. -/
def coneX {E EL : GCx S} (f : GHom E EL) (n : ℤ) : ModuleCat.{u} S := ModuleCat.of S (coneT f n)

/-- `d(e, z) = (de, f e − dz)`. -/
def coneD {E EL : GCx S} (f : GHom E EL) (i j : ℤ) (h : i + 1 = j) :
    coneT f i →ₗ[S] coneT f j where
  toFun c := (E.d i j h c.1, f.f i (j - 1) (by omega) c.1 - EL.d (i - 1) (j - 1) (by omega) c.2)
  map_add' c c' := by
    refine Prod.ext ?_ ?_ <;> simp only [map_add, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' r c := by
    refine Prod.ext ?_ ?_ <;>
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_sub]

/-- The target complex `Cone(E → E_L)[−1]`. -/
def coneCx {E EL : GCx S} (f : GHom E EL) : GCx S where
  X := coneX f
  d := coneD f
  d_d i j k hij hjk c := by
    obtain ⟨e, z⟩ := c
    have e1 := f.comm i j (j - 1) (k - 1) (by omega) hij (by omega) (by omega) e
    have e3 := EL.d_d (i - 1) (j - 1) (k - 1) (by omega) (by omega) z
    change (E.d j k hjk (E.d i j hij e),
      f.f j (k - 1) _ (E.d i j hij e) - EL.d (j - 1) (k - 1) _ (f.f i (j - 1) _ e -
        EL.d (i - 1) (j - 1) _ z)) = 0
    rw [E.d_d, e1, map_sub, e3]
    refine Prod.ext ?_ ?_ <;> simp

/-- The data of Nekovář's cup product on Selmer complexes: compatible pairings
`∪_G : G × G' → E`, `∪_L : L × L' → E_L`, `res_E : E → E_L` with
`res_E(a ∪_G b) = res a ∪_L res' b`, and an isotropy homotopy `h` of the local conditions. -/
structure SelPairData (D D' : SelData S) where
  /-- Global target. -/
  E : GCx S
  /-- Local target. -/
  EL : GCx S
  /-- Restriction on the target. -/
  resE : GHom E EL
  /-- Global cup product. -/
  cupG : GPair D.G D'.G E
  /-- Local cup product. -/
  cupL : GPair D.L D'.L EL
  compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j')
    (hk : k = k') (a : D.G.X i) (b : D'.G.X j),
    resE.f k k' hk (cupG.P i j k h a b) =
      cupL.P i' j' k' h' (D.res.f i i' hi a) (D'.res.f j j' hj b)
  /-- The isotropy homotopy, of degree `−1`. -/
  hU : ∀ i j k : ℤ, i + j = k + 1 → D.U.X i →ₗ[S] D'.U.X j →ₗ[S] EL.X k
  isotropy : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (u : D.U.X i) (v : D'.U.X j),
    EL.d k k₁ hk (hU i j k h u v) + hU i₁ j k₁ (by omega) (D.U.d i i₁ hi u) v +
        sgn i • hU i j₁ k₁ (by omega) u (D'.U.d j j₁ hj v) =
      cupL.P i j k₁ (by omega) (D.ι.f i i rfl u) (D'.ι.f j j rfl v)

variable {D D' : SelData S}

/-- The underlying function of the Selmer cup product. -/
def selCupFun (Q : SelPairData D D') (i j k : ℤ) (h : i + j = k) (c : selT D i)
    (c' : selT D' j) : coneT Q.resE k :=
  (Q.cupG.P i j k h c.1 c'.1,
    Q.cupL.P (i - 1) j (k - 1) (by omega) c.2.2 (D'.ι.f j j rfl c'.2.1) +
      sgn i • Q.cupL.P i (j - 1) (k - 1) (by omega) (D.res.f i i rfl c.1) c'.2.2 +
      Q.hU i j (k - 1) (by omega) c.2.1 c'.2.1)

/-- The Selmer cup product `(a, u, x) ∪ (b, v, y) = (a ∪ b, x ∪ ι' v + (−1)^i res a ∪ y + h(u, v))`,
as bilinear maps. -/
def selCup (Q : SelPairData D D') (i j k : ℤ) (h : i + j = k) :
    selT D i →ₗ[S] selT D' j →ₗ[S] coneT Q.resE k :=
  LinearMap.mk₂ S (selCupFun Q i j k h)
    (fun c₁ c₂ c' => by
      refine Prod.ext ?_ ?_ <;> simp only [selCupFun, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply,
        smul_add] <;> abel)
    (fun r c c' => by
      refine Prod.ext ?_ ?_ <;> simp only [selCupFun, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
        smul_add, smul_comm (sgn i) r])
    (fun c c₁ c₂ => by
      refine Prod.ext ?_ ?_ <;> simp only [selCupFun, Prod.fst_add, Prod.snd_add, map_add, smul_add] <;> abel)
    (fun r c c' => by
      refine Prod.ext ?_ ?_ <;> simp only [selCupFun, Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
        smul_comm (sgn i) r])

/-- **The cup product on Selmer complexes satisfies the Leibniz rule** (tex L3826–3836; reproves
the construction cited as Nekovář 6.2.5–6.2.8, locator UNVERIFIED): for local-condition data
`D, D'` and compatible pairings with an isotropy homotopy, `selCup` is a pairing of complexes
`C(D) × C(D') → Cone(E → E_L)[−1]` over `S`. Classification: PROVED. -/
def SelmerCupLeibniz : Prop :=
  ∀ (S : Type u) [CommRing S] (D D' : SelData S) (Q : SelPairData D D')
    (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k) (hi : i + 1 = i₁) (hj : j + 1 = j₁) (hk : k + 1 = k₁)
    (c : selX D i) (c' : selX D' j),
    (coneCx Q.resE).d k k₁ hk (selCup Q i j k h c c') =
      selCup Q i₁ j k₁ (by omega) ((selCx D).d i i₁ hi c) c' +
        sgn i • selCup Q i j₁ k₁ (by omega) c ((selCx D').d j j₁ hj c')

theorem selmerCupLeibniz_proof : SelmerCupLeibniz.{u} := by
  intro S _ D D' Q i i₁ j j₁ k k₁ h hi hj hk c c'
  subst hi hj hk h
  obtain ⟨a, u, x⟩ := c
  obtain ⟨b, v, y⟩ := c'
  -- the first component is the global Leibniz rule
  refine Prod.ext ?_ ?_
  · exact Q.cupG.leib i (i + 1) j (j + 1) (i + j) (i + j + 1) rfl rfl rfl rfl a b
  -- the second component
  change Q.resE.f (i + j) (i + j + 1 - 1) _ (Q.cupG.P i j (i + j) rfl a b) -
      Q.EL.d (i + j - 1) (i + j + 1 - 1) _
        (Q.cupL.P (i - 1) j (i + j - 1) _ x (D'.ι.f j j rfl v) +
          sgn i • Q.cupL.P i (j - 1) (i + j - 1) _ (D.res.f i i rfl a) y +
          Q.hU i j (i + j - 1) _ u v) =
    (Q.cupL.P (i + 1 - 1) j (i + j + 1 - 1) _
        (D.res.f i (i + 1 - 1) _ a - D.ι.f i (i + 1 - 1) _ u - D.L.d (i - 1) (i + 1 - 1) _ x)
          (D'.ι.f j j rfl v) +
      sgn (i + 1) • Q.cupL.P (i + 1) (j - 1) (i + j + 1 - 1) _
        (D.res.f (i + 1) (i + 1) rfl (D.G.d i (i + 1) rfl a)) y +
      Q.hU (i + 1) j (i + j + 1 - 1) _ (D.U.d i (i + 1) rfl u) v) +
    sgn i • (Q.cupL.P (i - 1) (j + 1) (i + j + 1 - 1) _ x
        (D'.ι.f (j + 1) (j + 1) rfl (D'.U.d j (j + 1) rfl v)) +
      sgn i • Q.cupL.P i (j + 1 - 1) (i + j + 1 - 1) _ (D.res.f i i rfl a)
        (D'.res.f j (j + 1 - 1) _ b - D'.ι.f j (j + 1 - 1) _ v - D'.L.d (j - 1) (j + 1 - 1) _ y) +
      Q.hU i (j + 1) (i + j + 1 - 1) _ u (D'.U.d j (j + 1) rfl v))
  -- the inputs
  have hc := Q.compat i j (i + j) i (j + 1 - 1) (i + j + 1 - 1) rfl (by omega) rfl (by omega)
    (by omega) a b
  have l1 := Q.cupL.leib (i - 1) (i + 1 - 1) j (j + 1) (i + j - 1) (i + j + 1 - 1) (by omega)
    (by omega) rfl (by omega) x (D'.ι.f j j rfl v)
  have l2 := Q.cupL.leib i (i + 1) (j - 1) (j + 1 - 1) (i + j - 1) (i + j + 1 - 1) (by omega)
    rfl (by omega) (by omega) (D.res.f i i rfl a) y
  have iso := Q.isotropy i (i + 1) j (j + 1) (i + j - 1) (i + j + 1 - 1) (by omega) rfl rfl
    (by omega) u v
  have c1 := D'.ι.comm j (j + 1) j (j + 1) rfl rfl rfl rfl v
  have c2 := D.res.comm i (i + 1) i (i + 1) rfl rfl rfl rfl a
  -- index congruences
  have k1 := Q.cupL.congr (k := i + j + 1 - 1) (fun n hn => D.res.f i n hn) (fun m hm => D'.ι.f j m hm)
    (i + 1 - 1) i j (j + 1 - 1) (by omega) rfl rfl (by omega) (by omega) (by omega) a v
  have k2 := Q.cupL.congr (k := i + j + 1 - 1) (fun n hn => D.ι.f i n hn) (fun m hm => D'.ι.f j m hm)
    (i + 1 - 1) i j j (by omega) rfl rfl rfl (by omega) (by omega) u v
  rw [← c1] at l1
  rw [← c2] at l2
  have hU' : Q.EL.d (i + j - 1) (i + j + 1 - 1) (by omega) (Q.hU i j (i + j - 1) (by omega) u v) =
      Q.cupL.P i j (i + j + 1 - 1) (by omega) (D.ι.f i i rfl u) (D'.ι.f j j rfl v) -
        Q.hU (i + 1) j (i + j + 1 - 1) (by omega) (D.U.d i (i + 1) rfl u) v -
        sgn i • Q.hU i (j + 1) (i + j + 1 - 1) (by omega) u (D'.U.d j (j + 1) rfl v) := by
    rw [← iso]; abel
  rw [map_add, map_add, map_zsmul, l1, l2, hU', hc, sgn_succ, sgn_pred]
  simp only [map_sub, LinearMap.sub_apply, smul_add, smul_sub, smul_smul, sgn_mul_self, one_smul,
    neg_smul]
  rw [k1, k2]
  abel

/-! ### Trace components -/

/-- The degree-three component `PD(w, y) = tr(P(w, y))` for `w ∈ C^i`, `y ∈ C'^{3−i}`. -/
def traceComp {A B T : GCx S} (P : GPair A B T) (tr : T.X 3 →ₗ[S] S) (i j : ℤ) (h : i + j = 3) :
    A.X i →ₗ[S] B.X j →ₗ[S] S :=
  (P.P i j 3 h).compr₂ tr

/-- **Trace components satisfy the two Leibniz relations used for `λ_z`** (tex L3752–3754,
L3858–3861: "Applying the integral duality chain map gives a closed element of
`Hom_S(C_U^2, S)`"). For a pairing `C_U × C' → T` and a trace `tr : T^3 → S` killing coboundaries,
`PD₁ = tr ∘ P_{1,2}`, `PD₂ = tr ∘ P_{2,1}`, `PD₃ = tr ∘ P_{3,0}` satisfy, on the Mathlib complexes,
the hypotheses of `IntegralClosedLift` (with `ε = 1`) and of `PairedFunctionalWellDefined` (with
`ε = −1`), in their exact statement form. Classification: PROVED. -/
def TraceComponentsLeibniz : Prop :=
  ∀ (S : Type u) [CommRing S] (A B T : GCx S) (P : GPair A B T) (tr : T.X 3 →ₗ[S] S),
    (∀ z, tr (T.d 2 3 rfl z) = 0) →
    let CU := A.toCC
    let C' := B.toCC
    let pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S := traceComp P tr 1 2 rfl
    let pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S := traceComp P tr 2 1 rfl
    let pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S := traceComp P tr 3 0 rfl
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = (1 : S) * pd1 w ((C'.d 1 2).hom y)) ∧
    (∀ w y, pd2 w ((C'.d 0 1).hom y) = (-1 : S) * pd3 ((CU.d 2 3).hom w) y)

theorem traceComponentsLeibniz_proof : TraceComponentsLeibniz.{u} := by
  intro S _ A B T P tr htr
  dsimp only
  refine ⟨fun w y => ?_, fun w y => ?_⟩
  · have hl := P.leib 1 2 1 2 2 3 rfl rfl rfl rfl w y
    have h0 := htr (P.P 1 1 2 rfl w y)
    rw [hl, map_add, map_zsmul, sgn_one] at h0
    simp only [traceComp, one_mul]
    rw [neg_smul, one_smul] at h0
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)
  · have hl := P.leib 2 3 0 1 2 3 rfl rfl rfl rfl w y
    have h0 := htr (P.P 2 0 2 rfl w y)
    rw [hl, map_add, map_zsmul, sgn_two, one_smul] at h0
    simp only [traceComp]
    rw [neg_one_mul]
    exact eq_neg_of_add_eq_zero_right h0

/-- The Selmer cup product as a pairing of complexes. -/
def selPair (Q : SelPairData D D') : GPair (selCx D) (selCx D') (coneCx Q.resE) where
  P := selCup Q
  leib i i₁ j j₁ k k₁ h hi hj hk c c' :=
    selmerCupLeibniz_proof S D D' Q i i₁ j j₁ k k₁ h hi hj hk c c'

/-- **The retained duality components on Selmer complexes** (tex L3752–3758, L3826–3836; GLUE of
`SelmerCupLeibniz` and `TraceComponentsLeibniz`): for local-condition data `D` (for `C_U`) and
`D'` (for `C_{U^⊥}`), compatible pairings with an isotropy homotopy, and a trace
`tr : K^3 → S` on `K = Cone(E → E_L)[−1]` killing coboundaries (the integral trace map of the
text), the components `PD_i` of the Selmer cup product satisfy the hypotheses of
`IntegralClosedLift` and `PairedFunctionalWellDefined` on the Mathlib Selmer complexes.
Classification: PROVED. -/
def SelmerDualityComponents : Prop :=
  ∀ (S : Type u) [CommRing S] (D D' : SelData S) (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[S] S), (∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) →
    let CU := (selCx D).toCC
    let C' := (selCx D').toCC
    let pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S := traceComp (selPair Q) tr 1 2 rfl
    let pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S := traceComp (selPair Q) tr 2 1 rfl
    let pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S := traceComp (selPair Q) tr 3 0 rfl
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = (1 : S) * pd1 w ((C'.d 1 2).hom y)) ∧
    (∀ w y, pd2 w ((C'.d 0 1).hom y) = (-1 : S) * pd3 ((CU.d 2 3).hom w) y)

theorem selmerDualityComponents_proof : SelmerDualityComponents.{u} :=
  fun S _ _ _ Q tr htr => traceComponentsLeibniz_proof S _ _ _ (selPair Q) tr htr

/-! ### Non-vacuity -/

/-- The complex with `S` in every degree and zero differential. -/
def constCx (S : Type u) [CommRing S] : GCx S where
  X _ := ModuleCat.of S S
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The identity chain map of `constCx`. -/
def constId (S : Type u) [CommRing S] : GHom (constCx S) (constCx S) where
  f _ _ _ := LinearMap.id
  comm _ _ _ _ _ _ _ _ _ := rfl

/-- The zero chain map of `constCx`. -/
def constZero (S : Type u) [CommRing S] : GHom (constCx S) (constCx S) where
  f _ _ _ := 0
  comm _ _ _ _ _ _ _ _ _ := rfl

/-- Multiplication as a pairing `constCx × constCx → constCx`. -/
def constMul (S : Type u) [CommRing S] : GPair (constCx S) (constCx S) (constCx S) where
  P _ _ _ _ := LinearMap.mul S S
  leib i _ _ _ _ _ _ _ _ _ x y := by
    change (0 : S) = (0 : S) * (show S from y) + sgn i • ((show S from x) * (0 : S))
    rw [zero_mul, mul_zero, smul_zero, add_zero]

/-- The local-condition data `constCx --id--> constCx <--0-- constCx`. -/
def constSel (S : Type u) [CommRing S] : SelData S :=
  ⟨constCx S, constCx S, constCx S, constId S, constZero S⟩

/-- Pairing data on `constSel` with `∪ = ·`, `res_E = id` and zero isotropy homotopy. -/
def constSelPair (S : Type u) [CommRing S] : SelPairData (constSel S) (constSel S) where
  E := constCx S
  EL := constCx S
  resE := constId S
  cupG := constMul S
  cupL := constMul S
  compat _ _ _ _ _ _ _ _ _ _ _ _ _ := rfl
  hU _ _ _ _ := 0
  isotropy i _ _ _ _ _ _ _ _ _ u v := by
    change (0 : S) + 0 + sgn i • (0 : S) = (0 : S) * (0 : S)
    simp

/-- **Non-vacuity of `SelmerDualityComponents`** : over every nontrivial commutative ring there are
Selmer data, pairing data and a trace killing coboundaries, with `PD₁ ≠ 0`. Classification:
PROVED. -/
theorem selmerDuality_nonvacuous (S : Type u) [CommRing S] [Nontrivial S] :
    ∃ (Q : SelPairData (constSel S) (constSel S)) (tr : (coneCx Q.resE).X 3 →ₗ[S] S),
      (∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) ∧ traceComp (selPair Q) tr 1 2 rfl ≠ 0 := by
  refine ⟨constSelPair S, LinearMap.fst S S S, fun z => ?_, fun h0 => ?_⟩
  · change (0 : S) = 0
    rfl
  · have := LinearMap.congr_fun₂ h0 ((1 : S), (0 : S), (0 : S)) ((1 : S), (0 : S), (0 : S))
    change (1 : S) * 1 = 0 at this
    simp at this

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
