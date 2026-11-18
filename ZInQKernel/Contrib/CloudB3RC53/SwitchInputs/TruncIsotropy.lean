import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchAdjunction

/-!
# RC53 SwitchInputs: Selmer pairing data with a truncated isotropy homotopy

Manuscript `diophantine_zq.tex`, tex L5068–5075 (the derivative conditions `D⁰ ⊂ D⁰ ⊕ (F ⊕ S)[−1]`
at the switch place and their localization duality) and Lemma `ex:limits-derivative-switch`
(tex L4834–4907); Nekovář, *Selmer complexes* (Astérisque 310), Sections 6.2–6.3 (as cited at
tex L3826–3836; locator UNVERIFIED).

`PairedFunctional.SelPairData` asks for an isotropy homotopy `h` of the local conditions with
`d h + h d = ι u ∪ ι' v` in **every** degree. For the text's truncated derivative conditions
(`D⁰ = τ≤0`, relaxed `D⁰ ⊕ (F ⊕ S)[−1] ⊂ τ≤1`) this is false: the cup product of a degree-zero and
a degree-one local class is a nonzero degree-one cochain, which no null-homotopy of the required
degree can produce (`exUntruncated_fails`). Nekovář's construction only needs the cup product
`U × U' → E_L` to be null-homotopic **after the canonical truncation `τ≥2`** of the local target:
the trace reads degree three of the cone, i.e. degree two of `E_L`.

This file:
* `truncGe2 A`: the canonical truncation `τ≥2 A` (`0` in degrees `≤ 1`, `A²/d(A¹)` in degree two,
  `Aⁿ` above), as the quotient of `A` by `truncSub A` (`⊤`, `im d¹`, `⊥`); `truncProj`,
  `truncPair` (a pairing of complexes induces one into `τ≥2`).
* `SelPairDataTrunc D D'`: Selmer pairing data whose isotropy identity is required only in local
  target degree two (modulo `d(E_L¹)`) and in degrees `≥ 3` (exactly) — Nekovář's `τ≥2` null-homotopy.
* `SelPairData.toTrunc` (untruncated data are truncated data) and `SelPairDataTrunc.toSelPairData`
  (truncated data give genuine `SelPairData` with local target `τ≥2 E_L`; PROVED). So the Leibniz
  rule of the Selmer cup product (`selmerCupLeibniz_proof`) and the trace components
  (`selmerDualityComponents_proof`) hold for the truncated cup product, `truncCupLeibniz`,
  `truncDualityComponents`.
* `SelPairDataTrunc.trT`: a trace on the original cone killing coboundaries descends to the
  truncated cone, and `trT_selCupFun` computes it by the original cup formula.
* `switchAdjunction_of_trunc` (PROVED): the switch duality adjunction from truncated data — the other
  team's `switchAdjunctionFromDuality_proof` applies to `toSelPairData`.
* Non-vacuity: the derivative conditions `D⁰` (degree 0) and `D⁰ ⊕ (F ⊕ S)[−1]` (degrees 0, 1) with a
  local cup product `L⁰ × L¹ → E_L¹`: `exUntruncated_fails` (no untruncated isotropy homotopy
  exists) and `exTrunc` (truncated data exist), hence genuine `SelPairData` over `τ≥2`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Uniform

universe u

section Trunc

variable {S : Type u} [CommRing S]

/-- The submodules defining `τ≥2`: everything in degrees `≤ 1`, the coboundaries `d(A¹)` in
degree two, nothing above. -/
def truncSub (A : GCx S) (n : ℤ) : Submodule S (A.X n) :=
  if n ≤ 1 then ⊤ else if h : n = 2 then LinearMap.range (A.d 1 n (by omega)) else ⊥

theorem truncSub_of_le (A : GCx S) {n : ℤ} (hn : n ≤ 1) : truncSub A n = ⊤ := by
  unfold truncSub; rw [if_pos hn]

theorem truncSub_of_eq (A : GCx S) {n : ℤ} (hn : n = 2) :
    truncSub A n = LinearMap.range (A.d 1 n (by omega)) := by
  unfold truncSub; rw [if_neg (by omega), dif_pos hn]

theorem truncSub_of_ge (A : GCx S) {n : ℤ} (hn : 3 ≤ n) : truncSub A n = ⊥ := by
  unfold truncSub; rw [if_neg (by omega), dif_neg (by omega)]

theorem d_mem_truncSub (A : GCx S) (i j : ℤ) (h : i + 1 = j) (x : A.X i)
    (hx : x ∈ truncSub A i) : A.d i j h x ∈ truncSub A j := by
  rcases lt_trichotomy i 1 with hi | rfl | hi
  · rw [truncSub_of_le A (by omega)]; trivial
  · rw [truncSub_of_eq A (by omega)]; exact ⟨x, rfl⟩
  · rcases (show i = 2 ∨ 3 ≤ i by omega) with rfl | hi3
    · rw [truncSub_of_eq A rfl] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [truncSub_of_ge A (by omega), A.d_d 1 2 j rfl h y]
      exact Submodule.zero_mem _
    · rw [truncSub_of_ge A hi3, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _

/-- **The canonical truncation `τ≥2 A`** (Nekovář, *Selmer complexes*, Section 6.2, as cited at
tex L3826–3836): the quotient of `A` by `truncSub A`. -/
def truncGe2 (A : GCx S) : GCx S where
  X n := ModuleCat.of S (A.X n ⧸ truncSub A n)
  d i j h := (truncSub A i).mapQ (truncSub A j) (A.d i j h)
    (fun x hx => d_mem_truncSub A i j h x hx)
  d_d i j k hij hjk x := by
    obtain ⟨y, rfl⟩ := (truncSub A i).mkQ_surjective x
    change (truncSub A k).mkQ (A.d j k hjk (A.d i j hij y)) = 0
    rw [A.d_d i j k hij hjk y, map_zero]

theorem truncGe2_d_mk (A : GCx S) (i j : ℤ) (h : i + 1 = j) (x : A.X i) :
    (truncGe2 A).d i j h ((truncSub A i).mkQ x) = (truncSub A j).mkQ (A.d i j h x) := rfl

/-- The projection `A → τ≥2 A`. -/
def truncProj (A : GCx S) : GHom A (truncGe2 A) where
  f i j h := by subst h; exact (truncSub A i).mkQ
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- A pairing of complexes induces a pairing into `τ≥2` of the target. -/
def truncPair {A B T : GCx S} (P : GPair A B T) : GPair A B (truncGe2 T) where
  P i j k h := (P.P i j k h).compr₂ (truncSub T k).mkQ
  leib i i₁ j j₁ k k₁ h hi hj hk x y := by
    have hl := P.leib i i₁ j j₁ k k₁ h hi hj hk x y
    change (truncSub T k₁).mkQ (T.d k k₁ hk (P.P i j k h x y)) =
      (truncSub T k₁).mkQ (P.P i₁ j k₁ _ (A.d i i₁ hi x) y) +
        sgn i • (truncSub T k₁).mkQ (P.P i j₁ k₁ _ x (B.d j j₁ hj y))
    rw [hl, map_add, map_zsmul]

end Trunc

section Data

variable {S : Type u} [CommRing S]

/-- **Selmer pairing data with a `τ≥2`-truncated isotropy homotopy** (Nekovář, *Selmer complexes*,
Sections 6.2–6.3, as cited at tex L3826–3836; locator UNVERIFIED): as `SelPairData`, but the
isotropy identity `d h + h d = ι u ∪ ι' v` is required only after projecting the local target to
`τ≥2`: in target degree two modulo the coboundaries `d(E_L¹)` (`isotropy₂`), and exactly in target
degrees `≥ 3` (`isotropy₃`). This is what the truncated derivative conditions of tex L5068–5072
admit. -/
structure SelPairDataTrunc (D D' : SelData S) where
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
  /-- Target degree two, modulo the coboundaries `d(E_L¹)`. -/
  isotropy₂ : ∀ (i i₁ j j₁ : ℤ) (h : i + j = 2) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (u : D.U.X i) (v : D'.U.X j),
    hU i₁ j 2 (by omega) (D.U.d i i₁ hi u) v + sgn i • hU i j₁ 2 (by omega) u (D'.U.d j j₁ hj v) -
        cupL.P i j 2 h (D.ι.f i i rfl u) (D'.ι.f j j rfl v) ∈ LinearMap.range (EL.d 1 2 rfl)
  /-- Target degrees `≥ 3`, exactly. -/
  isotropy₃ : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁), 3 ≤ k₁ → ∀ (u : D.U.X i) (v : D'.U.X j),
    EL.d k k₁ hk (hU i j k h u v) + hU i₁ j k₁ (by omega) (D.U.d i i₁ hi u) v +
        sgn i • hU i j₁ k₁ (by omega) u (D'.U.d j j₁ hj v) =
      cupL.P i j k₁ (by omega) (D.ι.f i i rfl u) (D'.ι.f j j rfl v)

variable {D D' : SelData S}

/-- Untruncated data are truncated data. PROVED. -/
def SelPairData.toTrunc (Q : SelPairData D D') : SelPairDataTrunc D D' where
  E := Q.E
  EL := Q.EL
  resE := Q.resE
  cupG := Q.cupG
  cupL := Q.cupL
  compat := Q.compat
  hU := Q.hU
  isotropy₂ i i₁ j j₁ h hi hj u v := by
    have hiso := Q.isotropy i i₁ j j₁ 1 2 (by omega) hi hj rfl u v
    refine ⟨-(Q.hU i j 1 (by omega) u v), ?_⟩
    rw [map_neg, ← hiso]
    abel
  isotropy₃ i i₁ j j₁ k k₁ h hi hj hk _ u v := Q.isotropy i i₁ j j₁ k k₁ h hi hj hk u v

/-- The restriction `E → τ≥2 E_L`. -/
def SelPairDataTrunc.resT (Q : SelPairDataTrunc D D') : GHom Q.E (truncGe2 Q.EL) where
  f i j h := (truncSub Q.EL j).mkQ ∘ₗ Q.resE.f i j h
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    change (truncSub Q.EL j₁).mkQ (Q.resE.f i₁ j₁ hj (Q.E.d i i₁ h₁ x)) =
      (truncSub Q.EL j₁).mkQ (Q.EL.d j j₁ h₂ (Q.resE.f i j hij x))
    rw [Q.resE.comm i i₁ j j₁ hij h₁ h₂ hj x]

/-- **Truncated data give genuine Selmer pairing data with local target `τ≥2 E_L`** (Nekovář,
*Selmer complexes*, Sections 6.2–6.3: the cup product on Selmer complexes only needs the `τ≥2`
null-homotopy). Classification: PROVED. -/
def SelPairDataTrunc.toSelPairData (Q : SelPairDataTrunc D D') : SelPairData D D' where
  E := Q.E
  EL := truncGe2 Q.EL
  resE := Q.resT
  cupG := Q.cupG
  cupL := truncPair Q.cupL
  compat i j k i' j' k' h h' hi hj hk a b := by
    change (truncSub Q.EL k').mkQ (Q.resE.f k k' hk (Q.cupG.P i j k h a b)) =
      (truncSub Q.EL k').mkQ (Q.cupL.P i' j' k' h' (D.res.f i i' hi a) (D'.res.f j j' hj b))
    rw [Q.compat i j k i' j' k' h h' hi hj hk a b]
  hU i j k h := (Q.hU i j k h).compr₂ (truncSub Q.EL k).mkQ
  isotropy i i₁ j j₁ k k₁ h hi hj hk u v := by
    change (truncSub Q.EL k₁).mkQ (Q.EL.d k k₁ hk (Q.hU i j k h u v)) +
        (truncSub Q.EL k₁).mkQ (Q.hU i₁ j k₁ _ (D.U.d i i₁ hi u) v) +
        sgn i • (truncSub Q.EL k₁).mkQ (Q.hU i j₁ k₁ _ u (D'.U.d j j₁ hj v)) =
      (truncSub Q.EL k₁).mkQ (Q.cupL.P i j k₁ _ (D.ι.f i i rfl u) (D'.ι.f j j rfl v))
    rw [← map_zsmul, ← map_add, ← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    rcases (show k₁ ≤ 1 ∨ k₁ = 2 ∨ 3 ≤ k₁ by omega) with hk1 | hk2 | hk3
    · rw [truncSub_of_le Q.EL hk1]; trivial
    · subst hk2
      obtain rfl : k = 1 := by omega
      rw [truncSub_of_eq Q.EL rfl]
      have h2 := Q.isotropy₂ i i₁ j j₁ (by omega) hi hj u v
      obtain ⟨y, hy⟩ := h2
      refine ⟨Q.hU i j 1 h u v + y, ?_⟩
      rw [map_add, hy]
      abel
    · rw [truncSub_of_ge Q.EL hk3, Q.isotropy₃ i i₁ j j₁ k k₁ h hi hj hk hk3 u v, sub_self]
      exact Submodule.zero_mem _

/-- **The Leibniz rule of the truncated Selmer cup product** (tex L3826–3836): the Selmer cup product
of truncated data, with values in `Cone(E → τ≥2 E_L)[−1]`, is a pairing of complexes. PROVED. -/
theorem truncCupLeibniz (Q : SelPairDataTrunc D D') (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k)
    (hi : i + 1 = i₁) (hj : j + 1 = j₁) (hk : k + 1 = k₁) (c : selX D i) (c' : selX D' j) :
    (coneCx Q.toSelPairData.resE).d k k₁ hk (selCup Q.toSelPairData i j k h c c') =
      selCup Q.toSelPairData i₁ j k₁ (by omega) ((selCx D).d i i₁ hi c) c' +
        sgn i • selCup Q.toSelPairData i j₁ k₁ (by omega) c ((selCx D').d j j₁ hj c') :=
  selmerCupLeibniz_proof S D D' Q.toSelPairData i i₁ j j₁ k k₁ h hi hj hk c c'

/-- The Selmer cup formula with the original (untruncated) local target. -/
def selCupFunT (Q : SelPairDataTrunc D D') (i j k : ℤ) (h : i + j = k) (c : selT D i)
    (c' : selT D' j) : coneT Q.resE k :=
  (Q.cupG.P i j k h c.1 c'.1,
    Q.cupL.P (i - 1) j (k - 1) (by omega) c.2.2 (D'.ι.f j j rfl c'.2.1) +
      sgn i • Q.cupL.P i (j - 1) (k - 1) (by omega) (D.res.f i i rfl c.1) c'.2.2 +
      Q.hU i j (k - 1) (by omega) c.2.1 c'.2.1)

/-- The truncated cup product is the original formula projected to `τ≥2`. PROVED. -/
theorem selCupFun_toSelPairData (Q : SelPairDataTrunc D D') (i j k : ℤ) (h : i + j = k)
    (c : selT D i) (c' : selT D' j) :
    selCupFun Q.toSelPairData i j k h c c' =
      ((selCupFunT Q i j k h c c').1, (truncSub Q.EL (k - 1)).mkQ (selCupFunT Q i j k h c c').2) := by
  refine Prod.ext rfl ?_
  change (truncSub Q.EL (k - 1)).mkQ _ + sgn i • (truncSub Q.EL (k - 1)).mkQ _ +
      (truncSub Q.EL (k - 1)).mkQ _ = _
  simp only [selCupFunT, map_add, map_zsmul]

/-- **The trace descends to the truncated cone.** A trace on `Cone(E → E_L)[−1]` in degree three
killing coboundaries vanishes on `(0, d(E_L¹))`, hence factors through
`Cone(E → τ≥2 E_L)[−1]³ = E³ ⊕ E_L²/d(E_L¹)`. -/
def SelPairDataTrunc.trT (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    (coneCx Q.toSelPairData.resE).X 3 →ₗ[S] S :=
  LinearMap.coprod (tr0 ∘ₗ LinearMap.inl S (Q.E.X 3) (Q.EL.X (3 - 1)))
    ((truncSub Q.EL (3 - 1)).liftQ (tr0 ∘ₗ LinearMap.inr S (Q.E.X 3) (Q.EL.X (3 - 1))) (by
      rw [truncSub_of_eq Q.EL (by norm_num)]
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have h0 := htr0 ((0 : Q.E.X 2), y)
      have e : (coneCx Q.resE).d 2 3 rfl ((0 : Q.E.X 2), y) =
          LinearMap.inr S (Q.E.X 3) (Q.EL.X (3 - 1)) (-(Q.EL.d 1 (3 - 1) (by norm_num) y)) := by
        change ((Q.E.d 2 3 rfl 0, Q.resE.f 2 (3 - 1) _ 0 - Q.EL.d (2 - 1) (3 - 1) _ y) :
          coneT Q.resE 3) = (0, -(Q.EL.d 1 (3 - 1) _ y))
        rw [map_zero, map_zero, zero_sub]
        rfl
      rw [e, map_neg] at h0
      exact neg_eq_zero.mp ((map_neg tr0 _).symm.trans h0)))

theorem SelPairDataTrunc.trT_mk (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) (a : Q.E.X 3) (b : Q.EL.X (3 - 1)) :
    Q.trT tr0 htr0 ((a, (truncSub Q.EL (3 - 1)).mkQ b) : coneT Q.toSelPairData.resE 3) =
      tr0 ((a, b) : coneT Q.resE 3) := by
  change tr0 (show (coneCx Q.resE).X 3 from (a, 0)) +
    tr0 (show (coneCx Q.resE).X 3 from (0, b)) = tr0 (a, b)
  rw [← map_add]
  congr 1
  exact Prod.ext (add_zero a) (zero_add b)

/-- The descended trace kills the coboundaries of the truncated cone. PROVED. -/
theorem SelPairDataTrunc.trT_kills (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) (z : (coneCx Q.toSelPairData.resE).X 2) :
    Q.trT tr0 htr0 ((coneCx Q.toSelPairData.resE).d 2 3 rfl z) = 0 := by
  obtain ⟨e, q⟩ := z
  obtain ⟨y, rfl⟩ := (truncSub Q.EL (2 - 1)).mkQ_surjective q
  have hd : (coneCx Q.toSelPairData.resE).d 2 3 rfl
      ((e, (truncSub Q.EL (2 - 1)).mkQ y) : coneT Q.toSelPairData.resE 2) =
      ((Q.E.d 2 3 rfl e, (truncSub Q.EL (3 - 1)).mkQ
        (Q.resE.f 2 (3 - 1) (by norm_num) e - Q.EL.d (2 - 1) (3 - 1) (by norm_num) y)) :
        coneT Q.toSelPairData.resE 3) := by
    change ((Q.E.d 2 3 rfl e, (truncSub Q.EL (3 - 1)).mkQ (Q.resE.f 2 (3 - 1) _ e) -
      (truncSub Q.EL (3 - 1)).mkQ (Q.EL.d (2 - 1) (3 - 1) _ y)) : coneT Q.toSelPairData.resE 3) = _
    rw [← map_sub]
  rw [hd, Q.trT_mk tr0 htr0]
  exact htr0 (e, y)

/-- The descended trace of the truncated cup product is the original trace of the original cup
formula. PROVED. -/
theorem trT_selCupFun (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) (i j : ℤ) (h : i + j = 3) (c : selT D i)
    (c' : selT D' j) :
    Q.trT tr0 htr0 (selCupFun Q.toSelPairData i j 3 h c c') = tr0 (selCupFunT Q i j 3 h c c') := by
  rw [selCupFun_toSelPairData]
  exact Q.trT_mk tr0 htr0 _ _

/-- **The trace components of the truncated cup product satisfy the Leibniz hypotheses** of
`IntegralClosedLift` / `PairedFunctionalWellDefined` (tex L3752–3758, L3826–3836): PROVED via
`selmerDualityComponents_proof` for `toSelPairData` and the descended trace. -/
theorem truncDualityComponents (Q : SelPairDataTrunc D D') (tr0 : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    let CU := (selCx D).toCC
    let C' := (selCx D').toCC
    let pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S := traceComp (selPair Q.toSelPairData) (Q.trT tr0 htr0) 1 2 rfl
    let pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S := traceComp (selPair Q.toSelPairData) (Q.trT tr0 htr0) 2 1 rfl
    let pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S := traceComp (selPair Q.toSelPairData) (Q.trT tr0 htr0) 3 0 rfl
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = (1 : S) * pd1 w ((C'.d 1 2).hom y)) ∧
    (∀ w y, pd2 w ((C'.d 0 1).hom y) = (-1 : S) * pd3 ((CU.d 2 3).hom w) y) :=
  selmerDualityComponents_proof S D D' Q.toSelPairData (Q.trT tr0 htr0) (Q.trT_kills tr0 htr0)

end Data

section Adjunction

/-- **The switch duality adjunction from truncated Selmer pairing data** (tex L5068–5075; Nekovář,
*Selmer complexes*, Prop. 6.3.3 and Thm. 6.3.4, as cited): the other team's
`switchAdjunctionFromDuality_proof` applies to the genuine `SelPairData` over `τ≥2` built from
truncated data. Inputs: the `τ≥2`-Selmer duality map is a quasi-isomorphism (Nekovář 6.3.4 for the
truncated cup product), and the coordinate pairing identity `hsw` stated with the ORIGINAL cup formula
and trace. Classification: PROVED (from the inputs). -/
theorem switchAdjunction_of_trunc (k : Type) [Field k] (R : QuasiRelaxedLocalization k)
    (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (Q : SelPairDataTrunc (restrictData R.D f) R.D) (tr0 : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hqi : QuasiIso (GHom.toCC (selmerDualityMap Q.toSelPairData (Q.trT tr0 htr0)
      (Q.trT_kills tr0 htr0))))
    (hsw : ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
        (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
        (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
      tr0 (selCupFunT Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
        switchPairing ε σ J (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu))) :
    SwitchDualityAdjunction R (restrictData R.D f) ε σ J hε hσ hJ2
      (switchDelta R f hfg hf hg hex) (switchDelta_exact R f hfg hf hg hex) :=
  switchAdjunctionFromDuality_proof k R Ustr f hfg hf hg hex Q.toSelPairData (Q.trT tr0 htr0)
    (Q.trT_kills tr0 htr0) ε σ J hε hσ hJ2 hqi
    (fun t u s ht hu ct cu hct hcu => (trT_selCupFun Q tr0 htr0 2 1 rfl _ _).trans
      (hsw t u s ht hu ct cu hct hcu))

end Adjunction

/-! ### Non-vacuity: the derivative conditions, where only the truncated isotropy holds -/

section Example

variable (S : Type u) [CommRing S]

/-- The complex with `S^{dim n}` in degree `n` and zero differentials. -/
def stdCx (dim : ℤ → ℕ) : GCx S where
  X n := ModuleCat.of S (Fin (dim n) → S)
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

theorem stdCx_d_apply (dim : ℤ → ℕ) (i j : ℤ) (h : i + 1 = j) (x : (stdCx S dim).X i) :
    (stdCx S dim).d i j h x = 0 := rfl

/-- Extension by zero `S^a → S^b`. -/
def embedL (a b : ℕ) : (Fin a → S) →ₗ[S] (Fin b → S) where
  toFun x m := if h : (m : ℕ) < a then x ⟨m, h⟩ else 0
  map_add' x y := by
    ext m; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r x := by
    ext m; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

/-- Strict derivative condition `D⁰`: one class in degree zero. -/
def dimStr (n : ℤ) : ℕ := if n = 0 then 1 else 0

/-- Relaxed derivative condition `D⁰ ⊕ (F ⊕ S)[−1]`: degree zero, and `F ⊕ S` in degree one. -/
def dimRel (n : ℤ) : ℕ := if n = 0 then 1 else if n = 1 then 2 else 0

/-- The local complex: degree zero and `F ⊕ S` in degree one. -/
def dimLoc (n : ℤ) : ℕ := if n = 0 then 1 else if n = 1 then 2 else 0

/-- The local target: degree one. -/
def dimTgt (n : ℤ) : ℕ := if n = 1 then 1 else 0

/-- The zero dimension. -/
def dimZero (_n : ℤ) : ℕ := 0

/-- A local condition map by extension by zero (zero differentials, so it is a chain map). -/
def stdEmbed (a b : ℤ → ℕ) : GHom (stdCx S a) (stdCx S b) where
  f i j h := by subst h; exact embedL S (a i) (b i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    rw [stdCx_d_apply, stdCx_d_apply, map_zero]

theorem stdEmbed_f (a b : ℤ → ℕ) (i : ℤ) : (stdEmbed S a b).f i i rfl = embedL S (a i) (b i) :=
  rfl

theorem lt_dimLoc_zero : 0 < dimLoc 0 := by simp [dimLoc]
theorem lt_dimLoc_one : 0 < dimLoc 1 := by simp [dimLoc]

/-- The local cup product `L⁰ × L¹ → E_L¹`, `(x, y) ↦ x₀ y₀` (pairing `D⁰` with the `F`-coordinate),
and zero in all other bidegrees. -/
def locCupP (i j k : ℤ) (_h : i + j = k) :
    (Fin (dimLoc i) → S) →ₗ[S] (Fin (dimLoc j) → S) →ₗ[S] (Fin (dimTgt k) → S) :=
  if hij : i = 0 ∧ j = 1 then
    LinearMap.mk₂ S (fun x y _ => x ⟨0, by rw [hij.1]; exact lt_dimLoc_zero⟩ *
        y ⟨0, by rw [hij.2]; exact lt_dimLoc_one⟩)
      (fun _ _ _ => by ext; simp [add_mul]) (fun _ _ _ => by ext; simp [mul_assoc])
      (fun _ _ _ => by ext; simp [mul_add]) (fun _ _ _ => by ext; simp [mul_left_comm])
  else 0

/-- The local cup product as a pairing of complexes (zero differentials). -/
def locCup : GPair (stdCx S dimLoc) (stdCx S dimLoc) (stdCx S dimTgt) where
  P := locCupP S
  leib i i₁ j j₁ k k₁ h hi hj hk x y := by
    rw [stdCx_d_apply, stdCx_d_apply, stdCx_d_apply]
    simp only [map_zero, smul_zero, add_zero, LinearMap.zero_apply]
    exact (LinearMap.map_zero₂ (locCupP S i₁ j k₁ (by omega)) y).symm

theorem locCup_P : (locCup S).P = locCupP S := rfl

/-- The zero pairing. -/
def zeroPair (A B T : GCx S) : GPair A B T where
  P _ _ _ _ := 0
  leib _ _ _ _ _ _ _ _ _ _ x y := by simp

/-- The strict local-condition data `D⁰ → L` (no global part). -/
def exStrData : SelData S :=
  ⟨stdCx S dimZero, stdCx S dimStr, stdCx S dimLoc, zeroGHom _ _, stdEmbed S dimStr dimLoc⟩

/-- The relaxed local-condition data `D⁰ ⊕ (F ⊕ S)[−1] → L` (no global part). -/
def exRelData : SelData S :=
  ⟨stdCx S dimZero, stdCx S dimRel, stdCx S dimLoc, zeroGHom _ _, stdEmbed S dimRel dimLoc⟩

/-- The test classes: the generator of `D⁰` and the vector `(1, 1)` of `F ⊕ S`. -/
def exU0 : (exStrData S).U.X 0 := fun _ => 1

/-- See `exU0`. -/
def exV1 : (exRelData S).U.X 1 := fun _ => 1

/-- **Non-vacuity: the untruncated isotropy fails for the derivative conditions.** For the local cup
product `locCup` (pairing `D⁰` with the `F`-coordinate of `(F ⊕ S)[−1]`, into degree one), no
isotropy homotopy `h` satisfies `d h + h d = ι u ∪ ι' v` in all degrees: in bidegree `(0, 1)` all
three terms of the left side vanish, while `ι(1) ∪ ι'(e_F) = 1 ≠ 0`. So the derivative conditions do
NOT give `PairedFunctional.SelPairData`. PROVED. -/
theorem exUntruncated_fails [Nontrivial S]
    (hU : ∀ i j k : ℤ, i + j = k + 1 →
      (exStrData S).U.X i →ₗ[S] (exRelData S).U.X j →ₗ[S] (stdCx S dimTgt).X k) :
    ¬ ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
      (hk : k + 1 = k₁) (u : (exStrData S).U.X i) (v : (exRelData S).U.X j),
      (stdCx S dimTgt).d k k₁ hk (hU i j k h u v) + hU i₁ j k₁ (by omega) ((exStrData S).U.d i i₁ hi u) v +
          sgn i • hU i j₁ k₁ (by omega) u ((exRelData S).U.d j j₁ hj v) =
        (locCup S).P i j k₁ (by omega) ((exStrData S).ι.f i i rfl u) ((exRelData S).ι.f j j rfl v) := by
  intro hiso
  have h := hiso 0 1 1 2 0 1 rfl rfl rfl rfl (exU0 S) (exV1 S)
  have hz : (exStrData S).U.d 0 1 rfl (exU0 S) = 0 := rfl
  have hz' : (exRelData S).U.d 1 2 rfl (exV1 S) = 0 := rfl
  have hd : (stdCx S dimTgt).d 0 1 rfl (hU 0 1 0 rfl (exU0 S) (exV1 S)) = 0 := rfl
  have hι : (exStrData S).ι.f 0 0 rfl = embedL S (dimStr 0) (dimLoc 0) := rfl
  have hι' : (exRelData S).ι.f 1 1 rfl = embedL S (dimRel 1) (dimLoc 1) := rfl
  rw [hz, hz', hd, hι, hι', locCup_P, map_zero, map_zero, LinearMap.zero_apply, smul_zero,
    add_zero, zero_add] at h
  have h1 : (locCupP S 0 1 1 rfl (embedL S (dimStr 0) (dimLoc 0) (exU0 S))
      (embedL S (dimRel 1) (dimLoc 1) (exV1 S))) ⟨0, by simp [dimTgt]⟩ = 1 := by
    rw [locCupP, dif_pos ⟨rfl, rfl⟩]
    show (if h : (0 : ℕ) < dimStr 0 then exU0 S ⟨0, h⟩ else 0) *
      (if h : (0 : ℕ) < dimRel 1 then exV1 S ⟨0, h⟩ else 0) = 1
    rw [dif_pos (by simp [dimStr]), dif_pos (by simp [dimRel])]
    exact mul_one 1
  have h0 := congrFun h ⟨0, by simp [dimTgt]⟩
  exact zero_ne_one (h0.trans h1)

/-- **Non-vacuity: the truncated isotropy holds for the derivative conditions.** With `h = 0`, both
truncated identities hold: the local cup product vanishes in target degrees `≥ 2` (its only nonzero
bidegree is `(0, 1)`, of target degree one). PROVED. -/
def exTrunc : SelPairDataTrunc (exStrData S) (exRelData S) where
  E := stdCx S dimZero
  EL := stdCx S dimTgt
  resE := zeroGHom _ _
  cupG := zeroPair S _ _ _
  cupL := locCup S
  compat i j k i' j' k' h h' hi hj hk a b := by
    change (0 : (stdCx S dimTgt).X k') =
      (locCup S).P i' j' k' h' (0 : (stdCx S dimLoc).X i') (0 : (stdCx S dimLoc).X j')
    rw [map_zero]
  hU _ _ _ _ := 0
  isotropy₂ i i₁ j j₁ h hi hj u v := by
    have hc : ¬ (i = 0 ∧ j = 1) := fun hij => by omega
    simp [locCup_P, locCupP, hc]
    exact ⟨0, rfl⟩
  isotropy₃ i i₁ j j₁ k k₁ h hi hj hk h3 u v := by
    have hc : ¬ (i = 0 ∧ j = 1) := fun hij => by omega
    simp [locCup_P, locCupP, hc, stdCx_d_apply]
    rfl

/-- **Non-vacuity: genuine Selmer pairing data over `τ≥2` for the derivative conditions**, although no
untruncated data exist for `locCup` (`exUntruncated_fails`). -/
def exTruncSelPairData : SelPairData (exStrData S) (exRelData S) := (exTrunc S).toSelPairData

end Example

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
