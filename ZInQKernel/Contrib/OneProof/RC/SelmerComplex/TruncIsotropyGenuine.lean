import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.TruncIsotropy
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# Lane RC26 (round 4): truncated isotropy data for the genuine Selmer complexes

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3456, the derived Kummer
step at tex 3443–3450), (4.3) at tex 3458–3463, and tex 3829–3835 (the hypotheses of Selmer
duality: orthogonal local diagrams with isotropy homotopies); Nekovář, *Selmer complexes*
(Astérisque 310, 2006), 6.1.2–6.3.4 (pp. 135–143): Nekovář's local products land in
`τ_{≥2} C^•_cont(G_v, J(1))` (6.2.1.3, 6.3.1: `C_3 = ⊕_v τ_{≥2} C(G_v, J(1))`), and only a
null-homotopy **after this truncation** is required.

The round-1 `IsotropyData` asks for a null-homotopy of the local product into the full local
complex `C^•_cont(G_v, T)`. For the text's Kummer conditions this is too strong: the derived Kummer
step holds into the `τ≥2` target but fails into the full target when `B(F)^∧₂` has `2`-torsion (the
summand `Hom(Tor₁(M, M), H¹)`), as settled at chain level by the other group
(`Duality.derivedKummerStep_trunc`, `Duality.pairEx_not_nullHomotopic`). This file restates the
isotropy input in Nekovář's convention, matching the other group's `SelPairDataTrunc`
(`SwitchInputs/TruncIsotropy.lean`), which yields `SelPairData` with local target `τ≥2`:

* `TruncIsotropyData ΔA ΔB`: homotopies `h_v` of degree `−1` with the isotropy identity required in
  local target degree two modulo `d(C¹(G_v, T))` (`isotropy₂`) and exactly in degrees `≥ 3`
  (`isotropy₃`);
* `genuinePairDataTrunc ΔA ΔB I : SelPairDataTrunc (selData ΔA) (selData ΔB)`, and its genuine
  Selmer pairing data over `τ≥2`: `genuinePairDataT := (genuinePairDataTrunc …).toSelPairData`;
* **the old full-target data are a special case**: `IsotropyData.toTrunc`, with
  `genuinePairDataTrunc_toTrunc : genuinePairDataTrunc ΔA ΔB I.toTrunc =
  SelPairData.toTrunc (genuinePairData ΔA ΔB I)` (definitional);
* `TruncIsotropyData.ofLowDegree`: the zero homotopies are truncated isotropy data whenever the
  local conditions live in degrees with `i + j ≤ 1` (e.g. a condition in degree `0` against one in
  degrees `0, 1`, the shape of the text's derivative conditions `D⁰ ⊂ D⁰ ⊕ (F ⊕ S)[−1]`) — where the
  untruncated isotropy generally fails (the other group's `exUntruncated_fails`);
* comparison of duality maps: `dualityMaps_eq_of_trace_eq` (the Selmer, local and global duality
  maps only depend on `c, c' ↦ tr(c ∪ c')`), `globalDualityMap_apply`, `localDualityMap_apply`, and
  `dualityMaps_toTrunc`: for full data `Q` and a trace `tr₀`, the three duality maps of
  `(SelPairData.toTrunc Q).toSelPairData` with the descended trace `trT tr₀` **are** those of
  `(Q, tr₀)`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs

universe u

/-! ### Comparison of the duality maps -/

section Compare

variable {S : Type u} [CommRing S] {D D' : SelData S}

/-- **The global duality map, explicitly**: `a ↦ ((b, y) ↦ tr((a, 0, 0) ∪ (b, 0, y)))`
(Nekovář 5.4.2, 6.3.3). -/
theorem globalDualityMap_apply (Q : SelPairData D D') (tr : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (i : ℤ) (a : D.G.X i)
    (b : D'.G.X (3 - i)) (y : D'.L.X (3 - i - 1)) :
    asDual ((globalDualityMap Q tr htr).f i i rfl a) ((b, y) : (compactCx D').X (3 - i)) =
      tr (selCupFun Q i (3 - i) 3 (by omega) (a, 0, 0) (b, 0, y)) :=
  rfl

/-- **The local duality map, explicitly**: `(u, x) ↦ (v ↦ tr((0, u, x) ∪ (0, v, 0)))`
(Nekovář 6.2.2, `u⁻`). -/
theorem localDualityMap_apply (Q : SelPairData D D') (tr : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (i : ℤ) (u : D.U.X i) (x : D.L.X (i - 1))
    (v : D'.U.X (3 - i)) :
    asDual ((localDualityMap Q tr htr).f i i rfl ((u, x) : (locCx D).X i)) v =
      tr (selCupFun Q i (3 - i) 3 (by omega) (0, u, x) (0, v, 0)) :=
  rfl

/-- **The duality maps only depend on the traced cup product**: if two pairing data with traces
give the same values `tr(c ∪ c')` in total degree three, their Selmer, local and global duality
maps coincide. PROVED. -/
theorem dualityMaps_eq_of_trace_eq (Q₁ Q₂ : SelPairData D D')
    (tr₁ : (coneCx Q₁.resE).X 3 →ₗ[S] S) (htr₁ : ∀ z, tr₁ ((coneCx Q₁.resE).d 2 3 rfl z) = 0)
    (tr₂ : (coneCx Q₂.resE).X 3 →ₗ[S] S) (htr₂ : ∀ z, tr₂ ((coneCx Q₂.resE).d 2 3 rfl z) = 0)
    (h : ∀ (i : ℤ) (c : selT D i) (c' : selT D' (3 - i)),
      tr₁ (selCupFun Q₁ i (3 - i) 3 (by omega) c c') = tr₂ (selCupFun Q₂ i (3 - i) 3 (by omega) c c')) :
    GHom.toCC (selmerDualityMap Q₁ tr₁ htr₁) = GHom.toCC (selmerDualityMap Q₂ tr₂ htr₂) ∧
    GHom.toCC (localDualityMap Q₁ tr₁ htr₁) = GHom.toCC (localDualityMap Q₂ tr₂ htr₂) ∧
    GHom.toCC (globalDualityMap Q₁ tr₁ htr₁) = GHom.toCC (globalDualityMap Q₂ tr₂ htr₂) := by
  refine ⟨GHom.toCC_ext fun i c => dualCx_ext fun c' => h i c c', GHom.toCC_ext fun i c =>
    dualCx_ext fun v => ?_, GHom.toCC_ext fun i a => dualCx_ext fun c' => ?_⟩
  · obtain ⟨u, x⟩ := c
    exact h i (0, u, x) (0, v, 0)
  · obtain ⟨b, y⟩ := c'
    exact h i (a, 0, 0) (b, 0, y)

/-- **The full-target data are a special case of the truncated ones**: for Selmer pairing data `Q`
(isotropy into the full local target) and a trace `tr₀` killing coboundaries, the Selmer, local and
global duality maps of the truncated data `(SelPairData.toTrunc Q).toSelPairData` (local target
`τ≥2 E_L`) with the descended trace `trT tr₀` are those of `(Q, tr₀)`. PROVED. -/
theorem dualityMaps_toTrunc (Q : SelPairData D D') (tr₀ : (coneCx Q.resE).X 3 →ₗ[S] S)
    (htr₀ : ∀ z, tr₀ ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    GHom.toCC (selmerDualityMap (SelPairData.toTrunc Q).toSelPairData
        ((SelPairData.toTrunc Q).trT tr₀ htr₀) ((SelPairData.toTrunc Q).trT_kills tr₀ htr₀)) =
      GHom.toCC (selmerDualityMap Q tr₀ htr₀) ∧
    GHom.toCC (localDualityMap (SelPairData.toTrunc Q).toSelPairData
        ((SelPairData.toTrunc Q).trT tr₀ htr₀) ((SelPairData.toTrunc Q).trT_kills tr₀ htr₀)) =
      GHom.toCC (localDualityMap Q tr₀ htr₀) ∧
    GHom.toCC (globalDualityMap (SelPairData.toTrunc Q).toSelPairData
        ((SelPairData.toTrunc Q).trT tr₀ htr₀) ((SelPairData.toTrunc Q).trT_kills tr₀ htr₀)) =
      GHom.toCC (globalDualityMap Q tr₀ htr₀) :=
  dualityMaps_eq_of_trace_eq _ _ _ _ _ _ fun i c c' =>
    trT_selCupFun (SelPairData.toTrunc Q) tr₀ htr₀ i (3 - i) (by omega) c c'

end Compare

/-! ### Truncated isotropy data for the genuine complexes -/

section TruncData

variable (k : Type u) [CommRing k] (GS : Type u) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {A B T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction GS A] [SMulCommClass GS k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul GS A]
  [AddCommGroup B] [Module k B] [DistribMulAction GS B] [SMulCommClass GS k B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul k B] [ContinuousSMul GS B]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : A →ₗ[k] B →ₗ[k] T) (hβ : ∀ (g : GS) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : A × B => β x.1 x.2)

/-- **Nekovář's orthogonality data, truncated** (6.2.1.3, p. 138; 6.3.1: the local product
`prod_v : U_v(A) ⊗ U_v(B) → τ_{≥2} C^•_cont(G_v, T)`): at every place `v` a family `h_v` of degree
`−1` such that `d h_v(x, y) + h_v(dx, y) + (−1)^i h_v(x, dy) = i_v x ∪ i_v y` holds after the
canonical truncation `τ≥2` of the local target: in target degree two modulo the coboundaries
`d(C¹_cont(G_v, T))` (`isotropy₂`; the `d h_v` term of degree one is itself such a coboundary) and
exactly in target degrees `≥ 3` (`isotropy₃`). The per-place form of the other group's
`SelPairDataTrunc`. -/
structure TruncIsotropyData (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) where
  /-- The homotopies `h_v`, of degree `−1`. -/
  h : ∀ (v : ι) (i j l : ℤ), i + j = l + 1 →
    (ΔA.U v).X i →ₗ[k] (ΔB.U v).X j →ₗ[k] (localCx k GS Gv loc T v).X l
  /-- Target degree two, modulo the coboundaries `d(C¹_cont(G_v, T))`. -/
  isotropy₂ : ∀ (v : ι) (i i₁ j j₁ : ℤ) (hh : i + j = 2) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (x : (ΔA.U v).X i) (y : (ΔB.U v).X j),
    h v i₁ j 2 (by omega) ((ΔA.U v).d i i₁ hi x) y +
        sgn i • h v i j₁ 2 (by omega) x ((ΔB.U v).d j j₁ hj y) -
      (localPair k GS Gv loc β hβ hβc v).P i j 2 hh ((ΔA.i v).f i i rfl x) ((ΔB.i v).f j j rfl y) ∈
      LinearMap.range ((localCx k GS Gv loc T v).d 1 2 rfl)
  /-- Target degrees `≥ 3`, exactly. -/
  isotropy₃ : ∀ (v : ι) (i i₁ j j₁ l l₁ : ℤ) (hh : i + j = l + 1) (hi : i + 1 = i₁)
    (hj : j + 1 = j₁) (hl : l + 1 = l₁), 3 ≤ l₁ → ∀ (x : (ΔA.U v).X i) (y : (ΔB.U v).X j),
    (localCx k GS Gv loc T v).d l l₁ hl (h v i j l hh x y) +
        h v i₁ j l₁ (by omega) ((ΔA.U v).d i i₁ hi x) y +
        sgn i • h v i j₁ l₁ (by omega) x ((ΔB.U v).d j j₁ hj y) =
      (localPair k GS Gv loc β hβ hβc v).P i j l₁ (by omega) ((ΔA.i v).f i i rfl x)
        ((ΔB.i v).f j j rfl y)

variable {k GS Gv loc β hβ hβc}

/-- **Untruncated isotropy data are truncated isotropy data** (the round-1 `IsotropyData`, a
null-homotopy into the full local complex, induces one into `τ≥2`). PROVED. -/
def IsotropyData.toTrunc {ΔA : LocalConditions k GS Gv loc A} {ΔB : LocalConditions k GS Gv loc B}
    (I : IsotropyData k GS Gv loc β hβ hβc ΔA ΔB) :
    TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB where
  h := I.h
  isotropy₂ v i i₁ j j₁ hh hi hj x y := by
    have hiso := I.isotropy v i i₁ j j₁ 1 2 (by omega) hi hj rfl x y
    refine ⟨-(I.h v i j 1 (by omega) x y), ?_⟩
    rw [map_neg, ← hiso]
    abel
  isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl _ x y := I.isotropy v i i₁ j j₁ l l₁ hh hi hj hl x y

variable (k GS Gv loc β hβ hβc)

/-- **The genuine cup-product data with truncated isotropy** (Nekovář 6.3.1 with
`C_3 = ⊕_v τ_{≥2} C(G_v, T)`): the global and local cup products of continuous cochains, the
restriction `res_S`, its compatibility with cup products (PROVED), and the truncated isotropy
homotopies — an instance of the other group's `SelPairDataTrunc`. -/
def genuinePairDataTrunc (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB) :
    SelPairDataTrunc (selData k GS Gv loc A ΔA) (selData k GS Gv loc B ΔB) where
  E := globalCx k GS T
  EL := localSumCx k GS Gv loc T
  resE := resS k GS Gv loc T
  cupG := globalPair k GS β hβ hβc
  cupL := localSumPair k GS Gv loc β hβ hβc
  compat i j l i' j' l' h h' hi hj hl a b := by
    subst hi hj hl
    funext v
    exact natF_natPairP _ _ _ _ _ (fun p q n hpq x y => res_cup k GS Gv loc β hβc v p q n hpq x y)
      i j l h a b
  hU i j l h := LinearMap.mk₂ k (fun x y v => I.h v i j l h (x v) (y v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact LinearMap.map_smul₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun _ _ _ => by funext v; exact map_smul _ _ _)
  isotropy₂ i i₁ j j₁ h hi hj x y := by
    choose w hw using fun v => I.isotropy₂ v i i₁ j j₁ h hi hj (x v) (y v)
    exact ⟨fun v => w v, funext fun v => hw v⟩
  isotropy₃ i i₁ j j₁ l l₁ h hi hj hl h3 x y := by
    funext v
    exact I.isotropy₃ v i i₁ j j₁ l l₁ h hi hj hl h3 (x v) (y v)

/-- **The genuine Selmer pairing data over `τ≥2`** (Nekovář's convention, 6.3.1): the other
group's `SelPairDataTrunc.toSelPairData` of `genuinePairDataTrunc`, with local target
`τ≥2 ⊕_v C^•_cont(G_v, T)`. -/
abbrev genuinePairDataT (ΔA : LocalConditions k GS Gv loc A) (ΔB : LocalConditions k GS Gv loc B)
    (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB) :
    SelPairData (selData k GS Gv loc A ΔA) (selData k GS Gv loc B ΔB) :=
  (genuinePairDataTrunc k GS Gv loc β hβ hβc ΔA ΔB I).toSelPairData

/-- **The round-1 data are the special case of full-target isotropy**: the truncated data of
`I.toTrunc` are the other group's truncation `SelPairData.toTrunc` of the round-1
`genuinePairData`. PROVED (definitional). -/
theorem genuinePairDataTrunc_toTrunc (ΔA : LocalConditions k GS Gv loc A)
    (ΔB : LocalConditions k GS Gv loc B) (I : IsotropyData k GS Gv loc β hβ hβc ΔA ΔB) :
    genuinePairDataTrunc k GS Gv loc β hβ hβc ΔA ΔB I.toTrunc =
      SelPairData.toTrunc (genuinePairData k GS Gv loc β hβ hβc ΔA ΔB I) :=
  rfl

variable {k GS Gv loc β hβ hβc}

/-- **The zero homotopies are truncated isotropy data for conditions of low total degree**: if at
every place, for all degrees with `i + j ≥ 2`, the degree-`i` term of `U_v(A)` or the degree-`j` term
of `U_v(B)` vanishes, then the local product lands in degrees `≤ 1` and is zero after `τ≥2`. This
covers a condition in degree `0` against one in degrees `0, 1` — the shape of the text's derivative
conditions `D⁰ ⊂ D⁰ ⊕ (F ⊕ S)[−1]` (tex 5068–5072) and of the `H⁰` condition against the unramified
condition — where the untruncated isotropy generally fails. PROVED. -/
def TruncIsotropyData.ofLowDegree {ΔA : LocalConditions k GS Gv loc A}
    {ΔB : LocalConditions k GS Gv loc B}
    (hdeg : ∀ (v : ι) (i j : ℤ), 2 ≤ i + j →
      Subsingleton ((ΔA.U v).X i) ∨ Subsingleton ((ΔB.U v).X j)) :
    TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB where
  h _ _ _ _ _ := 0
  isotropy₂ v i i₁ j j₁ hh hi hj x y := by
    have hP : (localPair k GS Gv loc β hβ hβc v).P i j 2 hh ((ΔA.i v).f i i rfl x)
        ((ΔB.i v).f j j rfl y) = 0 := by
      rcases hdeg v i j (by omega) with hs | hs
      · rw [Subsingleton.elim x 0]; simp
      · rw [Subsingleton.elim y 0]; simp
    rw [hP]
    refine ⟨0, ?_⟩
    simp
  isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl h3 x y := by
    have hP : (localPair k GS Gv loc β hβ hβc v).P i j l₁ (by omega) ((ΔA.i v).f i i rfl x)
        ((ΔB.i v).f j j rfl y) = 0 := by
      rcases hdeg v i j (by omega) with hs | hs
      · rw [Subsingleton.elim x 0]; simp
      · rw [Subsingleton.elim y 0]; simp
    rw [hP]
    simp

/-- **Non-vacuity**: the zero homotopies on the strict conditions (both sides), as truncated
isotropy data (also `IsotropyData.toTrunc` of the round-1 `strictIsotropy`). -/
def strictTruncIsotropy :
    TruncIsotropyData k GS Gv loc β hβ hβc (strictConditions k GS Gv loc A)
      (strictConditions k GS Gv loc B) :=
  TruncIsotropyData.ofLowDegree fun _ _ _ _ => Or.inl (show Subsingleton (PUnit) from inferInstance)

end TruncData

end ZInQ.Manuscript.RC.SelmerComplex
