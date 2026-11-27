import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest

/-!
# Lane RC2: a non-vacuity witness for the coefficient rules (forest weights)

This file is **not part of the manuscript**. It shows that the hypotheses `CoefficientRules`
(Lemma `ex:sec7-coefficient-rules`, tex 2102–2136) and the terminal hypotheses of the address
lemmas (tex 2209–2220, with the zero-total packets of App G, tex 10587–10623) are satisfiable, so
that the lemmas assuming them are not vacuous.

Construction (zero sign coordinate `ε = 0`, so compatible configurations have symmetric bits):
for an additive group `L` and `φ : L → ZMod 2` with `φ 0 = 0`, the bit graph of `Γ` has the pairs of
distinct vertices with bit one, and
`forestSymbol φ Γ = ∑_{S ⊆ E(Γ) forest} ∏_{blocks B of S} φ (∑_{v ∈ B} t v)`.

* Graph dependence: forests and block types are transported along the isomorphism.
* Contraction: deletion–contraction. The forest symbol is the forest polynomial
  `∑_{S forest} w(S) ∏_{e ∈ S} x_e` evaluated at the bits; its difference in the bit of `vw` is the
  sum over forests through `vw`, and these correspond to forests of `Γ/(v,w)`, where the parallel
  bits `vb`, `wb` merge into the bit `z_vb + z_wb` (an expansion of products of fibre sums; two
  parallel pairs never lie in one forest through `vw`).
* Primary isolation: an isolated vertex of type zero is its own block, of weight `φ 0 = 0`.

The filtered symbol (total type zero) also satisfies the rules; over `ZMod 2` with `φ = id` its
minimum seed is two vertices of type one. Fed into `packet_terminals`, it gives explicit inputs for
the one- and two-symbol address lemmas.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

section

variable {L : Type*} [AddCommGroup L]

/-- The bit graph of a configuration: the pairs of distinct vertices whose residue bit is one
(read with the zero sign coordinate, tex 2015–2041). Helper definition of the non-vacuity witness,
not part of the manuscript. -/
def bitEdges (Γ : Config L) : Finset (Sym2 ℕ) :=
  ((Γ.V ×ˢ Γ.V).filter (fun p => p.1 ≠ p.2 ∧ Γ.z p.1 p.2 = 1)).image (fun p => s(p.1, p.2))

open Classical in
/-- Weight of a pair set `S` on `V`: the product, over the blocks of `S`, of `φ` of the summed
block type, i.e. `∏ φ` over the types of `Γ.contractBy S` (tex 2050–2054, 2181–2185). Helper
definition of the non-vacuity witness, not part of the manuscript. -/
noncomputable def blockWeight (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L)
    (S : Finset (Sym2 ℕ)) : ZMod 2 :=
  ∏ r ∈ V.image (rep V S), φ (∑ u ∈ V.filter (fun u => rep V S u = r), t u)

open Classical in
/-- **The forest symbol** (non-vacuity witness for the coefficient rules of tex 2102–2136, not part
of the manuscript): the sum, over the forests `S` contained in the bit graph, of the product over
the blocks of `S` of `φ` of the summed block type. -/
noncomputable def forestSymbol (φ : L → ZMod 2) (Γ : Config L) : ZMod 2 :=
  ∑ S ∈ (bitEdges Γ).powerset.filter (fun S => IsForest Γ.V S), blockWeight φ Γ.V Γ.t S

namespace WitnessAux

open ForestAux

/-- Membership of an explicit pair in the pairs of a vertex set (tex 2209–2219). Kind: PROVED
(helper). -/
theorem mem_pairs_mk {V : Finset ℕ} {x y : ℕ} : s(x, y) ∈ pairs V ↔ x ∈ V ∧ y ∈ V ∧ x ≠ y := by
  rw [mem_pairs]
  constructor
  · rintro ⟨v, w, hv, hw, hvw, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hv, hw, hvw⟩
    · exact ⟨hw, hv, Ne.symm hvw⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, hxy, rfl⟩

/-- Injectivity on a set with one more point, in cardinality form (tex 2119–2129). Kind: PROVED
(helper). -/
theorem inj_insert_iff {α β : Type*} [DecidableEq α] [DecidableEq β] (μ : α → β) {S : Finset α}
    {p₀ : α} (h : p₀ ∉ S) :
    ((insert p₀ S).image μ).card = (insert p₀ S).card ↔
      (S.image μ).card = S.card ∧ ∀ p ∈ S, μ p ≠ μ p₀ := by
  rw [Finset.card_image_iff, Finset.card_image_iff, Finset.coe_insert,
    Set.injOn_insert (by simpa using h)]
  simp only [Set.mem_image, Finset.mem_coe, not_exists, not_and]

/-- Expansion of a polynomial in fibre sums: for `μ : α → β`, substituting `x' q = ∑_{μ p = q} x p`
gives the sum over the subsets on which `μ` is injective. This is the algebra behind the merging of
parallel bits in the contraction rule (tex 2119–2129). Kind: PROVED (helper). -/
theorem sum_powerset_prod_fiber {α β R : Type*} [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (μ : α → β) (x : α → R) : ∀ (P : Finset α) (Q : Finset β) (c : Finset β → R),
    P.image μ ⊆ Q →
    ∑ T ∈ Q.powerset, c T * ∏ q ∈ T, (∑ p ∈ P.filter (fun p => μ p = q), x p) =
    ∑ S ∈ P.powerset.filter (fun S => (S.image μ).card = S.card), c (S.image μ) * ∏ p ∈ S, x p := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih => ?_
  intro Q c hPQ
  rcases P.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [Finset.filter_empty, Finset.sum_empty, Finset.powerset_empty]
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_filter, Finset.sum_singleton, ite_eq_left (by simp)]
      simp
    · intro T _ hT
      obtain ⟨q, hq⟩ := Finset.nonempty_of_ne_empty hT
      rw [Finset.prod_eq_zero hq rfl, mul_zero]
    · intro h; exact absurd (Finset.empty_mem_powerset Q) h
  set q₀ := μ p₀ with hq₀
  set P₁ := P.erase p₀ with hP₁def
  set P₂ := P₁.filter (fun p => μ p ≠ q₀) with hP₂def
  have hp₀P₁ : p₀ ∉ P₁ := Finset.notMem_erase p₀ P
  have hq₀Q : q₀ ∈ Q := hPQ (Finset.mem_image_of_mem μ hp₀)
  have hP₁ : P₁ ⊂ P := Finset.erase_ssubset hp₀
  have hP₂ : P₂ ⊂ P := lt_of_le_of_lt (Finset.filter_subset _ _) hP₁
  have ih1 := ih P₁ hP₁ Q c
    (subset_trans (Finset.image_subset_image (Finset.erase_subset _ _)) hPQ)
  have ih2 := ih P₂ hP₂ (Q.erase q₀) (fun T => c (insert q₀ T)) (by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    have hp' := Finset.mem_filter.1 hp
    exact Finset.mem_erase.2 ⟨hp'.2,
      hPQ (Finset.mem_image_of_mem μ (Finset.mem_of_mem_erase hp'.1))⟩)
  -- fibres away from `q₀`
  have hfibP : ∀ q, q ≠ q₀ → P.filter (fun p => μ p = q) = P₂.filter (fun p => μ p = q) := by
    intro q hq
    ext p
    simp only [Finset.mem_filter, P₂, P₁, Finset.mem_erase]
    constructor
    · rintro ⟨hp, rfl⟩
      refine ⟨⟨⟨fun h => hq (by rw [h]), hp⟩, hq⟩, rfl⟩
    · rintro ⟨⟨⟨-, hp⟩, -⟩, rfl⟩
      exact ⟨hp, rfl⟩
  have hfibP₁ : ∀ q, q ≠ q₀ → P₁.filter (fun p => μ p = q) = P₂.filter (fun p => μ p = q) := by
    intro q hq
    ext p
    simp only [Finset.mem_filter, P₂]
    constructor
    · rintro ⟨hp, rfl⟩; exact ⟨⟨hp, hq⟩, rfl⟩
    · rintro ⟨⟨hp, -⟩, rfl⟩; exact ⟨hp, rfl⟩
  have hfib0 : ∑ p ∈ P.filter (fun p => μ p = q₀), x p =
      x p₀ + ∑ p ∈ P₁.filter (fun p => μ p = q₀), x p := by
    have : P.filter (fun p => μ p = q₀) = insert p₀ (P₁.filter (fun p => μ p = q₀)) := by
      rw [hP₁def, Finset.filter_erase, Finset.insert_erase
        (show p₀ ∈ P.filter (fun p => μ p = q₀) from Finset.mem_filter.2 ⟨hp₀, rfl⟩)]
    rw [this, Finset.sum_insert (fun h => hp₀P₁ (Finset.mem_filter.1 h).1)]
  -- splitting the left side along `q₀`
  have hsplit : ∀ (P' : Finset α), P' ⊆ P → (∀ q, q ≠ q₀ →
      P'.filter (fun p => μ p = q) = P₂.filter (fun p => μ p = q)) →
      ∑ T ∈ Q.powerset, c T * ∏ q ∈ T, (∑ p ∈ P'.filter (fun p => μ p = q), x p) =
      ∑ T ∈ (Q.erase q₀).powerset, c T * ∏ q ∈ T, (∑ p ∈ P₂.filter (fun p => μ p = q), x p) +
      (∑ p ∈ P'.filter (fun p => μ p = q₀), x p) *
        ∑ T ∈ (Q.erase q₀).powerset, c (insert q₀ T) *
          ∏ q ∈ T, (∑ p ∈ P₂.filter (fun p => μ p = q), x p) := by
    intro P' _ hfib
    have key := Finset.sum_powerset_insert (Finset.notMem_erase q₀ Q)
      (fun T => c T * ∏ q ∈ T, (∑ p ∈ P'.filter (fun p => μ p = q), x p))
    rw [Finset.insert_erase hq₀Q] at key
    rw [key, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro T hT
      congr 1
      apply Finset.prod_congr rfl
      intro q hq
      have hqq : q ≠ q₀ := fun h => Finset.notMem_erase q₀ Q
        (h ▸ (Finset.mem_powerset.1 hT hq))
      rw [hfib q hqq]
    · apply Finset.sum_congr rfl
      intro T hT
      have hq₀T : q₀ ∉ T := fun h => Finset.notMem_erase q₀ Q (Finset.mem_powerset.1 hT h)
      rw [Finset.prod_insert hq₀T]
      have : ∏ q ∈ T, (∑ p ∈ P'.filter (fun p => μ p = q), x p) =
          ∏ q ∈ T, (∑ p ∈ P₂.filter (fun p => μ p = q), x p) := by
        apply Finset.prod_congr rfl
        intro q hq
        rw [hfib q (fun h => hq₀T (h ▸ hq))]
      rw [this]
      ring
  rw [hsplit P le_rfl hfibP, hfib0]
  have h1 := hsplit P₁ (Finset.erase_subset _ _) hfibP₁
  rw [h1] at ih1
  -- the right side
  have hP : P = insert p₀ P₁ := (Finset.insert_erase hp₀).symm
  have hR : ∑ S ∈ P.powerset.filter (fun S => (S.image μ).card = S.card),
        c (S.image μ) * ∏ p ∈ S, x p =
      ∑ S ∈ P₁.powerset.filter (fun S => (S.image μ).card = S.card),
        c (S.image μ) * ∏ p ∈ S, x p +
      x p₀ * ∑ S ∈ P₂.powerset.filter (fun S => (S.image μ).card = S.card),
        c (insert q₀ (S.image μ)) * ∏ p ∈ S, x p := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, hP,
      Finset.sum_powerset_insert hp₀P₁]
    congr 1
    rw [Finset.mul_sum]
    symm
    let F : Finset α → R := fun S => if (S.image μ).card = S.card ∧ ∀ p ∈ S, μ p ≠ q₀ then
      x p₀ * (c (insert q₀ (S.image μ)) * ∏ p ∈ S, x p) else 0
    calc (∑ S ∈ P₂.powerset, x p₀ * if (S.image μ).card = S.card then
            c (insert q₀ (S.image μ)) * ∏ p ∈ S, x p else 0)
        = ∑ S ∈ P₂.powerset, F S := by
          apply Finset.sum_congr rfl
          intro S hS
          have hall : ∀ p ∈ S, μ p ≠ q₀ := fun p hp =>
            (Finset.mem_filter.1 (Finset.mem_powerset.1 hS hp)).2
          by_cases hinj : (S.image μ).card = S.card
          · simp only [F, ite_eq_left hinj, ite_eq_left (And.intro hinj hall)]
          · simp only [F, ite_eq_right hinj, mul_zero]
            rw [ite_eq_right (fun h => hinj h.1)]
      _ = ∑ S ∈ P₁.powerset, F S := by
          apply Finset.sum_subset
          · intro S hS
            exact Finset.mem_powerset.2
              ((Finset.mem_powerset.1 hS).trans (Finset.filter_subset _ _))
          · intro S hS hS2
            have hnot : ¬ ∀ p ∈ S, μ p ≠ q₀ := by
              intro hall
              apply hS2
              exact Finset.mem_powerset.2 (fun p hp => Finset.mem_filter.2
                ⟨Finset.mem_powerset.1 hS hp, hall p hp⟩)
            simp only [F]
            rw [ite_eq_right (fun h => hnot h.2)]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro S hS
          have hp₀S : p₀ ∉ S := fun h => hp₀P₁ (Finset.mem_powerset.1 hS h)
          simp only [F]
          by_cases h : (S.image μ).card = S.card ∧ ∀ p ∈ S, μ p ≠ q₀
          · rw [ite_eq_left h, ite_eq_left ((inj_insert_iff μ hp₀S).2 h), Finset.image_insert,
              Finset.prod_insert hp₀S]
            ring
          · rw [ite_eq_right h, ite_eq_right (fun h' => h ((inj_insert_iff μ hp₀S).1 h'))]
  rw [hR, ← ih1, ih2]
  ring

open Classical in
/-- Coefficient of the forest polynomial: the forest weight if `S` is a forest on `V`, else zero
(tex 2181–2185, 10627–10633). Helper definition of the non-vacuity witness. -/
noncomputable def coef (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L) (S : Finset (Sym2 ℕ)) :
    ZMod 2 :=
  if IsForest V S then blockWeight φ V t S else 0

/-- Weight of a vertex labelling: the product of `φ` over the summed types of its fibres (tex
2050–2054). Helper definition of the non-vacuity witness. -/
noncomputable def lw (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L) (f : ℕ → ℕ) : ZMod 2 :=
  ∏ r ∈ V.image f, φ (∑ u ∈ V.filter (fun u => f u = r), t u)

/-- The forest weight is the weight of the labelling by block representatives (tex 2181–2185).
Kind: PROVED (helper). -/
theorem blockWeight_eq_lw (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L) (S : Finset (Sym2 ℕ)) :
    blockWeight φ V t S = lw φ V t (rep V S) := rfl

/-- The labelling weight depends only on the induced partition (tex 2181–2185). Kind: PROVED
(helper). -/
theorem lw_congr (φ : L → ZMod 2) {V : Finset ℕ} (t : ℕ → L) {f h : ℕ → ℕ}
    (H : ∀ u ∈ V, ∀ u' ∈ V, f u = f u' ↔ h u = h u') : lw φ V t f = lw φ V t h := by
  obtain ⟨e, ht, -⟩ := cmap_iso (Γ := (⟨V, t, fun _ _ => 0⟩ : Config L)) H
  have h1 : lw φ V t f = ∏ r : (cmap (⟨V, t, fun _ _ => 0⟩ : Config L) f).V,
      φ ((cmap (⟨V, t, fun _ _ => 0⟩ : Config L) f).t r) :=
    (Finset.prod_coe_sort (cmap (⟨V, t, fun _ _ => 0⟩ : Config L) f).V
      (fun r => φ ((cmap (⟨V, t, fun _ _ => 0⟩ : Config L) f).t r))).symm
  have h2 : lw φ V t h = ∏ r : (cmap (⟨V, t, fun _ _ => 0⟩ : Config L) h).V,
      φ ((cmap (⟨V, t, fun _ _ => 0⟩ : Config L) h).t r) :=
    (Finset.prod_coe_sort (cmap (⟨V, t, fun _ _ => 0⟩ : Config L) h).V
      (fun r => φ ((cmap (⟨V, t, fun _ _ => 0⟩ : Config L) h).t r))).symm
  rw [h1, h2]
  exact Fintype.prod_equiv e _ _ (fun r => by rw [ht r])

/-- Labelling weight after pushing the vertices forward along a map that sums the types (tex
2050–2054). Kind: PROVED (helper). -/
theorem lw_map (φ : L → ZMod 2) {V : Finset ℕ} {t t' : ℕ → L} (g h : ℕ → ℕ)
    (ht' : ∀ c ∈ V.image g, t' c = ∑ u ∈ V.filter (fun u => g u = c), t u) :
    lw φ (V.image g) t' h = lw φ V t (h ∘ g) := by
  unfold lw
  rw [Finset.image_image]
  apply Finset.prod_congr rfl
  intro r _
  congr 1
  rw [Finset.sum_congr rfl (fun c hc => ht' c (Finset.mem_filter.1 hc).1)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := V.filter (fun u => (h ∘ g) u = r))
    (t := (V.image g).filter (fun c => h c = r)) (g := g)]
  · apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext u
    simp only [Finset.mem_filter, Function.comp_apply]
    have hc' := (Finset.mem_filter.1 hc).2
    constructor
    · rintro ⟨hu, rfl⟩; exact ⟨⟨hu, hc'⟩, rfl⟩
    · rintro ⟨⟨hu, -⟩, rfl⟩; exact ⟨hu, rfl⟩
  · intro u hu
    simp only [Finset.mem_filter, Function.comp_apply] at hu ⊢
    exact ⟨Finset.mem_image_of_mem g hu.1, hu.2⟩

/-- Connectivity is carried along a vertex map (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_map {S : Finset (Sym2 ℕ)} (g : ℕ → ℕ) {a b : ℕ} (h : conn S a b) :
    conn (S.image (Sym2.map g)) (g a) (g b) := by
  unfold conn at *
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Finset.mem_image.2 ⟨_, hxy, Sym2.map_mk g x y⟩)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Connectivity is reflected by a vertex map whose fibres are already connected (tex 2181–2185).
Kind: PROVED (helper). -/
theorem conn_of_conn_map {S : Finset (Sym2 ℕ)} {g : ℕ → ℕ} {V : Finset ℕ} (hS : S ⊆ pairs V)
    (hg : ∀ x ∈ V, ∀ y ∈ V, g x = g y → conn S x y) {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V)
    (h : conn (S.image (Sym2.map g)) (g a) (g b)) : conn S a b := by
  let R : ℕ → ℕ → Prop := fun c d => c = d ∨ ∃ x ∈ V, ∃ y ∈ V, g x = c ∧ g y = d ∧ conn S x y
  have hR : Equivalence R := by
    refine ⟨fun c => Or.inl rfl, fun {c d} hcd => ?_, fun {c d e} hcd hde => ?_⟩
    · rcases hcd with rfl | ⟨x, hx, y, hy, rfl, rfl, hc⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hy, x, hx, rfl, rfl, conn_symm hc⟩
    · rcases hcd with rfl | ⟨x, hx, y, hy, rfl, rfl, h1⟩
      · exact hde
      · rcases hde with rfl | ⟨y', hy', z, hz, hyy', rfl, h2⟩
        · exact Or.inr ⟨x, hx, y, hy, rfl, rfl, h1⟩
        · exact Or.inr ⟨x, hx, z, hz, rfl, rfl,
            conn_trans h1 (conn_trans (hg y hy y' hy' hyy'.symm) h2)⟩
  have hmono : Relation.EqvGen R (g a) (g b) := by
    refine Relation.EqvGen.mono ?_ _ _ h
    intro c d hcd
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 hcd
    induction p using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk] at hpe
      obtain ⟨hx, hy, -⟩ := mem_pairs_mk.1 (hS hp)
      rcases Sym2.eq_iff.1 hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨x, hx, y, hy, h1, h2, conn_of_mem hp⟩
      · exact Or.inr ⟨y, hy, x, hx, h2, h1, conn_symm (conn_of_mem hp)⟩
  rcases hR.eqvGen_iff.1 hmono with h' | ⟨x, hx, y, hy, hxa, hyb, hc⟩
  · exact hg a ha b hb h'
  · exact conn_trans (hg a ha x hx hxa.symm) (conn_trans hc (hg y hy b hb hyb))

/-- A loop does not change connectivity (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_insert_loop {T : Finset (Sym2 ℕ)} {c a b : ℕ} :
    conn (insert s(c, c) T) a b ↔ conn T a b := by
  rw [conn_insert_iff]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact conn_trans h1 h2
    · exact conn_trans h1 h2
  · exact Or.inl

/-- Block counts agree when connectivity is transferred along a vertex map (tex 2181–2185). Kind:
PROVED (helper). -/
theorem ncomp_transfer {V : Finset ℕ} {g : ℕ → ℕ} {S S' : Finset (Sym2 ℕ)}
    (hconn : ∀ a ∈ V, ∀ b ∈ V, conn S a b ↔ conn S' (g a) (g b)) :
    ncomp V S = ncomp (V.image g) S' := by
  have hgV : ∀ a ∈ V, g a ∈ V.image g := fun a ha => Finset.mem_image_of_mem g ha
  have hpart : ∀ u ∈ V, ∀ u' ∈ V,
      rep V S u = rep V S u' ↔ (rep (V.image g) S' ∘ g) u = (rep (V.image g) S' ∘ g) u' := by
    intro u hu u' hu'
    rw [rep_eq_iff hu hu', Function.comp_apply, Function.comp_apply,
      rep_eq_iff (hgV u hu) (hgV u' hu')]
    exact hconn u hu u' hu'
  unfold ncomp
  rw [card_image_eq_of_part hpart, ← Finset.image_image]

/-- Forest coefficients are transferred along a vertex map that preserves connectivity, sums the
types and has the right cardinalities (tex 2050–2054, 2181–2185). Kind: PROVED (helper). -/
theorem coef_transfer (φ : L → ZMod 2) {V : Finset ℕ} {t t' : ℕ → L} {g : ℕ → ℕ}
    {S S' : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V) (hS' : S' ⊆ pairs (V.image g))
    (hconn : ∀ a ∈ V, ∀ b ∈ V, conn S a b ↔ conn S' (g a) (g b))
    (ht' : ∀ c ∈ V.image g, t' c = ∑ u ∈ V.filter (fun u => g u = c), t u)
    (hcard : S.card + (V.image g).card = S'.card + V.card) :
    coef φ V t S = coef φ (V.image g) t' S' := by
  have hgV : ∀ a ∈ V, g a ∈ V.image g := fun a ha => Finset.mem_image_of_mem g ha
  have hpart : ∀ u ∈ V, ∀ u' ∈ V,
      rep V S u = rep V S u' ↔ (rep (V.image g) S' ∘ g) u = (rep (V.image g) S' ∘ g) u' := by
    intro u hu u' hu'
    rw [rep_eq_iff hu hu', Function.comp_apply, Function.comp_apply,
      rep_eq_iff (hgV u hu) (hgV u' hu')]
    exact hconn u hu u' hu'
  have hncomp := ncomp_transfer hconn
  have hW : blockWeight φ V t S = blockWeight φ (V.image g) t' S' := by
    rw [blockWeight_eq_lw, blockWeight_eq_lw, lw_congr φ t hpart, lw_map φ g _ ht']
  have hF : IsForest V S ↔ IsForest (V.image g) S' := by
    unfold IsForest
    constructor
    · rintro ⟨-, h⟩; exact ⟨hS', by omega⟩
    · rintro ⟨-, h⟩; exact ⟨hS, by omega⟩
  unfold coef
  by_cases h : IsForest V S
  · rw [ite_eq_left h, ite_eq_left (hF.1 h), hW]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hF.2 h'))]

/-- A pair set whose image loses a pair, with connectivity transferred, is not a forest: two
parallel pairs close a cycle through the contracted pair (tex 10627–10633). Kind: PROVED (helper).
-/
theorem not_isForest_of_card {V : Finset ℕ} {g : ℕ → ℕ} {S S' : Finset (Sym2 ℕ)}
    (hS' : S' ⊆ pairs (V.image g))
    (hconn : ∀ a ∈ V, ∀ b ∈ V, conn S a b ↔ conn S' (g a) (g b))
    (hcard : S'.card + V.card < S.card + (V.image g).card) : ¬ IsForest V S := by
  intro hF
  have hncomp := ncomp_transfer hconn
  have h1 := card_add_ncomp_ge hS'
  have h2 := hF.2
  omega


/-- The forest polynomial on `V` with types `t`, evaluated at the bits `x` (tex 2102–2136). Helper
definition of the non-vacuity witness. -/
noncomputable def polyForm (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L) (x : Sym2 ℕ → ZMod 2) :
    ZMod 2 :=
  ∑ S ∈ (pairs V).powerset, coef φ V t S * ∏ e ∈ S, x e

/-- Indicator function of the bit graph (tex 2015–2041). Helper definition of the non-vacuity
witness. -/
def bitFn (Γ : Config L) (e : Sym2 ℕ) : ZMod 2 :=
  if e ∈ bitEdges Γ then 1 else 0

omit [AddCommGroup L] in
/-- Membership of an explicit pair in the bit graph (tex 2015–2041). Kind: PROVED (helper). -/
theorem mem_bitEdges_mk {Γ : Config L} {a b : ℕ} :
    s(a, b) ∈ bitEdges Γ ↔ a ∈ Γ.V ∧ b ∈ Γ.V ∧ a ≠ b ∧ (Γ.z a b = 1 ∨ Γ.z b a = 1) := by
  constructor
  · intro he
    obtain ⟨⟨c, d⟩, hcd, he⟩ := Finset.mem_image.1 he
    simp only [Finset.mem_filter, Finset.mem_product] at hcd
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hcd.1.1, hcd.1.2, hcd.2.1, Or.inl hcd.2.2⟩
    · exact ⟨hcd.1.2, hcd.1.1, Ne.symm hcd.2.1, Or.inr hcd.2.2⟩
  · rintro ⟨ha, hb, hab, h | h⟩
    · exact Finset.mem_image.2 ⟨(a, b), by simp [ha, hb, hab, h], rfl⟩
    · exact Finset.mem_image.2 ⟨(b, a), by simp [ha, hb, Ne.symm hab, h], Sym2.eq_swap⟩

omit [AddCommGroup L] in
/-- The bit graph consists of pairs of distinct vertices (tex 2015–2041). Kind: PROVED (helper). -/
theorem bitEdges_subset (Γ : Config L) : bitEdges Γ ⊆ pairs Γ.V := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab, -⟩ := mem_bitEdges_mk.1 he
    exact mem_pairs_mk.2 ⟨ha, hb, hab⟩

/-- Values in the two-element field (tex 2037–2041). Kind: PROVED (helper). -/
theorem zmod2_symm_of_add : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
/-- Values in the two-element field (tex 2068–2079). Kind: PROVED (helper). -/
theorem zmod2_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide

/-- With the zero sign coordinate, compatible bits are symmetric (tex 2037–2041). Kind: PROVED
(helper). -/
theorem compat_symm {Γ : Config L} (hΓ : Γ.Compatible 0) {a b : ℕ} (ha : a ∈ Γ.V)
    (hb : b ∈ Γ.V) (hab : a ≠ b) : Γ.z b a = Γ.z a b := by
  have h := hΓ a ha b hb hab
  simp only [AddMonoidHom.zero_apply, mul_zero] at h
  exact zmod2_symm_of_add _ _ h

/-- For compatible bits (zero sign coordinate) the bit graph reads the residue bit (tex 2037–2041).
Kind: PROVED (helper). -/
theorem bitFn_mk {Γ : Config L} (hΓ : Γ.Compatible 0) {a b : ℕ} (ha : a ∈ Γ.V)
    (hb : b ∈ Γ.V) (hab : a ≠ b) : bitFn Γ s(a, b) = Γ.z a b := by
  unfold bitFn
  by_cases h : Γ.z a b = 1
  · rw [ite_eq_left (mem_bitEdges_mk.2 ⟨ha, hb, hab, Or.inl h⟩), h]
  · rw [ite_eq_right (fun h' => by
      obtain ⟨-, -, -, h1 | h1⟩ := mem_bitEdges_mk.1 h'
      · exact h h1
      · rw [compat_symm hΓ ha hb hab] at h1; exact h h1),
      zmod2_eq_zero_of_ne_one _ h]

/-- The vertex map merging `w` into `v` (tex 2050–2054). Helper definition. -/
def mergeMap (v w : ℕ) : ℕ → ℕ := fun u => if u = w then v else u

/-- The vertex set after merging `w` into `v` (tex 2050–2054). Kind: PROVED (helper). -/
theorem image_mergeMap {V : Finset ℕ} {v w : ℕ} (hv : v ∈ V) (hvw : v ≠ w) :
    V.image (mergeMap v w) = V.erase w := by
  ext u
  simp only [Finset.mem_image, Finset.mem_erase, mergeMap]
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a = w
    · rw [ite_eq_left h]; exact ⟨hvw, hv⟩
    · rw [ite_eq_right h]; exact ⟨h, ha⟩
  · rintro ⟨huw, hu⟩
    exact ⟨u, hu, by rw [ite_eq_right huw]⟩

/-- Merging maps the other pairs to pairs of the contraction (tex 2050–2054). Kind: PROVED
(helper). -/
theorem map_mem_pairs_merge {V : Finset ℕ} {v w : ℕ} (hv : v ∈ V) (hvw : v ≠ w) {p : Sym2 ℕ}
    (hp : p ∈ (pairs V).erase s(v, w)) : Sym2.map (mergeMap v w) p ∈ pairs (V.erase w) := by
  induction p using Sym2.ind with
  | _ a b =>
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    obtain ⟨ha, hb, hab⟩ := mem_pairs_mk.1 hp
    rw [Sym2.map_mk, ← image_mergeMap hv hvw]
    refine mem_pairs_mk.2 ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, ?_⟩
    simp only [mergeMap]
    intro h
    apply hne
    by_cases haw : a = w <;> by_cases hbw : b = w
    · exact absurd (haw.trans hbw.symm) hab
    · rw [ite_eq_left haw, ite_eq_right hbw] at h
      subst haw h; exact Sym2.eq_swap
    · rw [ite_eq_right haw, ite_eq_left hbw] at h
      subst hbw h; rfl
    · rw [ite_eq_right haw, ite_eq_right hbw] at h
      exact absurd h hab


/-- The forest symbol is the forest polynomial evaluated at the bits of the configuration (tex
2102–2136). Kind: PROVED (helper). -/
theorem forestSymbol_eq_polyForm (φ : L → ZMod 2) (Γ : Config L) :
    forestSymbol φ Γ = polyForm φ Γ.V Γ.t (bitFn Γ) := by
  unfold forestSymbol polyForm coef
  rw [Finset.sum_filter]
  symm
  refine (Finset.sum_subset (Finset.powerset_mono.2 (bitEdges_subset Γ)) ?_).symm.trans ?_
  · intro S _ hS
    obtain ⟨e, heS, heE⟩ := Finset.not_subset.1 (fun h => hS (Finset.mem_powerset.2 h))
    rw [Finset.prod_eq_zero heS (by unfold bitFn; rw [ite_eq_right heE]), mul_zero]
  · apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.prod_eq_one (fun e he => by
      unfold bitFn; rw [ite_eq_left (Finset.mem_powerset.1 hS he)]), mul_one]

/-- Finite difference of the forest polynomial in one bit: only the forests through that pair
survive (tex 2119–2129). Kind: PROVED (helper). -/
theorem polyForm_add (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L) {e : Sym2 ℕ} (he : e ∈ pairs V)
    (x x₂ : Sym2 ℕ → ZMod 2) (hx : ∀ p ∈ (pairs V).erase e, x₂ p = x p)
    (hxe : x₂ e = x e + 1) :
    polyForm φ V t x + polyForm φ V t x₂ =
      ∑ S ∈ ((pairs V).erase e).powerset, coef φ V t (insert e S) * ∏ p ∈ S, x p := by
  unfold polyForm
  have hP : pairs V = insert e ((pairs V).erase e) := (Finset.insert_erase he).symm
  have hne : e ∉ (pairs V).erase e := Finset.notMem_erase e _
  conv_lhs => rw [hP]
  rw [Finset.sum_powerset_insert hne, Finset.sum_powerset_insert hne]
  have hA : ∑ S ∈ ((pairs V).erase e).powerset, coef φ V t S * ∏ p ∈ S, x₂ p =
      ∑ S ∈ ((pairs V).erase e).powerset, coef φ V t S * ∏ p ∈ S, x p := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.prod_congr rfl (fun p hp => hx p (Finset.mem_powerset.1 hS hp))]
  rw [hA, add_add_add_comm, zmod2_add_self, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have heS : e ∉ S := fun h => hne (Finset.mem_powerset.1 hS h)
  rw [Finset.prod_insert heS, Finset.prod_insert heS, hxe,
    Finset.prod_congr rfl (fun p hp => hx p (Finset.mem_powerset.1 hS hp))]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (x e * (coef φ V t (insert e S) * ∏ p ∈ S, x p)) * h2

/-- Connectivity through the contracted pair versus connectivity of the merged pair set (tex
2050–2054, 2181–2185). Kind: PROVED (helper). -/
theorem conn_contract {V : Finset ℕ} {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V) :
    ∀ a ∈ V, ∀ b ∈ V, conn (insert s(v, w) S) a b ↔
      conn (S.image (Sym2.map (mergeMap v w))) (mergeMap v w a) (mergeMap v w b) := by
  have himg : (insert s(v, w) S).image (Sym2.map (mergeMap v w)) =
      insert s(v, v) (S.image (Sym2.map (mergeMap v w))) := by
    rw [Finset.image_insert, Sym2.map_mk]
    simp [mergeMap, hvw]
  have hS' : insert s(v, w) S ⊆ pairs V :=
    Finset.insert_subset (mem_pairs_mk.2 ⟨hv, hw, hvw⟩) hS
  intro a ha b hb
  constructor
  · intro h
    have := conn_map (mergeMap v w) h
    rwa [himg, conn_insert_loop] at this
  · intro h
    refine conn_of_conn_map hS' ?_ ha hb (by rw [himg, conn_insert_loop]; exact h)
    intro x _ y _ hxy
    have hvw' : conn (insert s(v, w) S) v w := conn_of_mem (Finset.mem_insert_self _ _)
    simp only [mergeMap] at hxy
    by_cases hxw : x = w <;> by_cases hyw : y = w
    · rw [hxw, hyw]; exact conn_refl _ _
    · rw [ite_eq_left hxw, ite_eq_right hyw] at hxy
      rw [hxw, ← hxy]; exact conn_symm hvw'
    · rw [ite_eq_right hxw, ite_eq_left hyw] at hxy
      rw [hyw, hxy]; exact hvw'
    · rw [ite_eq_right hxw, ite_eq_right hyw] at hxy
      rw [hxy]; exact conn_refl _ _

/-- The types of the contraction are fibre sums along the merging map (tex 2050–2054). Kind:
PROVED (helper). -/
theorem type_fiber_merge {V : Finset ℕ} {t : ℕ → L} {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w) : ∀ c ∈ V.image (mergeMap v w), Function.update t v (t v + t w) c =
      ∑ u ∈ V.filter (fun u => mergeMap v w u = c), t u := by
  intro c hc
  rw [image_mergeMap hv hvw] at hc
  obtain ⟨hcw, hcV⟩ := Finset.mem_erase.1 hc
  by_cases hcv : c = v
  · subst hcv
    have : V.filter (fun u => mergeMap c w u = c) = {c, w} := by
      ext u
      simp only [mergeMap, Finset.mem_insert, Finset.mem_singleton]
      grind
    rw [this, Finset.sum_pair hvw, Function.update_self]
  · have : V.filter (fun u => mergeMap v w u = c) = {c} := by
      ext u
      simp only [mergeMap, Finset.mem_singleton]
      grind
    rw [this, Finset.sum_singleton, Function.update_of_ne hcv]

/-- The bits of the contraction are fibre sums of bits along the merging map: the two parallel
bits `vb` and `wb` add (tex 2050–2054). Kind: PROVED (helper). -/
theorem fiber_contract {Γ : Config L} (hΓ : Γ.Compatible 0) {v w : ℕ} (hv : v ∈ Γ.V)
    (hw : w ∈ Γ.V) (hvw : v ≠ w) {q : Sym2 ℕ} (hq : q ∈ pairs (Γ.V.erase w)) :
    ∑ p ∈ ((pairs Γ.V).erase s(v, w)).filter (fun p => Sym2.map (mergeMap v w) p = q),
      bitFn Γ p = bitFn (Γ.contract v w) q := by
  induction q using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mem_pairs_mk.1 hq
    have hΓc := contract_compatible hΓ hv hw
    rw [bitFn_mk hΓc ha hb hab]
    obtain ⟨haw, ha'⟩ := Finset.mem_erase.1 ha
    obtain ⟨hbw, hb'⟩ := Finset.mem_erase.1 hb
    show _ = if a = v then Γ.z v b + Γ.z w b else if b = v then Γ.z a v + Γ.z a w else Γ.z a b
    by_cases hav : a = v
    · subst hav
      have hfib : ((pairs Γ.V).erase s(a, w)).filter
          (fun p => Sym2.map (mergeMap a w) p = s(a, b)) = {s(a, b), s(w, b)} := by
        ext p
        induction p using Sym2.ind with
        | _ c d =>
          simp only [Finset.mem_filter, Finset.mem_erase, mem_pairs_mk, Sym2.map_mk, mergeMap,
            Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, ne_eq]
          grind
      have hne : s(a, b) ≠ s(w, b) := by
        intro h
        rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hvw h1
        · exact hab h1
      rw [hfib, Finset.sum_pair hne, bitFn_mk hΓ ha' hb' hab, bitFn_mk hΓ hw hb' (Ne.symm hbw),
        ite_eq_left rfl]
    · by_cases hbv : b = v
      · subst hbv
        have hfib : ((pairs Γ.V).erase s(b, w)).filter
            (fun p => Sym2.map (mergeMap b w) p = s(a, b)) = {s(a, b), s(a, w)} := by
          ext p
          induction p using Sym2.ind with
          | _ c d =>
            simp only [Finset.mem_filter, Finset.mem_erase, mem_pairs_mk, Sym2.map_mk, mergeMap,
              Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, ne_eq]
            grind
        have hne : s(a, b) ≠ s(a, w) := by
          intro h
          rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact hvw h2
          · exact haw h1
        rw [hfib, Finset.sum_pair hne, bitFn_mk hΓ ha' hb' hab, bitFn_mk hΓ ha' hw haw,
          ite_eq_right hav, ite_eq_left rfl]
      · have hfib : ((pairs Γ.V).erase s(v, w)).filter
            (fun p => Sym2.map (mergeMap v w) p = s(a, b)) = {s(a, b)} := by
          ext p
          induction p using Sym2.ind with
          | _ c d =>
            simp only [Finset.mem_filter, Finset.mem_erase, mem_pairs_mk, Sym2.map_mk, mergeMap,
              Finset.mem_singleton, Sym2.eq_iff, ne_eq]
            grind
        rw [hfib, Finset.sum_singleton, bitFn_mk hΓ ha' hb' hab, ite_eq_right hav,
          ite_eq_right hbv]

/-- Contraction rule for the forest symbol, by deletion–contraction (tex 2119–2129). Kind: PROVED
(helper). -/
theorem forestSymbol_contraction (φ : L → ZMod 2) {Γ : Config L} (hΓ : Γ.Compatible 0)
    {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hvw : v ≠ w) :
    forestSymbol φ Γ + forestSymbol φ (Γ.flip v w) = forestSymbol φ (Γ.contract v w) := by
  have he : s(v, w) ∈ pairs Γ.V := mem_pairs_mk.2 ⟨hv, hw, hvw⟩
  have hΓf : (Γ.flip v w).Compatible 0 := flipBy_compatible hΓ _
  have hx : ∀ p ∈ (pairs Γ.V).erase s(v, w), bitFn (Γ.flip v w) p = bitFn Γ p := by
    intro p hp
    induction p using Sym2.ind with
    | _ a b =>
      obtain ⟨hne, hp'⟩ := Finset.mem_erase.1 hp
      obtain ⟨ha, hb, hab⟩ := mem_pairs_mk.1 hp'
      rw [bitFn_mk hΓf ha hb hab, bitFn_mk hΓ ha hb hab, flip_z hvw]
      have h1 : ¬ (a = v ∧ b = w) := fun h => hne (by rw [h.1, h.2])
      have h2 : ¬ (a = w ∧ b = v) := fun h => hne (by rw [h.1, h.2]; exact Sym2.eq_swap)
      rw [ite_eq_right h1, ite_eq_right h2, add_zero, add_zero]
  have hxe : bitFn (Γ.flip v w) s(v, w) = bitFn Γ s(v, w) + 1 := by
    rw [bitFn_mk hΓf hv hw hvw, bitFn_mk hΓ hv hw hvw, flip_z hvw,
      ite_eq_left (And.intro rfl rfl), ite_eq_right (fun h => hvw h.1), add_zero]
  rw [forestSymbol_eq_polyForm, forestSymbol_eq_polyForm, forestSymbol_eq_polyForm]
  show polyForm φ Γ.V Γ.t (bitFn Γ) + polyForm φ Γ.V Γ.t (bitFn (Γ.flip v w)) =
    polyForm φ (Γ.V.erase w) (Function.update Γ.t v (Γ.t v + Γ.t w)) (bitFn (Γ.contract v w))
  rw [polyForm_add φ Γ.V Γ.t he _ _ hx hxe]
  have himgP : ((pairs Γ.V).erase s(v, w)).image (Sym2.map (mergeMap v w)) ⊆
      pairs (Γ.V.erase w) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    exact map_mem_pairs_merge hv hvw hp
  have hcoef : ∀ S ∈ ((pairs Γ.V).erase s(v, w)).powerset,
      coef φ Γ.V Γ.t (insert s(v, w) S) =
        if (S.image (Sym2.map (mergeMap v w))).card = S.card then
          coef φ (Γ.V.erase w) (Function.update Γ.t v (Γ.t v + Γ.t w))
            (S.image (Sym2.map (mergeMap v w))) else 0 := by
    intro S hS
    have hS1 := Finset.mem_powerset.1 hS
    have hSV : S ⊆ pairs Γ.V := hS1.trans (Finset.erase_subset _ _)
    have heS : s(v, w) ∉ S := fun h => Finset.notMem_erase _ _ (hS1 h)
    have hS' : S.image (Sym2.map (mergeMap v w)) ⊆ pairs (Γ.V.image (mergeMap v w)) := by
      rw [image_mergeMap hv hvw]
      exact (Finset.image_subset_image hS1).trans himgP
    have hconn := conn_contract hv hw hvw hSV
    have hcardV : (Γ.V.image (mergeMap v w)).card + 1 = Γ.V.card := by
      rw [image_mergeMap hv hvw]; exact Finset.card_erase_add_one hw
    have hcardS : (insert s(v, w) S).card = S.card + 1 := Finset.card_insert_of_notMem heS
    by_cases hinj : (S.image (Sym2.map (mergeMap v w))).card = S.card
    · rw [ite_eq_left hinj]
      have := coef_transfer φ (t := Γ.t) (t' := Function.update Γ.t v (Γ.t v + Γ.t w))
        (Finset.insert_subset he hSV) hS' hconn (type_fiber_merge hv hw hvw) (by omega)
      rwa [image_mergeMap hv hvw] at this
    · rw [ite_eq_right hinj]
      have hle := Finset.card_image_le (s := S) (f := Sym2.map (mergeMap v w))
      unfold coef
      rw [ite_eq_right (not_isForest_of_card hS' hconn (by omega))]
  rw [Finset.sum_congr rfl (fun S hS => by rw [hcoef S hS])]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [(sum_powerset_prod_fiber (Sym2.map (mergeMap v w)) (bitFn Γ) ((pairs Γ.V).erase s(v, w))
    (pairs (Γ.V.erase w)) (coef φ (Γ.V.erase w) (Function.update Γ.t v (Γ.t v + Γ.t w)))
    himgP).symm]
  unfold polyForm
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  exact fiber_contract hΓ hv hw hvw (Finset.mem_powerset.1 hT hq)

/-- Graph dependence of the forest symbol (tex 2110–2118). Kind: PROVED (helper). -/
theorem forestSymbol_iso (φ : L → ZMod 2) {Γ Δ : Config L} (hΓ : Γ.Compatible 0)
    (hiso : Γ.IsIso Δ) : forestSymbol φ Γ = forestSymbol φ Δ := by
  have hΔ : Δ.Compatible 0 := compatible_of_iso hiso hΓ
  obtain ⟨e, ht, hz⟩ := hiso
  let g : ℕ → ℕ := fun u => if h : u ∈ Γ.V then (e ⟨u, h⟩ : ℕ) else u
  have hgV : ∀ u (hu : u ∈ Γ.V), g u = e ⟨u, hu⟩ := fun u hu => dite_eq_left hu
  have hginj : ∀ a ∈ Γ.V, ∀ b ∈ Γ.V, g a = g b → a = b := by
    intro a ha b hb h
    rw [hgV a ha, hgV b hb] at h
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  have hgmem : ∀ a ∈ Γ.V, g a ∈ Δ.V := fun a ha => by rw [hgV a ha]; exact (e ⟨a, ha⟩).2
  have himg : Γ.V.image g = Δ.V := by
    ext c
    constructor
    · intro hc
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hc
      exact hgmem u hu
    · intro hc
      obtain ⟨⟨u, hu⟩, he'⟩ := e.surjective ⟨c, hc⟩
      exact Finset.mem_image.2 ⟨u, hu, by rw [hgV u hu, he']⟩
  have hgt : ∀ a ∈ Γ.V, Δ.t (g a) = Γ.t a := fun a ha => by rw [hgV a ha]; exact ht ⟨a, ha⟩
  have hgz : ∀ a ∈ Γ.V, ∀ b ∈ Γ.V, a ≠ b → Δ.z (g a) (g b) = Γ.z a b := by
    intro a ha b hb hab
    rw [hgV a ha, hgV b hb]
    exact hz ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hab (congrArg Subtype.val h))
  have hμinj : Set.InjOn (Sym2.map g) ↑(pairs Γ.V) := by
    intro p hp p' hp' h
    induction p using Sym2.ind with
    | _ a b =>
    induction p' using Sym2.ind with
    | _ c d =>
      obtain ⟨ha, hb, -⟩ := mem_pairs_mk.1 hp
      obtain ⟨hc, hd, -⟩ := mem_pairs_mk.1 hp'
      rw [Sym2.map_mk, Sym2.map_mk] at h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hginj a ha c hc h1, hginj b hb d hd h2]
      · rw [hginj a ha d hd h1, hginj b hb c hc h2]; exact Sym2.eq_swap
  have himgP : (pairs Γ.V).image (Sym2.map g) ⊆ pairs Δ.V := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    induction p using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mem_pairs_mk.1 hp
      rw [Sym2.map_mk]
      exact mem_pairs_mk.2 ⟨hgmem a ha, hgmem b hb, fun h => hab (hginj a ha b hb h)⟩
  have hfilter : (pairs Γ.V).powerset.filter (fun S => (S.image (Sym2.map g)).card = S.card) =
      (pairs Γ.V).powerset :=
    Finset.filter_true_of_mem (fun S hS => Finset.card_image_of_injOn (hμinj.mono (by
      intro p hp; exact Finset.mem_coe.2 (Finset.mem_powerset.1 hS hp))))
  have hcoef : ∀ S ∈ (pairs Γ.V).powerset,
      coef φ Γ.V Γ.t S = coef φ Δ.V Δ.t (S.image (Sym2.map g)) := by
    intro S hS
    have hS1 := Finset.mem_powerset.1 hS
    have hS' : S.image (Sym2.map g) ⊆ pairs (Γ.V.image g) := by
      rw [himg]; exact (Finset.image_subset_image hS1).trans himgP
    have hconn : ∀ a ∈ Γ.V, ∀ b ∈ Γ.V, conn S a b ↔ conn (S.image (Sym2.map g)) (g a) (g b) := by
      intro a ha b hb
      exact ⟨conn_map g, conn_of_conn_map hS1
        (fun x hx y hy h => by rw [hginj x hx y hy h]; exact conn_refl _ _) ha hb⟩
    have ht' : ∀ c ∈ Γ.V.image g, Δ.t c = ∑ u ∈ Γ.V.filter (fun u => g u = c), Γ.t u := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
      have : Γ.V.filter (fun u => g u = g a) = {a} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hu, h⟩; exact hginj u hu a ha h
        · rintro rfl; exact ⟨ha, rfl⟩
      rw [this, Finset.sum_singleton, hgt a ha]
    have hcard : S.card + (Γ.V.image g).card = (S.image (Sym2.map g)).card + Γ.V.card := by
      rw [Finset.card_image_of_injOn (fun a ha b hb h => hginj a ha b hb h),
        Finset.card_image_of_injOn (hμinj.mono (fun p hp => Finset.mem_coe.2 (hS1 hp)))]
    have := coef_transfer φ hS1 hS' hconn ht' hcard
    rwa [himg] at this
  have hfib : ∀ q ∈ pairs Δ.V,
      ∑ p ∈ (pairs Γ.V).filter (fun p => Sym2.map g p = q), bitFn Γ p = bitFn Δ q := by
    intro q hq
    induction q using Sym2.ind with
    | _ c d =>
      obtain ⟨hc, hd, hcd⟩ := mem_pairs_mk.1 hq
      rw [← himg] at hc hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hd
      have hab : a ≠ b := fun h => hcd (by rw [h])
      have : (pairs Γ.V).filter (fun p => Sym2.map g p = s(g a, g b)) = {s(a, b)} := by
        ext p
        induction p using Sym2.ind with
        | _ x y =>
          simp only [Finset.mem_filter, Finset.mem_singleton, mem_pairs_mk, Sym2.map_mk]
          constructor
          · rintro ⟨⟨hx, hy, -⟩, h⟩
            rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [hginj x hx a ha h1, hginj y hy b hb h2]
            · rw [hginj x hx b hb h1, hginj y hy a ha h2]; exact Sym2.eq_swap
          · intro h
            rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨⟨ha, hb, hab⟩, rfl⟩
            · exact ⟨⟨hb, ha, Ne.symm hab⟩, Sym2.eq_swap⟩
      rw [this, Finset.sum_singleton, bitFn_mk hΓ ha hb hab,
        bitFn_mk hΔ (hgmem a ha) (hgmem b hb) hcd, hgz a ha b hb hab]
  rw [forestSymbol_eq_polyForm, forestSymbol_eq_polyForm]
  unfold polyForm
  calc ∑ S ∈ (pairs Γ.V).powerset, coef φ Γ.V Γ.t S * ∏ p ∈ S, bitFn Γ p
      = ∑ S ∈ (pairs Γ.V).powerset.filter (fun S => (S.image (Sym2.map g)).card = S.card),
          coef φ Δ.V Δ.t (S.image (Sym2.map g)) * ∏ p ∈ S, bitFn Γ p := by
        rw [hfilter]
        exact Finset.sum_congr rfl (fun S hS => by rw [hcoef S hS])
    _ = ∑ T ∈ (pairs Δ.V).powerset, coef φ Δ.V Δ.t T *
          ∏ q ∈ T, (∑ p ∈ (pairs Γ.V).filter (fun p => Sym2.map g p = q), bitFn Γ p) :=
        (sum_powerset_prod_fiber (Sym2.map g) (bitFn Γ) (pairs Γ.V) (pairs Δ.V)
          (coef φ Δ.V Δ.t) himgP).symm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        congr 1
        exact Finset.prod_congr rfl (fun q hq => hfib q (Finset.mem_powerset.1 hT hq))

/-- A vertex meeting no pair of `S` is connected only to itself (tex 2181–2185). Kind: PROVED
(helper). -/
theorem conn_isolated {S : Finset (Sym2 ℕ)} {v : ℕ} (h : ∀ u, s(v, u) ∉ S) {u : ℕ}
    (hc : conn S u v) : u = v := by
  let R : ℕ → ℕ → Prop := fun x y => (x = v ↔ y = v)
  have hR : Equivalence R := ⟨fun _ => Iff.rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  have : R u v := hR.eqvGen_iff.1 (Relation.EqvGen.mono (fun x y hxy => by
    have hx : x ≠ v := by rintro rfl; exact h y hxy
    have hy : y ≠ v := by rintro rfl; exact h x (by rw [Sym2.eq_swap]; exact hxy)
    exact ⟨fun h' => absurd h' hx, fun h' => absurd h' hy⟩) u v hc)
  exact this.2 rfl

open Classical in
/-- Primary isolation for the forest symbol: an isolated vertex of type zero is its own block, of
weight `φ 0 = 0` (tex 2130–2132). Kind: PROVED (helper). -/
theorem forestSymbol_isolation (φ : L → ZMod 2) (hφ : φ 0 = 0) {Γ : Config L} {v : ℕ}
    (hv : v ∈ Γ.V) (htv : Γ.t v = 0)
    (hiso : ∀ w ∈ Γ.V, w ≠ v → Γ.z v w = 0 ∧ Γ.z w v = 0) : forestSymbol φ Γ = 0 := by
  unfold forestSymbol
  apply Finset.sum_eq_zero
  intro S hS
  have hSE := Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1
  have hnot : ∀ u, s(v, u) ∉ S := by
    intro u hu
    obtain ⟨-, hu', hvu, h⟩ := mem_bitEdges_mk.1 (hSE hu)
    obtain ⟨h1, h2⟩ := hiso u hu' (Ne.symm hvu)
    rcases h with h | h
    · rw [h1] at h; exact zero_ne_one h
    · rw [h2] at h; exact zero_ne_one h
  have hfil : Γ.V.filter (fun u => rep Γ.V S u = rep Γ.V S v) = {v} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hu, h⟩; exact conn_isolated hnot ((rep_eq_iff hu hv).1 h)
    · rintro rfl; exact ⟨hv, rfl⟩
  unfold blockWeight
  apply Finset.prod_eq_zero (Finset.mem_image_of_mem _ hv)
  rw [hfil, Finset.sum_singleton, htv, hφ]

/-- Contraction preserves the total type (tex 2042–2054). Kind: PROVED (helper). -/
theorem total_contract {Γ : Config L} {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hvw : v ≠ w) :
    (Γ.contract v w).total = Γ.total := by
  show ∑ u ∈ Γ.V.erase w, Function.update Γ.t v (Γ.t v + Γ.t w) u = ∑ u ∈ Γ.V, Γ.t u
  have hv' : v ∈ Γ.V.erase w := Finset.mem_erase.2 ⟨hvw, hv⟩
  rw [← Finset.add_sum_erase _ _ hv', Function.update_self, ← Finset.add_sum_erase _ _ hw,
    ← Finset.add_sum_erase _ _ hv']
  rw [Finset.sum_congr rfl (fun u hu => Function.update_of_ne (Finset.ne_of_mem_erase hu) _ _)]
  abel

omit [AddCommGroup L] in
/-- Isomorphic configurations have the same total type (tex 2042–2044). Kind: PROVED (helper). -/
theorem total_iso' {M : Type*} [AddCommMonoid M] {Γ Δ : Config M} (h : Γ.IsIso Δ) :
    ∑ v ∈ Γ.V, Γ.t v = ∑ v ∈ Δ.V, Δ.t v := by
  obtain ⟨e, ht, -⟩ := h
  calc ∑ v ∈ Γ.V, Γ.t v = ∑ v : Γ.V, Γ.t v := (Finset.sum_coe_sort Γ.V Γ.t).symm
    _ = ∑ v : Δ.V, Δ.t v := Fintype.sum_equiv e _ _ (fun x => (ht x).symm)
    _ = ∑ v ∈ Δ.V, Δ.t v := Finset.sum_coe_sort Δ.V Δ.t

/-- Isomorphic configurations have the same total type (tex 2042–2044). Kind: PROVED (helper). -/
theorem total_iso {Γ Δ : Config L} (h : Γ.IsIso Δ) : Γ.total = Δ.total := total_iso' h

open Classical in
/-- The weight of the empty forest is the product over the vertices (tex 2181–2185). Kind: PROVED
(helper). -/
theorem blockWeight_empty (φ : L → ZMod 2) (V : Finset ℕ) (t : ℕ → L) :
    blockWeight φ V t ∅ = ∏ v ∈ V, φ (t v) := by
  rw [blockWeight_eq_lw, lw_congr φ t (h := id) (fun u hu u' hu' => by
    rw [rep_eq_iff hu hu']
    exact ⟨conn_empty, fun h => by rw [show u = u' from h]; exact conn_refl _ _⟩)]
  unfold lw
  rw [Finset.image_id]
  apply Finset.prod_congr rfl
  intro r hr
  have : V.filter (fun u => id u = r) = {r} := by
    ext u
    simp only [Finset.mem_filter, id, Finset.mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨hr, rfl⟩
  rw [this, Finset.sum_singleton]

end WitnessAux

end

/-- **Non-vacuity of the coefficient rules** (tex 2102–2136): for the zero sign coordinate and any
`φ` with `φ 0 = 0`, the forest symbol satisfies graph dependence, contraction and primary isolation.
Non-vacuity witness, not part of the manuscript. Kind: PROVED. -/
theorem forestSymbol_rules {L : Type*} [AddCommGroup L] (φ : L → ZMod 2) (hφ : φ 0 = 0) :
    CoefficientRules (0 : L →+ ZMod 2) (forestSymbol φ) :=
  ⟨fun _ _ hΓ hiso => WitnessAux.forestSymbol_iso φ hΓ hiso,
   fun _ hΓ _ hv _ hw hvw => WitnessAux.forestSymbol_contraction φ hΓ hv hw hvw,
   fun _ _ _ hv htv hiso => WitnessAux.forestSymbol_isolation φ hφ hv htv hiso⟩

/-- **Filtered witness** (tex 2079, 2102–2136): the forest symbol cut down to total type zero still
satisfies the coefficient rules, since flips, contractions and isomorphisms preserve the total type.
Non-vacuity witness, not part of the manuscript. Kind: PROVED. -/
theorem filteredForestSymbol_rules {L : Type*} [AddCommGroup L] [DecidableEq L]
    (φ : L → ZMod 2) (hφ : φ 0 = 0) :
    CoefficientRules (0 : L →+ ZMod 2) (fun Γ => if Γ.total = 0 then forestSymbol φ Γ else 0) := by
  have hA := forestSymbol_rules φ hφ
  refine ⟨fun Γ Δ hΓ hiso => ?_, fun Γ hΓ v hv w hw hvw => ?_, fun Γ hΓ v hv htv hiso => ?_⟩
  · show (if Γ.total = 0 then forestSymbol φ Γ else 0) =
      (if Δ.total = 0 then forestSymbol φ Δ else 0)
    rw [WitnessAux.total_iso hiso, hA.graph_dependence Γ Δ hΓ hiso]
  · show (if Γ.total = 0 then forestSymbol φ Γ else 0) +
        (if (Γ.flip v w).total = 0 then forestSymbol φ (Γ.flip v w) else 0) =
      (if (Γ.contract v w).total = 0 then forestSymbol φ (Γ.contract v w) else 0)
    rw [WitnessAux.total_contract hv hw hvw, show (Γ.flip v w).total = Γ.total from rfl]
    by_cases h : Γ.total = 0
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      exact hA.contraction Γ hΓ v hv w hw hvw
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, add_zero]
  · show (if Γ.total = 0 then forestSymbol φ Γ else 0) = 0
    rw [hA.primary_isolation Γ hΓ v hv htv hiso, ite_self]

/-- Two vertices of type `1` with no bit (tex 2176–2180). Helper definition of the non-vacuity
witness. -/
def witnessSeed : Config (ZMod 2) := ⟨{0, 1}, fun _ => 1, fun _ _ => 0⟩

/-- The witness seed has total type zero (tex 2042–2044). Kind: PROVED (helper). -/
theorem witnessSeed_total : witnessSeed.total = 0 := by
  decide

open Classical in
/-- The forest symbol of the witness seed is one (tex 2176–2180). Kind: PROVED (helper). -/
theorem witnessSeed_value : forestSymbol (fun t : ZMod 2 => t) witnessSeed = 1 := by
  have hE : bitEdges witnessSeed = ∅ := by
    ext p
    simp [bitEdges, witnessSeed]
  have hF : IsForest witnessSeed.V ∅ := ⟨Finset.empty_subset _, by simp [ForestAux.ncomp_empty]⟩
  unfold forestSymbol
  rw [hE, Finset.powerset_empty, Finset.filter_singleton, ite_eq_left hF, Finset.sum_singleton,
    WitnessAux.blockWeight_empty]
  decide

/-- **Minimum seed of total zero** (tex 2102–2136, 2176–2180, 10588–10596): over `L = ZMod 2` with
`φ = id`, the filtered forest symbol has the minimum nonempty seed `witnessSeed` (two vertices of
type one, no bit), of total type zero; a single vertex is never a unit seed. Non-vacuity witness,
not part of the manuscript. Kind: PROVED. -/
theorem witness_minSeed :
    IsMinSeed (0 : ZMod 2 →+ ZMod 2)
      (fun Γ => if Γ.total = 0 then forestSymbol (fun t : ZMod 2 => t) Γ else 0) witnessSeed ∧
    witnessSeed.total = 0 := by
  have hcomp : witnessSeed.Compatible (0 : ZMod 2 →+ ZMod 2) := by
    intro a _ b _ _
    simp [witnessSeed]
  have hA := filteredForestSymbol_rules (fun t : ZMod 2 => t) rfl
  refine ⟨⟨⟨hcomp, ?_⟩, ⟨0, by simp [witnessSeed]⟩, ?_⟩, witnessSeed_total⟩
  · show (if witnessSeed.total = 0 then _ else 0) = 1
    rw [ite_eq_left witnessSeed_total, witnessSeed_value]
  · intro Δ hΔ hne
    have hcard : witnessSeed.V.card = 2 := by decide
    rw [hcard]
    by_contra hlt
    have h1 : Δ.V.card = 1 := by have := hne.card_pos; omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.1 h1
    have hval : (if Δ.total = 0 then forestSymbol (fun t : ZMod 2 => t) Δ else 0) = 1 := hΔ.2
    by_cases ht : Δ.total = 0
    · have htu : Δ.t u = 0 := by
        unfold Config.total at ht
        rw [hu, Finset.sum_singleton] at ht
        exact ht
      have h0 := hA.primary_isolation Δ hΔ.1 u (by rw [hu]; exact Finset.mem_singleton_self u)
        htu (by
          intro w hw hwu
          rw [hu] at hw
          exact absurd (Finset.mem_singleton.1 hw) hwu)
      have : (if Δ.total = 0 then forestSymbol (fun t : ZMod 2 => t) Δ else 0) = 0 := h0
      rw [this] at hval
      exact zero_ne_one hval
    · rw [ite_eq_right ht] at hval
      exact zero_ne_one hval

/-- **The terminal hypotheses of the one-symbol address lemma are satisfiable** (tex 2102–2136,
2209–2220): a symbol obeying the coefficient rules and a nonempty compatible configuration with
nonzero terminal polynomial. Non-vacuity witness, not part of the manuscript. Kind: PROVED. -/
theorem witness_one_symbol : ∃ (A : Config (ZMod 2) → ZMod 2) (Γ : Config (ZMod 2)),
    CoefficientRules 0 A ∧ Γ.Compatible 0 ∧ Γ.V.Nonempty ∧ TerminalNonzero A Γ := by
  obtain ⟨hm, -⟩ := witness_minSeed
  have h := hm.1.2
  rw [← ForestAux.flipBy_empty witnessSeed] at h
  exact ⟨_, witnessSeed, filteredForestSymbol_rules (fun t : ZMod 2 => t) rfl, hm.1.1, hm.2.1,
    ⟨∅, Finset.empty_subset _, h⟩⟩

/-- **The terminal hypotheses of the two-symbol address lemma are satisfiable** (tex 2102–2136,
10587–10623): the zero-total packets built from the filtered forest symbol and its minimum seed
give, for every `b ≥ 1`, a compatible configuration with an activation reaching every nonzero vector
and a nonzero terminal polynomial at every nonzero address. Non-vacuity witness, not part of the
manuscript. Kind: PROVED. -/
theorem witness_two_symbol (b : ℕ) (hb : 1 ≤ b) : ∃ (A : Config (ZMod 2) → ZMod 2)
    (Γ : Config (ZMod 2)) (act' : ℕ → Option (Fin b → ZMod 2)),
    CoefficientRules 0 A ∧ Γ.Compatible 0 ∧ (∀ v ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' v = some w) ∧
    (∀ w : Fin b → ZMod 2, w ≠ 0 → ∃ v ∈ Γ.V, act' v = some w) ∧
    ∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A (Γ.at act' x) := by
  obtain ⟨hm, htot⟩ := witness_minSeed
  have hA := filteredForestSymbol_rules (fun t : ZMod 2 => t) rfl
  have hsurj : Function.Surjective (AddMonoidHom.id (ZMod 2)) := fun y => ⟨y, rfl⟩
  obtain ⟨V, t, act', h1, h2, h3⟩ := packet_terminals (ε := (0 : ZMod 2 →+ ZMod 2)) (by decide)
    (AddMonoidHom.id (ZMod 2)) (AddMonoidHom.id (ZMod 2)) hsurj hsurj (fun _ => rfl)
    (fun _ => rfl) hA hA hm hm htot htot b hb
  have hcomp : (Config.mk V t (fun _ _ => 0)).Compatible (0 : ZMod 2 →+ ZMod 2) := by
    intro a _ c _ _
    simp
  refine ⟨_, Config.mk V t (fun _ _ => 0), act', hA, hcomp, h1, h2, fun x hx => ?_⟩
  obtain ⟨-, -, hT, -⟩ := h3 _ hcomp x hx
  obtain ⟨U, hU, hval⟩ := hT
  exact ⟨U, hU, hval⟩


end ZInQ.Manuscript.RC.Symbols
