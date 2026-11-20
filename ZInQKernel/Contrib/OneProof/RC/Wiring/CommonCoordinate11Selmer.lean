import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10TwoSing
import ZInQKernel.Contrib.OneProof.RC.Wiring.RetentionGenuineFunctionals
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SupportChange

/-!
# The support triangle of Selmer complexes: the inclusion, its splitting and its quotient

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4166: "Let
`i : C_P → C_R` be the primitive-to-relaxed map … at `q` these are the maps from the unramified
condition to the full condition"), and the support comparisons (tex 3480–3496: "Replacing the
unramified condition by the full condition then gives the singular quotient by a cone of Selmer
cones").

For Selmer data `D = (G --res--> L <--ι-- U)` (the RC53 group's `SelData`, Selmer complex
`selCx D = Cone(G ⊕ U → L)[−1]`) and a split inclusion of local conditions `EU : U' ⊂ U`
(`SplitInclusion`, complements `W`):

* `selSplit D EU`: the primitive-to-relaxed map `changeMap D EU.i : C(U') → C(U)`,
  `(a, u', x) ↦ (a, i u', x)`, is a split inclusion of Selmer complexes, with complement
  `(0, W, 0)` (`selSplit_i`: its map is `changeMap`, by definition);
* `selQEquiv`, `selSplit_dQ`: its quotient complex is the quotient complex of the local
  conditions, `(0, w, 0) ↦ w`, compatibly with the differentials; `selQuotRetract`: a retract of
  the local quotient onto a model is a retract of the quotient of the support triangle.

Adding one place `q` to old Selmer data (`addPlace`, the convention of lane RC26's `newSelData`
and of the stage family: global cochains on the enlarged support, old conditions at the old
places, and the local complex `L_q`, its restriction and a condition `U_q → L_q` at `q`):

* `relaxedAt D res_q`: the full condition at `q` (`U_q = L_q`, `ι_q = id`); `primToRel D ι_q`:
  the identity on the old conditions and `ι_q` at `q`; `selRestrict_relaxedAt`: the primitive
  Selmer data `selRestrict (relaxedAt D res_q) (primToRel D ι_q)` ARE the data with the condition
  `U_q` at `q` (`addPlace D res_q ι_q`);
* `newSplit D EUq`: a split inclusion `EUq : U_q ⊂ L_q` at the new place gives the split
  inclusion of local conditions (complement `0 ⊕ W_q`), with quotient the local quotient at `q`
  (`newQEquiv`, `newSplit_dQ`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (changeMap idGHom ghomComp)
open ZInQ.Manuscript.RC.SelmerComplex (prodCx prodLift prodMapG)

/-- Two chain maps with equal components are equal (tex 4157–4166). Kind: PROVED. -/
theorem ghom_eq {S : Type} [CommRing S] {A B : GCx S} {f g : GHom A B}
    (h : ∀ i j (hij : i = j), f.f i j hij = g.f i j hij) : f = g := by
  cases f
  cases g
  congr 1
  funext i j hij
  exact h i j hij

/-! ### The split inclusion of Selmer complexes -/

section SelSplit

variable {S : Type} [CommRing S] (D : SelData S) {U' : GCx S} (EU : SplitInclusion U' D.U)

/-- The middle embedding `w ↦ (0, w, 0)` of the local condition into the Selmer complex
(tex 4157–4166). Kind: definition. -/
def selMid (n : ℤ) : D.U.X n →ₗ[S] (selCx D).X n :=
  (LinearMap.inr S (D.G.X n) (D.U.X n × D.L.X (n - 1))) ∘ₗ
    (LinearMap.inl S (D.U.X n) (D.L.X (n - 1)))

/-- `selMid w = (0, w, 0)`. (tex 4157–4166) Kind: PROVED (definitional). -/
theorem selMid_apply (n : ℤ) (w : D.U.X n) :
    selMid D n w = (((0 : D.G.X n), w, (0 : D.L.X (n - 1))) : selT D n) :=
  rfl

/-- The middle embedding is injective. (tex 4157–4166) Kind: PROVED. -/
theorem selMid_injective (n : ℤ) : Function.Injective (selMid D n) := fun w w' h => by
  have h' : (((0 : D.G.X n), w, (0 : D.L.X (n - 1))) : selT D n) = (0, w', 0) := h
  simp only [Prod.mk.injEq, true_and, and_true] at h'
  exact h'

/-- The primitive-to-relaxed map on elements: `(a, u', x) ↦ (a, i u', x)`. (tex 4157–4166)
Kind: PROVED (definitional). -/
theorem changeMap_apply (n : ℤ) (c : selT (selRestrict D EU.i) n) :
    (changeMap D EU.i).f n n rfl c = ((c.1, EU.i.f n n rfl c.2.1, c.2.2) : selT D n) :=
  rfl

/-- **The primitive-to-relaxed map is a split inclusion of Selmer complexes** (tex 4157–4166,
3489–3494): `changeMap D EU.i : C(U') → C(U)` with complement `(0, W, 0)`, `W` the complement of
the local conditions. Kind: definition (PROVED identities). -/
def selSplit : SplitInclusion (selCx (selRestrict D EU.i)) (selCx D) where
  i := changeMap D EU.i
  inj n := by
    intro c c' h
    have h' : ((c.1, EU.i.f n n rfl c.2.1, c.2.2) : selT D n) =
        (c'.1, EU.i.f n n rfl c'.2.1, c'.2.2) := h
    have h1 := congrArg Prod.fst h'
    have h2 := congrArg (fun t : selT D n => t.2.1) h'
    have h3 := congrArg (fun t : selT D n => t.2.2) h'
    exact Prod.ext h1 (Prod.ext (EU.inj n h2) h3)
  Qc n := (EU.Qc n).map (selMid D n)
  compl n := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro x ⟨c, rfl⟩ hx
      obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.1 hx
      have e : (((0 : D.G.X n), w, (0 : D.L.X (n - 1))) : selT D n) =
          (c.1, EU.i.f n n rfl c.2.1, c.2.2) := hwx
      have e1 := congrArg Prod.fst e
      have e2 := congrArg (fun t : selT D n => t.2.1) e
      have e3 := congrArg (fun t : selT D n => t.2.2) e
      have hw0 : w = 0 := by
        have hd := (EU.compl n).disjoint
        rw [Submodule.disjoint_def] at hd
        exact hd w ⟨c.2.1, e2.symm⟩ hw
      change ((c.1, EU.i.f n n rfl c.2.1, c.2.2) : selT D n) = 0
      have e2' : EU.i.f n n rfl c.2.1 = 0 := e2.symm.trans hw0
      exact Prod.ext e1.symm (Prod.ext e2' e3.symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      refine Submodule.mem_sup.2 ⟨(changeMap D EU.i).f n n rfl
        ((c.1, EU.coordP n c.2.1, c.2.2) : selT (selRestrict D EU.i) n), ⟨_, rfl⟩,
        selMid D n (EU.coordQ n c.2.1), Submodule.mem_map_of_mem (EU.coordQ n c.2.1).2, ?_⟩
      have hdec := EU.decompose n c.2.1
      change ((c.1, EU.i.f n n rfl (EU.coordP n c.2.1), c.2.2) : selT D n) +
        (0, (EU.coordQ n c.2.1 : D.U.X n), 0) = c
      exact Prod.ext (add_zero c.1) (Prod.ext hdec (add_zero c.2.2))

/-- The map of the split inclusion is the primitive-to-relaxed map `changeMap D EU.i`
(tex 4157–4166). Kind: PROVED (definitional). -/
theorem selSplit_i : (selSplit D EU).i = changeMap D EU.i :=
  rfl

/-- **The quotient of the support triangle is the quotient of the local conditions**, degreewise:
`W ≃ (0, W, 0)` (tex 3489–3494). Kind: definition. -/
def selQEquiv (n : ℤ) : EU.Qc n ≃ₗ[S] (selSplit D EU).Qc n :=
  Submodule.equivMapOfInjective (selMid D n) (selMid_injective D n) (EU.Qc n)

/-- `selQEquiv w = (0, w, 0)`. (tex 3489–3494) Kind: PROVED (definitional). -/
theorem selQEquiv_apply (n : ℤ) (w : EU.Qc n) :
    ((selQEquiv D EU n w : (selSplit D EU).Qc n) : (selCx D).X n) = selMid D n w :=
  rfl

/-- **The quotient differentials correspond** (tex 3489–3494): the quotient differential of the
support triangle at `(0, w, 0)` is `(0, d_W w, 0)`. Kind: PROVED. -/
theorem selSplit_dQ (a b : ℤ) (h : a + 1 = b) (w : EU.Qc a) :
    (selSplit D EU).dQ a b h (selQEquiv D EU a w) = selQEquiv D EU b (EU.dQ a b h w) := by
  set E := selSplit D EU
  have hmem : selMid D b (EU.dQ a b h w) ∈ E.Qc b :=
    Submodule.mem_map_of_mem (EU.dQ a b h w).2
  let x : (selCx (selRestrict D EU.i)).X b :=
    ((0 : D.G.X b), EU.offDiag a b h w, -(D.ι.f a (b - 1) (by omega) w))
  have hd : (selCx D).d a b h (selMid D a w) =
      E.i.f b b rfl x + ((⟨selMid D b (EU.dQ a b h w), hmem⟩ : E.Qc b) : (selCx D).X b) := by
    have hU := EU.d_Q a b h w
    change ((D.G.d a b h 0, D.U.d a b h w, D.res.f a (b - 1) (by omega) 0 -
        D.ι.f a (b - 1) (by omega) w - D.L.d (a - 1) (b - 1) (by omega) 0) : selT D b) =
      ((0, EU.i.f b b rfl (EU.offDiag a b h w), -(D.ι.f a (b - 1) (by omega) w)) : selT D b) +
        (0, (EU.dQ a b h w : D.U.X b), 0)
    rw [map_zero, map_zero, map_zero, zero_sub, sub_zero]
    exact Prod.ext (add_zero 0).symm (Prod.ext hU (add_zero _).symm)
  apply Subtype.ext
  change (E.coordQ b ((selCx D).d a b h (selMid D a w)) : (selCx D).X b) = selMid D b _
  rw [hd, map_add, E.coordQ_i, zero_add, E.coordQ_Q]

/-- The equivalence of quotient complexes commutes with the differentials (the form used by
`GRetract.ofEquiv`). (tex 3489–3494) Kind: PROVED. -/
theorem selQEquiv_comm (a b : ℤ) (h : a + 1 = b) (w : EU.quotientCx.X a) :
    (selSplit D EU).quotientCx.d a b h (selQEquiv D EU a w) =
      selQEquiv D EU b (EU.quotientCx.d a b h w) :=
  selSplit_dQ D EU a b h w

/-- **A retract of the local quotient is a retract of the quotient of the support triangle**
(tex 3489–3494, 5398–5424). Kind: definition. -/
def selQuotRetract {Q' : GCx S} (RW : GRetract EU.quotientCx Q') :
    GRetract (selSplit D EU).quotientCx Q' :=
  RW.ofEquiv (selQEquiv D EU) (selQEquiv_comm D EU)

end SelSplit

/-! ### Adding a place: the relaxed and the primitive Selmer data -/

section AddPlace

variable {S : Type} [CommRing S] (D : SelData S) {Lq : GCx S} (resq : GHom D.G Lq)

/-- **Selmer data with one more place** (tex 3480–3496; lane RC26's `newSelData` convention):
the global complex of `D`, the local complex `L ⊕ L_q`, the restriction `(res, res_q)` and the
local condition `U ⊕ U_q --(ι, ι_q)--> L ⊕ L_q`. Kind: definition. -/
def addPlace {Uq : GCx S} (ιq : GHom Uq Lq) : SelData S where
  G := D.G
  U := prodCx D.U Uq
  L := prodCx D.L Lq
  res := prodLift D.res resq
  ι := prodMapG D.ι ιq

/-- **The relaxed Selmer data at `q`**: the full condition `L_q --id--> L_q` at the new place
(tex 4157–4166). Kind: definition. -/
abbrev relaxedAt : SelData S := addPlace D resq (idGHom Lq)

/-- **The primitive-to-relaxed map of local conditions**: the identity on the old conditions and
`ι_q : U_q → L_q` at the new place (tex 4157–4166: "at `q` these are the maps from the
unramified condition to the full condition"). Kind: definition. -/
abbrev primToRel {Uq : GCx S} (ιq : GHom Uq Lq) :
    GHom (prodCx D.U Uq) (relaxedAt D resq).U :=
  prodMapG (idGHom D.U) ιq

/-- **The primitive Selmer data are the data with the condition `U_q` at `q`** (tex 4157–4166,
3483–3487): restricting the relaxed data along `primToRel` gives `addPlace D res_q ι_q`.
Kind: PROVED. -/
theorem selRestrict_relaxedAt {Uq : GCx S} (ιq : GHom Uq Lq) :
    selRestrict (relaxedAt D resq) (primToRel D resq ιq) = addPlace D resq ιq := by
  have h : ghomComp (primToRel D resq ιq) (relaxedAt D resq).ι = prodMapG D.ι ιq :=
    ghom_eq fun i j hij => by
      subst hij
      exact LinearMap.ext fun x => rfl
  show (⟨D.G, prodCx D.U Uq, prodCx D.L Lq, prodLift D.res resq,
    ghomComp (primToRel D resq ιq) (relaxedAt D resq).ι⟩ : SelData S) =
      ⟨D.G, prodCx D.U Uq, prodCx D.L Lq, prodLift D.res resq, prodMapG D.ι ιq⟩
  exact congrArg (fun ι => (⟨D.G, prodCx D.U Uq, prodCx D.L Lq, prodLift D.res resq, ι⟩ :
    SelData S)) h

/-- **The split inclusion of local conditions from a split inclusion at the new place**
(tex 4157–4166, 3489–3494): `id ⊕ i_q : U ⊕ U_q → U ⊕ L_q`, complement `0 ⊕ W_q`.
Kind: definition (PROVED identities). -/
def newSplit {Uq : GCx S} (EUq : SplitInclusion Uq Lq) :
    SplitInclusion (prodCx D.U Uq) (relaxedAt D resq).U where
  i := primToRel D resq EUq.i
  inj n := by
    rintro ⟨u, y⟩ ⟨u', y'⟩ h
    have h' : ((u, EUq.i.f n n rfl y) : D.U.X n × Lq.X n) = (u', EUq.i.f n n rfl y') := h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, hy⟩ := h'
    rw [EUq.inj n hy]
  Qc n := (⊥ : Submodule S (D.U.X n)).prod (EUq.Qc n)
  compl n := by
    have hr : LinearMap.range ((primToRel D resq EUq.i).f n n rfl) =
        (⊤ : Submodule S (D.U.X n)).prod (LinearMap.range (EUq.i.f n n rfl)) := by
      change LinearMap.range ((LinearMap.id : D.U.X n →ₗ[S] D.U.X n).prodMap
        (EUq.i.f n n rfl)) = _
      rw [LinearMap.range_prodMap, LinearMap.range_id]
    have hc := EUq.compl n
    have key : IsCompl ((⊤ : Submodule S (D.U.X n)).prod (LinearMap.range (EUq.i.f n n rfl)))
        ((⊥ : Submodule S (D.U.X n)).prod (EUq.Qc n)) := by
      refine ⟨?_, ?_⟩
      · rw [disjoint_iff, Submodule.prod_inf_prod, top_inf_eq, hc.inf_eq_bot,
          Submodule.prod_bot]
      · rw [codisjoint_iff, Submodule.prod_sup_prod, top_sup_eq, hc.sup_eq_top,
          Submodule.prod_top]
    rw [hr]
    exact key

/-- The map of `newSplit` is `primToRel`. (tex 4157–4166) Kind: PROVED (definitional). -/
theorem newSplit_i {Uq : GCx S} (EUq : SplitInclusion Uq Lq) :
    (newSplit D resq EUq).i = primToRel D resq EUq.i :=
  rfl

/-- The embedding `w ↦ (0, w)` of the complement at the new place. (tex 3489–3494)
Kind: definition. -/
def newMid (n : ℤ) : Lq.X n →ₗ[S] (relaxedAt D resq).U.X n :=
  LinearMap.inr S (D.U.X n) (Lq.X n)

/-- **The quotient of the local conditions is the local quotient at the new place**, degreewise
(tex 3489–3494: "the singular quotient by a cone of Selmer cones"). Kind: definition. -/
def newQEquiv {Uq : GCx S} (EUq : SplitInclusion Uq Lq) (n : ℤ) :
    EUq.Qc n ≃ₗ[S] (newSplit D resq EUq).Qc n :=
  (Submodule.equivMapOfInjective (newMid D resq n) LinearMap.inr_injective (EUq.Qc n)).trans
    (LinearEquiv.ofEq _ _ (by
      change (EUq.Qc n).map (LinearMap.inr S (D.U.X n) (Lq.X n)) =
        (⊥ : Submodule S (D.U.X n)).prod (EUq.Qc n)
      ext ⟨u, y⟩
      simp only [Submodule.mem_map, LinearMap.inr_apply, Prod.mk.injEq, Submodule.mem_prod,
        Submodule.mem_bot]
      constructor
      · rintro ⟨w, hw, rfl, rfl⟩
        exact ⟨rfl, hw⟩
      · rintro ⟨rfl, hy⟩
        exact ⟨y, hy, rfl, rfl⟩))

/-- `newQEquiv w = (0, w)`. (tex 3489–3494) Kind: PROVED (definitional). -/
theorem newQEquiv_apply {Uq : GCx S} (EUq : SplitInclusion Uq Lq) (n : ℤ) (w : EUq.Qc n) :
    ((newQEquiv D resq EUq n w : (newSplit D resq EUq).Qc n) : (relaxedAt D resq).U.X n) =
      (((0 : D.U.X n), (w : Lq.X n)) : D.U.X n × Lq.X n) :=
  rfl

/-- **The quotient differentials correspond** (tex 3489–3494). Kind: PROVED. -/
theorem newSplit_dQ {Uq : GCx S} (EUq : SplitInclusion Uq Lq) (a b : ℤ) (h : a + 1 = b)
    (w : EUq.Qc a) :
    (newSplit D resq EUq).dQ a b h (newQEquiv D resq EUq a w) =
      newQEquiv D resq EUq b (EUq.dQ a b h w) := by
  set E := newSplit D resq EUq
  have hmem : (((0 : D.U.X b), ((EUq.dQ a b h w : EUq.Qc b) : Lq.X b)) : D.U.X b × Lq.X b) ∈
      E.Qc b := ⟨(Submodule.mem_bot S).2 rfl, (EUq.dQ a b h w).2⟩
  let x : (prodCx D.U Uq).X b := ((0 : D.U.X b), EUq.offDiag a b h w)
  have hd : (relaxedAt D resq).U.d a b h (((0 : D.U.X a), (w : Lq.X a)) : D.U.X a × Lq.X a) =
      E.i.f b b rfl x +
        ((⟨((0 : D.U.X b), ((EUq.dQ a b h w : EUq.Qc b) : Lq.X b)), hmem⟩ : E.Qc b) :
          (relaxedAt D resq).U.X b) := by
    have hq := EUq.d_Q a b h w
    change ((D.U.d a b h 0, Lq.d a b h (w : Lq.X a)) : D.U.X b × Lq.X b) =
      (((0 : D.U.X b), EUq.i.f b b rfl (EUq.offDiag a b h w)) : D.U.X b × Lq.X b) +
        ((0 : D.U.X b), ((EUq.dQ a b h w : EUq.Qc b) : Lq.X b))
    rw [map_zero]
    exact Prod.ext (add_zero 0).symm hq
  apply Subtype.ext
  change (E.coordQ b ((relaxedAt D resq).U.d a b h
    (((0 : D.U.X a), (w : Lq.X a)) : D.U.X a × Lq.X a)) : (relaxedAt D resq).U.X b) = _
  rw [hd, map_add, E.coordQ_i, zero_add, E.coordQ_Q]
  rfl

/-- The equivalence of quotient complexes commutes with the differentials. (tex 3489–3494)
Kind: PROVED. -/
theorem newQEquiv_comm {Uq : GCx S} (EUq : SplitInclusion Uq Lq) (a b : ℤ) (h : a + 1 = b)
    (w : EUq.quotientCx.X a) :
    (newSplit D resq EUq).quotientCx.d a b h (newQEquiv D resq EUq a w) =
      newQEquiv D resq EUq b (EUq.quotientCx.d a b h w) :=
  newSplit_dQ D resq EUq a b h w

/-- **A retract of the local quotient at the new place is a retract of the quotient of the local
conditions** (tex 3489–3494). Kind: definition. -/
def newQuotRetract {Uq : GCx S} (EUq : SplitInclusion Uq Lq) {Q' : GCx S}
    (RW : GRetract EUq.quotientCx Q') : GRetract (newSplit D resq EUq).quotientCx Q' :=
  RW.ofEquiv (newQEquiv D resq EUq) (newQEquiv_comm D resq EUq)

end AddPlace

end ZInQ.Manuscript.RC.Wiring
