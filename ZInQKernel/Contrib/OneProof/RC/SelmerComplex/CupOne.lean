import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# Graded commutativity of the continuous cup product up to homotopy, in degree `(1, 1)`

Manuscript `diophantine_zq.tex`, tex 2813–2818; Nekovář, *Selmer complexes*, Astérisque 310
(2006), 3.4.5 (the cup products of continuous cochains are graded commutative up to an explicit
homotopy) and 6.2–6.3 (the symmetry of the induced pairings on Selmer complexes).

Let `β : A × A → T` be a `k`-bilinear, `G`-equivariant, jointly continuous pairing which is
`ε`-symmetric, `β(a, a') = ε • β(a', a)`. For continuous inhomogeneous `1`-cochains `a, b` with
values in `A` the two cup products `a ∪ b` and `b ∪ a` (with respect to `β`) differ, up to the
sign `ε`, by an explicit coboundary-plus-correction:
```
a ∪ b + ε • (b ∪ a) = d(cupOne11 a b) + cupOne21 (da) b + cupOne12 a (db)      in C²(T),
```
where (for `g, h ∈ G`)
* `cupOne11 a b : C¹(T)`, `g ↦ −β(a(g), b(g))`;
* `cupOne21 x b : C²(T)`, `(g, h) ↦ β(x(g, h), g • b(h) + b(g))` for a `2`-cochain `x`;
* `cupOne12 a y : C²(T)`, `(g, h) ↦ β(a(g h), y(g, h))` for a `2`-cochain `y`.
In particular, for cocycles `a, b` the class of `a ∪ b + ε • (b ∪ a)` vanishes. The proof uses
only the equivariance of `β`, its `ε`-symmetry and the expansion
`a(g h) = g • a(h) + a(g) − (da)(g, h)` of the inhomogeneous differential in degree one.

## Main declarations

* `cupOne11Fun`, `cupOne21Fun`, `cupOne12Fun`: the three correction cochains, as functions;
  `cupOne11Lin`, `cupOne21Lin`, `cupOne12Lin`: the same as `k`-bilinear maps.
* `cupFun_comm_homotopy`: the identity for arbitrary (not necessarily continuous) cochains.
* `contCupOne11`, `contCupOne21`, `contCupOne12`: the correction terms on continuous cochains
  (bilinear maps between the terms of `C^•_cont(G, −)`).
* `contCup_comm_homotopy`: the identity on `C^•_cont(G, −)` for the cup product `contCup`.
* `localCupOne11`, `localCupOne21`, `localCupOne12`, `localPair_comm_homotopy`: the local
  version on the complexes `C^•_cont(G_v, −)` and the local cup products `localPair`.

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

universe u

variable {k : Type u} [CommRing k]

/-! ### Low-degree formulas -/

section LowDegree

variable {G : Type u} [Group G]

/-- The inhomogeneous differential of a `1`-cochain: `(df)(g, h) = g • f(h) − f(g h) + f(g)`
(the degree-one case of the differential of Nekovář, *Selmer complexes*, 3.4.1; manuscript
tex 2813–2818). -/
theorem dFun_one_apply {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
    (f : (Fin 1 → G) → M) (g : Fin 2 → G) :
    dFun k 1 f g = g 0 • f (fun _ => g 1) - f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have e2 : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have e3 : Fin.contractNth (1 : Fin 2) (· * ·) g = fun _ => g 0 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have s0 : (-1 : k) ^ (((0 : Fin 2) : ℕ) + 1) = -1 := by norm_num
  have s1 : (-1 : k) ^ (((1 : Fin 2) : ℕ) + 1) = 1 := by norm_num
  show g 0 • f (fun i => g i.succ) + ∑ j : Fin 2, (-1 : k) ^ ((j : ℕ) + 1) •
      f (Fin.contractNth j (· * ·) g) = _
  rw [Fin.sum_univ_two, e1, e2, e3, s0, s1, neg_one_smul, one_smul]
  abel

/-- The product of the first entry of a pair: `headProd 1 2 (g, h) = g` (the translation in the
cup product of two `1`-cochains, Nekovář, *Selmer complexes*, 3.4.5). -/
theorem headProd_one_two (h : 1 ≤ 2) (g : Fin 2 → G) : headProd 1 2 h g = g 0 := by
  rw [headProd_succ 0 2 h g, headProd_zero, one_mul]
  rfl

/-- The cup product of two `1`-cochains: `(a ∪ b)(g, h) = β(a(g), g • b(h))` (Nekovář,
*Selmer complexes*, 3.4.5.1; manuscript tex 2813–2818). -/
theorem cupFun_one_one_apply {A B T : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] [MulAction G B] [AddCommGroup T] [Module k T] (β : A →ₗ[k] B →ₗ[k] T)
    (a : (Fin 1 → G) → A) (b : (Fin 1 → G) → B) (g : Fin 2 → G) :
    cupFun β 1 1 2 rfl a b g = β (a fun _ => g 0) (g 0 • b fun _ => g 1) := by
  have e1 : (fun i : Fin 1 => g (Fin.castLE (by omega) i)) = fun _ => g 0 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have e2 : (fun j : Fin 1 => g ⟨1 + j, by omega⟩) = fun _ => g 1 := by
    funext j; rw [Subsingleton.elim j 0]; rfl
  rw [cupFun_apply, e1, e2, headProd_one_two]

end LowDegree

/-! ### The correction cochains and the homotopy identity for arbitrary cochains -/

section Raw

variable {G : Type u} [Group G]
  {A T : Type u} [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  (β : A →ₗ[k] A →ₗ[k] T)

/-- The degree-`1` homotopy term `cupOne11 a b : C¹(T)`, `g ↦ −β(a(g), b(g))`, for two
`1`-cochains `a, b` (the `∪₁`-product of Nekovář, *Selmer complexes*, 3.4.5, in degree
`(1, 1)`; manuscript tex 2813–2818). -/
def cupOne11Fun (a b : (Fin 1 → G) → A) : (Fin 1 → G) → T :=
  fun g => -β (a g) (b g)

/-- The correction term `cupOne21 x b : C²(T)`, `(g, h) ↦ β(x(g, h), g • b(h) + b(g))`, for a
`2`-cochain `x` and a `1`-cochain `b` (the `∪₁`-product in degree `(2, 1)`, Nekovář,
*Selmer complexes*, 3.4.5; manuscript tex 2813–2818). -/
def cupOne21Fun (x : (Fin 2 → G) → A) (b : (Fin 1 → G) → A) : (Fin 2 → G) → T :=
  fun g => β (x g) (g 0 • b (fun _ => g 1) + b (fun _ => g 0))

/-- The correction term `cupOne12 a y : C²(T)`, `(g, h) ↦ β(a(g h), y(g, h))`, for a
`1`-cochain `a` and a `2`-cochain `y` (the `∪₁`-product in degree `(1, 2)`, Nekovář,
*Selmer complexes*, 3.4.5; manuscript tex 2813–2818). -/
def cupOne12Fun (a : (Fin 1 → G) → A) (y : (Fin 2 → G) → A) : (Fin 2 → G) → T :=
  fun g => β (a (fun _ => g 0 * g 1)) (y g)

/-- `cupOne11` as a `k`-bilinear map (Nekovář, *Selmer complexes*, 3.4.5). -/
def cupOne11Lin :
    ((Fin 1 → G) → A) →ₗ[k] ((Fin 1 → G) → A) →ₗ[k] ((Fin 1 → G) → T) :=
  LinearMap.mk₂ k (cupOne11Fun β)
    (fun a₁ a₂ b => by
      funext g
      simp only [cupOne11Fun, Pi.add_apply, map_add, LinearMap.add_apply, neg_add])
    (fun c a b => by
      funext g
      simp only [cupOne11Fun, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_neg])
    (fun a b₁ b₂ => by
      funext g
      simp only [cupOne11Fun, Pi.add_apply, map_add, neg_add])
    (fun c a b => by
      funext g
      simp only [cupOne11Fun, Pi.smul_apply, map_smul, smul_neg])

/-- `cupOne21` as a `k`-bilinear map (Nekovář, *Selmer complexes*, 3.4.5). -/
def cupOne21Lin :
    ((Fin 2 → G) → A) →ₗ[k] ((Fin 1 → G) → A) →ₗ[k] ((Fin 2 → G) → T) :=
  LinearMap.mk₂ k (cupOne21Fun β)
    (fun x₁ x₂ b => by
      funext g
      simp only [cupOne21Fun, Pi.add_apply, map_add, LinearMap.add_apply]
      abel)
    (fun c x b => by
      funext g
      simp only [cupOne21Fun, Pi.smul_apply, map_smul, LinearMap.smul_apply])
    (fun x b₁ b₂ => by
      funext g
      simp only [cupOne21Fun, Pi.add_apply, smul_add, map_add]
      abel)
    (fun c x b => by
      funext g
      simp only [cupOne21Fun, Pi.smul_apply]
      rw [smul_comm (g 0) c, ← smul_add, map_smul])

/-- `cupOne12` as a `k`-bilinear map (Nekovář, *Selmer complexes*, 3.4.5). -/
def cupOne12Lin :
    ((Fin 1 → G) → A) →ₗ[k] ((Fin 2 → G) → A) →ₗ[k] ((Fin 2 → G) → T) :=
  LinearMap.mk₂ k (cupOne12Fun β)
    (fun a₁ a₂ y => by
      funext g
      simp only [cupOne12Fun, Pi.add_apply, map_add, LinearMap.add_apply])
    (fun c a y => by
      funext g
      simp only [cupOne12Fun, Pi.smul_apply, map_smul, LinearMap.smul_apply])
    (fun a y₁ y₂ => by
      funext g
      simp only [cupOne12Fun, Pi.add_apply, map_add])
    (fun c a y => by
      funext g
      simp only [cupOne12Fun, Pi.smul_apply, map_smul])

omit [DistribMulAction G A] [SMulCommClass G k A] [DistribMulAction G T]
  [SMulCommClass G k T] in
/-- The pointwise algebraic identity behind the homotopy: for `ε`-symmetric `β` and elements
`A₁ = g • a(h)`, `A₂ = a(g h)`, `A₃ = a(g)` (and `B₁, B₂, B₃` likewise for `b`),
`β(A₃, B₁) + ε β(B₃, A₁) = (−β(A₁, B₁) − (−β(A₂, B₂)) + (−β(A₃, B₃)))
  + β(A₁ − A₂ + A₃, B₁ + B₃) + β(A₂, B₁ − B₂ + B₃)`; the first bracket is `d(cupOne11 a b)(g, h)`
(Nekovář, *Selmer complexes*, 3.4.5; manuscript tex 2813–2818). -/
theorem cupOne_key_identity (ε : k) (hε : ∀ a a' : A, β a a' = ε • β a' a)
    (A₁ A₂ A₃ B₁ B₂ B₃ : A) :
    β A₃ B₁ + ε • β B₃ A₁ =
      -β A₁ B₁ - -β A₂ B₂ + -β A₃ B₃ + β (A₁ - A₂ + A₃) (B₁ + B₃) +
        β A₂ (B₁ - B₂ + B₃) := by
  rw [← hε]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

omit [SMulCommClass G k A] [SMulCommClass G k T] in
/-- **Graded commutativity of the cup product up to homotopy, in degree `(1, 1)`, for arbitrary
inhomogeneous cochains.** For a `G`-equivariant, `ε`-symmetric pairing `β` and `1`-cochains
`a, b`: `a ∪ b + ε • (b ∪ a) = d(cupOne11 a b) + cupOne21 (da) b + cupOne12 a (db)` (Nekovář,
*Selmer complexes*, 3.4.5; manuscript tex 2813–2818). PROVED. -/
theorem cupFun_comm_homotopy (hβ : ∀ (g : G) (a a' : A), β (g • a) (g • a') = g • β a a')
    (ε : k) (hε : ∀ a a' : A, β a a' = ε • β a' a) (a b : (Fin 1 → G) → A) :
    cupFun β 1 1 2 rfl a b + ε • cupFun β 1 1 2 rfl b a =
      dFun k 1 (cupOne11Fun β a b) + cupOne21Fun β (dFun k 1 a) b +
        cupOne12Fun β a (dFun k 1 b) := by
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, cupFun_one_one_apply, dFun_one_apply, cupOne21Fun,
    cupOne12Fun, cupOne11Fun, smul_neg, ← hβ]
  exact cupOne_key_identity β ε hε _ _ _ _ _ _

end Raw

/-! ### Continuous cochains -/

section Continuous

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul G A]
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul G T]
  (β : A →ₗ[k] A →ₗ[k] T)

omit [Group G] [IsTopologicalGroup G] [DistribMulAction G A] [SMulCommClass G k A]
  [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul G A] [DistribMulAction G T]
  [SMulCommClass G k T] [ContinuousAdd T] [ContinuousSMul G T] in
/-- `cupOne11` of continuous cochains is continuous (Nekovář, *Selmer complexes*, 3.4.5). -/
theorem continuous_cupOne11Fun (hβc : Continuous fun x : A × A => β x.1 x.2)
    {a b : (Fin 1 → G) → A} (ha : Continuous a) (hb : Continuous b) :
    Continuous (cupOne11Fun β a b) := by
  have e : cupOne11Fun β a b = fun g => (-1 : k) • β (a g) (b g) :=
    funext fun g => (neg_one_smul k _).symm
  rw [e]
  exact (hβc.comp (ha.prodMk hb)).const_smul (-1 : k)

omit [IsTopologicalGroup G] [SMulCommClass G k A] [ContinuousConstSMul k A]
  [DistribMulAction G T] [SMulCommClass G k T] [ContinuousAdd T] [ContinuousConstSMul k T]
  [ContinuousSMul G T] in
/-- `cupOne21` of continuous cochains is continuous (Nekovář, *Selmer complexes*, 3.4.5). -/
theorem continuous_cupOne21Fun (hβc : Continuous fun x : A × A => β x.1 x.2)
    {x : (Fin 2 → G) → A} {b : (Fin 1 → G) → A} (hx : Continuous x) (hb : Continuous b) :
    Continuous (cupOne21Fun β x b) := by
  have h1 : Continuous fun g : Fin 2 → G => b fun _ => g 1 :=
    hb.comp (continuous_pi fun _ => continuous_apply 1)
  have h0 : Continuous fun g : Fin 2 → G => b fun _ => g 0 :=
    hb.comp (continuous_pi fun _ => continuous_apply 0)
  exact hβc.comp (hx.prodMk (((continuous_apply 0).smul h1).add h0))

omit [DistribMulAction G A] [SMulCommClass G k A] [ContinuousAdd A] [ContinuousConstSMul k A]
  [ContinuousSMul G A] [DistribMulAction G T] [SMulCommClass G k T] [ContinuousAdd T]
  [ContinuousConstSMul k T] [ContinuousSMul G T] in
/-- `cupOne12` of continuous cochains is continuous (Nekovář, *Selmer complexes*, 3.4.5). -/
theorem continuous_cupOne12Fun (hβc : Continuous fun x : A × A => β x.1 x.2)
    {a : (Fin 1 → G) → A} {y : (Fin 2 → G) → A} (ha : Continuous a) (hy : Continuous y) :
    Continuous (cupOne12Fun β a y) :=
  hβc.comp ((ha.comp (continuous_pi fun _ =>
    (continuous_apply 0).mul (continuous_apply 1))).prodMk hy)

/-- **The homotopy term `cupOne11 : C¹_cont(G, A) × C¹_cont(G, A) → C¹_cont(G, T)`**,
`(a, b) ↦ (g ↦ −β(a(g), b(g)))`, a `k`-bilinear map (Nekovář, *Selmer complexes*, 3.4.5;
manuscript tex 2813–2818). -/
def contCupOne11 (hβc : Continuous fun x : A × A => β x.1 x.2) :
    (contCochains k G A).X 1 →ₗ[k] (contCochains k G A).X 1 →ₗ[k] (contCochains k G T).X 1 :=
  LinearMap.mk₂ k
    (fun a b => (contSubCx k G T).ofSub ⟨cupOne11Fun β (cFun a) (cFun b),
      continuous_cupOne11Fun β hβc ((contSubCx k G A).el a).2 ((contSubCx k G A).el b).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (cupOne11Lin β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (cupOne11Lin β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (cupOne11Lin β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (cupOne11Lin β _) _ _))

/-- **The correction term `cupOne21 : C²_cont(G, A) × C¹_cont(G, A) → C²_cont(G, T)`**,
`(x, b) ↦ ((g, h) ↦ β(x(g, h), g • b(h) + b(g)))`, a `k`-bilinear map (Nekovář,
*Selmer complexes*, 3.4.5; manuscript tex 2813–2818). -/
def contCupOne21 (hβc : Continuous fun x : A × A => β x.1 x.2) :
    (contCochains k G A).X 2 →ₗ[k] (contCochains k G A).X 1 →ₗ[k] (contCochains k G T).X 2 :=
  LinearMap.mk₂ k
    (fun x b => (contSubCx k G T).ofSub ⟨cupOne21Fun β (cFun x) (cFun b),
      continuous_cupOne21Fun β hβc ((contSubCx k G A).el x).2 ((contSubCx k G A).el b).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (cupOne21Lin β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (cupOne21Lin β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (cupOne21Lin β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (cupOne21Lin β _) _ _))

/-- **The correction term `cupOne12 : C¹_cont(G, A) × C²_cont(G, A) → C²_cont(G, T)`**,
`(a, y) ↦ ((g, h) ↦ β(a(g h), y(g, h)))`, a `k`-bilinear map (Nekovář, *Selmer complexes*,
3.4.5; manuscript tex 2813–2818). -/
def contCupOne12 (hβc : Continuous fun x : A × A => β x.1 x.2) :
    (contCochains k G A).X 1 →ₗ[k] (contCochains k G A).X 2 →ₗ[k] (contCochains k G T).X 2 :=
  LinearMap.mk₂ k
    (fun a y => (contSubCx k G T).ofSub ⟨cupOne12Fun β (cFun a) (cFun y),
      continuous_cupOne12Fun β hβc ((contSubCx k G A).el a).2 ((contSubCx k G A).el y).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (cupOne12Lin β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (cupOne12Lin β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (cupOne12Lin β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (cupOne12Lin β _) _ _))

/-- **Graded commutativity of the continuous cup product up to homotopy, in degree `(1, 1)`**
(Nekovář, *Selmer complexes*, 3.4.5; manuscript tex 2813–2818): for a `G`-equivariant, jointly
continuous, `ε`-symmetric pairing `β : A × A → T` and continuous `1`-cochains `a, b`,
`a ∪ b + ε • (b ∪ a) = d(cupOne11 a b) + cupOne21 (da) b + cupOne12 a (db)` in `C²_cont(G, T)`.
PROVED. -/
theorem contCup_comm_homotopy (hβ : ∀ (g : G) (a a' : A), β (g • a) (g • a') = g • β a a')
    (hβc : Continuous fun x : A × A => β x.1 x.2) (ε : k) (hε : ∀ a a' : A, β a a' = ε • β a' a)
    (a b : (contCochains k G A).X 1) :
    contCup β hβc 1 1 2 rfl a b + ε • contCup β hβc 1 1 2 rfl b a =
      ((contCochains k G T).d 1 2).hom (contCupOne11 β hβc a b) +
        contCupOne21 β hβc (((contCochains k G A).d 1 2).hom a) b +
        contCupOne12 β hβc a (((contCochains k G A).d 1 2).hom b) := by
  apply Subtype.ext
  exact cupFun_comm_homotopy β hβ ε hε (cFun a) (cFun b)

end Continuous

/-! ### The local version on `C^•_cont(G_v, −)` -/

section Local

variable (k) (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {A T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction GS A] [SMulCommClass GS k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul GS A]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : A →ₗ[k] A →ₗ[k] T) (hβ : ∀ (g : GS) (a b : A), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : A × A => β x.1 x.2)

/-- The local homotopy term `cupOne11` on `C¹_cont(G_v, A)` (with `G_v` acting through
`loc_v`), `(a, b) ↦ (g ↦ −β(a(g), b(g)))` (Nekovář, *Selmer complexes*, 3.4.5 and 6.2–6.3;
manuscript tex 2813–2818). -/
def localCupOne11 (v : ι) :
    (localCx k GS Gv loc A v).X 1 →ₗ[k] (localCx k GS Gv loc A v).X 1 →ₗ[k]
      (localCx k GS Gv loc T v).X 1 :=
  contCupOne11 (G := Gv v) (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))

/-- The local correction term `cupOne21 : C²_cont(G_v, A) × C¹_cont(G_v, A) → C²_cont(G_v, T)`,
`(x, b) ↦ ((g, h) ↦ β(x(g, h), g • b(h) + b(g)))` (Nekovář, *Selmer complexes*, 3.4.5 and
6.2–6.3; manuscript tex 2813–2818). -/
def localCupOne21 (v : ι) :
    (localCx k GS Gv loc A v).X 2 →ₗ[k] (localCx k GS Gv loc A v).X 1 →ₗ[k]
      (localCx k GS Gv loc T v).X 2 :=
  contCupOne21 (G := Gv v) (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))

/-- The local correction term `cupOne12 : C¹_cont(G_v, A) × C²_cont(G_v, A) → C²_cont(G_v, T)`,
`(a, y) ↦ ((g, h) ↦ β(a(g h), y(g, h)))` (Nekovář, *Selmer complexes*, 3.4.5 and 6.2–6.3;
manuscript tex 2813–2818). -/
def localCupOne12 (v : ι) :
    (localCx k GS Gv loc A v).X 1 →ₗ[k] (localCx k GS Gv loc A v).X 2 →ₗ[k]
      (localCx k GS Gv loc T v).X 2 :=
  contCupOne12 (G := Gv v) (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))

omit [IsTopologicalGroup GS] in
/-- **Graded commutativity of the local cup product up to homotopy, in degree `(1, 1)`**
(Nekovář, *Selmer complexes*, 3.4.5, as used in 6.2–6.3; manuscript tex 2813–2818): for an
`ε`-symmetric pairing `β : A × A → T` and `a, b ∈ C¹_cont(G_v, A)`,
`a ∪ b + ε • (b ∪ a) = d(cupOne11 a b) + cupOne21 (da) b + cupOne12 a (db)`, where `∪` is the local
cup product `localPair`. PROVED. -/
theorem localPair_comm_homotopy (ε : k) (hε : ∀ a a' : A, β a a' = ε • β a' a) (v : ι)
    (a b : (localCx k GS Gv loc A v).X 1) :
    (localPair k GS Gv loc β hβ hβc v).P 1 1 2 rfl a b +
        ε • (localPair k GS Gv loc β hβ hβc v).P 1 1 2 rfl b a =
      (localCx k GS Gv loc T v).d 1 2 rfl (localCupOne11 k GS Gv loc β hβc v a b) +
        localCupOne21 k GS Gv loc β hβc v ((localCx k GS Gv loc A v).d 1 2 rfl a) b +
        localCupOne12 k GS Gv loc β hβc v a ((localCx k GS Gv loc A v).d 1 2 rfl b) :=
  contCup_comm_homotopy (G := Gv v) (resPairing k GS β (loc v)) (fun h a b => hβ (loc v h) a b)
    (resPairing_continuous k GS β hβc (loc v)) ε hε a b

end Local

end ZInQ.Manuscript.RC.SelmerComplex
