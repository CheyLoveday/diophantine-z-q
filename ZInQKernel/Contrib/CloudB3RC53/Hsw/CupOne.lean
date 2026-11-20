import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# RC53 cup-one: graded commutativity of the cup product in degrees `(1, 1)`

This file gives the Steenrod cup-one product on inhomogeneous cochains in the degrees needed at a
switched place (`H¹ × H¹ → H²`).

For a bilinear pairing `β : M × M → T` and `1`-cochains `a, b`, the cup-one product is

  `(a ∪₁ b)(g) = β(a(g), b(g))`   (`cupOneFun`).

Suppose `β` is `G`-equivariant and `c`-symmetric (`β x y = c • β y x`; the Weil pairing has
`c = −1`), and `b` is a `1`-cocycle. Then

  `d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X(da, b)`,
  `X(x, b)(g₀, g₁) = β(x(g₀, g₁), b(g₀) + g₀ • b(g₁))`   (`dFun_cupOneFun`).

So the cup product of `1`-cochains is graded-commutative up to an explicit homotopy. The correction
term `X` vanishes when `a` is also a cocycle.

* `dFun_one`, `cupFun_one_one_apply`: the differential and the cup product in low degrees.
* `dFun_cupOneFun`: the coboundary formula on inhomogeneous cochains.
* `contCupOne`, `contX2`, `contCupOne_d`: the same on continuous cochains `C^•_cont(G, −)` (the
  cochains of `Cochains.lean`).

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.SelmerComplex

universe u

/-! ### Inhomogeneous cochains -/

section Fun

variable {k G : Type u} [CommRing k] [Group G]
  {M T : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [AddCommGroup T] [Module k T] [DistribMulAction G T]

/-- **The cup-one product** of two inhomogeneous `1`-cochains, `(a ∪₁ b)(g) = β(a(g), b(g))`. -/
def cupOneFun (β : M →ₗ[k] M →ₗ[k] T) (a b : (Fin 1 → G) → M) : (Fin 1 → G) → T :=
  fun g => β (a g) (b g)

/-- The correction term `X(x, b)(g₀, g₁) = β(x(g₀, g₁), b(g₀) + g₀ • b(g₁))` for a `2`-cochain `x`
and a `1`-cochain `b`. -/
def x2Fun (β : M →ₗ[k] M →ₗ[k] T) (x : (Fin 2 → G) → M) (b : (Fin 1 → G) → M) :
    (Fin 2 → G) → T :=
  fun g => β (x g) (b (fun _ => g 0) + g 0 • b (fun _ => g 1))

omit [Group G] in
theorem fin1_eta (φ : Fin 1 → G) : φ = fun _ => φ 0 := by
  funext i; rw [Subsingleton.elim i 0]

/-- The inhomogeneous differential in degree one:
`(d f)(g₀, g₁) = g₀ • f(g₁) − f(g₀ g₁) + f(g₀)`. -/
theorem dFun_one (f : (Fin 1 → G) → M) (g : Fin 2 → G) :
    dFun k 1 f g = g 0 • f (fun _ => g 1) - f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  simp only [dFun, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one]
  have h0 : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have h1 : Fin.contractNth (1 : Fin 2) (· * ·) g = fun _ => g 0 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have hs : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  rw [h0, h1, hs]
  simp
  abel

omit [DistribMulAction G T] in
/-- The cup product in degrees `(1, 1)`: `(a ∪ b)(g₀, g₁) = β(a(g₀), g₀ • b(g₁))`. -/
theorem cupFun_one_one_apply (β : M →ₗ[k] M →ₗ[k] T) (a b : (Fin 1 → G) → M) (g : Fin 2 → G) :
    cupFun β 1 1 2 rfl a b g = β (a fun _ => g 0) (g 0 • b fun _ => g 1) := by
  rw [cupFun_apply]
  have h1 : (fun i : Fin 1 => g (Fin.castLE (by omega) i)) = fun _ => g 0 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have h2 : (fun j : Fin 1 => g ⟨1 + j, by omega⟩) = fun _ => g 1 := by
    funext j; rw [Subsingleton.elim j 0]; rfl
  have h3 : headProd 1 2 (by omega) g = g 0 := by
    change Fin.partialProd g (Fin.succ 0) = g 0
    rw [Fin.partialProd_succ, Fin.castSucc_zero, Fin.partialProd_zero, one_mul]
  rw [h1, h2, h3]

/-- **The cup-one coboundary formula in degrees `(1, 1)`** (Steenrod; graded commutativity of the
cup product up to an explicit homotopy). Let `β` be `G`-equivariant and `c`-symmetric,
`β x y = c • β y x`, and let `b` be a `1`-cocycle. Then
`d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X(da, b)`. `PROVED`. -/
theorem dFun_cupOneFun (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : G) (x y : M), β (g • x) (g • y) = g • β x y) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (a b : (Fin 1 → G) → M) (hb : dFun k 1 b = 0) :
    dFun k 1 (cupOneFun β a b) = -cupFun β 1 1 2 rfl a b - c • cupFun β 1 1 2 rfl b a +
      x2Fun β (dFun k 1 a) b := by
  funext g
  have hbg : g 0 • b (fun _ => g 1) - b (fun _ => g 0 * g 1) + b (fun _ => g 0) = 0 := by
    have := congrFun hb g
    rw [dFun_one] at this
    exact this
  have hB : b (fun _ => g 0 * g 1) = g 0 • b (fun _ => g 1) + b (fun _ => g 0) := by
    rw [sub_add_eq_add_sub, sub_eq_zero] at hbg
    exact hbg.symm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, dFun_one,
    cupFun_one_one_apply, x2Fun, cupOneFun]
  rw [hB, ← hβ, ← hc]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Fun

/-! ### Continuous cochains -/

section Cont

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M T : Type u}
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul G T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- The cup-one product as a bilinear map of inhomogeneous `1`-cochains. -/
def cupOneBil : ((Fin 1 → G) → M) →ₗ[k] ((Fin 1 → G) → M) →ₗ[k] ((Fin 1 → G) → T) :=
  LinearMap.mk₂ k (cupOneFun β)
    (fun _ _ _ => by funext g; simp [cupOneFun])
    (fun _ _ _ => by funext g; simp [cupOneFun])
    (fun _ _ _ => by funext g; simp [cupOneFun])
    (fun _ _ _ => by funext g; simp [cupOneFun])

/-- The correction term as a bilinear map. -/
def x2Bil : ((Fin 2 → G) → M) →ₗ[k] ((Fin 1 → G) → M) →ₗ[k] ((Fin 2 → G) → T) :=
  LinearMap.mk₂ k (x2Fun β)
    (fun _ _ _ => by funext g; simp [x2Fun])
    (fun _ _ _ => by funext g; simp [x2Fun])
    (fun _ _ _ => by funext g; simp [x2Fun, smul_add]; abel)
    (fun _ _ _ => by funext g; simp [x2Fun, smul_comm _ (_ : k)])

omit [Group G] [IsTopologicalGroup G] [DistribMulAction G M] [SMulCommClass G k M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M] [DistribMulAction G T]
  [SMulCommClass G k T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul G T] in
include hβc in
theorem continuous_cupOneFun {a b : (Fin 1 → G) → M} (ha : Continuous a) (hb : Continuous b) :
    Continuous (cupOneFun β a b) :=
  hβc.comp (ha.prodMk hb)

omit [IsTopologicalGroup G] [SMulCommClass G k M] [ContinuousConstSMul k M]
  [DistribMulAction G T] [SMulCommClass G k T] [ContinuousAdd T] [ContinuousConstSMul k T]
  [ContinuousSMul G T] in
include hβc in
theorem continuous_x2Fun {x : (Fin 2 → G) → M} {b : (Fin 1 → G) → M} (hx : Continuous x)
    (hb : Continuous b) : Continuous (x2Fun β x b) := by
  have c0 : Continuous fun g : Fin 2 → G => (fun _ : Fin 1 => g 0) :=
    continuous_pi fun _ => continuous_apply 0
  have c1 : Continuous fun g : Fin 2 → G => (fun _ : Fin 1 => g 1) :=
    continuous_pi fun _ => continuous_apply 1
  exact hβc.comp (hx.prodMk ((hb.comp c0).add ((continuous_apply 0).smul (hb.comp c1))))

/-- **The cup-one product of continuous `1`-cochains**, `C¹_cont(G, M) × C¹_cont(G, M) →
C¹_cont(G, T)`. -/
def contCupOne :
    (contCochains k G M).X 1 →ₗ[k] (contCochains k G M).X 1 →ₗ[k] (contCochains k G T).X 1 :=
  LinearMap.mk₂ k
    (fun a b => (contSubCx k G T).ofSub ⟨cupOneFun β (cFun a) (cFun b),
      continuous_cupOneFun β hβc ((contSubCx k G M).el a).2 ((contSubCx k G M).el b).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (cupOneBil β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (cupOneBil β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (cupOneBil β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (cupOneBil β _) _ _))

/-- The correction term on continuous cochains, `C²_cont(G, M) × C¹_cont(G, M) → C²_cont(G, T)`. -/
def contX2 :
    (contCochains k G M).X 2 →ₗ[k] (contCochains k G M).X 1 →ₗ[k] (contCochains k G T).X 2 :=
  LinearMap.mk₂ k
    (fun x b => (contSubCx k G T).ofSub ⟨x2Fun β (cFun x) (cFun b),
      continuous_x2Fun β hβc ((contSubCx k G M).el x).2 ((contSubCx k G M).el b).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (x2Bil β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (x2Bil β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (x2Bil β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (x2Bil β _) _ _))

/-- **The cup-one coboundary formula on continuous cochains** in degrees `(1, 1)`: for a
`c`-symmetric equivariant pairing and a continuous `1`-cocycle `y`,
`d(x ∪₁ y) = −x ∪ y − c • (y ∪ x) + X(dx, y)`. `PROVED`. -/
theorem contCupOne_d (hβ : ∀ (g : G) (x y : M), β (g • x) (g • y) = g • β x y) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (x y : (contCochains k G M).X 1)
    (hy : ((contCochains k G M).d 1 2).hom y = 0) :
    ((contCochains k G T).d 1 2).hom (contCupOne β hβc x y) =
      -contCup β hβc 1 1 2 rfl x y - c • contCup β hβc 1 1 2 rfl y x +
        contX2 β hβc (((contCochains k G M).d 1 2).hom x) y := by
  have hy' : dFun k 1 (cFun y) = 0 := by
    have h := congrArg (fun z : (contCochains k G M).X (1 + 1) =>
      asFun k G M (((contSubCx k G M).el z : contCochain k G M (1 + 1)) :
        (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1))) hy
    simp only at h
    rw [contCochains_d_coe] at h
    exact h
  apply Subtype.ext
  change ((((contSubCx k G T).el (((contCochains k G T).d 1 (1 + 1)).hom
      (contCupOne β hβc x y))) : contCochain k G T (1 + 1)) :
        (groupCohomology.inhomogeneousCochains (rep k G T)).X (1 + 1)) =
    -cupFun β 1 1 2 rfl (cFun x) (cFun y) - c • cupFun β 1 1 2 rfl (cFun y) (cFun x) +
      x2Fun β (asFun k G M ((((contSubCx k G M).el (((contCochains k G M).d 1 (1 + 1)).hom x)) :
        contCochain k G M (1 + 1)) : (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1)))
        (cFun y)
  rw [contCochains_d_coe, contCochains_d_coe]
  exact dFun_cupOneFun β hβ c hc (cFun x) (cFun y) hy'

end Cont

end ZInQ.Contrib.CloudB3RC53.Hsw
