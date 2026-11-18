import ZInQKernel.Contrib.CloudB3RC53.Hsw.CupOneTrunc

/-!
# RC53 cup-one: the general coboundary formula and strict conditions with degree-two terms

`CupOneReverse.lean` built `ReverseIsotropy` when the strict condition vanishes in degree two.
Here the strict condition may have degree-two terms. The cup-one formula is then needed for
arbitrary `1`-cochains:

  `d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X(da, b) + Y(a, db) − Z(da, db)`,

with `Y(a, y)(g₀, g₁) = β(a(g₀) + g₀ • a(g₁), y(g₀, g₁))` and `Z(x, y) = β(x, y)` pointwise
(`dFun_cupOneFun_gen`, `contCupOne_d_gen`). On top of that, `ReverseIsotropy` needs one constraint
on the isotropy homotopy `h`: its graded symmetry on strict × strict cochains in degree `(2, 1)`,

  `h(s, f t') = c • h(t', f s) + X(ι f s, ι f t') − Z(ι f s, ι f dt')`   (`StrictSymm`).

* `PairCupOneGen`, `PairCupOneGen.trunc`: general cup-one data and their `τ≥2` images.
* `reverseIsotropy_of_cupOneGen`: a general cup-one datum and `StrictSymm` give
  `ReverseIsotropy`.
* `strictSymm_of_zero`: `StrictSymm` is automatic when the strict condition vanishes in degree
  two, which recovers `CupOneReverse.lean`.
* `StrictSymmTrunc`, `strictSymm_trunc`: for `τ≥2`-truncated data the constraint is needed only
  modulo local coboundaries `d(E_L¹)`.
* `exists_residuePairing_trunc_of_cupOneGen`: the `hsw` descent for truncated data with
  degree-two strict terms.
* `localPairCupOneGen`: the general genuine cup-one datum on `⊕_v C^•_cont(G_v, −)`.
* `genuine_strictOrth_gen`: `StrictOrth` for the genuine switch under `StrictSymm`.
* Non-vacuity: `exGenuine_strictOrth_gen`.

`StrictSymm` is a condition on the chosen isotropy data. Some condition of this kind is needed:
`StrictOrth` is not implied by the axioms of `SelPairData` (`strictOrth_counterexample` in
`Descent.lean`, where the strict condition is nonzero in degree two).

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs

universe u

section Fun

variable {k G : Type u} [CommRing k] [Group G]
  {M T : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [AddCommGroup T] [Module k T] [DistribMulAction G T]

/-- The correction term `Y(a, y)(g₀, g₁) = β(a(g₀) + g₀ • a(g₁), y(g₀, g₁))`. -/
def y2Fun (β : M →ₗ[k] M →ₗ[k] T) (a : (Fin 1 → G) → M) (y : (Fin 2 → G) → M) :
    (Fin 2 → G) → T :=
  fun g => β (a (fun _ => g 0) + g 0 • a (fun _ => g 1)) (y g)

/-- The correction term `Z(x, y)(g₀, g₁) = β(x(g₀, g₁), y(g₀, g₁))`. -/
def zFun (β : M →ₗ[k] M →ₗ[k] T) (x y : (Fin 2 → G) → M) : (Fin 2 → G) → T :=
  fun g => β (x g) (y g)

/-- **The general cup-one coboundary formula in degrees `(1, 1)`** (`PROVED`): for a
`G`-equivariant `c`-symmetric pairing and arbitrary `1`-cochains `a, b`,
`d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X(da, b) + Y(a, db) − Z(da, db)`. -/
theorem dFun_cupOneFun_gen (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : G) (x y : M), β (g • x) (g • y) = g • β x y) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (a b : (Fin 1 → G) → M) :
    dFun k 1 (cupOneFun β a b) = -cupFun β 1 1 2 rfl a b - c • cupFun β 1 1 2 rfl b a +
      x2Fun β (dFun k 1 a) b + y2Fun β a (dFun k 1 b) - zFun β (dFun k 1 a) (dFun k 1 b) := by
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, dFun_one,
    cupFun_one_one_apply, x2Fun, y2Fun, zFun, cupOneFun]
  rw [← hβ, ← hc]
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

/-- `Y` as a bilinear map. -/
def y2Bil : ((Fin 1 → G) → M) →ₗ[k] ((Fin 2 → G) → M) →ₗ[k] ((Fin 2 → G) → T) :=
  LinearMap.mk₂ k (y2Fun β)
    (fun _ _ _ => by funext g; simp [y2Fun, smul_add]; abel)
    (fun _ _ _ => by funext g; simp [y2Fun, smul_comm _ (_ : k)])
    (fun _ _ _ => by funext g; simp only [y2Fun, Pi.add_apply, map_add])
    (fun _ _ _ => by funext g; simp [y2Fun])

/-- `Z` as a bilinear map. -/
def zBil : ((Fin 2 → G) → M) →ₗ[k] ((Fin 2 → G) → M) →ₗ[k] ((Fin 2 → G) → T) :=
  LinearMap.mk₂ k (zFun β)
    (fun _ _ _ => by funext g; simp [zFun])
    (fun _ _ _ => by funext g; simp [zFun])
    (fun _ _ _ => by funext g; simp [zFun])
    (fun _ _ _ => by funext g; simp [zFun])

omit [IsTopologicalGroup G] [SMulCommClass G k M] [ContinuousConstSMul k M]
  [DistribMulAction G T] [SMulCommClass G k T] [ContinuousAdd T] [ContinuousConstSMul k T]
  [ContinuousSMul G T] in
include hβc in
theorem continuous_y2Fun {a : (Fin 1 → G) → M} {y : (Fin 2 → G) → M} (ha : Continuous a)
    (hy : Continuous y) : Continuous (y2Fun β a y) := by
  have c0 : Continuous fun g : Fin 2 → G => (fun _ : Fin 1 => g 0) :=
    continuous_pi fun _ => continuous_apply 0
  have c1 : Continuous fun g : Fin 2 → G => (fun _ : Fin 1 => g 1) :=
    continuous_pi fun _ => continuous_apply 1
  exact hβc.comp (((ha.comp c0).add ((continuous_apply 0).smul (ha.comp c1))).prodMk hy)

omit [Group G] [IsTopologicalGroup G] [DistribMulAction G M] [SMulCommClass G k M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M] [DistribMulAction G T]
  [SMulCommClass G k T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul G T] in
include hβc in
theorem continuous_zFun {x y : (Fin 2 → G) → M} (hx : Continuous x) (hy : Continuous y) :
    Continuous (zFun β x y) :=
  hβc.comp (hx.prodMk hy)

/-- `Y` on continuous cochains, `C¹_cont × C²_cont → C²_cont`. -/
def contY2 :
    (contCochains k G M).X 1 →ₗ[k] (contCochains k G M).X 2 →ₗ[k] (contCochains k G T).X 2 :=
  LinearMap.mk₂ k
    (fun a y => (contSubCx k G T).ofSub ⟨y2Fun β (cFun a) (cFun y),
      continuous_y2Fun β hβc ((contSubCx k G M).el a).2 ((contSubCx k G M).el y).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (y2Bil β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (y2Bil β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (y2Bil β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (y2Bil β _) _ _))

/-- `Z` on continuous cochains, `C²_cont × C²_cont → C²_cont`. -/
def contZ :
    (contCochains k G M).X 2 →ₗ[k] (contCochains k G M).X 2 →ₗ[k] (contCochains k G T).X 2 :=
  LinearMap.mk₂ k
    (fun x y => (contSubCx k G T).ofSub ⟨zFun β (cFun x) (cFun y),
      continuous_zFun β hβc ((contSubCx k G M).el x).2 ((contSubCx k G M).el y).2⟩)
    (fun _ _ _ => Subtype.ext (LinearMap.map_add₂ (zBil β) _ _ _))
    (fun _ _ _ => Subtype.ext (LinearMap.map_smul₂ (zBil β) _ _ _))
    (fun _ _ _ => Subtype.ext (map_add (zBil β _) _ _))
    (fun _ _ _ => Subtype.ext (map_smul (zBil β _) _ _))

/-- **The general cup-one formula on continuous cochains** (`PROVED`). -/
theorem contCupOne_d_gen (hβ : ∀ (g : G) (x y : M), β (g • x) (g • y) = g • β x y) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (x y : (contCochains k G M).X 1) :
    ((contCochains k G T).d 1 2).hom (contCupOne β hβc x y) =
      -contCup β hβc 1 1 2 rfl x y - c • contCup β hβc 1 1 2 rfl y x +
        contX2 β hβc (((contCochains k G M).d 1 2).hom x) y +
        contY2 β hβc x (((contCochains k G M).d 1 2).hom y) -
        contZ β hβc (((contCochains k G M).d 1 2).hom x) (((contCochains k G M).d 1 2).hom y) := by
  apply Subtype.ext
  change ((((contSubCx k G T).el (((contCochains k G T).d 1 (1 + 1)).hom
      (contCupOne β hβc x y))) : contCochain k G T (1 + 1)) :
        (groupCohomology.inhomogeneousCochains (rep k G T)).X (1 + 1)) =
    -cupFun β 1 1 2 rfl (cFun x) (cFun y) - c • cupFun β 1 1 2 rfl (cFun y) (cFun x) +
      x2Fun β (asFun k G M ((((contSubCx k G M).el (((contCochains k G M).d 1 (1 + 1)).hom x)) :
        contCochain k G M (1 + 1)) : (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1)))
        (cFun y) +
      y2Fun β (cFun x)
        (asFun k G M ((((contSubCx k G M).el (((contCochains k G M).d 1 (1 + 1)).hom y)) :
        contCochain k G M (1 + 1)) :
          (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1))) -
      zFun β (asFun k G M ((((contSubCx k G M).el (((contCochains k G M).d 1 (1 + 1)).hom x)) :
        contCochain k G M (1 + 1)) : (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1)))
        (asFun k G M ((((contSubCx k G M).el (((contCochains k G M).d 1 (1 + 1)).hom y)) :
        contCochain k G M (1 + 1)) : (groupCohomology.inhomogeneousCochains (rep k G M)).X (1 + 1)))
  rw [contCochains_d_coe, contCochains_d_coe, contCochains_d_coe]
  exact dFun_cupOneFun_gen β hβ c hc (cFun x) (cFun y)

end Cont

/-! ### Reverse isotropy with degree-two strict terms -/

section Abstract

variable {k : Type} [Field k]

/-- **A general cup-one datum** for a self-pairing `P : A × A → T` in degrees `(1, 1)`:
`d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X(da, b) + Y(a, db) − Z(da, db)` for all `1`-cochains. -/
structure PairCupOneGen {A T : GCx k} (P : GPair A A T) (c : k) where
  /-- The cup-one product `A¹ × A¹ → T¹`. -/
  C11 : A.X 1 →ₗ[k] A.X 1 →ₗ[k] T.X 1
  /-- `X : A² × A¹ → T²`. -/
  X2 : A.X 2 →ₗ[k] A.X 1 →ₗ[k] T.X 2
  /-- `Y : A¹ × A² → T²`. -/
  Y2 : A.X 1 →ₗ[k] A.X 2 →ₗ[k] T.X 2
  /-- `Z : A² × A² → T²`. -/
  Z : A.X 2 →ₗ[k] A.X 2 →ₗ[k] T.X 2
  /-- The coboundary formula. -/
  formula : ∀ a b : A.X 1, T.d 1 2 rfl (C11 a b) = -P.P 1 1 2 rfl a b - c • P.P 1 1 2 rfl b a +
    X2 (A.d 1 2 rfl a) b + Y2 a (A.d 1 2 rfl b) - Z (A.d 1 2 rfl a) (A.d 1 2 rfl b)

variable (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)
  (Q : SelPairData (restrictData D f) D)

/-- The isotropy homotopy in degrees `(2, 1)`, arguments swapped. -/
def hUrev21 : D.U.X 1 →ₗ[k] Ustr.X 2 →ₗ[k] Q.EL.X 2 := (Q.hU 2 1 2 rfl).flip

/-- **The strict graded-symmetry condition** on the isotropy homotopy (degree `(2, 1)`):
`h(s, f t') = c • h(t', f s) + X(ι f s, ι f t') − Z(ι f s, ι f dt')`. It holds trivially when the
strict condition vanishes in degree two. -/
def StrictSymm {P : GPair D.L D.L Q.EL} {c : k} (Cd : PairCupOneGen P c) : Prop :=
  ∀ (s : Ustr.X 2) (t' : Ustr.X 1), Q.hU 2 1 2 rfl s (f.f 1 1 rfl t') =
    c • Q.hU 1 2 2 rfl t' (f.f 2 2 rfl s) +
      Cd.X2 (D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) -
      Cd.Z (D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t')))

/-- **Reverse isotropy with degree-two strict terms** (`PROVED`). A general cup-one datum and the
strict graded-symmetry condition `StrictSymm` give `ReverseIsotropy`, with
* `h'(u, t') = −c • h(t', u) − ι u ∪₁ ι f t'`,
* `h'(x, t') = c • h(t', x) + X(ι x, ι f t') − Z(ι x, ι f dt')`,
* `h'(u, y) = c • h(y, u) − Y(ι u, ι f y)`. -/
def reverseIsotropy_of_cupOneGen {P : GPair D.L D.L Q.EL} {c : k} (Cd : PairCupOneGen P c)
    (hP : ∀ a b, Q.cupL.P 1 1 2 rfl a b = P.P 1 1 2 rfl a b) (hsym : StrictSymm D Ustr f Q Cd) :
    ReverseIsotropy D Ustr f Q where
  h11 := -(c • hUrev11 D Ustr f Q) -
    Cd.C11.compl₁₂ (D.ι.f 1 1 rfl) (D.ι.f 1 1 rfl ∘ₗ f.f 1 1 rfl)
  h21 := c • hUrev12 D Ustr f Q +
    Cd.X2.compl₁₂ (D.ι.f 2 2 rfl) (D.ι.f 1 1 rfl ∘ₗ f.f 1 1 rfl) -
    Cd.Z.compl₁₂ (D.ι.f 2 2 rfl) (D.ι.f 2 2 rfl ∘ₗ f.f 2 2 rfl ∘ₗ Ustr.d 1 2 rfl)
  h12 := c • hUrev21 D Ustr f Q - Cd.Y2.compl₁₂ (D.ι.f 1 1 rfl) (D.ι.f 2 2 rfl ∘ₗ f.f 2 2 rfl)
  iso u t' := by
    have hform := Cd.formula (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))
    have iso : Q.EL.d 1 2 rfl (Q.hU 1 1 1 rfl t' u) + Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl t') u +
        sgn 1 • Q.hU 1 2 2 rfl t' (D.U.d 1 2 rfl u) =
        Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) (D.ι.f 1 1 rfl u) :=
      Q.isotropy 1 2 1 2 1 2 rfl rfl rfl rfl t' u
    have hda : D.L.d 1 2 rfl (D.ι.f 1 1 rfl u) = D.ι.f 2 2 rfl (D.U.d 1 2 rfl u) :=
      (D.ι.comm 1 2 1 2 rfl rfl rfl rfl u).symm
    have hdb : D.L.d 1 2 rfl (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) =
        D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t')) := by
      rw [← D.ι.comm 1 2 1 2 rfl rfl rfl rfl, ← f.comm 1 2 1 2 rfl rfl rfl rfl]
    rw [sgn_one, neg_one_smul, hP (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) (D.ι.f 1 1 rfl u)] at iso
    rw [hda, hdb] at hform
    change Q.EL.d 1 2 rfl (-(c • Q.hU 1 1 1 rfl t' u) -
        Cd.C11 (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))) +
      (c • Q.hU 1 2 2 rfl t' (D.U.d 1 2 rfl u) +
        Cd.X2 (D.ι.f 2 2 rfl (D.U.d 1 2 rfl u)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) -
        Cd.Z (D.ι.f 2 2 rfl (D.U.d 1 2 rfl u))
          (D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t')))) +
      sgn 1 • (c • Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl t') u -
        Cd.Y2 (D.ι.f 1 1 rfl u) (D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t')))) = _
    rw [hP (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')), map_sub, map_neg, map_smul, hform,
      sgn_one, neg_one_smul]
    have e : Q.EL.d 1 2 rfl (Q.hU 1 1 1 rfl t' u) =
        P.P 1 1 2 rfl (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) (D.ι.f 1 1 rfl u) -
          Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl t') u + Q.hU 1 2 2 rfl t' (D.U.d 1 2 rfl u) := by
      rw [← iso]; abel
    rw [e, smul_add, smul_sub]
    abel
  compat s t' := hsym s t'

/-- **`StrictSymm` is automatic when the strict condition vanishes in degree two**. -/
theorem strictSymm_of_zero {P : GPair D.L D.L Q.EL} {c : k} (Cd : PairCupOneGen P c)
    (h2 : ∀ x : Ustr.X 2, x = 0) : StrictSymm D Ustr f Q Cd := by
  intro s t'
  have hs : s = 0 := h2 s
  subst hs
  have hd : Ustr.d 1 2 rfl t' = 0 := h2 _
  change Q.hU 2 1 2 rfl 0 (f.f 1 1 rfl t') = c • Q.hU 1 2 2 rfl t' (f.f 2 2 rfl 0) +
      Cd.X2 (D.ι.f 2 2 rfl (f.f 2 2 rfl 0)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) -
      Cd.Z (D.ι.f 2 2 rfl (f.f 2 2 rfl 0)) (D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t')))
  rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, map_zero, smul_zero, map_zero,
    LinearMap.zero_apply, map_zero, LinearMap.zero_apply, add_zero, sub_zero]

end Abstract

/-! ### Truncated data -/

section Trunc

variable {k : Type} [Field k]

/-- Pushing a general cup-one datum into `τ≥2` (`PROVED`). -/
def PairCupOneGen.trunc {A T : GCx k} {P : GPair A A T} {c : k} (Cd : PairCupOneGen P c) :
    PairCupOneGen (truncPair P) c where
  C11 := Cd.C11.compr₂ (truncSub T 1).mkQ
  X2 := Cd.X2.compr₂ (truncSub T 2).mkQ
  Y2 := Cd.Y2.compr₂ (truncSub T 2).mkQ
  Z := Cd.Z.compr₂ (truncSub T 2).mkQ
  formula a b := by
    change (truncSub T 2).mkQ (T.d 1 2 rfl (Cd.C11 a b)) =
      -(truncSub T 2).mkQ (P.P 1 1 2 rfl a b) - c • (truncSub T 2).mkQ (P.P 1 1 2 rfl b a) +
        (truncSub T 2).mkQ (Cd.X2 (A.d 1 2 rfl a) b) +
        (truncSub T 2).mkQ (Cd.Y2 a (A.d 1 2 rfl b)) -
        (truncSub T 2).mkQ (Cd.Z (A.d 1 2 rfl a) (A.d 1 2 rfl b))
    rw [Cd.formula a b]
    simp only [map_add, map_sub, map_neg, map_smul]

variable (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)

/-- **The strict graded-symmetry condition modulo local coboundaries**: the condition
`StrictSymm` for `τ≥2`-truncated data only has to hold modulo `d(E_L¹)`. -/
def StrictSymmTrunc (Q : SelPairDataTrunc (restrictData D f) D) {P : GPair D.L D.L Q.EL} {c : k}
    (Cd : PairCupOneGen P c) : Prop :=
  ∀ (s : Ustr.X 2) (t' : Ustr.X 1), Q.hU 2 1 2 rfl s (f.f 1 1 rfl t') -
    (c • Q.hU 1 2 2 rfl t' (f.f 2 2 rfl s) +
      Cd.X2 (D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) -
      Cd.Z (D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t')))) ∈
    LinearMap.range (Q.EL.d 1 2 rfl)

/-- `StrictSymmTrunc` gives `StrictSymm` for the `τ≥2` data (`PROVED`). -/
theorem strictSymm_trunc (Q : SelPairDataTrunc (restrictData D f) D) {P : GPair D.L D.L Q.EL}
    {c : k} (Cd : PairCupOneGen P c) (hsym : StrictSymmTrunc D Ustr f Q Cd) :
    StrictSymm D Ustr f Q.toSelPairData Cd.trunc := by
  intro s t'
  change (truncSub Q.EL 2).mkQ (Q.hU 2 1 2 rfl s (f.f 1 1 rfl t')) =
    c • (truncSub Q.EL 2).mkQ (Q.hU 1 2 2 rfl t' (f.f 2 2 rfl s)) +
      (truncSub Q.EL 2).mkQ
        (Cd.X2 (D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))) -
      (truncSub Q.EL 2).mkQ
        (Cd.Z (D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (D.ι.f 2 2 rfl (f.f 2 2 rfl (Ustr.d 1 2 rfl t'))))
  rw [← map_smul, ← map_add, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, truncSub_of_eq Q.EL rfl]
  exact hsym s t'

end Trunc

/-! ### Descent with degree-two strict terms -/

section DescentGen

variable {k : Type} [Field k]

/-- **The `hsw` descent for `τ≥2`-truncated data with degree-two strict terms** (`PROVED`). Assume
the switch exactness data, a trace killing cone coboundaries, a general cup-one datum for the
local cup product, and the strict graded-symmetry condition modulo local coboundaries. Then the
truncated `hsw` left-hand side is a residue pairing. -/
theorem exists_residuePairing_trunc_of_cupOneGen (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairDataTrunc (restrictData R.D f) R.D)
    (tr0 : (coneCx Q.resE).X 3 →ₗ[k] k) (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    {P : GPair R.D.L R.D.L Q.EL} {c : k} (Cd : PairCupOneGen P c)
    (hP : ∀ a b, Q.cupL.P 1 1 2 rfl a b = P.P 1 1 2 rfl a b)
    (hsym : StrictSymmTrunc R.D Ustr f Q Cd) :
    ∃ P' : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)),
      ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
        (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
        (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
        tr0 (selCupFunT Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
          P' (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu)) :=
  exists_residuePairing_trunc R Ustr f Q tr0 htr0 hfg hf hg hex
    (strictOrth_of_reverseIsotropy R.D Ustr f Q.toSelPairData (Q.trT tr0 htr0)
      (Q.trT_kills tr0 htr0)
      (reverseIsotropy_of_cupOneGen R.D Ustr f Q.toSelPairData Cd.trunc
        (fun a b => by
          change (truncSub Q.EL 2).mkQ (Q.cupL.P 1 1 2 rfl a b) =
            (truncSub Q.EL 2).mkQ (P.P 1 1 2 rfl a b)
          rw [hP])
        (strictSymm_trunc R.D Ustr f Q Cd hsym)))

end DescentGen

/-! ### The genuine local cup product -/

section Local

variable {k : Type} [Field k] (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {M T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GS) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- The place-wise `Y`. -/
def sumY2 : (localSumCx k GS Gv loc M).X 1 →ₗ[k] (localSumCx k GS Gv loc M).X 2 →ₗ[k]
    (localSumCx k GS Gv loc T).X 2 :=
  LinearMap.mk₂ k (fun a b v =>
      contY2 (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v)) (a v) (b v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by
      funext v
      exact LinearMap.map_smul₂
        (contY2 (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))) _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun c a b => by
      funext v
      exact map_smul (contY2 (resPairing k GS β (loc v))
        (resPairing_continuous k GS β hβc (loc v)) (a v)) c (b v))

/-- The place-wise `Z`. -/
def sumZ : (localSumCx k GS Gv loc M).X 2 →ₗ[k] (localSumCx k GS Gv loc M).X 2 →ₗ[k]
    (localSumCx k GS Gv loc T).X 2 :=
  LinearMap.mk₂ k (fun a b v =>
      contZ (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v)) (a v) (b v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by
      funext v
      exact LinearMap.map_smul₂
        (contZ (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))) _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun c a b => by
      funext v
      exact map_smul (contZ (resPairing k GS β (loc v))
        (resPairing_continuous k GS β hβc (loc v)) (a v)) c (b v))

/-- **The general genuine cup-one datum** of `⊕_v C^•_cont(G_v, −)` (`PROVED`), for a
`c`-symmetric equivariant self-pairing. -/
def localPairCupOneGen (c : k) (hc : ∀ x y, β x y = c • β y x) :
    PairCupOneGen (localSumPair k GS Gv loc β hβ hβc) c where
  C11 := sumCupOne GS Gv loc β hβc
  X2 := sumX2 GS Gv loc β hβc
  Y2 := sumY2 GS Gv loc β hβc
  Z := sumZ GS Gv loc β hβc
  formula a b := by
    funext v
    exact contCupOne_d_gen (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))
      (fun h x y => hβ (loc v h) x y) c hc (a v) (b v)

end Local

/-! ### The genuine switch -/

section Genuine

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **`StrictOrth` for the genuine switch with degree-two strict terms** (`PROVED`). For a
`c`-symmetric equivariant self-pairing and isotropy data satisfying the strict graded-symmetry
condition `StrictSymm`, the cone-trace cup product vanishes on strict cocycles in the second
slot. -/
theorem genuine_strictOrth_gen (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hsym : StrictSymm X.toQuasi.D (piCx X.US) (piMap X.φ)
      (galoisPairData K S k β hβ X.ΔS X.ΔR I)
      (localPairCupOneGen (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
        β hβ (continuous_pairing β) c hc)) :
    StrictOrth X.toQuasi.D (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr :=
  strictOrth_of_reverseIsotropy _ _ _ _ tr htr
    (reverseIsotropy_of_cupOneGen _ _ _ _ _ (fun _ _ => rfl) hsym)

end Genuine

/-! ### Non-vacuity (LESSON 2) -/

section NonVacuity

/-- **Non-vacuity of `genuine_strictOrth_gen`** (`PROVED`): on the example genuine switch (zero
pairing, `c = 1`, zero isotropy data, zero trace) `StrictSymm` holds (`strictSymm_of_zero`), and
`StrictOrth` follows. -/
theorem exGenuine_strictOrth_gen {k : Type} [Field k] (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    StrictOrth (exGenuineSwitch (k := k) K q).toQuasi.D (piCx (exGenuineSwitch K q).US)
      (piMap (exGenuineSwitch K q).φ) (galoisPairData K {q} k _ _ _ _ (exIsotropy K q)) 0 :=
  genuine_strictOrth_gen (exGenuineSwitch (k := k) K q) _ _ (1 : k) (fun _ _ => rfl)
    (exIsotropy K q) 0 (fun _ => rfl)
    (strictSymm_of_zero _ _ _ _ _ (fun x => funext fun v => exGenuineSwitch_US2 K q v (x v)))

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.Hsw
