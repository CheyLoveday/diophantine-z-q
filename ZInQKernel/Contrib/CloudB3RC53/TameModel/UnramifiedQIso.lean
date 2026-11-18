import ZInQKernel.Contrib.CloudB3RC53.TameModel.QIsoCriterion
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.CdOne

/-!
# The unramified two-term complex is quasi-isomorphic to the genuine continuous cochains of `ℤ̂`

Manuscript `diophantine_zq.tex`, tex 3478–3481 (the unramified complex `[Φ − 1]` in degrees zero
and one) and the unramified half of the tame model (4.4), L3443–3448.

**Cohomological dimension one on the genuine cochains, all degrees.** Through the all-degree
comparison `contCohomologyLinearEquiv` (ContBridge) the unramified-complex lane's
`Hⁿ(ℤ̂, W) = 0` (`n ≥ 2`, Mathlib's `continuousCohomology`) becomes the vanishing of lane RC26's
`contCohomology k G M n`:

* `subsingleton_contCohomology_ge_two`: finite discrete `M`, any coefficient ring `k`;
* `subsingleton_contCohomology_of_torsion`: discrete torsion `M`, `k = ℤ`.

**The quasi-isomorphism.** For `G ≃ₜ* ℤ̂` and a finite discrete continuous representation `X`
of `G` on `W`, lane RC26's cochain map `urToLocal` (degree `0`: constants; degree `1`:
`x ↦ c_x`, the `ℤ̂`-cocycle with `c_x(Frob) = x`), taken along the identity of `G` and of `W`
(`urSelf`), is a quasi-isomorphism `[W --(Φ−1)--> W] ⟶ C^•_cont(G, W)` of `ℤ`-indexed complexes
(`urSelf_quasiIso`): on `H⁰` both sides are `W^G = ker (Φ − 1)` (the Frobenius powers are dense);
on `H¹` a continuous cocycle is determined by its value at the Frobenius
(`eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top`) and `c_x = d m` forces
`x = (Φ − 1) m`; in degrees `≥ 2` both sides vanish (the first part); in negative degrees both
complexes are zero. The criterion used is `quasiIsoAt_of_elem` (`QIsoCriterion.lean`).
`urSelf_galois_quasiIso`: the instance at a finite place of a number field,
`G = Gal(K_w^ur/K_w)`.

This supersedes the chain map `twoTermToCont` of `ProcyclicTwoTerm.lean` (same formulas, but into
the `GCx` form `natCx` and with its own choice of period): the canonical map is RC26's
`urToLocal`, and it is the one proved to be a quasi-isomorphism here.

Kinds: everything PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameModel

open CategoryTheory Limits TauCeti.ContCohomology ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.ContBridge

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Cohomological dimension one on the genuine cochains -/

section CdOne

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [LocallyCompactSpace G]
  (e : G ≃ₜ* TauCeti.zHat.{0})

include e in
/-- **`Hⁿ_cont(G, M) = 0` for `n ≥ 2` on lane RC26's genuine cochains**, `G ≃ₜ* ℤ̂`, `M` finite
discrete (PROVED). -/
theorem subsingleton_contCohomology_ge_two (k : Type) [CommRing k] [TopologicalSpace k]
    (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [SMulCommClass G k M] [ContinuousSMul k M] [ContinuousSMul G M]
    [Finite M] (n : ℕ) (hn : 2 ≤ n) : Subsingleton (contCohomology k G M n) := by
  have : ContinuousSMul G (TauCeti.ofDiscreteModule k G M).V :=
    ⟨(continuous_smul : Continuous fun p : G × M => p.1 • p.2)⟩
  have : Finite (TauCeti.ofDiscreteModule k G M).V := inferInstanceAs (Finite M)
  have := subsingleton_continuousCohomology_ge_two e (TauCeti.ofDiscreteModule k G M) n hn
  exact (contCohomologyLinearEquiv k G M n).symm.injective.subsingleton

include e in
/-- **`Hⁿ_cont(G, M) = 0` for `n ≥ 2` and discrete torsion `M`** (integral coefficients) on lane
RC26's genuine cochains (PROVED). -/
theorem subsingleton_contCohomology_of_torsion (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] (hT : IsAddTorsion M)
    (n : ℕ) (hn : 2 ≤ n) : Subsingleton (contCohomology ℤ G M n) := by
  have : ContinuousSMul ℤ M := continuousSMul_of_discrete ℤ M
  have := subsingleton_continuousCohomology_of_torsion e n hn M hT
  exact (contCohomologyLinearEquiv ℤ G M n).symm.injective.subsingleton

end CdOne

/-! ### The quasi-isomorphism -/

section QIso

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : G ≃ₜ* TauCeti.zHat.{0}) (X : TopRep.{0} k G)
  [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V]

/-- **The unramified comparison map** `[W --(Φ−1)--> W] ⟶ C^•_cont(G, W)`: lane RC26's
`urToLocal` along the identities of `G` and `W`. -/
def urSelf : frobCx (frob e X) ⟶ locCC (k := k) (G := G) (M := X.V) :=
  urToLocal e (ContinuousMonoidHom.id G) X LinearMap.id (fun _ _ => rfl)

theorem eq_zero_of_isZero {R : Type} [Ring R] {Z : ModuleCat.{0} R} (h : IsZero Z) (x : Z) :
    x = 0 :=
  congrArg (fun f => f.hom x) (h.eq_of_src (𝟙 Z) 0)

theorem urSelf_f₀ (x : (frobCx (frob e X)).X 0) :
    ((urSelf e X).f 0).hom x = urLin₀ (G := G) X LinearMap.id
      ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).hom.hom x) := by
  exact congrArg (fun f => f.hom x)
    (urToLocal_f₀ e (ContinuousMonoidHom.id G) X LinearMap.id (fun _ _ => rfl))

theorem urSelf_f₁ (x : (frobCx (frob e X)).X 1) :
    ((urSelf e X).f 1).hom x = urLin₁ e (ContinuousMonoidHom.id G) X LinearMap.id
      ((HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob e X - 1)) rel01
        (by decide)).hom.hom x) := by
  exact congrArg (fun f => f.hom x)
    (urToLocal_f₁ e (ContinuousMonoidHom.id G) X LinearMap.id (fun _ _ => rfl))

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V] in
theorem frobCx_d01_apply (x : (frobCx (frob e X)).X 0) :
    ((frobCx (frob e X)).d 0 1).hom x =
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob e X - 1)) rel01 (by decide)).inv.hom
        ((frob e X - 1) ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1))
          rel01).hom.hom x)) := by
  rw [frobCx_d01]
  rfl

omit [Finite X.V] in
/-- The differential of `locCC` between nonnegative degrees is that of `contCochains`. -/
theorem locCC_d_apply (n : ℕ) (x : (contCochains k G X.V).X n) :
    ((locCC (k := k) (G := G) (M := X.V)).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x =
      ((contCochains k G X.V).d n (n + 1)).hom x :=
  PairedFunctional.GCx.toCC_d_hom (natCx (contCochains k G X.V)) (n : ℤ) ((n + 1 : ℕ) : ℤ)
    (by push_cast; rfl) x

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem fin1_eq' (v : Fin 1 → G) : v = fun _ => v 0 := by
  funext i
  rw [Subsingleton.elim i 0]

omit [IsTopologicalGroup G] [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V] in
/-- Elements of `frobCx` outside degrees `0, 1` vanish. -/
theorem frobCx_eq_zero (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (x : (frobCx (frob e X)).X n) : x = 0 :=
  eq_zero_of_isZero (isZero_X _ n h0 h1) x

/-- Degree `0`: both sides are `W^G`. -/
theorem urSelf_quasiIsoAt_zero : QuasiIsoAt (urSelf e X) 0 := by
  refine quasiIsoAt_of_elem _ (-1) 0 1 prev0 next0 ?_ ?_
  · intro (y : (contCochains k G X.V).X 0) hy
    have hy' : ((contCochains k G X.V).d 0 1).hom y = 0 := (locCC_d_apply X 0 y).symm.trans hy
    set m₀ := contFun (k := k) (G := G) (M := X.V) (y : (contCochains k G X.V).X 0)
      Fin.elim0 with hm₀
    have hinv : ∀ g : G, g • m₀ - m₀ = 0 := fun g => by
      have := congrArg (fun c => contFun (k := k) (G := G) (M := X.V) c (fun _ => g)) hy'
      exact (contFun_d01 (k := k) (G := G) (M := X.V) y g).symm.trans this
    refine ⟨(HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).inv.hom m₀,
      ?_, 0, ?_⟩
    · refine (frobCx_d01_apply e X _).trans ?_
      rw [Iso.inv_hom_id_apply, LinearMap.sub_apply, frob_apply,
        Module.End.one_apply, hinv, map_zero]
      exact rfl
    · have key : urLin₀ (G := G) X LinearMap.id m₀ = y := by
        refine Subtype.ext (funext fun v => ?_)
        change m₀ = contFun (k := k) (G := G) (M := X.V) (y : (contCochains k G X.V).X 0) v
        rw [hm₀, Subsingleton.elim v Fin.elim0]
      rw [map_zero]
      exact (urSelf_f₀ e X _).trans ((congrArg _ (Iso.inv_hom_id_apply _ _)).trans
        (key.trans (add_zero y).symm))
  · intro x _ z hxz
    have hz0 : z = 0 := rfl
    rw [hz0, map_zero, urSelf_f₀] at hxz
    have hval := congrArg (fun c : contCochain k G X.V 0 =>
      contFun (k := k) (G := G) (M := X.V) (c : (contCochains k G X.V).X 0) Fin.elim0) hxz
    change (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).hom.hom x = 0
      at hval
    refine ⟨0, ?_⟩
    rw [map_zero]
    have := Iso.hom_inv_id_apply (HomologicalComplex.doubleXIso₀
      (ModuleCat.ofHom (frob e X - 1)) rel01) x
    rw [hval, map_zero] at this
    exact this

/-- Degree `1`: a continuous cocycle is determined by its value at the Frobenius, and
`c_x = d m` forces `x = (Φ − 1) m`. -/
theorem urSelf_quasiIsoAt_one : QuasiIsoAt (urSelf e X) 1 := by
  refine quasiIsoAt_of_elem _ 0 1 2 prev1 next1 ?_ ?_
  · intro (y : (contCochains k G X.V).X 1) hy
    have hy' : ((contCochains k G X.V).d 1 2).hom y = 0 := (locCC_d_apply X 1 y).symm.trans hy
    have hZ := mem_Z1_of_d_eq_zero (k := k) (G := G) (M := X.V) y hy'
    set m₁ := contFun (k := k) (G := G) (M := X.V) y (fun _ => frobElt e) with hm₁
    have hc : urCocycle e X m₁ = fun g : G => contFun (k := k) (G := G) (M := X.V) y (fun _ => g) :=
      eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top (urCocycle_mem e X m₁) hZ
        (closure_frob_eq_top e) (fun g hg => by
          rw [Set.mem_singleton_iff] at hg
          subst hg
          exact urCocycle_frob e X m₁)
    refine ⟨(HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob e X - 1)) rel01
      (by decide)).inv.hom m₁, ?_, 0, ?_⟩
    · rw [frobCx_d_next]
      exact rfl
    · have key : urLin₁ e (ContinuousMonoidHom.id G) X LinearMap.id m₁ = y := by
        refine Subtype.ext (funext fun v => ?_)
        change urCocycle e X m₁ (v 0) =
          contFun (k := k) (G := G) (M := X.V) (y : (contCochains k G X.V).X 1) v
        rw [hc, fin1_eq' v]
      rw [map_zero]
      exact (urSelf_f₁ e X _).trans ((congrArg _ (Iso.inv_hom_id_apply _ _)).trans
        (key.trans (add_zero y).symm))
  · intro x _ (z : (contCochains k G X.V).X 0) hxz
    have hxz' := hxz.trans (locCC_d_apply X 0 z)
    rw [urSelf_f₁] at hxz'
    set m := (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob e X - 1)) rel01
      (by decide)).hom.hom x with hm
    have hval := congrArg (fun c : contCochain k G X.V 1 =>
      contFun (k := k) (G := G) (M := X.V) (c : (contCochains k G X.V).X 1)
        (fun _ => frobElt e)) hxz'
    change urCocycle e X m (frobElt e) = _ at hval
    rw [urCocycle_frob, contFun_d01] at hval
    refine ⟨(HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).inv.hom
      (contFun (k := k) (G := G) (M := X.V) z Fin.elim0), ?_⟩
    refine (frobCx_d01_apply e X _).trans ?_
    rw [Iso.inv_hom_id_apply, LinearMap.sub_apply, frob_apply, Module.End.one_apply, ← hval, hm]
    exact Iso.hom_inv_id_apply _ x

variable [CompactSpace G] [TotallyDisconnectedSpace G] [LocallyCompactSpace G]

/-- Degrees `≥ 2`: both sides vanish. -/
theorem urSelf_quasiIsoAt_ge_two (m : ℕ) : QuasiIsoAt (urSelf e X) ((m + 2 : ℕ) : ℤ) := by
  refine quasiIsoAt_of_elem _ ((m + 1 : ℕ) : ℤ) ((m + 2 : ℕ) : ℤ) ((m + 2 + 1 : ℕ) : ℤ)
    (by simp; omega) (by simp) ?_ ?_
  · intro (y : (contCochains k G X.V).X (m + 2)) hy
    have hy' : ((contCochains k G X.V).d (m + 2) (m + 2 + 1)).hom y = 0 :=
      (locCC_d_apply X (m + 2) y).symm.trans hy
    have hsub := subsingleton_contCohomology_ge_two e k X.V (m + 2) (by omega)
    have hex : (contCochains k G X.V).ExactAt (m + 2) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (ModuleCat.isZero_of_subsingleton _)
    rw [HomologicalComplex.exactAt_iff' _ (m + 1) (m + 2) (m + 2 + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hex
    obtain ⟨z, hz⟩ := hex y hy'
    have h2 : ((locCC (k := k) (G := G) (M := X.V)).d ((m + 1 : ℕ) : ℤ) ((m + 2 : ℕ) : ℤ)).hom
        (-z) = -y :=
      (locCC_d_apply X (m + 1) (-z)).trans ((map_neg _ z).trans (congrArg Neg.neg hz))
    refine ⟨0, map_zero _, -z, ?_⟩
    refine (map_zero _).trans ?_
    rw [h2]
    exact (add_neg_cancel y).symm
  · intro x _ z _
    refine ⟨0, ?_⟩
    rw [map_zero, frobCx_eq_zero e X _ (by omega) (by omega) x]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [LocallyCompactSpace G] in
/-- Negative degrees: both complexes vanish. -/
theorem urSelf_quasiIsoAt_neg (m : ℕ) : QuasiIsoAt (urSelf e X) (Int.negSucc m) := by
  refine quasiIsoAt_of_elem _ (Int.negSucc m - 1) (Int.negSucc m) (Int.negSucc m + 1)
    (by simp) (by simp) ?_ ?_
  · intro y _
    refine ⟨0, map_zero _, 0, ?_⟩
    have hy : y = 0 := rfl
    rw [hy, map_zero, map_zero, add_zero]
  · intro x _ z _
    refine ⟨0, ?_⟩
    rw [map_zero, frobCx_eq_zero e X _ (by omega) (by omega) x]

/-- **The unramified comparison `[W --(Φ−1)--> W] ⟶ C^•_cont(G, W)` is a quasi-isomorphism**
(`G ≃ₜ* ℤ̂`, `W` finite discrete). PROVED. -/
theorem urSelf_quasiIso : QuasiIso (urSelf e X) := by
  refine ⟨fun n => ?_⟩
  rcases n with (_ | _ | m) | m
  · exact urSelf_quasiIsoAt_zero e X
  · exact urSelf_quasiIsoAt_one e X
  · exact urSelf_quasiIsoAt_ge_two e X m
  · exact urSelf_quasiIsoAt_neg e X m

end QIso

/-! ### At a finite place of a number field -/

section Galois

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

/-- **At a finite place `w` of a number field**: the unramified comparison
`[W --(Φ−1)--> W] ⟶ C^•_cont(Gal(K_w^ur/K_w), W)` is a quasi-isomorphism for every finite
discrete continuous representation `W` of `Gal(K_w^ur/K_w)`. PROVED. -/
theorem urSelf_galois_quasiIso (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {k : Type} [CommRing k] [TopologicalSpace k]
    (X : TopRep.{0} k (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]
    [Finite X.V] : QuasiIso (urSelf (eUr K w) X) :=
  have := locallyCompactSpace_GUr K w
  urSelf_quasiIso (eUr K w) X

/-- **Cohomological dimension one at a finite place, on the genuine cochains**:
`Hⁿ_cont(Gal(K_w^ur/K_w), M) = 0` for `n ≥ 2`, `M` finite discrete. PROVED. -/
theorem ur_subsingleton_contCohomology_ge_two (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (k : Type) [CommRing k] [TopologicalSpace k]
    (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (GUr K w) M] [SMulCommClass (GUr K w) k M] [ContinuousSMul k M]
    [ContinuousSMul (GUr K w) M] [Finite M] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (contCohomology k (GUr K w) M n) :=
  have := locallyCompactSpace_GUr K w
  subsingleton_contCohomology_ge_two (eUr K w) k M n hn

end Galois

end ZInQ.Contrib.CloudB3RC53.TameModel
