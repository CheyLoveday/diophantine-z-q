import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthLocalDuality
import ZInQKernel.Contrib.OneProof.RC.Local.TameQuasiIsoLow

/-!
# From cohomological cup perfectness to the local cup adjoint

The two clauses of `CupPerfectAt` express separation and representation of
characters on cohomology in terms of the original cycles. Self-injectivity
extends a form vanishing on the cycles across the outgoing differential.
Thus equality on cycles gives equality modulo a boundary in the dual complex.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Local (quasiIsoAt_toCC_of_elementwise)
open ZInQ.Manuscript.RC.SelmerComplex (InducesIsoH2)

variable {R : Type} [CommRing R] {C D E : GCx R}

/-- The trace cup pairing separates the cohomology of `C` in degree `n`
and represents every character on `H^(2-n)(D)`. A character is presented by
a form on cochains killing boundaries. -/
def CupPerfectAt (cup : GPair C D E) (tr : E.X 2 →ₗ[R] R) (n : ℤ) : Prop :=
  (∀ x : C.X n, C.d n (n + 1) rfl x = 0 →
    (∀ y : D.X (2 - n), D.d (2 - n) (2 - (n - 1)) (by omega) y = 0 →
      tr (cup.P n (2 - n) 2 (by omega) x y) = 0) →
    ∃ z, C.d (n - 1) n (by omega) z = x) ∧
  ∀ φ : D.X (2 - n) →ₗ[R] R,
    (∀ z, φ (D.d (2 - (n + 1)) (2 - n) (by omega) z) = 0) →
    ∃ x : C.X n, C.d n (n + 1) rfl x = 0 ∧
      ∀ y : D.X (2 - n), D.d (2 - n) (2 - (n - 1)) (by omega) y = 0 →
        tr (cup.P n (2 - n) 2 (by omega) x y) = φ y

/-- Perfectness in degree `n` proves the quasi-isomorphism in that degree for
the repository's actual adjoint with its signed dual differential. -/
theorem quasiIsoAt_adjHom_of_cupPerfect [Module.Injective R R]
    (cup : GPair C D E) (tr : E.X 2 →ₗ[R] R)
    (htr : ∀ z, tr (E.d 1 2 rfl z) = 0) (n : ℤ)
    (h : CupPerfectAt cup tr n) : QuasiIsoAt (GHom.toCC (adjHom cup 2 tr htr)) n := by
  apply quasiIsoAt_toCC_of_elementwise _ (n - 1) n (n + 1) (by omega) rfl
  · intro x hx ψ hψ
    apply h.1 x hx
    intro y hy
    have he := congrArg (fun f => asDual f y) hψ
    rw [dualCx_d_apply, hy, map_zero, smul_zero] at he
    exact he.symm
  · intro φ hφ
    have hkill : ∀ z, asDual φ (D.d (2 - (n + 1)) (2 - n) (by omega) z) = 0 := by
      intro z
      have he := congrArg (fun f => asDual f z) hφ
      rw [dualCx_d_apply] at he
      change (-(sgn n)) • asDual φ (D.d (2 - (n + 1)) (2 - n) (by omega) z) = (0 : R) at he
      have hsign := congrArg (fun a : R => (-(sgn n)) • a) he
      simpa only [smul_smul, neg_mul_neg, sgn_mul_self, one_smul, smul_zero] using hsign
    obtain ⟨x, hx, hpair⟩ := h.2 (asDual φ) hkill
    let δ : D.X (2 - n) →ₗ[R] R := tr.comp (cup.P n (2 - n) 2 (by omega) x) - asDual φ
    obtain ⟨ψ, hψ⟩ := orthLD_extend (D.d (2 - n) (2 - (n - 1)) (by omega)) δ (by
      intro y hy
      change tr (cup.P n (2 - n) 2 (by omega) x y) - asDual φ y = 0
      exact sub_eq_zero.mpr (hpair y hy))
    refine ⟨x, hx, (-(sgn (n - 1))) • ψ, dualCx_ext fun y => ?_⟩
    change δ y = (-(sgn (n - 1))) •
      ((-(sgn (n - 1))) • ψ (D.d (2 - n) (2 - (n - 1)) (by omega) y))
    rw [smul_smul, neg_mul_neg, sgn_mul_self, one_smul, hψ]

/-- If both complementary cohomology groups vanish, perfectness holds in
that degree. -/
theorem cupPerfectAt_of_exact (cup : GPair C D E) (tr : E.X 2 →ₗ[R] R) (n : ℤ)
    (hC : Function.Exact (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl))
    (hD : Function.Exact (D.d (2 - (n + 1)) (2 - n) (by omega))
      (D.d (2 - n) (2 - (n - 1)) (by omega))) : CupPerfectAt cup tr n := by
  constructor
  · exact fun x hx _ => (hC x).mp hx
  · intro φ hφ
    refine ⟨0, map_zero _, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := (hD y).mp hy
    rw [hφ z, LinearMap.map_zero₂, map_zero]

private theorem gcx_exact_of_subsingleton_homology (C : GCx R) (i j k : ℤ)
    (hij : i + 1 = j) (hjk : j + 1 = k) (h : Subsingleton (C.toCC.homology j)) :
    Function.Exact (C.d i j hij) (C.d j k hjk) := by
  have he := (C.toCC.exactAt_iff_isZero_homology j).2 (ModuleCat.isZero_iff_subsingleton.2 h)
  rw [HomologicalComplex.exactAt_iff' _ i j k ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk), ShortComplex.moduleCat_exact_iff] at he
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := he x ((GCx.toCC_d_hom C j k hjk x).trans hx)
    exact ⟨y, (GCx.toCC_d_hom C i j hij y).symm.trans hy⟩
  · rintro ⟨y, rfl⟩
    exact C.d_d i j k hij hjk y

/-- For cohomology supported in `[0, 2]`, the three degree pairings determine
the quasi-isomorphism of the cup adjoint. -/
theorem quasiIso_adjHom_of_cupPerfect_zero_two [Module.Injective R R]
    (cup : GPair C D E) (tr : E.X 2 →ₗ[R] R) (htr : ∀ z, tr (E.d 1 2 rfl z) = 0)
    (hC : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (C.toCC.homology n))
    (hD : ∀ n : ℤ, n < 0 ∨ 2 < n → Subsingleton (D.toCC.homology n))
    (h : ∀ n : ℤ, 0 ≤ n → n ≤ 2 → CupPerfectAt cup tr n) :
    QuasiIso (GHom.toCC (adjHom cup 2 tr htr)) := by
  rw [quasiIso_iff]
  intro n
  apply quasiIsoAt_adjHom_of_cupPerfect cup tr htr n
  by_cases hn : 0 ≤ n ∧ n ≤ 2
  · exact h n hn.1 hn.2
  · exact cupPerfectAt_of_exact cup tr n
      (gcx_exact_of_subsingleton_homology C (n - 1) n (n + 1) (by omega) rfl (hC n (by omega)))
      (gcx_exact_of_subsingleton_homology D (2 - (n + 1)) (2 - n) (2 - (n - 1))
        (by omega) (by omega) (hD (2 - n) (by omega)))

/-- A generating additive character of `R` detects perfectness of the
`R`-bilinear trace cup pairing. Separation follows by forgetting scalars.
For representation, test the equality of characters on every scalar multiple
of a cycle, then use the generating property to recover equality in `R`. -/
theorem cupPerfectAt_of_additive_character {A : Type} [AddCommGroup A]
    (cup : GPair C D E) (tr : E.X 2 →ₗ[R] R) (n : ℤ) (χ : R →+ A)
    (hχ : ∀ a : R, (∀ b : R, χ (b * a) = 0) → a = 0)
    (hsep : ∀ x : C.X n, C.d n (n + 1) rfl x = 0 →
      (∀ y : D.X (2 - n), D.d (2 - n) (2 - (n - 1)) (by omega) y = 0 →
        χ (tr (cup.P n (2 - n) 2 (by omega) x y)) = 0) →
      ∃ z, C.d (n - 1) n (by omega) z = x)
    (hrep : ∀ φ : D.X (2 - n) →+ A,
      (∀ z, φ (D.d (2 - (n + 1)) (2 - n) (by omega) z) = 0) →
      ∃ x : C.X n, C.d n (n + 1) rfl x = 0 ∧
        ∀ y : D.X (2 - n), D.d (2 - n) (2 - (n - 1)) (by omega) y = 0 →
          χ (tr (cup.P n (2 - n) 2 (by omega) x y)) = φ y) : CupPerfectAt cup tr n := by
  constructor
  · intro x hx hpair
    exact hsep x hx fun y hy => by rw [hpair y hy, map_zero]
  · intro φ hφ
    obtain ⟨x, hx, hpair⟩ := hrep (χ.comp φ.toAddMonoidHom) fun z => by
      change χ (φ (D.d (2 - (n + 1)) (2 - n) (by omega) z)) = 0
      rw [hφ z, map_zero]
    refine ⟨x, hx, fun y hy => sub_eq_zero.mp (hχ _ fun b => ?_)⟩
    have he := hpair (b • y) (by rw [map_smul, hy, smul_zero])
    change χ (tr (cup.P n (2 - n) 2 (by omega) x (b • y))) = χ (φ (b • y)) at he
    simp only [map_smul, smul_eq_mul] at he
    rw [mul_sub, map_sub, he, sub_self]

/-- The cup of cycles is a cycle in total degree two by the Leibniz rule. -/
def cupCycle (cup : GPair C D E) (n : ℤ)
    (x : LinearMap.ker (C.d n (n + 1) rfl))
    (y : LinearMap.ker (D.d (2 - n) (2 - (n - 1)) (by omega))) :
    LinearMap.ker (E.d 2 3 rfl) :=
  ⟨cup.P n (2 - n) 2 (by omega) x.1 y.1, by
    have hx : C.d n (n + 1) rfl x.1 = 0 := x.2
    have hy : D.d (2 - n) (2 - (n - 1)) (by omega) y.1 = 0 := y.2
    rw [LinearMap.mem_ker, cup.leib n (n + 1) (2 - n) (2 - (n - 1)) 2 3
      (by omega) rfl (by omega) rfl, hx, hy, LinearMap.map_zero₂, map_zero, smul_zero, add_zero]⟩

/-- A map out of the degree-two classes factors through a supplied trace
isomorphism. If its scalar translates detect every class, the resulting
additive character of the coefficient ring is generating. -/
theorem factorTraceCharacter {A : Type} [AddCommGroup A] (tr : E.X 2 →ₗ[R] R)
    (ht : InducesIsoH2 tr) (ξ : LinearMap.ker (E.d 2 3 rfl) →+ A)
    (hξ : ∀ z : LinearMap.ker (E.d 2 3 rfl),
      (∃ t, E.d 1 2 rfl t = z.1) → ξ z = 0)
    (hgen : ∀ z : LinearMap.ker (E.d 2 3 rfl), (∀ r : R, ξ (r • z) = 0) → tr z.1 = 0) :
    ∃ χ : R →+ A, (∀ z : LinearMap.ker (E.d 2 3 rfl), χ (tr z.1) = ξ z) ∧
      ∀ a : R, (∀ b : R, χ (b * a) = 0) → a = 0 := by
  obtain ⟨z, hz, hz1⟩ := ht.2
  let c : LinearMap.ker (E.d 2 3 rfl) := ⟨z, hz⟩
  let χ : R →+ A :=
    { toFun := fun a => ξ (a • c)
      map_zero' := by rw [zero_smul, map_zero]
      map_add' := fun a b => by rw [add_smul, map_add] }
  refine ⟨χ, ?_, ?_⟩
  · intro x
    let d := x - tr x.1 • c
    have hd : tr d.1 = 0 := by
      change tr (x.1 - tr x.1 • z) = 0
      rw [map_sub, map_smul, smul_eq_mul, hz1, mul_one, sub_self]
    have h := hξ d (ht.1 d.1 d.2 hd)
    change ξ (x - tr x.1 • c) = 0 at h
    rw [map_sub] at h
    exact (sub_eq_zero.mp h).symm
  · intro a ha
    have h := hgen (a • c) (fun b => by rw [smul_smul]; exact ha b)
    change tr (a • z) = 0 at h
    rwa [map_smul, smul_eq_mul, hz1, mul_one] at h

/-- Lift an additive functional on cycles to classes using the class map's
surjectivity and its kernel. The functional on cochains kills boundaries. -/
private def functionalOfClasses {X Y H A : Type} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup H] [AddCommGroup A] {d : X →ₗ[R] Y}
    (q : LinearMap.ker d →+ H) (hq : Function.Surjective q) (φ : X →+ A)
    (hφ : ∀ x : LinearMap.ker d, q x = 0 → φ x.1 = 0) : H →+ A := by
  have hf : ∀ x y : LinearMap.ker d, q x = q y → φ x.1 = φ y.1 := by
    intro x y hxy
    have h := hφ (x - y) (by rw [map_sub, hxy, sub_self])
    change φ (x.1 - y.1) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  exact
    { toFun := fun h => φ (hq h).choose.1
      map_zero' := hφ (hq 0).choose (hq 0).choose_spec
      map_add' := fun a b => by
        have h := hf (hq (a + b)).choose ((hq a).choose + (hq b).choose) (by
          rw [(hq (a + b)).choose_spec, map_add, (hq a).choose_spec, (hq b).choose_spec])
        rw [h]
        exact map_add φ _ _ }

/-- A bijective additive cohomological cup adjoint proves perfectness of the
original trace pairing once the two evaluations agree on cycles. -/
theorem cupPerfectAt_of_class_pairing {L H A : Type} [AddCommGroup L] [AddCommGroup H]
    [AddCommGroup A] (cup : GPair C D E) (tr : E.X 2 →ₗ[R] R) (n : ℤ)
    (χ : R →+ A) (hχ : ∀ a : R, (∀ b : R, χ (b * a) = 0) → a = 0)
    (qL : LinearMap.ker (C.d n (n + 1) rfl) →+ L)
    (qH : LinearMap.ker (D.d (2 - n) (2 - (n - 1)) (by omega)) →+ H)
    (hL : Function.Surjective qL) (hH : Function.Surjective qH)
    (hL0 : ∀ x, qL x = 0 → ∃ z, C.d (n - 1) n (by omega) z = x.1)
    (hH0 : ∀ y, qH y = 0 → ∃ z, D.d (2 - (n + 1)) (2 - n) (by omega) z = y.1)
    (b : L →+ H →+ A) (hb : Function.Bijective b)
    (he : ∀ x y, χ (tr (cupCycle cup n x y).1) = b (qL x) (qH y)) :
    CupPerfectAt cup tr n := by
  apply cupPerfectAt_of_additive_character cup tr n χ hχ
  · intro x hx hp
    let x₀ : LinearMap.ker (C.d n (n + 1) rfl) := ⟨x, hx⟩
    apply hL0 x₀
    apply hb.injective
    rw [map_zero b]
    ext h
    obtain ⟨y, rfl⟩ := hH h
    exact (he x₀ y).symm.trans (hp y.1 y.2)
  · intro φ hφ
    have hf : ∀ y, qH y = 0 → φ y.1 = 0 := by
      intro y hy
      obtain ⟨z, hz⟩ := hH0 y hy
      rw [← hz]
      exact hφ z
    let ψ := functionalOfClasses qH hH φ hf
    obtain ⟨l, hl⟩ := hb.surjective ψ
    obtain ⟨x, rfl⟩ := hL l
    refine ⟨x.1, x.2, ?_⟩
    intro y hy
    let y₀ : LinearMap.ker (D.d (2 - n) (2 - (n - 1)) (by omega)) := ⟨y, hy⟩
    change χ (tr (cupCycle cup n x y₀).1) = φ y
    rw [he, hl]
    let y₁ := (hH (qH y₀)).choose
    have h0 : qH (y₁ - y₀) = 0 := by
      rw [map_sub, (hH (qH y₀)).choose_spec, sub_self]
    have h := hf (y₁ - y₀) h0
    change φ (y₁.1 - y) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h

end ZInQ.Manuscript.RC.KummerMaps
