import ZInQKernel.Contrib.OneProof.RC.Limits.SDRNormalize

/-!
# Lane RC31, round 6: a normalized retract onto the target of a surjective quasi-isomorphism

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451), with the
normalized deformation retract data of tex 4423–4437.

Over a field, for complexes `X`, `Y` strictly concentrated in degrees `≥ a` and a degreewise
surjective quasi-isomorphism `p : X → Y`, there is a `GRetract X Y` whose projection is `p`
(`exists_retract_of_surjective_quasiIso_field`). With a homotopy inverse `g`, homotopies
`p g − 1 = d H₀ + H₀ d` and `g p − 1 = d K + K d`, and a degreewise linear section `s` of `p`,
put `H = s H₀` and `i = g − d H − H d` (`sectHom`, with `p i = 1`). Since `p` commutes with `d`,
`1 − i p = d (H p − K) + (H p − K) d` (`sect_retract_homotopy`), and `GRetract.ofDeformation`
normalizes the homotopy keeping `i` and `p`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section Retract

variable {k : Type} [Field k] {X Y : GCx k}

/-- If `g p − 1 = d K + K d`, then for `i = g − d H − H d` one has
`1 − i p = d (H p − K) + (H p − K) d` (tex 4423–4437). Kind: PROVED. -/
theorem sect_retract_homotopy (p : GHom X Y) (g : ∀ n, Y.X n →ₗ[k] X.X n)
    (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y))
    (K : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[k] X.X b)
    (hK : ∀ n (x : X.X n), g n (p.f n n rfl x) =
      K (n + 1) n rfl (X.d n (n + 1) rfl x) + X.d (n - 1) n (by omega) (K n (n - 1) (by omega) x)
        + x)
    (n : ℤ) (x : X.X n) :
    x - (sectHom g H hg).f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) ((H n (n - 1) (by omega) ∘ₗ p.f n n rfl - K n (n - 1) (by omega)) x)
        + (H (n + 1) n rfl ∘ₗ p.f (n + 1) (n + 1) rfl - K (n + 1) n rfl) (X.d n (n + 1) rfl x) := by
  rw [sectHom_f]
  simp only [sectComp, sectCompGen, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [p.comm n (n + 1) n (n + 1) rfl rfl rfl rfl x, hK]
  abel

/-- **A normalized retract onto the target of a surjective quasi-isomorphism over a field**
(tex 4391–4451, 4423–4437). For complexes `X`, `Y` over a field, strictly concentrated in
degrees `≥ a`, and a degreewise surjective quasi-isomorphism `p : X → Y`, there is a
`GRetract X Y` whose projection is `p`. Kind: PROVED. -/
theorem exists_retract_of_surjective_quasiIso_field (a : ℤ) (p : GHom X Y)
    (hsurj : ∀ n, Function.Surjective (p.f n n rfl))
    [X.toCC.IsStrictlyGE a] [Y.toCC.IsStrictlyGE a] [QuasiIso (GHom.toCC p)] :
    ∃ R : GRetract X Y, ∀ n (x : X.X n), R.p.f n n rfl x = p.f n n rfl x := by
  obtain ⟨e, he⟩ := homotopyEquiv_of_quasiIso_field a (GHom.toCC p)
  let g : ∀ n, Y.X n →ₗ[k] X.X n := fun n => (e.inv.f n).hom
  let H₀ : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] Y.X b := fun a b _ =>
    (e.homotopyInvHomId.hom a b).hom
  choose s hs using fun n => (p.f n n rfl).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (hsurj n))
  let H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b := fun a b hab => s b ∘ₗ H₀ a b hab
  have hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y) := by
    intro i j hij y
    have h1 : (X.toCC.d i j).hom ((e.inv.f i).hom y) = (e.inv.f j).hom ((Y.toCC.d i j).hom y) :=
      congrArg (fun φ => φ.hom y) (e.inv.comm i j)
    have e1 := GCx.toCC_d_hom X i j hij ((e.inv.f i).hom y)
    have e2 := GCx.toCC_d_hom Y i j hij y
    exact (congrArg (fun z => (e.inv.f j).hom z) e2.symm).trans (h1.symm.trans e1)
  have hpH : ∀ a b (hab : b + 1 = a) (y : Y.X a), p.f b b rfl (H a b hab y) = H₀ a b hab y :=
    fun a b _ y => LinearMap.congr_fun (hs b) _
  have hhom : ∀ n (y : Y.X n), p.f n n rfl (g n y) =
      H₀ (n + 1) n rfl (Y.d n (n + 1) rfl y) + Y.d (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y)
        + y := by
    intro n y
    have h1 := congrArg (fun φ => φ.hom y) (e.homotopyInvHomId.comm n)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at h1
    have hp : ∀ x : X.X n, (e.hom.f n).hom x = p.f n n rfl x := fun x => by rw [he]; rfl
    have h2 : (e.hom.f n).hom (g n y) = H₀ (n + 1) n rfl (Y.d n (n + 1) rfl y) +
        Y.d (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y) + y := by
      have e2 := GCx.toCC_d_hom Y n (n + 1) rfl y
      have e3 := GCx.toCC_d_hom Y (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y)
      rw [← e2, ← e3]
      exact h1
    rw [hp] at h2
    exact h2
  let K : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[k] X.X b := fun a b _ =>
    (e.homotopyHomInvId.hom a b).hom
  have hK : ∀ n (x : X.X n), g n (p.f n n rfl x) =
      K (n + 1) n rfl (X.d n (n + 1) rfl x) + X.d (n - 1) n (by omega) (K n (n - 1) (by omega) x)
        + x := by
    intro n x
    have h1 := congrArg (fun φ => φ.hom x) (e.homotopyHomInvId.comm n)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at h1
    have hp : ∀ x : X.X n, (e.hom.f n).hom x = p.f n n rfl x := fun x => by rw [he]; rfl
    have h2 : g n ((e.hom.f n).hom x) = K (n + 1) n rfl (X.d n (n + 1) rfl x) +
        X.d (n - 1) n (by omega) (K n (n - 1) (by omega) x) + x := by
      have e2 := GCx.toCC_d_hom X n (n + 1) rfl x
      have e3 := GCx.toCC_d_hom X (n - 1) n (by omega) (K n (n - 1) (by omega) x)
      rw [← e2, ← e3]
      exact h1
    rw [hp] at h2
    exact h2
  exact ⟨GRetract.ofDeformation (sectHom g H hg) p
    (fun a b hab => H a b hab ∘ₗ p.f a a rfl - K a b hab) (p_sectComp p g H H₀ hpH hhom)
    (sect_retract_homotopy p g H hg K hK), fun _ _ => rfl⟩

end Retract

end ZInQ.Manuscript.RC.Limits
