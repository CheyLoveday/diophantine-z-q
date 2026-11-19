import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel
import ZInQKernel.Contrib.OneProof.RC.Limits.FieldQuasiIso

/-!
# Lane RC31, round 6: normalizing a deformation retract (Lambe–Stasheff)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451), the normalized
deformation retract data of tex 4423–4437.

Input: relation-indexed complexes `X`, `Y` over a commutative ring `A`, chain maps `i : Y → X`,
`p : X → Y` with `p i = 1`, and a degree `−1` map `h` with `1 − i p = d h + h d` in every degree.
Output (`GRetract.ofDeformation`): a `GRetract X Y` with the same `i`, `p` and the homotopy
`h'' = h' d h'`, where `h' = π h π` and `π = 1 − i p`.

* `sdrProj i p n = 1 − i p` in degree `n` (definition); it commutes with `d` (`sdrProj_d`), kills
  `i` (`sdrProj_i`), is killed by `p` (`p_sdrProj`) and is idempotent (`sdrProj_sdrProj`).
* `sdrH1 = π h π` (definition) satisfies `h' i = 0`, `p h' = 0`, `π = d h' + h' d`
  (`sdrH1_i`, `p_sdrH1`, `sdrH1_homotopy`).
* `sdrH2 = h' d h'` (definition) satisfies in addition `h''² = 0` (`sdrH2_sdrH2`).

Strict sections over a field (`exists_strict_section`, tex 4391–4451): for complexes `X`, `Y` over
a field, strictly concentrated in degrees `≥ a`, a degreewise surjective quasi-isomorphism
`p : X → Y` has a chain map `i : Y → X` with `p i = 1` strictly. A homotopy inverse `g` with
`p g − 1 = d H₀ + H₀ d` exists (`homotopyEquiv_of_quasiIso_field`); lifting `H₀` through a
degreewise linear section of `p` to `H`, the chain map `i = g − d H − H d` (`sectHom`) works.
No finiteness of the terms is needed.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section Normalize

variable {A : Type} [CommRing A] {X Y : GCx A} (i : GHom Y X) (p : GHom X Y)

/-- The projection `π = 1 − i p` in degree `n` (tex 4423–4437). Kind: definition. -/
def sdrProj (n : ℤ) : X.X n →ₗ[A] X.X n := LinearMap.id - i.f n n rfl ∘ₗ p.f n n rfl

/-- Component formula for `π = 1 − i p` (tex 4423–4437). Kind: PROVED. -/
theorem sdrProj_apply (n : ℤ) (x : X.X n) :
    sdrProj i p n x = x - i.f n n rfl (p.f n n rfl x) := rfl

/-- `π` commutes with the differential (tex 4423–4437). Kind: PROVED. -/
theorem sdrProj_d (a c : ℤ) (hac : a + 1 = c) (x : X.X a) :
    X.d a c hac (sdrProj i p a x) = sdrProj i p c (X.d a c hac x) := by
  rw [sdrProj_apply, sdrProj_apply, map_sub, p.comm a c a c rfl hac hac rfl x,
    i.comm a c a c rfl hac hac rfl]

variable {i p}

/-- `π i = 0` when `p i = 1` (tex 4423–4437). Kind: PROVED. -/
theorem sdrProj_i (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (n : ℤ)
    (y : Y.X n) : sdrProj i p n (i.f n n rfl y) = 0 := by
  rw [sdrProj_apply, hpi, sub_self]

/-- `p π = 0` when `p i = 1` (tex 4423–4437). Kind: PROVED. -/
theorem p_sdrProj (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (n : ℤ)
    (x : X.X n) : p.f n n rfl (sdrProj i p n x) = 0 := by
  rw [sdrProj_apply, map_sub, hpi, sub_self]

/-- `π² = π` when `p i = 1` (tex 4423–4437). Kind: PROVED. -/
theorem sdrProj_sdrProj (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (n : ℤ)
    (x : X.X n) : sdrProj i p n (sdrProj i p n x) = sdrProj i p n x := by
  rw [sdrProj_apply i p n (sdrProj i p n x), p_sdrProj hpi, map_zero, sub_zero]

/-- The homotopy identity `1 − i p = d h + h d` with arbitrary index expressions
(tex 4423–4437). Kind: PROVED. -/
theorem sdr_homotopy_gen {h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b}
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x))
    (a b c : ℤ) (hba : b + 1 = a) (hac : a + 1 = c) (x : X.X a) :
    sdrProj i p a x = X.d b a hba (h a b hba x) + h c a hac (X.d a c hac x) := by
  obtain rfl : b = a - 1 := by omega
  subst hac
  exact hom a x

variable (i p) in
/-- The first normalization `h' = π h π` (tex 4423–4437). Kind: definition. -/
def sdrH1 (h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b) (a b : ℤ) (hab : b + 1 = a) :
    X.X a →ₗ[A] X.X b :=
  sdrProj i p b ∘ₗ h a b hab ∘ₗ sdrProj i p a

variable (i p) in
/-- Component formula for `h' = π h π` (tex 4423–4437). Kind: PROVED. -/
theorem sdrH1_apply (h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b) (a b : ℤ)
    (hab : b + 1 = a) (x : X.X a) :
    sdrH1 i p h a b hab x = sdrProj i p b (h a b hab (sdrProj i p a x)) := rfl

variable {h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b}

/-- `h' i = 0` (tex 4423–4437). Kind: PROVED. -/
theorem sdrH1_i (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (a b : ℤ)
    (hab : b + 1 = a) (y : Y.X a) : sdrH1 i p h a b hab (i.f a a rfl y) = 0 := by
  rw [sdrH1_apply, sdrProj_i hpi, map_zero, map_zero]

/-- `p h' = 0` (tex 4423–4437). Kind: PROVED. -/
theorem p_sdrH1 (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (a b : ℤ)
    (hab : b + 1 = a) (x : X.X a) : p.f b b rfl (sdrH1 i p h a b hab x) = 0 := by
  rw [sdrH1_apply, p_sdrProj hpi]

/-- `π h' = h'` (tex 4423–4437). Kind: PROVED. -/
theorem sdrProj_sdrH1 (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (a b : ℤ)
    (hab : b + 1 = a) (x : X.X a) :
    sdrProj i p b (sdrH1 i p h a b hab x) = sdrH1 i p h a b hab x := by
  rw [sdrH1_apply, sdrProj_sdrProj hpi]

/-- `h' π = h'` (tex 4423–4437). Kind: PROVED. -/
theorem sdrH1_sdrProj (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (a b : ℤ)
    (hab : b + 1 = a) (x : X.X a) :
    sdrH1 i p h a b hab (sdrProj i p a x) = sdrH1 i p h a b hab x := by
  rw [sdrH1_apply, sdrH1_apply, sdrProj_sdrProj hpi]

/-- `π = d h' + h' d` (tex 4423–4437). Kind: PROVED. -/
theorem sdrH1_homotopy (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x))
    (a b c : ℤ) (hba : b + 1 = a) (hac : a + 1 = c) (x : X.X a) :
    sdrProj i p a x =
      X.d b a hba (sdrH1 i p h a b hba x) + sdrH1 i p h c a hac (X.d a c hac x) := by
  rw [sdrH1_apply, sdrH1_apply, sdrProj_d, ← sdrProj_d i p a c hac, ← map_add,
    ← sdr_homotopy_gen hom a b c hba hac, sdrProj_sdrProj hpi, sdrProj_sdrProj hpi]

variable (i p) in
/-- The second normalization `h'' = h' d h'` (tex 4423–4437). Kind: definition. -/
def sdrH2 (h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b) (a b : ℤ) (hab : b + 1 = a) :
    X.X a →ₗ[A] X.X b :=
  sdrH1 i p h a b hab ∘ₗ X.d b a hab ∘ₗ sdrH1 i p h a b hab

variable (i p h) in
/-- Component formula for `h'' = h' d h'`, with `h' = π h π` and `π = 1 − i p`
(tex 4423–4437). Kind: PROVED. -/
theorem sdrH2_apply (a b : ℤ) (hab : b + 1 = a) (x : X.X a) :
    sdrH2 i p h a b hab x = sdrH1 i p h a b hab (X.d b a hab (sdrH1 i p h a b hab x)) := rfl

/-- `h'' i = 0` (tex 4423–4437). Kind: PROVED. -/
theorem sdrH2_i (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (a b : ℤ)
    (hab : b + 1 = a) (y : Y.X a) : sdrH2 i p h a b hab (i.f a a rfl y) = 0 := by
  rw [sdrH2_apply, sdrH1_i hpi, map_zero, map_zero]

/-- `p h'' = 0` (tex 4423–4437). Kind: PROVED. -/
theorem p_sdrH2 (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y) (a b : ℤ)
    (hab : b + 1 = a) (x : X.X a) : p.f b b rfl (sdrH2 i p h a b hab x) = 0 := by
  rw [sdrH2_apply, p_sdrH1 hpi]

/-- `π = d h'' + h'' d` (tex 4423–4437). Kind: PROVED. -/
theorem sdrH2_homotopy (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x))
    (a b c : ℤ) (hba : b + 1 = a) (hac : a + 1 = c) (x : X.X a) :
    sdrProj i p a x =
      X.d b a hba (sdrH2 i p h a b hba x) + sdrH2 i p h c a hac (X.d a c hac x) := by
  have e1 : X.d b a hba (sdrH1 i p h a b hba (X.d b a hba (sdrH1 i p h a b hba x))) =
      X.d b a hba (sdrH1 i p h a b hba x) := by
    have := sdrH1_homotopy hpi hom a b c hba hac (X.d b a hba (sdrH1 i p h a b hba x))
    rw [X.d_d, map_zero, add_zero, ← sdrProj_d i p b a hba, sdrProj_sdrH1 hpi] at this
    exact this.symm
  have e2 : X.d a c hac (sdrH1 i p h c a hac (X.d a c hac x)) = sdrProj i p c (X.d a c hac x) := by
    have := sdrH1_homotopy hpi hom c a (c + 1) hac rfl (X.d a c hac x)
    rw [X.d_d, map_zero, add_zero] at this
    exact this.symm
  rw [sdrH2_apply, sdrH2_apply, e1, e2, sdrH1_sdrProj hpi]
  exact sdrH1_homotopy hpi hom a b c hba hac x

/-- `h''² = 0` (Lambe–Stasheff; tex 4423–4437). Kind: PROVED. -/
theorem sdrH2_sdrH2 (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x))
    (a b c : ℤ) (hab : b + 1 = a) (hbc : c + 1 = b) (x : X.X a) :
    sdrH2 i p h b c hbc (sdrH2 i p h a b hab x) = 0 := by
  have e1 : sdrH1 i p h a b hab (X.d b a hab (sdrH1 i p h a b hab x)) =
      sdrH1 i p h a b hab x - X.d c b hbc (sdrH1 i p h b c hbc (sdrH1 i p h a b hab x)) := by
    have := sdrH1_homotopy hpi hom b c a hbc hab (sdrH1 i p h a b hab x)
    rw [sdrProj_sdrH1 hpi] at this
    exact eq_sub_of_add_eq' this.symm
  have e2 : sdrH1 i p h b c hbc
      (sdrH1 i p h a b hab x - X.d c b hbc (sdrH1 i p h b c hbc (sdrH1 i p h a b hab x))) =
      X.d (c - 1) c (by omega)
        (sdrH1 i p h c (c - 1) (by omega) (sdrH1 i p h b c hbc (sdrH1 i p h a b hab x))) := by
    rw [map_sub]
    have := sdrH1_homotopy hpi hom c (c - 1) b (by omega) hbc
      (sdrH1 i p h b c hbc (sdrH1 i p h a b hab x))
    rw [sdrProj_sdrH1 hpi] at this
    exact sub_eq_of_eq_add this
  rw [sdrH2_apply, sdrH2_apply, e1, e2, X.d_d, map_zero]

/-- **Lambe–Stasheff normalization** (tex 4423–4437). From chain maps `i : Y → X`, `p : X → Y`
with `p i = 1` and a degree `−1` map `h` with `1 − i p = d h + h d`, the normalized deformation
retract with the same `i`, `p` and homotopy `h'' = h' d h'`, `h' = π h π`, `π = 1 − i p`
(component formula `GRetract.ofDeformation_h_apply`). Kind: definition (with PROVED
identities). -/
def GRetract.ofDeformation (i : GHom Y X) (p : GHom X Y)
    (h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b)
    (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x)) :
    GRetract X Y where
  i := i
  p := p
  h := sdrH2 i p h
  p_i := hpi
  homotopy n x := (sdrProj_apply i p n x).symm.trans
    (sdrH2_homotopy hpi hom n (n - 1) (n + 1) (by omega) rfl x)
  h_h a b c hab hbc x := sdrH2_sdrH2 hpi hom a b c hab hbc x
  h_i a b hab y := sdrH2_i hpi a b hab y
  p_h a b hab x := p_sdrH2 hpi a b hab x

/-- The inclusion of `GRetract.ofDeformation` is the given `i` (tex 4423–4437). Kind: PROVED. -/
theorem GRetract.ofDeformation_i (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x)) :
    (GRetract.ofDeformation i p h hpi hom).i = i := rfl

/-- The projection of `GRetract.ofDeformation` is the given `p` (tex 4423–4437). Kind: PROVED. -/
theorem GRetract.ofDeformation_p (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x)) :
    (GRetract.ofDeformation i p h hpi hom).p = p := rfl

/-- Component formula for the homotopy of `GRetract.ofDeformation`: with `π x = x − i (p x)`,
`h'' x = π (h (π (d (π (h (π x))))))` (tex 4423–4437). Kind: PROVED. -/
theorem GRetract.ofDeformation_h_apply (hpi : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y)
    (hom : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x))
    (a b : ℤ) (hab : b + 1 = a) (x : X.X a) :
    (GRetract.ofDeformation i p h hpi hom).h a b hab x =
      sdrProj i p b (h a b hab (sdrProj i p a (X.d b a hab
        (sdrProj i p b (h a b hab (sdrProj i p a x)))))) := rfl

end Normalize

section StrictSection

variable {k : Type} [Field k] {X Y : GCx k}

/-- The corrected section `g − d H − H d` in degree `n`, with arbitrary neighbouring indices
(tex 4391–4451). Kind: definition. -/
def sectCompGen (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (n b c : ℤ) (hbn : b + 1 = n) (hnc : n + 1 = c) : Y.X n →ₗ[k] X.X n :=
  g n - X.d b n hbn ∘ₗ H n b hbn - H c n hnc ∘ₗ Y.d n c hnc

/-- The corrected section `g − d H − H d` in degree `n` (tex 4391–4451). Kind: definition. -/
def sectComp (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (n : ℤ) : Y.X n →ₗ[k] X.X n :=
  sectCompGen g H n (n - 1) (n + 1) (by omega) rfl

/-- The corrected section does not depend on the index expressions (tex 4391–4451).
Kind: PROVED. -/
theorem sectComp_eq_gen (g : ∀ n, Y.X n →ₗ[k] X.X n)
    (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b) (n b c : ℤ) (hbn : b + 1 = n)
    (hnc : n + 1 = c) : sectComp g H n = sectCompGen g H n b c hbn hnc := by
  obtain rfl : b = n - 1 := by omega
  subst hnc
  rfl

/-- The corrected section as a chain map, for a chain map `g` (tex 4391–4451).
Kind: definition. -/
def sectHom (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y)) :
    GHom Y X where
  f i j hij := by subst hij; exact sectComp g H i
  comm i i₁ j j₁ hij h₁ h₂ hj y := by
    subst hij h₁ hj
    change sectComp g H (i + 1) (Y.d i (i + 1) h₂ y) = X.d i (i + 1) h₂ (sectComp g H i y)
    rw [sectComp_eq_gen g H (i + 1) i (i + 1 + 1) h₂ rfl,
      sectComp_eq_gen g H i (i - 1) (i + 1) (by omega) h₂]
    simp only [sectCompGen, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, Y.d_d, X.d_d,
      map_zero, sub_zero, hg]

/-- The components of `sectHom` (tex 4391–4451). Kind: PROVED. -/
theorem sectHom_f (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y))
    (n : ℤ) (y : Y.X n) : (sectHom g H hg).f n n rfl y = sectComp g H n y := rfl

/-- If `p g − 1 = d H₀ + H₀ d` and `p H = H₀`, then `p (g − d H − H d) = 1`
(tex 4391–4451). Kind: PROVED. -/
theorem p_sectComp (p : GHom X Y) (g : ∀ n, Y.X n →ₗ[k] X.X n)
    (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b) (H₀ : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] Y.X b)
    (hpH : ∀ a b (hab : b + 1 = a) (y : Y.X a), p.f b b rfl (H a b hab y) = H₀ a b hab y)
    (hhom : ∀ n (y : Y.X n), p.f n n rfl (g n y) =
      H₀ (n + 1) n rfl (Y.d n (n + 1) rfl y) + Y.d (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y)
        + y)
    (n : ℤ) (y : Y.X n) : p.f n n rfl (sectComp g H n y) = y := by
  simp only [sectComp, sectCompGen, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [p.comm (n - 1) n (n - 1) n rfl (by omega) (by omega) rfl, hpH, hpH, hhom]
  abel

/-- **A strict chain section of a degreewise surjective quasi-isomorphism over a field**
(tex 4391–4451). For relation-indexed complexes `X`, `Y` over a field, both strictly concentrated
in degrees `≥ a`, and a chain map `p : X → Y` that is degreewise surjective and a
quasi-isomorphism, there is a chain map `i : Y → X` with `p i = 1` strictly. Proof: a homotopy
inverse `g` with `p g − 1 = d H₀ + H₀ d` (`homotopyEquiv_of_quasiIso_field`), a degreewise
linear section `s` of `p`, and `i = g − d H − H d` with `H = s H₀`. Kind: PROVED. -/
theorem exists_strict_section (a : ℤ) (p : GHom X Y)
    (hsurj : ∀ n, Function.Surjective (p.f n n rfl))
    [X.toCC.IsStrictlyGE a] [Y.toCC.IsStrictlyGE a] [QuasiIso (GHom.toCC p)] :
    ∃ i : GHom Y X, ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y := by
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
  exact ⟨sectHom g H hg, p_sectComp p g H H₀ hpH hhom⟩

end StrictSection

end ZInQ.Manuscript.RC.Limits
