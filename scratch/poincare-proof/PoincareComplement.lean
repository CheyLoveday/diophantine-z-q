import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# poincare-proof: Poincaré's complete reducibility, complement form, from open fields

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task poincare-proof, 2026-11-16).

Proves the field `poincareComplement : ZInQ.Contrib.AVB1.PoincareComplement` (Milne 1986, Prop. 12.1;
Mumford §19 Thm 1) from five fields of the current open bundles (no new leaf):

* `T09Pic.PicRepresentableAbVar`, `T09Pic.PicZeroAbVar`, `T09Pic.PhiAmpleIsogeny` (the open added leaves
  L1-L3 of t09-pic: Picard scheme, `Pic⁰` an abelian variety, `λ_L` an isogeny for ample `L`);
* `AvSplit.MilneIsogenyQuasiInverse` (an isogeny has a quasi-inverse up to `[d]`);
* `AVGlue.CartierSmooth` (Cartier: group schemes of finite type in characteristic `0` are smooth),

with `ZInQ.Contrib.AbVarBC.mulIsogeny` (`[d]` finite and surjective in characteristic `0`, proved) and
`AVGlue.imageFactorization_of_cartier` (images of homomorphisms, proved from Cartier).

The proof (Milne 1986 §12, made explicit). Let `i : B → J` be a closed immersion and a homomorphism.
* (Polarization.) Take a very ample `L` on `J`; `L' = i^*L` is very ample on `B`. Let `ψ' : J → Pic_{B/k}`
  classify the family `(i × 1)^*Λ(L)` on `B × J` (`Λ(L)` the Mumford bundle). Then `ψ'(0) = 0`, so `ψ'`
  factors through `Pic⁰_{B/k} = B^` by a homomorphism `ψ : J → B^`, and `ψ ∘ i = λ_{L'}` (naturality of
  `Λ`), an isogeny by L3.
* (Algebra.) With `φ = ψ ∘ i` and a quasi-inverse `φ'` (`φ'φ = [d]_B`, `φφ' = [d]_{B^}`), put
  `F = [d] - iφ'ψ ∈ End J`, `C` the image of `F` (`F = g ∘ h`, `h` surjective, `g` a closed immersion), and
  `m = i + g : B × C → J`, `m' = (φ'ψ, h) : J → B × C`. Then `m' ; m = [d]_J` (so `m` is surjective) and
  `m ; m' = [d]_B × [d]_C` (finite, so `m` is finite since `m'` is separated).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.OneProof.PoincareComplement

open PkgI3 PkgI3.AbVar

variable {k : Type} [Field k]

/-! ## §1. Small lemmas on homomorphisms -/

/-- `[N] ≫ q = q ^ N` for a homomorphism `q`. -/
theorem natCast_hom_comp {A Y : AbVar k} (q : A.X ⟶ Y.X) [IsMonHom q] (N : ℕ) :
    (((N : ℤ) : End A)).hom ≫ q = q ^ N := by
  have h := AvSplit.comp_natCast_hom' A (𝟙 A.X) N
  rw [Category.id_comp] at h
  rw [h, MonObj.pow_comp, Category.id_comp]

/-- A surjective morphism onto an abelian variety is an epimorphism among morphisms to an abelian
variety (`C` reduced, the target separated). -/
theorem cancel_surj {A C Y : AbVar k} (h : A.X ⟶ C.X) (hs : Surjective h.left) {u v : C.X ⟶ Y.X}
    (huv : h ≫ u = h ≫ v) : u = v := by
  haveI : IsIntegral C.X.left := GeometricallyIntegral.isIntegral_of_subsingleton C.X.hom
  haveI := hs
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.X.hom (by rw [Over.w u, Over.w v]) h.left
    (by rw [← Over.comp_left, huv, Over.comp_left])

/-- A closed immersion is a monomorphism. -/
theorem cancel_closedImm {T : Over (Spec (CommRingCat.of k))} {C A : AbVar k} (g : C.X ⟶ A.X)
    [IsClosedImmersion g.left] {u v : T ⟶ C.X} (h : u ≫ g = v ≫ g) : u = v := by
  apply Over.OverMorphism.ext
  exact (cancel_mono g.left).1 (by rw [← Over.comp_left, h, Over.comp_left])

/-- `a × b` is finite when `a` and `b` are. -/
theorem isFinite_tensorHom {R S T U : Over (Spec (CommRingCat.of k))} (a : R ⟶ S) (b : T ⟶ U)
    (ha : IsFinite a.left) (hb : IsFinite b.left) : IsFinite (a ⊗ₘ b).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsFinite.{0}) ha hb (Over.w a).symm (Over.w b).symm

/-! ## §2. The algebraic step -/

/-- **The complement, given `ψ : J → D` with `ψ ∘ i` an isogeny.** -/
theorem complement_of_psi (hQ : AvSplit.MilneIsogenyQuasiInverse) (hC : AVGlue.CartierSmooth)
    [CharZero k] (J B D : AbVar k) (i : Hom B J) (hi : IsClosedImmersion i.hom.left)
    (ψ : Hom J D) (hφ : IsIsogenyMor (i.hom ≫ ψ.hom)) :
    ∃ (Z : AbVar k) (g : Hom Z J), IsIsogenyMor (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom) := by
  haveI := hi
  obtain ⟨d, hd, φ', hφφ', hφ'φ⟩ := hQ k B D (Hom.mk' (i.hom ≫ ψ.hom)) hφ
  rw [Hom.hom_mk'] at hφφ' hφ'φ
  simp only [Category.assoc] at hφφ' hφ'φ
  have hd0 : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  let E : End J := Hom.mk' (ψ.hom ≫ φ'.hom ≫ i.hom)
  have hEh : E.hom = ψ.hom ≫ φ'.hom ≫ i.hom := Hom.hom_mk' _
  let F : End J := ((d : ℤ) : End J) - E
  have hFE : F.hom * E.hom = (((d : ℤ) : End J)).hom := by
    rw [← Hom.hom_add, sub_add_cancel]
  obtain ⟨Z, h, g, hs, hg, hfac⟩ := AVGlue.imageFactorization_of_cartier hC k J J F
  haveI := hg
  -- `i ≫ F = 0`
  have hiE : i.hom ≫ E.hom = i.hom ^ d := by
    rw [hEh, ← Category.assoc, ← Category.assoc, Category.assoc i.hom, hφφ', natCast_hom_comp]
  have hiF : i.hom ≫ F.hom = 1 := by
    have h1 : i.hom ≫ F.hom * i.hom ≫ E.hom = i.hom ≫ E.hom := by
      rw [← MonObj.comp_mul, hFE, AvSplit.comp_natCast_hom', hiE]
    exact mul_eq_right.mp h1
  -- `F ≫ ψ = 0`
  have hEψ : E.hom ≫ ψ.hom = ψ.hom ^ d := by
    rw [hEh, Category.assoc, Category.assoc, hφ'φ, AvSplit.comp_natCast_hom']
  have hFψ : F.hom ≫ ψ.hom = 1 := by
    have h1 : F.hom ≫ ψ.hom * E.hom ≫ ψ.hom = E.hom ≫ ψ.hom := by
      rw [← MonObj.mul_comp, hFE, natCast_hom_comp, hEψ]
    exact mul_eq_right.mp h1
  -- `g ≫ ψ = 0`, `i ≫ h = 0`, `g ≫ h = [d]`
  have hgψ : g.hom ≫ ψ.hom = 1 := by
    apply cancel_surj h.hom hs
    rw [← Category.assoc, ← hfac, hFψ, MonObj.comp_one]
  have hih : i.hom ≫ h.hom = 1 := by
    apply cancel_closedImm g.hom
    rw [Category.assoc, ← hfac, hiF, MonObj.one_comp]
  have hgh : g.hom ≫ h.hom = (((d : ℤ) : End Z)).hom := by
    apply cancel_surj h.hom hs
    have h1 : F.hom ≫ h.hom * E.hom ≫ h.hom = h.hom ^ d := by
      rw [← MonObj.mul_comp, hFE, natCast_hom_comp]
    have h2 : E.hom ≫ h.hom = 1 := by
      rw [hEh, Category.assoc, Category.assoc, hih, MonObj.comp_one, MonObj.comp_one]
    rw [h2, _root_.mul_one] at h1
    rw [← Category.assoc, ← hfac, h1, AvSplit.comp_natCast_hom']
  -- the two maps
  refine ⟨Z, g, ?_⟩
  let m : B.X ⊗ Z.X ⟶ J.X := fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom
  let m' : J.X ⟶ B.X ⊗ Z.X := lift (ψ.hom ≫ φ'.hom) h.hom
  change IsIsogenyMor m
  have hM1 : m' ≫ m = (((d : ℤ) : End J)).hom := by
    change m' ≫ (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom) = _
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, ← hfac, ← hFE,
      mul_comm, hEh, Category.assoc]
  have hmψ : m ≫ ψ.hom = fst B.X Z.X ≫ i.hom ≫ ψ.hom := by
    change (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom) ≫ ψ.hom = _
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hgψ, MonObj.comp_one, _root_.mul_one]
  have hmh : m ≫ h.hom = snd B.X Z.X ≫ (((d : ℤ) : End Z)).hom := by
    change (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom) ≫ h.hom = _
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hih, hgh, MonObj.comp_one, _root_.one_mul]
  have hM2 : m ≫ m' = (((d : ℤ) : End B)).hom ⊗ₘ (((d : ℤ) : End Z)).hom := by
    rw [← lift_fst_comp_snd_comp]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, hmψ, Category.assoc,
        Category.assoc, hφφ']
    · rw [Category.assoc, lift_snd, lift_snd, hmh]
  constructor
  · have hfin : IsFinite (m ≫ m').left := by
      rw [hM2]
      exact isFinite_tensorHom _ _ (ZInQ.Contrib.AbVarBC.mulIsogeny k B _ hd0).1
        (ZInQ.Contrib.AbVarBC.mulIsogeny k Z _ hd0).1
    rw [Over.comp_left] at hfin
    haveI : IsSeparated (m'.left ≫ (B.X ⊗ Z.X).hom) := by rw [Over.w m']; infer_instance
    haveI : IsSeparated m'.left := IsSeparated.of_comp m'.left (B.X ⊗ Z.X).hom
    exact IsFinite.of_comp m.left m'.left
  · have hs' : Surjective (m' ≫ m).left := by
      rw [hM1]; exact (ZInQ.Contrib.AbVarBC.mulIsogeny k J _ hd0).2
    rw [Over.comp_left] at hs'
    exact Surjective.of_comp m'.left m.left

end ZInQ.Contrib.OneProof.PoincareComplement
