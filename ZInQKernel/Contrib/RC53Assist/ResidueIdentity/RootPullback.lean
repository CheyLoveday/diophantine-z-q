import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.Arithmetic

/-!
# Arithmetic local pullback in root coordinates

A local representative is recorded by its action on the coefficient
field, on the chosen uniformizer root, and on roots of unity. Its induced
pullback acts on the uniformizer character through the cyclotomic power.
This reduces the character identity to algebraic root equations, not to
an identity of local cup-product pairings
(tex 2798–2805, 3090–3096, 4860–4863, 5027–5032).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidueIdentity.RootPullback

open TauCeti
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo
open ZInQ.Contrib.CloudB3RC53.TameQuotient

section Algebraic

variable {F : Type} [Field F] {n : ℕ} [NeZero n]

/-- Kind: definition. The local algebraic representative gives a
pullback by conjugation on the absolute local Galois group. The input
records its restriction to the coefficient field, not a cohomology action
(tex 2798–2805, 5027–5032). -/
def conjugateHom (a : AlgebraicClosure F ≃+* AlgebraicClosure F) (κ : F ≃+* F)
    (ha : ∀ x : F, a (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (κ x)) :
    Gal(AlgebraicClosure F/F) →* Gal(AlgebraicClosure F/F) where
  toFun g :=
    { (a.symm.trans (g.toRingEquiv.trans a)) with
      commutes' := fun x => by
        have hinv : a.symm (algebraMap F (AlgebraicClosure F) x) =
            algebraMap F (AlgebraicClosure F) (κ.symm x) := by
          apply a.injective
          rw [a.apply_symm_apply, ha, κ.apply_symm_apply]
        change a (g (a.symm (algebraMap F (AlgebraicClosure F) x))) =
          algebraMap F (AlgebraicClosure F) x
        rw [hinv, g.commutes, ha, κ.apply_symm_apply] }
  map_one' := by
    ext x
    change a ((1 : Gal(AlgebraicClosure F/F)) (a.symm x)) = x
    simp
  map_mul' g h := by
    ext x
    change a ((g * h) (a.symm x)) = a (g (a.symm (a (h (a.symm x)))))
    rw [a.symm_apply_apply]
    rfl

/-- Kind: proved theorem. The induced algebraic local pullback is
conjugation by the original representative (tex 2798–2805, 5027–5032). -/
theorem conjugateHom_apply (a : AlgebraicClosure F ≃+* AlgebraicClosure F) (κ : F ≃+* F)
    (ha : ∀ x : F, a (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (κ x)) (g : Gal(AlgebraicClosure F/F))
    (x : AlgebraicClosure F) : conjugateHom a κ ha g x = a (g (a.symm x)) := rfl

omit [NeZero n] in
/-- Kind: proved theorem. If the representative fixes the chosen
uniformizer root and acts on roots of unity by a prescribed power, its
local pullback scales every actual Kummer value by that power
(tex 3090–3096, 4860–4863, 5027–5032). -/
theorem kummerVal_conjugate
    (a : AlgebraicClosure F ≃+* AlgebraicClosure F) (κ : F ≃+* F)
    (ha : ∀ x : F, a (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (κ x))
    {b : F} {β : AlgebraicClosure F} (hβ : β ^ n = algebraMap F (AlgebraicClosure F) b)
    (hβ0 : β ≠ 0) (hfix : a β = β) (r : ℕ)
    (hcyc : ∀ ζ : AlgebraicClosure F, ζ ^ n = 1 → a ζ = ζ ^ r)
    (g : Gal(AlgebraicClosure F/F)) :
    kummerVal β (conjugateHom a κ ha g) = kummerVal β g ^ r := by
  have hinv : a.symm β = β := by
    apply a.injective
    rw [a.apply_symm_apply, hfix]
  rw [kummerVal, conjugateHom_apply, hinv]
  calc
    a (g β) / β = a (g β) / a β := by rw [hfix]
    _ = a (g β / β) := (map_div₀ a (g β) β).symm
    _ = kummerVal β g ^ r := hcyc (kummerVal β g) (kummerVal_pow hβ hβ0 g)

/-- Kind: proved theorem. The exact uniformizer logarithm scales by the
cyclotomic residue power of the actual local algebraic representative.
The hypotheses are field restriction, root fixation, and root-of-unity
power equations, not a character or pairing-table identity
(tex 3090–3096, 4860–4863, 5027–5032). -/
theorem kummerLog_conjugate
    (a : AlgebraicClosure F ≃+* AlgebraicClosure F) (κ : F ≃+* F)
    (ha : ∀ x : F, a (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (κ x))
    {b : F} {β : AlgebraicClosure F} (hβ : β ^ n = algebraMap F (AlgebraicClosure F) b)
    (hβ0 : β ≠ 0) {σ : Gal(AlgebraicClosure F/F)}
    (hprim : IsPrimitiveRoot (kummerVal β σ) n) (hfix : a β = β) (r : ℕ)
    (hcyc : ∀ ζ : AlgebraicClosure F, ζ ^ n = 1 → a ζ = ζ ^ r)
    (g : Gal(AlgebraicClosure F/F)) :
    kummerLog hβ hβ0 hprim (conjugateHom a κ ha g) = (r : ZMod n) * kummerLog hβ hβ0 hprim g := by
  apply (kummerLog_eq_iff hβ hβ0 hprim _ _).mpr
  rw [ZMod.val_mul, ZMod.val_natCast]
  have he : (r % n * (kummerLog hβ hβ0 hprim g).val) % n =
      (r * (kummerLog hβ hβ0 hprim g).val) % n := by simp [Nat.mul_mod]
  rw [he]
  have hmod := pow_mod_orderOf (kummerVal β σ) (r * (kummerLog hβ hβ0 hprim g).val)
  rw [← hprim.eq_orderOf] at hmod
  rw [hmod, Nat.mul_comm r, pow_mul, pow_kummerLog,
    kummerVal_conjugate a κ ha hβ hβ0 hfix r hcyc]

/-- Kind: proved theorem. Scalar extension preserves the local root
pullback formula. This is the precise tame character input for the
finite coefficient cup calculation (tex 3090–3096, 4860–4863, 5027–5032). -/
theorem coefficient_kummerLog_conjugate
    (R : Type) [CommRing R] [Algebra (ZMod n) R]
    (a : AlgebraicClosure F ≃+* AlgebraicClosure F) (κ : F ≃+* F)
    (ha : ∀ x : F, a (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (κ x))
    {b : F} {β : AlgebraicClosure F} (hβ : β ^ n = algebraMap F (AlgebraicClosure F) b)
    (hβ0 : β ≠ 0) {σ : Gal(AlgebraicClosure F/F)}
    (hprim : IsPrimitiveRoot (kummerVal β σ) n) (hfix : a β = β) (r : ℕ)
    (hcyc : ∀ ζ : AlgebraicClosure F, ζ ^ n = 1 → a ζ = ζ ^ r)
    (g : Gal(AlgebraicClosure F/F)) :
    algebraMap (ZMod n) R (kummerLog hβ hβ0 hprim (conjugateHom a κ ha g)) =
      (r : R) * algebraMap (ZMod n) R (kummerLog hβ hβ0 hprim g) := by
  rw [kummerLog_conjugate a κ ha hβ hβ0 hprim hfix r hcyc, map_mul, map_natCast]

end Algebraic

end ZInQ.Contrib.RC53Assist.ResidueIdentity.RootPullback
