import ZInQKernel.Contrib.RC53Assist.LocalDegreeTwo.NormalizedPairing

/-!
# Double-exponent lifts of the arithmetic tame characters

The extra finite precision in (H12) is used as arithmetic root-of-unity
precision, not as division by two in a residue ring. The unramified character
always lifts. For a uniformizer root at twice the retained exponent, its
square gives the retained root and the Kummer logarithms reduce exactly.
Fixed roots of unity at the larger exponent make the larger logarithm
additive and continuous (tex 3090–3096, 4860–4863, 5027–5042).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidueIdentity.Characters

open TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo
open ZInQ.Contrib.CloudB3RC53.TameQuotient

/-- Kind: definition. Reduction from twice the retained exponent to the
 retained exponent (tex 3090–3096, 4860–4863). -/
def reduceDouble (n : ℕ) : ZMod (2 * n) →+* ZMod n :=
  ZMod.castHom (by exact ⟨2, by ring⟩) (ZMod n)

/-- Kind: proved theorem. Double-exponent reduction is the residue of the
 canonical integer representative (tex 3090–3096, 4860–4863). -/
theorem reduceDouble_val (n : ℕ) [NeZero n] (x : ZMod (2 * n)) :
    reduceDouble n x = (x.val : ZMod n) := by
  have : NeZero (2 * n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  rw [reduceDouble, ZMod.castHom_apply, ZMod.cast_eq_val]

section Unramified

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n]

/-- Kind: proved theorem. The arithmetic unramified characters are
 compatible under double-exponent reduction. This is a statement about
 the arithmetic Frobenius character, with no cup product in its type
 (tex 3090–3096, 5027–5032). -/
theorem unramified_double_reduction (g : Gal(AlgebraicClosure F/F)) :
    reduceDouble n (urCharN F (2 * n) g) = urCharN F n g := by
  have : NeZero (2 * n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  let f : Multiplicative (ZMod (2 * n)) →ₜ* Multiplicative (ZMod n) :=
    ⟨(reduceDouble n).toAddMonoidHom.toMultiplicative, continuous_of_discreteTopology⟩
  have h : f.comp (zHat.lift (Multiplicative.ofAdd (1 : ZMod (2 * n)))) =
      zHat.lift (Multiplicative.ofAdd (1 : ZMod n)) := by
    apply zHat.lift_unique
    change f ((zHat.lift (Multiplicative.ofAdd (1 : ZMod (2 * n)))) zHat.gen) =
      Multiplicative.ofAdd 1
    rw [zHat.lift_gen]
    change Multiplicative.ofAdd (reduceDouble n 1) = Multiplicative.ofAdd 1
    rw [map_one]
  have hv := congrArg Multiplicative.toAdd (DFunLike.congr_fun h
    (maximalUnramifiedGaloisGroupEquivZHat F (AlgebraicClosure F)
      (restrictMaximalUnramifiedHom F g)))
  exact hv

/-- Kind: proved theorem. The arithmetic unramified character has a
 continuous additive double-exponent lift (tex 3090–3096, 5027–5032). -/
theorem exists_unramified_doubleLift :
    ∃ χ : Gal(AlgebraicClosure F/F) → ZMod (2 * n),
      Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
        ∀ g, urCharN F n g = ((χ g).val : ZMod n) := by
  have : NeZero (2 * n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  refine ⟨urCharN F (2 * n), continuous_urCharN,
    urCharN_mul (K := F) (n := 2 * n), ?_⟩
  intro g
  exact (unramified_double_reduction n g).symm.trans (reduceDouble_val n _)

end Unramified

section Kummer

variable {F : Type} [Field F] {n : ℕ} [NeZero n]
  {a : F} {γ : AlgebraicClosure F}

omit [NeZero n] in
/-- Kind: proved theorem. The square of a double-exponent uniformizer root
 is a root at the retained exponent (tex 3090–3096, 4860–4863). -/
theorem squareRoot_power (hγ : γ ^ (2 * n) = algebraMap F (AlgebraicClosure F) a) :
    (γ ^ 2) ^ n = algebraMap F (AlgebraicClosure F) a := by
  rw [← pow_mul]
  exact hγ

/-- Kind: proved theorem. Squaring the root squares every actual Kummer
 value (tex 3090–3096, 4860–4863). -/
theorem kummerVal_square (γ : AlgebraicClosure F) (g : Gal(AlgebraicClosure F/F)) :
    kummerVal (γ ^ 2) g = kummerVal γ g ^ 2 := by
  simp only [kummerVal, map_pow, div_pow]

/-- Kind: proved theorem. A primitive double-exponent tame generator
 remains primitive at the retained exponent after squaring the root
 (tex 3090–3096, 4860–4863). -/
theorem squaredKummerPrimitive {σ : Gal(AlgebraicClosure F/F)}
    (hζ : IsPrimitiveRoot (kummerVal γ σ) (2 * n)) :
    IsPrimitiveRoot (kummerVal (γ ^ 2) σ) n := by
  rw [kummerVal_square]
  exact IsPrimitiveRoot.pow (Nat.mul_pos (by decide) (NeZero.pos n)) hζ rfl

/-- Kind: proved theorem. The actual Kummer logarithm of the squared
 uniformizer root is the exact reduction of the double-exponent logarithm.
 No invariant or pairing formula is assumed (tex 3090–3096, 4860–4863). -/
theorem kummerLog_square_reduction
    (hγ : γ ^ (2 * n) = algebraMap F (AlgebraicClosure F) a) (hγ0 : γ ≠ 0)
    {σ : Gal(AlgebraicClosure F/F)}
    (hζ : IsPrimitiveRoot (kummerVal γ σ) (2 * n)) (g : Gal(AlgebraicClosure F/F)) :
    kummerLog (squareRoot_power hγ) (pow_ne_zero 2 hγ0) (squaredKummerPrimitive hζ) g =
      reduceDouble n (kummerLog hγ hγ0 hζ g) := by
  have : NeZero (2 * n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  apply (kummerLog_eq_iff (squareRoot_power hγ) (pow_ne_zero 2 hγ0)
    (squaredKummerPrimitive hζ) g _).mpr
  rw [reduceDouble_val, ZMod.val_natCast]
  have hmod := pow_mod_orderOf (kummerVal (γ ^ 2) σ) (kummerLog hγ hγ0 hζ g).val
  rw [← (squaredKummerPrimitive hζ).eq_orderOf] at hmod
  rw [hmod, kummerVal_square, kummerVal_square]
  rw [← pow_mul, Nat.mul_comm 2, pow_mul, pow_kummerLog]

/-- Kind: proved theorem. Fixed roots of unity at twice the exponent
 provide a continuous additive lift of the actual retained Kummer
 logarithm. The remaining input is precisely a larger root-of-unity fact
 (tex 3090–3096, 4860–4863, 5035–5042). -/
theorem exists_kummer_doubleLift
    (hγ : γ ^ (2 * n) = algebraMap F (AlgebraicClosure F) a) (hγ0 : γ ≠ 0)
    {σ : Gal(AlgebraicClosure F/F)}
    (hζ : IsPrimitiveRoot (kummerVal γ σ) (2 * n))
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F),
      ζ ^ (2 * n) = 1 → g ζ = ζ) :
    ∃ χ : Gal(AlgebraicClosure F/F) → ZMod (2 * n),
      Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
        ∀ g, kummerLog (squareRoot_power hγ) (pow_ne_zero 2 hγ0)
          (squaredKummerPrimitive hζ) g = ((χ g).val : ZMod n) := by
  have : NeZero (2 * n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  refine ⟨kummerLog hγ hγ0 hζ, continuous_kummerLog hγ hγ0 hζ hμ,
    kummerLog_mul hγ hγ0 hζ hμ, ?_⟩
  intro g
  exact (kummerLog_square_reduction hγ hγ0 hζ g).trans (reduceDouble_val n _)

end Kummer

end ZInQ.Contrib.RC53Assist.ResidueIdentity.Characters
