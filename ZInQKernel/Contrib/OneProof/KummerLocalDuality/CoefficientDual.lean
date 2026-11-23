import ZInQKernel.Contrib.OneProof.RC.KummerMaps.UrMilneActual
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.GroupAction.InternalHom.Basic

/-!
# The coefficient pairing at the local Tate-duality interface

Composing the actual Weil form with the generating character of `Acoef i(1)`
identifies the inverse-character module with the additive dual into roots of
unity. The character is used to test perfectness. The arithmetic trace in
`actLPerf` keeps its original `Acoef i`-valued codomain.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open TauCeti (InternalHom)

section AdditiveDual

variable {R G M N T A : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T] [AddCommGroup A]

private def scalarizedDual (β : M →ₗ[R] N →ₗ[R] T) (λ : T →+ A) : N →+ InternalHom G M A where
  toFun y := InternalHom.of G (λ.comp (β.flip y).toAddMonoidHom)
  map_zero' := by
    apply InternalHom.ext
    ext x
    change λ (β x 0) = 0
    rw [map_zero, map_zero]
  map_add' y y' := by
    apply InternalHom.ext
    ext x
    change λ (β x (y + y')) = λ (β x y) + λ (β x y')
    rw [map_add, map_add]

private theorem scalarizedDual_injective (β : M →ₗ[R] N →ₗ[R] T) (λ : T →+ A)
    (hβ : Function.Injective β.flip) (hλ : ∀ t, (∀ r : R, λ (r • t) = 0) → t = 0) :
    Function.Injective (scalarizedDual (G := G) β λ) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  apply (injective_iff_map_eq_zero _).mp hβ y
  ext x
  change β x y = 0
  apply hλ
  intro r
  rw [← LinearMap.map_smul₂]
  exact congrArg (fun f : InternalHom G M A => f.toAddMonoidHom (r • x)) hy

end AdditiveDual

section Kummer

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (i : ℕ) [NeZero i] (v : Places K S) (hμ : HasRootsOfUnity K S₀ (2 ^ i))

/-- The top-coefficient character of the local twist, with its values in the
actual roots of unity of the algebraic closure of the completion. -/
def localRootCharacter : Tate1 (Acoef i) hμ →+ MuAlg (v.1.adicCompletion K) (2 ^ i) :=
  (kmilneF hS i v hμ).symm.toAddMonoidHom.comp (urMTopTate hS i hμ v)

theorem localRootCharacter_smul (g : Gloc K v.1) (z : Tate1 (Acoef i) hμ) :
    localRootCharacter hS i v hμ (inflMap K hS (locMap K S v.1 g) • z) =
      g • localRootCharacter hS i v hμ z := by
  apply urMMuIncl_injective (v.1.adicCompletion K) (2 ^ i)
  change urMLam hS i hμ v (inflMap K hS (locMap K S v.1 g) • z) =
      urMMuIncl (v.1.adicCompletion K) (2 ^ i) (g • localRootCharacter hS i v hμ z)
  rw [urMMuIncl_smul]
  exact urMLam_smul hS i hμ v g z

private theorem localRootCharacter_generating (z : Tate1 (Acoef i) hμ)
    (hz : ∀ r : Acoef i, localRootCharacter hS i v hμ (r • z) = 0) : z = 0 :=
  urMLam_generating hS i hμ v z fun r => by
    change urMMuIncl (v.1.adicCompletion K) (2 ^ i) (localRootCharacter hS i v hμ (r • z)) = 0
    rw [hz r, map_zero]

private theorem localRootDual_card_le (M : Type) [AddCommGroup M] [Finite M] :
    Nat.card (InternalHom (Gloc K v.1) M (MuAlg (v.1.adicCompletion K) (2 ^ i))) ≤ Nat.card M := by
  let incl := urMMuIncl (v.1.adicCompletion K) (2 ^ i)
  obtain ⟨hfinite, hcard⟩ := urM_hom_finite_card (v.1.adicCompletion K) M
  letI := hfinite
  refine (Nat.card_le_card_of_injective (fun f : InternalHom (Gloc K v.1) M
    (MuAlg (v.1.adicCompletion K) (2 ^ i)) => incl.comp f.toAddMonoidHom) ?_).trans hcard
  intro f g hfg
  apply InternalHom.ext
  exact AddMonoidHom.ext fun m => urMMuIncl_injective _ _ (DFunLike.congr_fun hfg m)

variable (W : WeierstrassCurve K) [W.IsElliptic] (α : GKS K S₀ →* (Acoef i)ˣ)
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)] [IsOpenKer α]
  (hFull : FullTorsion K S₀ W (2 ^ i))

abbrev kummerLocalCoeff (α : GKS K S₀ →* (Acoef i)ˣ) :=
  ResMod (locMap K S v.1) (MinS hS W i α)

/-- The inverse-character module is the additive roots-of-unity dual of the
actual coefficient module. The equivalence is induced by the literal local
Weil pairing at this place. -/
def localCoefficientTateDual : kummerLocalCoeff hS i v W (charInv α) ≃+
    InternalHom (Gloc K v.1) (kummerLocalCoeff hS i v W α) (MuAlg (v.1.adicCompletion K) (2 ^ i)) := by
  let β := kannBeta hS W i v hμ α
  let λ := localRootCharacter hS i v hμ
  have hgen := localRootCharacter_generating hS i v hμ
  have hf := scalarizedDual_injective (G := Gloc K v.1) β λ
    (weilPairingM_flip_bijective (S := S₀) W hμ (Acoef i) α hFull).injective hgen
  have hg := scalarizedDual_injective (G := Gloc K v.1) β.flip λ
    (weilPairingM_bijective (S := S₀) W hμ (Acoef i) α hFull).injective hgen
  letI : Finite (kummerLocalCoeff hS i v W α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  letI : Finite (kummerLocalCoeff hS i v W (charInv α)) := inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  have hcard := (localRootDual_card_le i v (kummerLocalCoeff hS i v W α)).trans
    ((Nat.card_le_card_of_injective _ hg).trans (localRootDual_card_le i v (kummerLocalCoeff hS i v W (charInv α))))
  exact AddEquiv.ofBijective (scalarizedDual β λ) (hf.bijective_of_nat_card_le hcard)

/-- Evaluation of the additive dual is the original Weil form followed by the
same generating character. -/
theorem localCoefficientTateDual_apply (x : kummerLocalCoeff hS i v W α)
    (y : kummerLocalCoeff hS i v W (charInv α)) :
    (localCoefficientTateDual hS i v hμ W α hFull y).toAddMonoidHom x =
      localRootCharacter hS i v hμ (kannBeta hS W i v hμ α x y) := rfl

/-- The coefficient dual identification intertwines the local Galois action. -/
theorem localCoefficientTateDual_smul (g : Gloc K v.1) (y : kummerLocalCoeff hS i v W (charInv α)) :
    localCoefficientTateDual hS i v hμ W α hFull (g • y) =
      g • localCoefficientTateDual hS i v hμ W α hFull y := by
  apply InternalHom.ext
  apply AddMonoidHom.ext
  intro x
  rw [localCoefficientTateDual_apply, InternalHom.toAddMonoidHom_smul, TauCeti.homAction]
  change localRootCharacter hS i v hμ (kannBeta hS W i v hμ α x (g • y)) =
    g • (localCoefficientTateDual hS i v hμ W α hFull y).toAddMonoidHom (g⁻¹ • x)
  rw [localCoefficientTateDual_apply, ← localRootCharacter_smul]
  change localRootCharacter hS i v hμ (kannBeta hS W i v hμ α x (g • y)) =
    localRootCharacter hS i v hμ (g • kannBeta hS W i v hμ α (g⁻¹ • x) y)
  rw [← kannBeta_smul, smul_inv_smul]

end Kummer

end ZInQ.Manuscript.RC.KummerMaps
