import ZInQKernel.Contrib.OneProof.R16CoreYSatDet

/-! The target field `r16CoreY`, copied verbatim from `ZInQKernel/Contrib/OneProof/R16Split.lean` (l. 534),
with a definitional check against the original and the discharge at the copy. -/

namespace R16CloseTarget

open CategoryTheory AlgebraicGeometry LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)

def R16CoreY : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p)

theorem copy_iff : R16CoreY ↔ R16Split.R16CoreY := Iff.rfl

theorem r16CoreY_copy (h1 : AfTateLam.HeckeJ1DS) (h2 : AfTateLam.AfShimura)
    (hS : AfTateLam.AfTateDSLambdaSat) (hD : AfTateLam.AfDetLambda) (hI : X1Igusa.IgusaGL2DS)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16CoreY :=
  AfTateLam.r16CoreY_of_sat_det h1 h2 hS hD hI hM

end R16CloseTarget

#print axioms R16CloseTarget.r16CoreY_copy
