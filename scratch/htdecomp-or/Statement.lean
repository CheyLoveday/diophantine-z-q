import ZInQKernel.Contrib.OneProof.HodgeTateDecompOr

/-! Verbatim copy of the research field `hodgeTateDecompExists`
(`ZInQKernel/Contrib/OneProof/HodgeTatePairingDecomp.lean` L44 at wip/leaf-fold33b), checked `Iff.rfl`
against the tree's definition and against the type of the bundle field of the current top generation. -/

namespace HTOrScratch

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

def HodgeTateDecompExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

theorem same : HodgeTateDecompExists ↔ ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists := Iff.rfl

/-- The scratch copy follows from the or-leaf. -/
theorem copy_of_or (h : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr) : HodgeTateDecompExists :=
  ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or h

end HTOrScratch

#print axioms HTOrScratch.copy_of_or
