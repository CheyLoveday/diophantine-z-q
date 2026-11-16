import ZInQKernel.Contrib.OneProof.EichlerBound.Quadratic

/-! TEMPORARY development copy of `GRCountX6.OptEmb` and `GRCountX6.ConjRel` (verbatim from
`ZInQKernel/Contrib/OneProof/GRCountX6.lean`); replaced by `import ZInQKernel.Contrib.OneProof.GRCountX6` in the
final module. -/

noncomputable section

namespace GRCountX6

def OptEmb (k : Type) [Field k] [NumberField k] (R : Subring k) : Type :=
  {Φ : k →ₐ[ℚ] LeafQM.B // LeafQM.O.comap Φ.toRingHom = R}

def ConjRel {k : Type} [Field k] [NumberField k] (R : Subring k) (Φ Ψ : OptEmb k R) : Prop :=
  ∃ u : (↥LeafQM.O)ˣ, ∀ x : k,
    Ψ.1 x = ((u : LeafQM.O) : LeafQM.B) * Φ.1 x * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B)

end GRCountX6
