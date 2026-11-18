import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Bridge

/-!
# Lane RC28 round 2, part 8: the round-1 collapse obstruction disappears at the fibres

Manuscript `diophantine_zq.tex` (11/5), tex 4976–5200; lane RC0's
`regularityInputsG_iff_of_unitFibre` and its condition `E`.

In round 1 the condition `E` was refuted for the finite coefficient data because every genuine
Galois Selmer complex over `k(𝔭)` with `2`-power torsion coefficients has subsingleton terms
(`subsingleton_selCx_galois`, `collapse_refuted_actual`). For the fibres `V_𝔭` of `𝕋`:

* `isUnit_two_fibreField`, `charZero_fibreField` (`Bridge.lean`): `k(𝔭)` has characteristic zero;
* `not_two_pow_torsion` (`Bridge.lean`): a nonzero `V_𝔭` is not `2`-power torsion;
* **`nontrivial_selCx_one`**: the degree-one term of the genuine Selmer complex of `V_𝔭` (any local
  conditions) is nonzero as soon as `V_𝔭` is (constant `1`-cochains are continuous), so the
  argument of round 1 (`isEmpty_homotopyEquiv_unitFibre`, which needs a subsingleton degree-one
  term) does not apply; `fibreFamily` (`Bridge.lean`) is the genuine slot for the switching data.

Whether `E` holds for these fibres is the content of the switching argument (the continuous
Galois cohomology of `V_𝔭` must be computed); it is neither proved nor refuted here.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain CategoryTheory
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx selT)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-- The constant continuous `1`-cochain with value `v`. -/
def constOneCochain (v : VP K S W P α) :
    contCochain (ResAt P) (GKS K S) (VP K S W P α) 1 :=
  ⟨(fun _ => v : (Fin 1 → GKS K S) → VP K S W P α), continuous_const⟩

theorem constOneCochain_injective : Function.Injective (constOneCochain W P α) := by
  intro v w h
  have := congrArg (fun c : contCochain (ResAt P) (GKS K S) (VP K S W P α) 1 =>
    (c.1 : (Fin 1 → GKS K S) → VP K S W P α) (fun _ => 1)) h
  exact this

/-- **The degree-one term of the genuine Selmer complex of a nonzero `V_𝔭` is nonzero**, for any
local conditions: the round-1 vanishing argument does not apply. Kind: PROVED. -/
theorem nontrivial_selCx_one [Nontrivial (VP K S W P α)]
    (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α)) :
    Nontrivial ((selCx (fibreSelData W P α Δ)).toCC.X 1) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : VP K S W P α)
  let g : (fibreSelData W P α Δ).G.X 1 := constOneCochain W P α v
  refine ⟨⟨(show selT (fibreSelData W P α Δ) 1 from (g, 0, 0)), 0, fun h => hv ?_⟩⟩
  have h1 := congrArg (fun x : selT (fibreSelData W P α Δ) 1 => x.1) h
  have h2 : constOneCochain W P α v = constOneCochain W P α 0 := by
    refine h1.trans ?_
    apply Subtype.ext
    rfl
  exact constOneCochain_injective W P α h2

end ZInQ.Manuscript.RC.LambdaCoef
