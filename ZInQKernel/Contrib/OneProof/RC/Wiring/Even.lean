import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# Theorem 5.3, Lane RC0 round 2: the normalized central values (lane RC11)

`lstarTarget_of` (PROVED from lane RC11's `CentralNormalization.lstar_ne_zero_iff`): the field
`RCSteps.lstar_ne_zero_iff` (tex 1825–1830) when the skeleton's `L_*` is RC11's normalized central
value `CentralNormalization.Lstar` (fixed periods `|Ω^±|`, `L_*(h) = √|h| L(E^{(h)},1)/|Ω^{sign h}|`;
its existence is GLUE, Birch–Manin), using that every twist has an entire continuation, which
follows from the GLUE `RootNumberExists` (modularity with Hecke's functional equation).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **`L_*` is RC11's normalization** (GLUE: Birch–Manin rationality of
`√|h| L(E^{(h)},1)/Ω^{sign h}`, with the periods fixed by `π` and the integral lattice, tex
1825–1830, 7175–7177; owner RC11). -/
def LstarNormalized {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ N : Even.CentralNormalization (Ecurve ℓ), N.Lstar = D.Lstar

/-- **`lstar_ne_zero_iff`** (PROVED from lane RC11's `CentralNormalization.lstar_ne_zero_iff`). -/
theorem lstarTarget_of {ℓ : ℕ} (hℓ : 0 < ℓ) (hRN : Nonvanishing.FromRC8.RootNumberExists)
    {D : RCData ℓ} (hN : LstarNormalized D) : LstarTarget D := by
  obtain ⟨N, hN⟩ := hN
  intro h hh
  have hE : (Etw ℓ h).IsElliptic := by
    rw [Etw_eq_curve]
    exact PoleRC.curve_isElliptic (by exact_mod_cast mul_ne_zero hh (by exact_mod_cast hℓ.ne'))
  obtain ⟨w, -, -, F, hF, -⟩ := hRN _ hE
  rw [← hN]
  exact N.lstar_ne_zero_iff hh hF

end ZInQ.Manuscript.RC.Wiring
