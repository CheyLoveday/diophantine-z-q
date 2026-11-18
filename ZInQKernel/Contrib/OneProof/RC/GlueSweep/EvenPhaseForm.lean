import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenPhaseBridge

/-!
# Lane RC22 (glue sweep), even share: the reference form of `EvenPhaseData` from Waldspurger's
# nonvanishing print

Lane RC11's structure `EvenPhaseData E L σ D₀` (`EvenPhase.lean`, Proposition `ex:app-even-phase`,
tex 7792–8134) bundles, as ELLIOT data, the reference form — a level `N` with `4 ∣ N`, characters
`ψ, η = ψχ_{−σ}` and a weight-`3/2` form `g` in the good-Hecke eigenspace of `E` with
`a_g(D₀) ≠ 0` (fields `N, hN, ψ, η, hψη, g, hg, ha₀`; its docstring: "Waldspurger's theta theorem
and Elliot's local scalar type, tex 7821–7940; RC8's `WaldspurgerNonvanishing`") — together with
the phase data `retained, z, z_root, z_sq, rational` (tex 8041–8134).

Lane RC8 states the first part as the PRINT `WaldspurgerNonvanishing` (Waldspurger, JMPA 60
(1981), Prop. 18 and its proof, pp. 466–467; ICM 1983, Thm. 1 and Prop. 1; with Elliot's local
construction), from `ord_{s=1} L(E^{(σD₀)}, s) = 0`. The bridge `evenPhaseData_of_waldspurgerNonvanishing`
discharges the reference-form fields from that print, leaving as ELLIOT input only the phase data
for the reference form (`EvenPhaseRest`); the nonvanishing `ord_{s=1} L(E^{(σD₀)}, s) = 0` comes
from `L_*(σD₀) ≠ 0` (`lstar_ne_zero_iff_of_bcdt`).

All results here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic

/-- **The phase data of Proposition `ex:app-even-phase` for a fixed reference form** (ELLIOT;
tex 8041–8134; the fields `retained`, `retained_spec`, `D₀_mem`, `z`, `z_root`, `z_sq`,
`rational` of lane RC11's `EvenPhaseData`, verbatim, for the level `N`, the character `ψ` and the
form `g`): the retained positive squarefree `D` prime to `N` in the unit squareclasses of `D₀` at
the level (containing `D₀`), the phase `z_D` (a two-power root of unity with
`z_D² = ψ(D)ψ(D₀)⁻¹`), and the Galois comparison `a_g(D)/(a_g(D₀) z_D) ∈ ℚ` (on Ramsey's model). -/
structure EvenPhaseRest (D₀ : ℕ) (N : ℕ) (ψ : DirichletCharacter ℂ N) (g : UpperHalfPlane → ℂ)
    where
  retained : Set ℕ
  retained_spec : ∀ D ∈ retained,
    0 < D ∧ Squarefree D ∧ D.Coprime N ∧ SameUnitClassesAtLevel N D D₀
  D₀_mem : D₀ ∈ retained
  z : ℕ → ℂ
  z_root : ∀ D ∈ retained, ∃ k : ℕ, z D ^ (2 ^ k) = 1
  z_sq : ∀ D ∈ retained, z D ^ 2 = ψ D * (ψ D₀)⁻¹
  rational : ∀ D ∈ retained, ∃ r : ℚ, hiwCoeff g D / hiwCoeff g D₀ = z D * (r : ℂ)

/-- **`EvenPhaseData` with its reference form discharged by Waldspurger's nonvanishing print**
(tex 7812–7940 for the form, 8041–8134 for the phase; PROVED from lane RC8's PRINT
`WaldspurgerNonvanishing`, the shared printed leaf `PoleS12.BCDTThmA`, lane RC8's GLUE
`HasseConvergence`, and the ELLIOT phase data `rest`, supplied for every reference form that the
print can return). The fixed finite set `S₀ ∋ 2` of primes contains every prime of the level of
every functional equation of `L(E, s)` (the conductor's primes), and `D₀ > 0` is squarefree, prime
to `S₀`, with `L_*(σD₀) ≠ 0`. Consumer: lane RC11's structure `EvenPhaseData` (its fields
`N, hN, ψ, η, hψη, g, hg, ha₀`); discharger: `WaldspurgerNonvanishing` with
`lstar_ne_zero_iff_of_bcdt` for `ord_{s=1} L(E^{(σD₀)}, s) = 0`. Requiring the phase data for every
such form is no stronger in substance: by (E.10) and the proportional-functionals step
(tex 8030–8039) the ratios `a_g(D)/a_g(D₀)` do not depend on the form. -/
theorem evenPhaseData_of_waldspurgerNonvanishing (hWN : WaldspurgerNonvanishing)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (S₀ : Finset ℕ) (hS₀ : ∀ p ∈ S₀, p.Prime) (h2 : 2 ∈ S₀)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0)
    (rest : ∀ (N : ℕ) (ψ η : DirichletCharacter ℂ N) (g : UpperHalfPlane → ℂ), 4 ∣ N →
      (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) →
      (∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)) →
      IsInWaldspurgerEigenspace E N ψ η g → hiwCoeff g D₀ ≠ 0 → EvenPhaseRest D₀ N ψ g) :
    Nonempty (ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀) := by
  have hA : AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 :=
    (lstar_ne_zero_iff_of_bcdt hB hH L (ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀)).mp hL₀
  obtain ⟨N, hN, hNS, ψ, η, hψη, g, hg, ha₀⟩ :=
    hWN E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq₀ hD₀S hA
  let R := rest N ψ η g hN hNS hψη hg ha₀
  exact ⟨{ N := N, hN := hN, ψ := ψ, η := η, hψη := hψη, g := g, hg := hg, ha₀ := ha₀,
           retained := R.retained, retained_spec := R.retained_spec, D₀_mem := R.D₀_mem,
           z := R.z, z_root := R.z_root, z_sq := R.z_sq, rational := R.rational }⟩

end ZInQ.Manuscript.RC.GlueSweep.Even
