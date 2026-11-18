import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Glue
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# G0: the newform of a modular elliptic curve, from Li 1975 and Carayol 1986

The peer package `RC53Assist/NewformPeriods` names the translation step G0,
`NewformOfModularCurveGlue`: a modular `E/ℚ` (`IsModular E`: a weight-two cusp form on `Γ₀(N)`
with the coefficients of `L(E, s)`) has, at some level `M`, a normalized full Hecke eigenform with
trivial character whose coefficients are `aₙ = E.LFunction n`.

**What is a print, and what is proved.**
* `LiCarayolNewformOfModular` (PRINT, consequence form; statement not read against the papers
  here, UNVERIFIED as a reading): the newform theory of W.-C. W. Li, *Newforms and functional
  equations*, Math. Ann. **212** (1975), 285–315 (bibitem `li-newforms`, tex L11050–11052; the
  manuscript's locator: p. 296): the decomposition of `S₂(Γ₀(N))` into newforms of levels
  `M ∣ N` and their images, with multiplicity one, so the eigenvalue system of a form on `Γ₀(N)`
  that is a Hecke eigenform away from `N` is that of a unique newform of some level `M ∣ N`;
  together with H. Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires
  de Hilbert*, Ann. Sci. ÉNS **19** (1986), 409–468 (bibitem `carayol`, tex L11205–11208; the
  manuscript's locator: Theorem A): the level of that newform is the conductor of `E`, and its
  coefficients at the primes dividing the level are those of the local factors of `L(E, s)`.
  The Lean statement keeps the consequence used here: for a modular `E` there are `M ∣ N` and
  a newform of level `M`, weight `2` and trivial nebentypus (Tau Ceti's `HeckeRing.GL2.Newform`,
  Miyake's primitive form) whose coefficients are `E.LFunction n` for every `n ≥ 1`. The
  identification of the level with the conductor is not used and is not stated (Mathlib has no
  conductor of an elliptic curve). Nothing beyond the two papers is added.
* **`newformOfModularCurveGlue_of_print` (PROVED)**: `LiCarayolNewformOfModular →
  NewformOfModularCurveGlue`. The full eigen-ness at every `Tₙ`, the primes dividing the level
  included, is Tau Ceti's theorem `Newform.toEigenform` (Diamond–Shurman Theorem 5.8.2, Miyake
  Theorem 4.6.13), and the passage from `Γ₁(M)` with trivial character to `Γ₀(M)` is
  `cuspFormCharSpaceOneEquiv`. Both preserve the underlying function on `ℍ`.

**Classification.** `LiCarayolNewformOfModular` PRINT (consequence form; the manuscript's
locators Li p. 296 and Carayol Theorem A, statement not read against the papers here); the
reduction PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open CongruenceSubgroup UpperHalfPlane HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformPeriods ZInQ.Manuscript.PoleS12

/-- **Li 1975 and Carayol 1986: the newform of a modular elliptic curve** (PRINT, consequence
form; bibitems `li-newforms`, `carayol`; the manuscript's locators: Li, Math. Ann. 212 (1975),
p. 296, tex L11050–11052, and Carayol, Ann. Sci. ÉNS 19 (1986), Theorem A, tex L11205–11208;
statement not read against the papers here, UNVERIFIED as a reading). If `E/ℚ` has a
weight-two cusp form on `Γ₀(N)`, `N > 0`, with the coefficients of `L(E, s)`, then for some
`M ∣ N` there is a newform of level `M`, weight `2` and trivial nebentypus whose coefficients are
`E.LFunction n` for every `n ≥ 1`. -/
def LiCarayolNewformOfModular : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
    ∀ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      (∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
      ∃ (M : ℕ) (_ : NeZero M) (F : Newform M 2), M ∣ N ∧ F.χ = 1 ∧
        ∀ n : ℕ, 0 < n → (qExpansion 1 F.toCuspForm).coeff n = (E.LFunction n : ℂ)

/-- **G0 from the Li–Carayol print** (PROVED). -/
theorem newformOfModularCurveGlue_of_print (h : LiCarayolNewformOfModular) :
    NewformOfModularCurveGlue := by
  intro E hE hM
  obtain ⟨N, hN, f, hf⟩ := hM
  obtain ⟨M, hM0, F, -, hχ, hcoeff⟩ := h E hE N hN f hf
  have hmem : F.toCuspForm ∈ cuspFormCharSpace (N := M) 2 (1 : (ZMod M)ˣ →* ℂˣ) :=
    hχ ▸ F.mem_charSpace
  set g := TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨F.toCuspForm, hmem⟩
  have hg : ⇑g = ⇑F.toCuspForm := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply _
  refine ⟨M, hM0, g, ⟨?_, F.toEigenform, by rw [Newform.toEigenform_χ, hχ], fun τ => ?_⟩,
    fun n hn => ?_⟩
  · rw [show qExpansion 1 g = qExpansion 1 F.toCuspForm from congrArg (qExpansion 1) hg]
    exact Newform.qExpansion_coeff_one F
  · rw [Newform.toEigenform_toCuspForm, hg]
  · rw [show qExpansion 1 g = qExpansion 1 F.toCuspForm from congrArg (qExpansion 1) hg]
    exact hcoeff n hn

end ZInQ.Contrib.CloudB3RC53.ModularWeil
