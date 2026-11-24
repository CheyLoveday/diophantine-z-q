import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Dictionary

/-!
# Theorem A of Breuil–Conrad–Diamond–Taylor in the printed vocabulary

`BCDTThmAPrinted` (`Statement.lean`) is stated over Mathlib's cusp forms and the vendored Hecke
operators. Here the same statement is written with the definitions of pp. 1–2 of the author
manuscript themselves, and the two are proved equivalent (`bcdtThmAPrintedLiteral_iff`):

* a cusp form is a function on the upper half plane with the three printed properties
  (`IsPrintedCuspForm`, `Dictionary.lean`);
* its coefficients `c_n(f)` are those of the printed expansion
  `f(z) = ∑_{n=1}^∞ c_n(f) e^{2πinz}` (`IsPrintedExpansion`), and `L(f, s) = ∑ c_n(f)/n^s`;
* `T_p` is the printed formula (`printedHeckeT`), with any matrix `(a b; c d) ∈ SL₂(ℤ)` such that
  `c ≡ 0` and `d ≡ p mod N` (`IsPrintedHeckeMatrix`);
* an eigenform is a nonzero simultaneous eigenvector of these `T_p`, `p ∤ N`
  (`IsPrintedEigenform`).

As in `Statement.lean`, the level `N(E)` is replaced by an unspecified positive level.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.BCDTPrint

open Complex CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Real

variable {N : ℕ}

/-! ### The printed Hecke operators and eigenforms -/

/-- **DEFINITION**, the matrices admitted in the printed definition of `T_p`
(Breuil–Conrad–Diamond–Taylor, p. 2): `(a b; c d) ∈ SL₂(ℤ)` "with `c ≡ 0 mod N` and
`d ≡ p mod N`". -/
def IsPrintedHeckeMatrix (N p : ℕ) (γ : SL(2, ℤ)) : Prop :=
  ((γ 1 0 : ℤ) : ZMod N) = 0 ∧ ((γ 1 1 : ℤ) : ZMod N) = p

/-- **PROVED**, from the surjectivity of `Γ₀(N) → (ℤ/Nℤ)ˣ` (vendored
`Gamma0Map_toHomUnits_surjective`): for a prime `p ∤ N` an admissible matrix exists. -/
theorem exists_isPrintedHeckeMatrix [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    ∃ γ : SL(2, ℤ), IsPrintedHeckeMatrix N p γ := by
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) (ZMod.unitOfCoprime p hcop)
  refine ⟨g, Gamma0_mem.mp g.2, ?_⟩
  have h := congrArg Units.val hg
  rwa [MonoidHom.coe_toHomUnits, Gamma0Map_apply, ZMod.coe_unitOfCoprime] at h

/-- **DEFINITION**, the printed Hecke operator (Breuil–Conrad–Diamond–Taylor, p. 2):
`(f|T_p)(z) = p^{−1} ∑_{i=0}^{p−1} f((z + i)/p) + p^{k−1} (cpz + d)^{−k} f((apz + b)/(cpz + d))`
for `γ = (a b; c d)`. Values are read through Mathlib's chart `ofComplex`; for `p ≥ 1` every
argument lies in the upper half plane. -/
def printedHeckeT (k : ℤ) (p : ℕ) (γ : SL(2, ℤ)) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ i ∈ Finset.range p, (f ∘ ofComplex) ((z + i) / p) +
    (p : ℂ) ^ (k - 1) * ((γ 1 0 : ℂ) * p * z + γ 1 1) ^ (-k) *
      (f ∘ ofComplex) (((γ 0 0 : ℂ) * p * z + γ 0 1) / ((γ 1 0 : ℂ) * p * z + γ 1 1))

/-- **PROVED**, `heckeTCuspNat_apply_eq_printed` restated: on a cusp form, the vendored `T_p`
is `printedHeckeT` at every admissible matrix. -/
theorem heckeTCuspNat_apply_eq_printedHeckeT [NeZero N] {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬p ∣ N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {γ : SL(2, ℤ)}
    (hγ : IsPrintedHeckeMatrix N p γ) (z : ℍ) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f z = printedHeckeT k p γ f z :=
  heckeTCuspNat_apply_eq_printed hp hpN f γ hγ.1 hγ.2 z

/-- **DEFINITION**, an eigenform of weight `k` and level `N` in the printed vocabulary
(Breuil–Conrad–Diamond–Taylor, pp. 1–2): a cusp form in the printed sense which is a
simultaneous eigenvector, hence nonzero, of the printed operators `T_p` for the primes `p ∤ N`;
"defined by [the formula] for any" admissible matrix is read as: the eigen-relation holds with
every admissible matrix. -/
def IsPrintedEigenform (N : ℕ) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  IsPrintedCuspForm N k f ∧ f ≠ 0 ∧
    ∀ p : ℕ, p.Prime → ¬p ∣ N → ∃ c : ℂ, ∀ γ : SL(2, ℤ), IsPrintedHeckeMatrix N p γ →
      ∀ z : ℍ, printedHeckeT k p γ f z = c * f z

/-- **PROVED**, by `heckeTCuspNat_apply_eq_printedHeckeT` and `exists_isPrintedHeckeMatrix`:
for a Mathlib cusp form on `Γ₁(N)`, being an eigenform in the printed vocabulary is
`IsBCDTEigenform`. -/
theorem isPrintedEigenform_iff [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IsPrintedEigenform N k f ↔ IsBCDTEigenform f := by
  constructor
  · rintro ⟨-, hne, heig⟩
    refine ⟨fun h ↦ hne (by rw [h]; rfl), fun p hp hpN ↦ ?_⟩
    obtain ⟨c, hc⟩ := heig p hp hpN
    obtain ⟨γ, hγ⟩ := exists_isPrintedHeckeMatrix hp hpN
    refine ⟨c, CuspForm.ext fun z ↦ ?_⟩
    rw [heckeTCuspNat_apply_eq_printedHeckeT hp hpN f hγ, hc γ hγ z]
    rfl
  · rintro ⟨hne, heig⟩
    refine ⟨isPrintedCuspForm f, fun h ↦ hne (DFunLike.coe_injective h), fun p hp hpN ↦ ?_⟩
    obtain ⟨c, hc⟩ := heig p hp hpN
    refine ⟨c, fun γ hγ z ↦ ?_⟩
    rw [← heckeTCuspNat_apply_eq_printedHeckeT hp hpN f hγ, hc]
    rfl

/-! ### The printed expansion and condition (2) -/

/-- **DEFINITION**, the printed expansion (Breuil–Conrad–Diamond–Taylor, p. 1): "If
`f ∈ S_k(N)` then it has an expansion `f(z) = ∑_{n=1}^∞ c_n(f) e^{2πinz}`". The sum is indexed
from `0` with `c_0 = 0`. -/
def IsPrintedExpansion (f : ℍ → ℂ) (c : ℕ → ℂ) : Prop :=
  c 0 = 0 ∧ ∀ z : ℍ, HasSum (fun n : ℕ ↦ c n * cexp (2 * π * Complex.I * n * z)) (f z)

/-- **PROVED**, the power of the local parameter: `q^n = e^{2πinz}` for `q = e^{2πiz}`. -/
theorem qParam_one_pow (z : ℂ) (n : ℕ) :
    Function.Periodic.qParam 1 z ^ n = cexp (2 * π * Complex.I * n * z) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **PROVED**, by Mathlib's `ModularForm.hasSum_qExpansion` and
`ModularFormClass.qExpansion_coeff_unique`: for a cusp form on `Γ₁(N)`, a sequence is the
sequence of printed coefficients exactly when it is the sequence of `q`-expansion
coefficients of period one. -/
theorem isPrintedExpansion_iff [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (c : ℕ → ℂ) : IsPrintedExpansion f c ↔ c = fun n ↦ (qExpansion 1 f).coeff n := by
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma1_map N
  constructor
  · rintro ⟨-, hc⟩
    funext n
    refine ModularFormClass.qExpansion_coeff_unique one_pos hΓ (fun z ↦ ?_) n
    simpa only [qParam_one_pow, smul_eq_mul] using hc z
  · rintro rfl
    refine ⟨CuspFormClass.qExpansion_coeff_zero f one_pos hΓ, fun z ↦ ?_⟩
    simpa only [qParam_one_pow] using ModularForm.hasSum_qExpansion (f := f) one_pos hΓ z

/-- **DEFINITION**, condition (2) of Breuil–Conrad–Diamond–Taylor (Introduction, p. 3) at a
level `N`, in the printed vocabulary: there are an eigenform `f` of weight 2 and level `N` and
the sequence `c_n(f)` of its expansion with `L(E, s) = ∑ c_n(f)/n^s` on a right half-plane. -/
def PrintedCondition2At (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  ∃ f : ℍ → ℂ, IsPrintedEigenform N 2 f ∧ ∃ c : ℕ → ℂ, IsPrintedExpansion f c ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = LSeries c s

/-- **PROVED**, by `cuspFormOfPrinted`, `isPrintedEigenform_iff` and `isPrintedExpansion_iff`:
condition (2) in the printed vocabulary is `Condition2At`. -/
theorem printedCondition2At_iff [NeZero N] (E : WeierstrassCurve ℚ) :
    PrintedCondition2At E N ↔ Condition2At E N := by
  constructor
  · rintro ⟨f, ⟨hcusp, hne, heig⟩, c, hc, σ, hL⟩
    let F := cuspFormOfPrinted (by norm_num) hcusp
    have hF : IsBCDTEigenform F := (isPrintedEigenform_iff F).mp ⟨hcusp, hne, heig⟩
    have hcF : c = fun n ↦ (qExpansion 1 F).coeff n := (isPrintedExpansion_iff F c).mp hc
    exact ⟨F, hF, σ, fun s hs ↦ by rw [hL s hs, hcF]; rfl⟩
  · rintro ⟨F, hF, σ, hL⟩
    exact ⟨F, (isPrintedEigenform_iff F).mpr hF, _, (isPrintedExpansion_iff F _).mpr rfl, σ, hL⟩

/-- **DEFINITION**, Theorem A of Breuil–Conrad–Diamond–Taylor read with condition (2), in the
printed vocabulary of pp. 1–3 of the author manuscript (see the verbatim text on
`BCDTThmAPrinted`): every elliptic curve `E/ℚ` satisfies condition (2) at some positive level.
The level `N(E)` of the print is replaced by an unspecified positive level, as in
`BCDTThmAPrinted`, to which it is equivalent (`bcdtThmAPrintedLiteral_iff`). It is a second
spelling of the same printed statement, recorded to show that the formalization over library
objects is faithful; the PRINT input remains `BCDTThmAPrinted`. -/
def BCDTThmAPrintedLiteral : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ N : ℕ, 0 < N ∧ PrintedCondition2At E N

/-- **PROVED**, by `printedCondition2At_iff`: the statement in the printed vocabulary is
equivalent to `BCDTThmAPrinted`. -/
theorem bcdtThmAPrintedLiteral_iff : BCDTThmAPrintedLiteral ↔ BCDTThmAPrinted := by
  constructor
  · intro h E hE
    obtain ⟨N, hN, hc⟩ := h E hE
    have : NeZero N := ⟨hN.ne'⟩
    exact ⟨N, inferInstance, (printedCondition2At_iff E).mp hc⟩
  · intro h E hE
    obtain ⟨N, _, hc⟩ := h E hE
    exact ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), (printedCondition2At_iff E).mpr hc⟩

/-- **PROVED**, `bcdtThmAPrintedLiteral_iff` and `bcdtThmA_of_printed`: the printed statement
in its own vocabulary gives the tree's `PoleS12.BCDTThmA`. -/
theorem bcdtThmA_of_printedLiteral (hB : BCDTThmAPrintedLiteral) :
    ZInQ.Manuscript.PoleS12.BCDTThmA :=
  bcdtThmA_of_printed (bcdtThmAPrintedLiteral_iff.mp hB)

end ZInQ.Contrib.RC53Assist.BCDTPrint
