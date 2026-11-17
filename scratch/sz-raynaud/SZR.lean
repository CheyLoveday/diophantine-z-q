import ZInQKernel.Contrib.OneProof.GaRigiditySGA7
import ZInQKernel.Contrib.OneProof.RaynaudSemistableOr
import ZInQKernel.Contrib.OneProof.NeronDVR
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# sz-raynaud: the manuscript's route at diophantine_zq.tex L814-818

See the module doc of `ZInQKernel/Contrib/OneProof/SZRaynaud.lean` (this is its development copy).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq)
open ReductSplit ReductGlue ZInQ.HeightSplit

namespace SZRaynaud

/-! ## §1. Wild inertia -/

/-- **Wild inertia** of a valuation ring `w` of `Ω ⊇ K` (the first lower ramification group `G₁`; Serre, *Corps
locaux*, IV §1-§2; numbers UNVERIFIED): `σ` moves every nonzero `x` by less than `x`, i.e. `v_w(σx - x) > v_w(x)`,
equivalently `σx/x ≡ 1 mod 𝔪_w`. This is the valuation-ring form of the kernel's `wildSet`
(TailH: `‖σ z - z‖ < ‖z‖` for `z ≠ 0` in `ℚ̄_p`). -/
def IsWildInertia {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x

/-! ## §2. Raynaud's criterion as Silverberg–Zarhin Theorem 3.5 states it -/

/-- **LEAF `SilverbergZarhinThm35`** (Raynaud's criterion as cited by the manuscript, diophantine_zq.tex L816,
`\cite[Theorem 3.5]{silverbergzarhin}`: A. Silverberg, Yu. G. Zarhin, *Semistable reduction and torsion subgroups of
abelian varieties*, Ann. Inst. Fourier 45 (1995), 403-420, Theorem 3.5, p. 406, which cites SGA 7 IX Prop. 4.7).
Provenance (b): a cited print, cited by the manuscript's bibliography (L11077). Wording UNVERIFIED (Silverberg–
Zarhin's page not re-read, no network). *As the manuscript and the notes give it*: `F` a field with a discrete
valuation, `n ≥ 3` not divisible by the residue characteristic, `A/F` an abelian variety whose points of order `n`
are defined over an unramified extension of `F`; then `A` has semistable reduction.

*Lean form* (a specialization): the unramified extension is `F` itself (the `m`-torsion is rational over `K`, which
is how the manuscript uses it: `F = L_v(A[3])`); "semistable reduction" is the disjunction of its two readings,
over the residue field `k` (`IsSemistableResT`: the identity component of `𝒩_k` is an extension of an abelian
variety by a torus, for every Néron model) and on the geometric special fibre (`SemistableNeronModels`, the kernel's
form), so either reading of the print gives this by or-introduction (as dict-models' `RaynaudSemistableSHOr`).
Known issues (docs/research/sz-raynaud.md §4): the printed threshold at `n = 3` is unconfirmed (locators R6: the
extraction reads like `> 3`); the printed base (any discretely valued field, or complete/henselian) is unconfirmed;
Silverberg–Zarhin's definition of semistable reduction is unconfirmed (if it is "no unipotent subgroup", use
`SilverbergZarhinThm35Def34`). -/
def SilverbergZarhinThm35 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    (∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → DictModels.RaynaudOr.IsSemistableResT 𝒩) ∨
      SemistableNeronModels A O

/-- **Raynaud's criterion over every DVR, the kernel's form** (`ReductSplit.RaynaudSemistable`, statement
unchanged) from Silverberg–Zarhin 3.5 and the proved ascent `k → k̄` (Stacks 04KV,
`geomConnOfRationalPoint_proof`). No strict henselization, no base change: the manuscript's route. -/
theorem raynaudSemistable_of_sz35 (h : SilverbergZarhinThm35) : ReductSplit.RaynaudSemistable := by
  intro K _ O _ A m hm hu ht
  rcases h K O A m hm hu ht with h1 | h2
  · exact fun 𝒩 h𝒩 =>
      DictModels.RaynaudOr.isSemistable_of_resT geomConnOfRationalPoint_proof 𝒩 (h1 𝒩 h𝒩)
  · exact h2

/-- **The field `raynaudSemistableSHOr`, statement unchanged** (SGA 7 IX 4.7 over a strictly henselian DVR), as
the specialization of Silverberg–Zarhin 3.5 to strictly henselian discrete valuation rings. -/
theorem raynaudSemistableSHOr_of_sz35 (h : SilverbergZarhinThm35) :
    DictModels.RaynaudOr.RaynaudSemistableSHOr :=
  fun K _ O _ _ A m hm hu ht => h K O A m hm hu ht

/-! ## §3. The manuscript's sentence at L817-818 -/

/-- **LEAF `ElliotWildInertiaTrivial`** (ELLIOT: uncited manuscript sentence, diophantine_zq.tex:817-818, "Its wild
inertia acts trivially on each `V_ℓ(A)` with `ℓ ≠ p`", said of `F = L_v(A[3])` right after semistable reduction
over `F`). Provenance (a): in diophantine_zq.tex, no citation. *Lean form*: `O ⊆ K` a discrete valuation ring,
`Ω` an algebraic closure of `K`, `w` a valuation ring of `Ω` over `O`, `ℓ` a prime invertible in `O`; if `A` has
semistable reduction at `O` (the kernel's form, `HasSemistableReduction`), every wild inertia element `σ` of `w`
(`IsInertia`, `IsWildInertia`) acts trivially on `T_ℓ(A) = lim A(Ω)[ℓⁿ]` (`galTΩ`). `T_ℓ` for `V_ℓ = T_ℓ ⊗ ℚ_ℓ`:
`T_ℓ` is torsion-free, so trivial on `V_ℓ` is trivial on `T_ℓ` (a consequence of the sentence). Standard
(mathematically: SGA 7 IX 3.5 (unipotence) with wild inertia pro-`p`; `elliot_of_semistableUnipotent` proves it
from those), but the manuscript cites nothing for it. -/
def ElliotWildInertiaTrivial : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsWildInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ t = t

/-! ## §4. L814-818 in Lean: wild inertia fixes `A[ℓⁿ]` once `A[m]` is rational -/

/-- **D2 on the manuscript's route** (diophantine_zq.tex L814-818), at number fields, in the objects of r6
(`PkgI2.RaynaudCriterionNF`): `O` a discrete valuation ring of the number field `K`, `w` over it in `K̄`, `m ≥ 3`
invertible in `O` with `A[m]` fixed by `Gal(K̄/K)`; then every wild inertia element of `w` fixes `A(K̄)[ℓⁿ]` for every
prime `ℓ` invertible in `O`. (r6 gives `(σ-1)² = 0` for every inertia element instead.) -/
def RaynaudWildNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ → IsWildInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x

/-- From `σ = 1` on `T_ℓ` to `σ x = x` at a point lifted to level `n`. -/
theorem fix_of_tate {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (B : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (σ : Ω ≃ₐ[K] Ω) (t : TΩ B Ω ℓ) (n : ℕ) (x : B.Pt Ω)
    (ht : t.1 n = Additive.ofMul x) (h : galTΩ B ℓ σ t = t) : B.galAct σ x = x := by
  have h' := congrArg (fun s : TΩ B Ω ℓ => Additive.toMul (s.1 n)) h
  simp only [galTΩ, PkgI3.Tate.map_apply, ht, MonoidHom.toAdditive_apply_apply, toMul_ofMul] at h'
  exact h'

/-- **L814-818 proved from its two leaves** (Silverberg–Zarhin 3.5 and the ELLIOT sentence), the Néron field at
number fields (as r6's proof `GapNeron.raynaudCriterion_leavesNF`), and proved glue: Galois-fixed `m`-torsion is
rational (`[m]` étale, `mulEtaleAbelianScheme_proof`), the ascent `k → k̄` (`geomConnOfRationalPoint_proof`), and
the lift of `A(K̄)[ℓⁿ]` to `T_ℓ` (Mumford's torsion count, `mumfordTorsionAlgClosed_proof`). -/
theorem raynaudWildNF_of_leaves (hSZ : SilverbergZarhinThm35) (hE : ElliotWildInertiaTrivial)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) : RaynaudWildNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ hwild ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hF := ReductGlue.fixedTorsionRational_of_mulEtale
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
  have hT := AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hss : SemistableNeronModels B O :=
    raynaudSemistable_of_sz35 hSZ K O B m hm hmO
      (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact fix_of_tate B ℓ σ t n x ht
    (hE K O (AlgebraicClosure K) w hw B (GapNeron.hasSemistableReduction_ofNF hN O B hss) ℓ hℓO σ hσ
      hwild t)

/-! ## §5. The ELLIOT sentence from SGA 7 IX 3.5 (sanity: what the kernel's old route used) -/

/-- **GLUE `WildPeriodCoprime`** (on-the-spot statement, in neither the manuscript nor Silverberg–Zarhin; standard:
wild inertia is pro-`p`, `p` the residue characteristic, and acts on the finite set `A(Ω)[ℓⁿ]` through a finite
quotient, so with period a power of `p`, prime to `ℓ`; Serre, *Corps locaux*, IV §2, numbers UNVERIFIED). Not
proved here; only used to show that the ELLIOT sentence follows from SGA 7 IX 3.5. -/
def WildPeriodCoprime : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsWildInertia w σ →
      ∀ (n : ℕ) (x : A.Pt Ω), x ^ (ℓ ^ n) = 1 →
        ∃ N : ℕ, Nat.Coprime N (ℓ ^ n) ∧ (A.galAct σ)^[N] x = x

/-- The `n`-th component of an element of `T_ℓ` is killed by `ℓⁿ`. -/
theorem pow_smul_tate {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M] (t : PkgI3.Tate.T ℓ M) (n : ℕ) :
    (ℓ ^ n) • t.1 n = 0 := by
  induction n with
  | zero => simpa using t.2.1
  | succ n ih => rw [pow_succ, mul_smul, t.2.2 n, ih]

/-- **The ELLIOT sentence from the kernel's old route**: SGA 7 IX 3.5's unipotence (`ReductSplit.SemistableUnipotent`,
which the field `sga7_IX_3_5_ForwardGeom` gives through `UnipotentForward.semistableUnipotent_of_forwardGeom`) and
the glue `WildPeriodCoprime` give `ElliotWildInertiaTrivial`. The converse fails (the ELLIOT sentence says nothing
about tame inertia), so the manuscript's route does not give `SemistableUnipotent`. -/
theorem elliot_of_semistableUnipotent (hU : SemistableUnipotent) (hP : WildPeriodCoprime) :
    ElliotWildInertiaTrivial := by
  intro K _ O _ Ω _ _ _ w hw A hA ℓ _ hℓO σ hσ hwild t
  apply Subtype.ext
  funext n
  set x : A.Pt Ω := Additive.toMul (t.1 n) with hxdef
  have ht : t.1 n = Additive.ofMul x := rfl
  have hx : x ^ (ℓ ^ n) = 1 := by
    have := pow_smul_tate t n
    rw [ht] at this
    exact this
  have hu := unipSq_of_tate A ℓ σ t n x ht (hU K O Ω w hw A hA ℓ hℓO σ hσ t)
  obtain ⟨N, hcop, hit⟩ := hP K O Ω w hw A ℓ hℓO σ hσ hwild n x hx
  have hfix : A.galAct σ x = x :=
    PkgI2.fixed_of_unipSq_of_iterate (ObjBridge.toGrp A) σ x ℓ n N 1 (by rwa [pow_one]) hx hu
      (by rwa [pow_one])
  show Additive.ofMul (A.galAct σ (Additive.toMul (t.1 n))) = t.1 n
  rw [← hxdef, hfix]
  rfl

/-! ## §6. Reading-robust pair: semistability as "no `𝔾_a`" (GaRigidity) -/

/-- **LEAF variant `SilverbergZarhinThm35Def34`** (same source and provenance as `SilverbergZarhinThm35`, wording
UNVERIFIED): the conclusion also admits the reading "the identity component of the geometric special fibre of the
Néron model contains no `𝔾_a`" (`GaRigidity.SGA7.IsSemistableDef34`), should Silverberg–Zarhin define semistable
reduction by the absence of a unipotent part. Implied by `SilverbergZarhinThm35` (`sz35Def34_of_sz35`). -/
def SilverbergZarhinThm35Def34 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    (∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → DictModels.RaynaudOr.IsSemistableResT 𝒩) ∨
      SemistableNeronModels A O ∨
      (∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → GaRigidity.SGA7.IsSemistableDef34 𝒩)

theorem sz35Def34_of_sz35 (h : SilverbergZarhinThm35) : SilverbergZarhinThm35Def34 :=
  fun K _ O _ A m hm hu ht => (h K O A m hm hu ht).imp_right Or.inl

/-- **LEAF variant `ElliotWildInertiaTrivialDef34`** (ELLIOT, diophantine_zq.tex:817-818, as
`ElliotWildInertiaTrivial`) with semistable reduction read as "no `𝔾_a` in the identity component of the geometric
special fibre" (`GaRigidity.SGA7.HasSemistableReductionDef34`). Implies `ElliotWildInertiaTrivial` by rigidity for
`𝔾_a` (`elliot_of_def34`). -/
def ElliotWildInertiaTrivialDef34 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, GaRigidity.SGA7.HasSemistableReductionDef34 A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsWildInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ t = t

theorem elliot_of_def34 (h : ElliotWildInertiaTrivialDef34) : ElliotWildInertiaTrivial :=
  fun K _ O _ Ω _ _ _ w hw A hA ℓ _ hℓO σ hσ hwild t =>
    h K O Ω w hw A (GaRigidity.SGA7.hasSemistableReductionDef34_of_has hA) ℓ hℓO σ hσ hwild t

/-- **L814-818 from the "no `𝔾_a`" pair**: under that reading both leaves are literal, and the composite is proved
with rigidity for `𝔾_a` (`GaRigidity.SGA7.isSemistableDef34_of_isSemistable`) on the extension disjuncts. -/
theorem raynaudWildNF_of_def34 (hSZ : SilverbergZarhinThm35Def34) (hE : ElliotWildInertiaTrivialDef34)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) : RaynaudWildNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ hwild ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hF := ReductGlue.fixedTorsionRational_of_mulEtale
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
  have hT := AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have h34 : ∀ 𝒩 : GroupModelO B O, 𝒩.IsNeronModel → GaRigidity.SGA7.IsSemistableDef34 𝒩 := by
    rcases hSZ K O B m hm hmO
      (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx)) with h1 | h2 | h3
    · exact fun 𝒩 h𝒩 => GaRigidity.SGA7.isSemistableDef34_of_isSemistable 𝒩
        (DictModels.RaynaudOr.isSemistable_of_resT geomConnOfRationalPoint_proof 𝒩 (h1 𝒩 h𝒩))
    · exact fun 𝒩 h𝒩 => GaRigidity.SGA7.isSemistableDef34_of_isSemistable 𝒩 (h2 𝒩 h𝒩)
    · exact h3
  obtain ⟨𝒩, h𝒩⟩ := GapNeron.exists_neron_groupModelNF hN O B
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact fix_of_tate B ℓ σ t n x ht
    (hE K O (AlgebraicClosure K) w hw B ⟨𝒩, h𝒩, h34 𝒩 h𝒩⟩ ℓ hℓO σ hσ hwild t)

end SZRaynaud
