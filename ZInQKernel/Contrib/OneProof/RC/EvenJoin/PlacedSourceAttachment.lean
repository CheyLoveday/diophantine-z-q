import ZInQKernel.Contrib.OneProof.CarayolRefold
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.AttachmentCoefficients
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedInventory
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Galois
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PrimeComparison

/-! Transport both good Frobenius values and unramifiedness from Carayol's
source completion to the chosen receiving completion (tex 9762–9797). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine BlocksPerU HeckeRing.GL2 IsDedekindDomain NumberField
open PrintsArith ThetaCoeff
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1500000

section Source

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}

private abbrev NormalizedCuspSource.printField (s : NormalizedCuspSource) :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  DSCoeffExt.coeffField (s.newform.toCuspForm : PkgI4.CF s.level 2)

/-- Restrict the receiving prime to the actual coefficient field of one
source, and extend its attached representation along the completed
inclusion. Arithmetic Frobenius is the same element before and after
changing coefficient fields. -/
def NormalizedCuspSource.attachmentOfCarayol (s : NormalizedCuspSource)
    {E : IntermediateField ℚ ℂ} [NumberField E] (hs : s.field ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (2 : 𝓞 E) ∈ w.asIdeal)
    (hCarayol : CarayolRefold.CarayolThmAFrob)
    (κ : FixedField w →+* ℂ)
    (hκ : ∀ x : E, κ (algebraMap E (FixedField w) x) = (x : ℂ))
    (ha : ∀ n, ∃ x : FixedField w, κ x = s.coeff n)
    (hχ : ∀ u, ∃ x : FixedField w, κ x = (s.char u : ℂ)) :
    SourceAttachment (T := T) s.level (chooseFrob frobeniusExists) (s.eigen κ ha hχ) := by
  letI : NeZero s.level := ⟨s.level_ne⟩
  let K := s.printField
  have hKE : K ≤ E := s.attachment_field.trans_le hs
  let j := IntermediateField.inclusion hKE
  letI : NumberField K := {
    to_finiteDimensional := FiniteDimensional.of_injective j.toLinearMap j.injective }
  letI : Algebra K E := j.toAlgebra
  let Q := w.asIdeal.under (𝓞 K)
  have hQ : (2 : 𝓞 K) ∈ Q := by
    change algebraMap (𝓞 K) (𝓞 E) 2 ∈ w.asIdeal
    rwa [map_ofNat]
  have hQ0 : Q ≠ ⊥ := fun h => two_ne_zero (Ideal.mem_bot.mp (h ▸ hQ))
  let v : HeightOneSpectrum (𝓞 K) := ⟨Q, inferInstance, hQ0⟩
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let data := hCarayol s.level s.newform 2 v (by exact_mod_cast hQ)
  let ρ := data.choose
  obtain ⟨hc, -, hgood, -⟩ := data.choose_spec
  let e : v.adicCompletion K →+* w.adicCompletion E := v.adicCompletionExtension K E w
  let ρE : GalQ →* GL (Fin 2) (FixedField w) := (Matrix.GeneralLinearGroup.map e).comp ρ
  have he (x : K) : κ (e (algebraMap K (v.adicCompletion K) x)) = (x : ℂ) := by
    change κ (v.adicCompletionExtension K E w (x : v.adicCompletion K)) = _
    rw [v.adicCompletionExtension_coe K E w x]
    exact hκ (j x)
  have hmat (g : GalQ) :
      (ρE g : Matrix (Fin 2) (Fin 2) (FixedField w)) =
        (ρ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map e := rfl
  refine SourceAttachment.ofCusp _ _ _ _ ρE ?_ ?_
  · simp only [hmat]
    exact (Units.continuous_val.comp hc).matrix_map
      (v.continuous_adicCompletionExtension K E w)
  · intro q hq
    have hqn : ¬ q ∣ s.level * 2 := fun hd => (hq.1.1.dvd_mul.mp hd).elim
      (Nat.Prime.coprime_iff_not_dvd hq.1.1 |>.mp hq.2)
      (fun h => hq.1.ne_two ((Nat.prime_dvd_prime_iff_eq hq.1.1 Nat.prime_two).mp h))
    obtain ⟨hI, hF⟩ := hgood q hq.1.1 hqn
    refine ⟨?_, ?_⟩
    · intro Q hQ hqQ g hg
      let := hQ.isPrime
      have hqQ' : (q : Zbar) ∈ Q := by exact_mod_cast hqQ
      obtain ⟨z, hz, rfl⟩ := PrimeComparison.inertia Q hq.1.1 hqQ' hg
      have h1 := hI _ (PrimeComparison.liesOver Q hq.1.1 hqQ') z hz
      change Matrix.GeneralLinearGroup.map e (ρ (z : GalQ)) = 1
      rw [h1, map_one]
    · obtain ⟨Q, hQ, hqQ, hf⟩ := chooseFrob_spec frobeniusExists hq.1.1
      let := hQ.isPrime
      have hqQ' : (q : Zbar) ∈ Q := by exact_mod_cast hqQ
      obtain ⟨htr, hdet⟩ := hF _ _ (PrimeComparison.liesOver Q hq.1.1 hqQ')
        (PrimeComparison.arithFrob Q hq.1.1 hqQ' hQ hf)
      let u := ZMod.unitOfCoprime q hq.2
      have hchar : (s.char u : ℂ) ∈ K := by
        change (s.char u : ℂ) ∈ IntermediateField.adjoin ℚ (Set.range s.coeff)
        rw [s.attachment_field]
        exact s.char_mem_field u
      let b : K := (q : K) * ⟨(s.char u : ℂ), hchar⟩
      have hb : (b : ℂ) = (q : ℂ) * ((s.newform.χ u : ℂˣ) : ℂ) := by
        change (q : ℂ) * (s.char u : ℂ) = _
        rfl
      have hd := hdet u b rfl hb
      change GoodValues ρE _ (s.eigen (T := T) κ ha hχ).a (s.eigen (T := T) κ ha hχ).χ q
      constructor
      · rw [hmat, ← AddMonoidHom.map_trace e, htr]
        apply κ.injective
        rw [he, s.eigen_a]
        rfl
      · rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det e, hd]
        apply κ.injective
        rw [he, map_mul, map_natCast, s.eigen_char κ ha hχ hq.2, charAt_apply]
        exact hb

end Source

section Inventory

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε}
variable {D : Type} [Fintype D] {N : ℕ} [NeZero N]
variable {m : D → ℕ} {a : D → ℕ → ℂ}
variable {A : ∀ b, CuspBlockExpansion (m b) (a b)} {hm : ∀ b, m b ∣ N}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable (P : PlacedCuspLists A hm v)

omit [NeZero N] [NumberField F] in
/-- The selected receiving place is above two when the fixed place is. -/
theorem PlacedCuspLists.two_mem_receiving (h2 : (2 : 𝓞 F) ∈ v.asIdeal) :
    (2 : 𝓞 P.E) ∈ P.w.asIdeal := by
  let : Algebra F P.E := (IntermediateField.inclusion P.includes).toAlgebra
  have h : P.w.asIdeal.under (𝓞 F) = v.asIdeal := P.liesOver.over.symm
  rw [← h] at h2
  change algebraMap (𝓞 F) (𝓞 P.E) 2 ∈ P.w.asIdeal at h2
  simpa only [map_ofNat] using h2

/-- Attach one representation per distinct source. All its old degrees
refer to that same representation via the inventory's source index. -/
def PlacedCuspLists.attachmentsOfCarayol (hLi : OldNewIndependenceWeightTwo)
    (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (hCarayol : CarayolRefold.CarayolThmAFrob) :
    ∀ s, SourceAttachment ((P.inventory T hLi).sourceLevel s) (chooseFrob frobeniusExists)
      ((P.inventory T hLi).source s) := by
  intro s
  have hs : s.val.field ≤ P.E := by
    obtain ⟨x, hx⟩ := cuspSource_exists _ s
    rw [← hx]
    exact P.source_mem x
  exact s.val.attachmentOfCarayol hs P.w (P.two_mem_receiving h2) hCarayol P.κ
    (constituentComplexEmbedding_constituent P.w) _ _

end Inventory

end ZInQ.Manuscript.RC.EvenJoin
