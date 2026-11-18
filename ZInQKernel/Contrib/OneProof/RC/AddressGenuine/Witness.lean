import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Assembly

/-!
# Lane RC24: the odd witness from a bounded-weight sequence of visible indices

Manuscript `diophantine_zq.tex`: Proposition `ex:app-odd-minimum` (tex 10152–10199, in particular
10190–10199: "Consider the integers `r` for which a bounded-weight sequence of visible `D_M` has
`v₂ a_M(D_M) − ω(D_M) = r` on a set in the ultrafilter. … Let its attained minimum be `δ_o`"; §7,
tex 2537–2542), the final companion (tex 2588–2593), Proposition `ex:app-nonempty-seeds`
(tex 10501–10505) and Proposition `ex:app-odd-stabilization` (tex 10508–10552, in particular
10527–10547: "Thus the elementary label groups, their projections and their finite addition
tables have bounded size. … There are finitely many such tables; select the one occurring on a set
in the same ultrafilter. … The bounded-weight witness remains a witness in these tables").

The manuscript supplies the odd witness as a bounded-weight SEQUENCE of visible indices: at the
stages of a set of the ultrafilter, a nonempty set `U θ` of at most `Wb` good primes whose index
`D_θ = ∏_{q ∈ U θ} q` reads one in the intrinsic odd reading `Rodd` (`OddWitnessSeq`, ELLIOT). The
set of primes may move with the stage; only the stabilized finite tables fix a typed graph.
Lane RC24's assembly (`addressPackageStaged_of_genuine`) consumes the fixed-graph form
`OddWitness`. This file PROVES that the sequence form gives it (`oddWitness_of_seq`):

* the normalized typed graph of `U θ` at stage `θ` (`stageNorm`: vertices `0, …, |U θ| − 1` in
  increasing order of the primes, the stage types and the residue bits of the enumerated primes,
  as lane RC2's normalized data of the cutoff `Wb`) ranges over a finite type, so by lane RC2's
  `label_type_stabilizes` it is one fixed datum on a set of the ultrafilter; let `Γ` be its graph;
* at a stage of that set, the primes of `U θ` realize `Γ` (`exists_isReal_of_iso` along lane RC2's
  `normalize_iso`), with the set of primes `U θ` itself;
* at a stage which also carries App F's fixed-`U` factorization within the budget `Wb + 1`
  (`OddReadings` at the cutoff `Wb`), the stage symbol of `Γ` is the reading of any realization
  (`stageSymbol_eq_reading`), hence `Rodd W D θ (U θ) = 1`; `Γ` is compatible
  (`compatible_of_real`) and nonempty.

Conversely the fixed-graph form gives the sequence form (`oddWitnessSeq_of_oddWitness`), so under
`OddReadings` the two are equivalent (`oddWitness_iff_seq`), and the assembly holds with the
sequence form (`addressPackageStaged_of_genuine_seq`).

The sequence itself is derived from batch 3's attained odd minimum (`δ_o ∈ DepthSet`) when the
empty configuration is not a unit, following the stabilization argument (tex 10527–10547)
(`oddWitnessSeq_of_depthMin`, `oddWitness_of_depthMin`; tex 2590–2593: "The bounded-weight witness
then supplies a least nonempty odd seed"): the witness index `D_θ ≠ 1`, positive, squarefree and
prime to `m₁ ℓ₀`, is the product of its prime set.

All statements are PROVED; the only new input is `OddWitnessSeq` (ELLIOT), itself PROVED from the
attained minimum in `oddWitnessSeq_of_depthMin`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter Finset

/-! ## The input: the witness sequence -/

/-- **The bounded-weight witness sequence of visible indices** (ELLIOT; Proposition
`ex:app-odd-minimum`, tex 10190–10199: "Consider the integers `r` for which a bounded-weight
sequence of visible `D_M` has `v₂ a_M(D_M) − ω(D_M) = r` on a set in the ultrafilter. The fixed
witness `D_w` and (O.2),(O.7) make this set nonempty. … Let its attained minimum be `δ_o`"; the
final companion, tex 2588–2593: "assume that the empty configuration is not a unit. The
bounded-weight witness then supplies a least nonempty odd seed"; tex 10501–10505): a weight bound
`Wb` and, at the stages of a set of the ultrafilter, a nonempty set `U θ` of at most `Wb` good
primes of the stage types whose index `D_θ = ∏_{q ∈ U θ} q` reads one in the intrinsic odd reading
(`Rodd`: `D_θ` in the intrinsic odd filter and `v₂ a_{M_θ}(D_θ) = δ_o + |U θ|`, the attained
minimum). The set `U θ` may change with the stage; no typed graph is fixed.
DEPARTURE (weaker than the text): the visibility `v₂ a_{M_θ}(D_θ) < M_θ` of the text's sequence
(tex 2083) is not recorded, being unused. Nonemptiness is the case where the empty configuration is
not a unit (tex 2588–2593): otherwise `D_θ = 1` on a set of the ultrafilter. -/
def OddWitnessSeq {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) : Prop :=
  ∃ (Wb : ℕ) (U : ℕ → Finset ℕ), ∀ᶠ θ in (W.stages : Filter ℕ),
    (U θ).Nonempty ∧ (U θ).card ≤ Wb ∧ (∀ q ∈ U θ, (D.T₁ θ).Good q) ∧ Rodd W D θ (U θ) = 1

/-! ## Realizations and normalized typed graphs -/

section Realizations

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **A realization is carried along an isomorphism of typed graphs, by the same primes**
(PROVED; Definition `ex:sec7-typed-graph`, tex 2031–2034, and rule 1 of Lemma
`ex:sec7-coefficient-rules`, tex 2108–2116: a realization depends only on the typed graph; the
argument of batch 3's `symb_graph_dependence`): if `f` realizes `Γ` and `e : Γ ≅ Δ`, then
`f ∘ e⁻¹` realizes `Δ`, with the same set of primes. -/
theorem exists_isReal_of_iso {T : TypeData L ε} {Γ Δ : Config L} (hiso : Γ.IsIso Δ) {f : ℕ → ℕ}
    (hf : IsReal T Γ f) : ∃ g : ℕ → ℕ, IsReal T Δ g ∧ Δ.V.image g = Γ.V.image f := by
  classical
  obtain ⟨e, het, hez⟩ := hiso
  let g : ℕ → ℕ := fun u => if h : u ∈ Δ.V then f (e.symm ⟨u, h⟩) else 0
  have hgv : ∀ (u : ℕ) (h : u ∈ Δ.V), g u = f (e.symm ⟨u, h⟩) := fun u h => dite_eq_left h
  refine ⟨g, ⟨fun a ha b hb hab => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩, ?_⟩
  · rw [hgv a ha, hgv b hb] at hab
    have h1 := hf.1 (e.symm ⟨a, ha⟩).2 (e.symm ⟨b, hb⟩).2 hab
    have h2 : (⟨a, ha⟩ : Δ.V) = ⟨b, hb⟩ := e.symm.injective (Subtype.ext h1)
    exact congrArg Subtype.val h2
  · rw [hgv a ha]
    have h1 := hf.2.1 _ (e.symm ⟨a, ha⟩).2
    have h2 := het (e.symm ⟨a, ha⟩)
    rw [e.apply_symm_apply] at h2
    exact ⟨h1.1, h1.2.trans h2.symm⟩
  · rw [hgv a ha, hgv b hb]
    have hne : e.symm ⟨a, ha⟩ ≠ e.symm ⟨b, hb⟩ := fun h =>
      hab (congrArg Subtype.val (e.symm.injective h))
    have hne' : (e.symm ⟨a, ha⟩ : ℕ) ≠ e.symm ⟨b, hb⟩ := fun h => hne (Subtype.ext h)
    have h2 := hez (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) hne
    rw [e.apply_symm_apply, e.apply_symm_apply] at h2
    rw [hf.2.2 _ (e.symm ⟨a, ha⟩).2 _ (e.symm ⟨b, hb⟩).2 hne', h2]
  · ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (e.symm ⟨u, hu⟩).2, (hgv u hu).symm⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨e ⟨u, hu⟩, (e ⟨u, hu⟩).2, ?_⟩
      rw [hgv _ (e ⟨u, hu⟩).2]
      simp

/-- **A set of good primes realizes its own typed graph** (PROVED; tex 2031–2034): the typed
graph `primeConfig U T.typ` of a set `U` of good primes (the types `T.typ`, the residue bits
`legBit`) is realized by the identity. -/
theorem isReal_primeConfig (T : TypeData L ε) {U : Finset ℕ} (hU : ∀ q ∈ U, T.Good q) :
    IsReal T (primeConfig U T.typ) id :=
  ⟨Set.injOn_id _, fun v hv => ⟨hU v hv, rfl⟩, fun _ _ _ _ _ => rfl⟩

end Realizations

/-- **The normalized typed graph of a set of primes at a stage** (definition; Definition
`ex:sec7-typed-graph`, tex 2015–2034; Proposition `ex:app-odd-stabilization`, tex 10527–10540):
the typed graph of `U` at stage `θ` (`primeConfig U (D.T₁ θ).typ`: the stage types of the primes
and their residue bits), renamed in increasing order to the vertices `0, …, |U| − 1`, as lane
RC2's normalized data of the cutoff `Wb` (`normalize`); the zero datum when `|U| > Wb + 1`. The
data range over the finite type `NormData D.L₁ Wb`. -/
def stageNorm {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) (Wb θ : ℕ) (U : Finset ℕ) :
    NormData D.L₁ Wb :=
  if hc : (primeConfig U (D.T₁ θ).typ).V.card ≤ Wb + 1 then
    Symbols.normalize (primeConfig U (D.T₁ θ).typ) hc
  else (0, fun _ => 0, fun _ _ => 0)

/-- **The typed graph of `U` is isomorphic to the graph of its normalized datum** (PROVED; lane
RC2's `normalize_iso`, tex 10513–10514, 10538–10540). -/
theorem primeConfig_iso_stageNorm {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) {Wb θ : ℕ}
    {U : Finset ℕ} (hc : U.card ≤ Wb + 1) :
    (primeConfig U (D.T₁ θ).typ).IsIso (normConfig (stageNorm D Wb θ U)) := by
  have hc' : (primeConfig U (D.T₁ θ).typ).V.card ≤ Wb + 1 := hc
  unfold stageNorm
  rw [dite_eq_left hc']
  exact normalize_iso _ hc'

/-! ## The stabilization of the witness -/

/-- **The bounded-weight witness sequence gives a fixed-graph witness** (PROVED; the stabilization
of the typed graph on the ultrafilter, Proposition `ex:app-odd-stabilization`, tex 10508–10552, in
particular 10527–10547: "Thus the elementary label groups, their projections and their finite
addition tables have bounded size. … There are finitely many such tables; select the one occurring
on a set in the same ultrafilter. … The bounded-weight witness remains a witness in these tables").
The normalized typed graph of `U θ` takes values in a finite type (at most `Wb + 1` vertices, the
finite alphabet `D.L₁`), so it is one fixed graph `Γ` on a set of the ultrafilter (lane RC2's
`label_type_stabilizes`). At a stage of that set where the witness holds and App F's fixed-`U`
factorization holds within the budget `Wb + 1` (`OddReadings` at the cutoff `Wb`), the primes of
`U θ` realize `Γ` with image `U θ`, so the stage symbol of `Γ` is `Rodd W D θ (U θ) = 1`
(`stageSymbol_eq_reading`); `Γ` is compatible, being realized, and nonempty. -/
theorem oddWitness_of_seq {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) (hodd : OddReadings W D)
    (h : OddWitnessSeq W D) : OddWitness W D := by
  obtain ⟨Wb, U, hU⟩ := h
  -- the normalized typed graphs take finitely many values: one occurs on a set of the ultrafilter
  obtain ⟨d₀, hd₀⟩ := label_type_stabilizes W.stages (fun θ => stageNorm D Wb θ (U θ))
  -- at such a stage the witness primes realize the fixed graph, with the witness set as image
  have hreal : ∀ θ, (∀ q ∈ U θ, (D.T₁ θ).Good q) → (U θ).card ≤ Wb →
      stageNorm D Wb θ (U θ) = d₀ →
      ∃ g : ℕ → ℕ, IsReal (D.T₁ θ) (normConfig d₀) g ∧ (normConfig d₀).V.image g = U θ := by
    intro θ hgood hcard hθ
    have hiso := primeConfig_iso_stageNorm D (θ := θ) (Nat.le_succ_of_le hcard)
    rw [hθ] at hiso
    obtain ⟨g, hg, himg⟩ := exists_isReal_of_iso hiso (isReal_primeConfig (D.T₁ θ) hgood)
    exact ⟨g, hg, himg.trans Finset.image_id⟩
  obtain ⟨θ₀, ⟨hne₀, hcard₀, hgood₀, -⟩, hθ₀⟩ := (hU.and hd₀).exists
  obtain ⟨g₀, hg₀, himg₀⟩ := hreal θ₀ hgood₀ hcard₀ hθ₀
  refine ⟨normConfig d₀, compatible_of_real _ hg₀, ?_, ?_⟩
  · rw [← himg₀] at hne₀
    exact hne₀.of_image
  · filter_upwards [hU, hd₀, hodd Wb] with θ hθU hθ hR
    obtain ⟨-, hcard, hgood, h1⟩ := hθU
    obtain ⟨g, hg, himg⟩ := hreal θ hgood hcard hθ
    have hB : (normConfig d₀).V.card ≤ Wb + 1 := by
      have hc := Finset.card_image_of_injOn hg.1
      rw [himg] at hc
      omega
    rw [stageSymbol_eq_reading (D.T₁ θ) (Rodd W D θ) hR.1 (compatible_of_real _ hg) hB hg, himg]
    exact h1

/-- **Conversely, a fixed-graph witness gives a witness sequence** (PROVED; Definition
`ex:sec7-symbol`, tex 2068–2079, App F tex 9670–9704): at a stage where the stage symbol of the
nonempty graph `Γ` is one, a prime realization of `Γ` exists and reads one; its primes form a
nonempty set of at most `|V(Γ)|` good primes with `Rodd = 1`. -/
theorem oddWitnessSeq_of_oddWitness {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    (h : OddWitness W D) : OddWitnessSeq W D := by
  classical
  obtain ⟨Γ, -, hne, hev⟩ := h
  have hU : ∀ θ, ∃ U : Finset ℕ, stageSymbol (D.T₁ θ) (Rodd W D θ) Γ = 1 →
      U.Nonempty ∧ U.card ≤ Γ.V.card ∧ (∀ q ∈ U, (D.T₁ θ).Good q) ∧ Rodd W D θ U = 1 := by
    intro θ
    by_cases h1 : stageSymbol (D.T₁ θ) (Rodd W D θ) Γ = 1
    · obtain ⟨f, hf⟩ := stageSymbol_realized h1
      refine ⟨Γ.V.image f, fun _ => ⟨hne.image f, Finset.card_image_le, fun q hq => ?_,
        stageSymbol_reads h1 hf⟩⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      exact (hf.2.1 v hv).1
    · exact ⟨∅, fun h => absurd h h1⟩
  choose U hU using hU
  exact ⟨Γ.V.card, U, hev.mono fun θ hθ => hU θ hθ⟩

/-- **Under App F's readings the two witness forms are equivalent** (PROVED;
`oddWitness_of_seq`, `oddWitnessSeq_of_oddWitness`; tex 10190–10199, 10508–10552). -/
theorem oddWitness_iff_seq {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) (hodd : OddReadings W D) :
    OddWitness W D ↔ OddWitnessSeq W D :=
  ⟨oddWitnessSeq_of_oddWitness D, oddWitness_of_seq D hodd⟩

/-! ## The witness from the attained odd minimum -/

/-- **The attained odd minimum supplies a nonempty witness sequence** (PROVED; the final
companion, tex 2590–2593: "assume that the empty configuration is not a unit. The bounded-weight
witness then supplies a least nonempty odd seed"; Proposition `ex:app-odd-minimum`, tex
10190–10199; tex 10501–10505). The proof supplies the bounded-weight witness of the
stabilization argument (tex 10527–10547). The minimum
`δ_o ∈ DepthSet` (batch 3's set of the integers `r` attained by a bounded-weight sequence of
visible admissible `D_θ` with `v₂ a_{M_θ}(D_θ) − ω(D_θ) = r` on a set of the ultrafilter) gives a
weight bound `Wb` and such a sequence for `r = δ_o`. Since the empty configuration is not a unit
(`¬ OddEmptyUnit`), `D_θ ≠ 1` on a set of the ultrafilter. Admissible indices are positive and
squarefree (`hsf`) and prime to `m₁ ℓ₀` (`hcop`), so `D_θ = ∏ q` over its prime set
`U θ = primeFactors |D_θ|`, a nonempty set of at most `Wb` good primes of the stage types with
`|U θ| = ω(D_θ)`; the stage support lies in the intrinsic odd filter (`hsub`: the later
exclusions only remove primes, tex 2027–2029, 9481–9483), so `Rodd W D θ (U θ) = 1`. -/
theorem oddWitnessSeq_of_depthMin {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    (hδ : W.δo ∈ AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd))
      W.admissible)
    (hU : ¬ W.OddEmptyUnit)
    (hsf : ∀ θ D', W.admissible θ D' → 0 < D' ∧ Squarefree D')
    (hcop : ∀ θ D', W.admissible θ D' → Nat.Coprime D'.natAbs (D.m₁ * D.ℓ₀ θ))
    (hsub : ∀ θ D', W.admissible θ D' → D.oddAdmissible θ D') : OddWitnessSeq W D := by
  obtain ⟨Wb, Ds, hDs⟩ := hδ
  -- the empty configuration is not a unit: the witness index is not `1`
  have hne1 : ∀ᶠ θ in (W.stages : Filter ℕ), Ds θ ≠ 1 := by
    have h1 : ∀ᶠ θ in (W.stages : Filter ℕ), ¬ vZ (W.aθ θ 1) = W.δo :=
      Ultrafilter.eventually_not.mpr hU
    filter_upwards [h1, hDs] with θ hθ1 hθ2 heq
    apply hθ1
    have h := hθ2.2.2.2
    rw [heq] at h
    have h0 : AppGEndpoints.omega 1 = 0 := by
      simp [AppGEndpoints.omega]
    rw [h0] at h
    simpa using h
  -- the prime set of the witness index
  refine ⟨Wb, fun θ => (Ds θ).natAbs.primeFactors, ?_⟩
  filter_upwards [hDs, hne1] with θ hθ hθ1
  obtain ⟨hadm, hω, -, hval⟩ := hθ
  obtain ⟨hpos, hsq⟩ := hsf θ _ hadm
  have hcard : ((Ds θ).natAbs.primeFactors).card = AppGEndpoints.omega (Ds θ) := rfl
  have hprod : (∏ q ∈ (Ds θ).natAbs.primeFactors, (q : ℤ)) = Ds θ := by
    have hsqn : Squarefree (Ds θ).natAbs := Int.squarefree_natAbs.mpr hsq
    have h1 : (∏ q ∈ (Ds θ).natAbs.primeFactors, q) = (Ds θ).natAbs :=
      Nat.prod_primeFactors_of_squarefree hsqn
    have h2 : (∏ q ∈ (Ds θ).natAbs.primeFactors, (q : ℤ)) =
        ((∏ q ∈ (Ds θ).natAbs.primeFactors, q : ℕ) : ℤ) := by push_cast; rfl
    rw [h2, h1]
    exact Int.natAbs_of_nonneg hpos.le
  refine ⟨?_, hcard ▸ hω, fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, ?_⟩, ?_⟩
  · have hgt : 1 < (Ds θ).natAbs := by omega
    exact Nat.nonempty_primeFactors.mpr hgt
  · rw [D.T₁_m]
    exact Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq) (hcop θ _ hadm)
  · unfold Rodd
    refine ite_eq_left ⟨by rw [hprod]; exact hsub θ _ hadm, ?_⟩
    rw [hprod, hcard]
    exact hval

/-- **The attained odd minimum gives the fixed-graph witness** (PROVED; tex 2590–2593: "The
bounded-weight witness then supplies a least nonempty odd seed"; tex 10190–10199, 10501–10505,
10541–10547: "The bounded-weight witness remains a witness in these tables"). The proof follows
the stabilization argument (tex 10527–10547): the nonempty witness sequence of the attained minimum
(`oddWitnessSeq_of_depthMin`), stabilized to one typed graph on the ultrafilter
(`oddWitness_of_seq`). Hypotheses: `δ_o` attained (`δ_o ∈ DepthSet`), the empty configuration not
a unit, App F's odd readings, admissible indices positive, squarefree and prime to `m₁ ℓ₀`, and
the stage support inside the intrinsic odd filter. -/
theorem oddWitness_of_depthMin {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    (hδ : W.δo ∈ AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd))
      W.admissible)
    (hU : ¬ W.OddEmptyUnit) (hodd : OddReadings W D)
    (hsf : ∀ θ D', W.admissible θ D' → 0 < D' ∧ Squarefree D')
    (hcop : ∀ θ D', W.admissible θ D' → Nat.Coprime D'.natAbs (D.m₁ * D.ℓ₀ θ))
    (hsub : ∀ θ D', W.admissible θ D' → D.oddAdmissible θ D') : OddWitness W D :=
  oddWitness_of_seq D hodd (oddWitnessSeq_of_depthMin D hδ hU hsf hcop hsub)

/-- **Lane RC0's `AddressPackageStaged` over the genuine objects, with the witness in the text's
sequence form** (PROVED from the inputs; tex 2015–2174, 2595–2672, App F 9447–9976, App G
10190–10199, 10258–10861): `addressPackageStaged_of_genuine` with `OddWitness` supplied by
`oddWitness_of_seq`. -/
theorem addressPackageStaged_of_genuine_seq {ℓ : ℕ} (W : WData ℓ) (D : LabelData W)
    (Rev : Finset ℕ → ZMod 2) (hℓ : Adm ℓ) (hk : Odd W.kfin) (hksf : Squarefree W.kfin)
    (hfresh : FreshPrime W D) (hodd : OddReadings W D) (hwit : OddWitnessSeq W D)
    (hofilt : OddFilter W D) (hprep : PreparedFilter W D) (hev : EvenReadings W D Rev)
    (hefilt : EvenFilter W D Rev) (hseed : KSplitSeed W D Rev) (hread : EvenReading W D Rev)
    (Ccoarse : ℚ) : AddressPackageStaged W Ccoarse :=
  addressPackageStaged_of_genuine W D Rev hℓ hk hksf hfresh hodd (oddWitness_of_seq D hodd hwit)
    hofilt hprep hev hefilt hseed hread Ccoarse

end ZInQ.Manuscript.RC.AddressGenuine
