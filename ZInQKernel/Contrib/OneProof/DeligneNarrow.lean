import ZInQKernel.Contrib.OneProof.Y3HodgePrint
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used

/-! The three readers of the Deligne input share the same fine witness and point map. This file
keeps exactly the kinds of point-map data needed by the live route and proves its three outputs
directly, without rebuilding the intermediate full canonical-model packages. -/

namespace Y3Hodge

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open NumberField IsDedekindDomain ShimuraCFT RayClassCFT ShimuraGlue.Ray
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

abbrev UpperPointMap (Y : Over (Spec (CommRingCat.of ℚ))) :=
  UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)

/-- The three CM fields whose ray class fields the proof uses. -/
def RayCase (k : Type) : Prop := k = K4 ∨ k = K3 ∨ k = K24

/-- Only these double coset equalities are used: starting at (i), moving to a unit
representative, or moving at the same upper half-plane point from a unit representative. -/
def FibresUsed {Y : Over (Spec (CommRingCat.of ℚ))} (Ψ : UpperPointMap Y) : Prop :=
  ∀ τ g τ' g', (τ = UpperHalfPlane.I ∨ g' ∈ OhatU ∨ (τ = τ' ∧ g ∈ OhatU)) →
    DCRel τ g τ' g' → Ψ τ g = Ψ τ' g'

/-- Reciprocity for connectedness: the one point `tau0` and the one finite idele `s4` (or its
inverse, depending on the Artin convention), acting on all `g`. -/
def ConnectedRecAt {Y : Over (Spec (CommRingCat.of ℚ))} (Ψ : UpperPointMap Y)
    (ε : ℤˣ) (δ : Bool) : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K4) K4), s = DCY3Used.s4 ∨ s = DCY3Used.s4⁻¹ →
    ArtinCondC (if δ then DCY3Used.kappa0 else (starRingEnd ℂ).comp DCY3Used.kappa0) σ s →
    ∀ g, galPt σ (Ψ DCY3Used.tau0 g) = Ψ DCY3Used.tau0 (qHatU DCY3Used.q4 s ^ (ε : ℤ) * g)

/-- Reciprocity for descent: the three CM cases, an integral embedding, a unit representative
and an idele trivial in the ray class quotient modulo three. -/
def RayRecAt {Y : Over (Spec (CommRingCat.of ℚ))} (Ψ : UpperPointMap Y)
    (ε : ℤˣ) (δ : Bool) : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [IsTotallyComplex k], RayCase k →
    Module.finrank ℚ k = 2 → ∀ (κ : k →+* ℂ) (q : k →ₐ[ℚ] B) (τ : UpperHalfPlane),
    (∀ x : 𝓞 k, InO (q x)) →
    IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) τ →
    ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 k) k), ArtinCondC κ σ s →
    (s : IdeleClassGroup (𝓞 k) k) ∈ raySubgroup (mod3 k) →
    ∀ u ∈ OhatU, galPt σ (Ψ τ u) = Ψ τ (qHatU q s ^ (ε : ℤ) * u)

/-- The unit moduli clause is read at `1` for the whole holomorphic family, and at other
units only for representatives of algebraic points with one of the three indicated CM types
(as witnessed by the object of the algebraic point). -/
def ModuliAtUsedUnitsHP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperPointMap Y) : Prop :=
  ∀ u ∈ OhatU, ∀ τ : UpperHalfPlane,
    (u = 1 ∨ ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
      Ψ τ u = fieldMap ιC ≫ y ∧ Φ Qbar y = M3.mk P ∧
        (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q)) →
    ∃ P : QML3 ℂ, Φ ℂ (Ψ τ u) = M3.mk P ∧ IsHodgeH1Print P τ

/-- The clauses on a single point map after restriction to the live readers. -/
def BodyNarrow (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperPointMap Y) : Prop :=
  (∀ y : fieldPt ℂ ⟶ Y, ∃ τ g, Ψ τ g = y) ∧
  FibresUsed Ψ ∧
  (∀ g, ∀ U : Y.left.Opens, IsOpen {τ | ShimuraSplit.ptC (Ψ τ g).left ∈ U}) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ τ 1).left) ∧
  ModuliAtUsedUnitsHP Y Φ Ψ ∧
  ∃ (ε : ℤˣ) (δ : Bool), ConnectedRecAt Ψ ε δ ∧ RayRecAt Ψ ε δ

/-- **Consequence, pending review:** the read part of Shimura's Main Theorem I in Deligne's form
for `Y₃ = Sh_{K₃}(B^×, ℍ^±)`, `B = (2, −3 | ℚ)`, over each printed fine witness.

Locators UNVERIFIED: Shimura, *Construction of class fields and zeta functions of algebraic
curves*, Ann. of Math. 85 (1967), Main Theorem I; Deligne, *Travaux de Shimura*, Sém. Bourbaki
389 (1971), §4 (double cosets, moduli lattice `B ∩ 𝒪̂ g⁻¹`), §5 (Cor. 5.7 / Ex. 5.8,
canonical model over `E(G,X) = ℚ` and reciprocity); Milne, *Introduction to Shimura varieties*,
§§5–8, 12–14. As in the parent statement, the moduli clause uses genuine integral `H₁`, omits
polarization and level structure, and the reciprocity conventions are existential. The polarized
PEL comparison (see the R1 row of `docs/research/locators.md`, Lemma P on genuine `H₁` and
Riemann's theorem) and the sign of `h` (see `F0_iff`) remain reading points where the Hodge clause
is retained.

No live reader reads lower-half-plane values, the equality-to-double-coset implication, or
analyticity of regular evaluations away from `g = 1`. The separate body moduli clause at
`g = 1` is unnecessary as a second hypothesis: its moduli content is the `u = 1` case of the
unit clause, and its holomorphy is the `g = 1` case of the general holomorphy clause.
Outside the displayed fibre, unit-moduli and reciprocity instances there is no live reader. -/
def DeligneCanonicalModelY3Narrow : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), Y3Fix.R1fpPropsAbP Y Φ →
    ∃ Ψ : UpperPointMap Y, BodyNarrow Y Φ Ψ

/-- Restrict the old point map to the upper half-plane and keep only the read data. -/
theorem bodyNarrow_of_PM {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (hb : DeligneBodyAtPM Y Φ Ψ)
    (hu : ModuliAtUnitsHP Y Φ Ψ) : BodyNarrow Y Φ (fun τ g => Ψ (toPM τ) g) := by
  obtain ⟨honto, hfib, hhol, -, ε, δ, hrec⟩ := hb
  refine ⟨?_, ?_, fun g => (hhol g).1, hhol 1, fun u hU τ _ => hu u hU τ, ε, δ, ?_, ?_⟩
  · intro y
    obtain ⟨z, g, rfl⟩ := honto y
    obtain ⟨τ, g', hr⟩ := exists_upper z g
    exact ⟨τ, g', ((hfib z g (toPM τ) g').2 hr).symm⟩
  · intro τ g τ' g' _ hr
    exact (hfib _ _ _ _).2 ((dcRelPM_iff τ τ' g g').2 hr)
  · intro σ s _ hs g
    exact hrec K4 finrank_K4 _ DCY3Used.q4 DCY3Used.tau0 (DCY3Used.isCM_delta δ) σ s hs g
  · intro k _ _ _ _ hk κ q τ _ hcm σ s hs _ u _
    exact hrec k hk κ q τ hcm σ s hs u

theorem narrow_of_print : DeligneCanonicalModelY3EveryPrint → DeligneCanonicalModelY3Narrow := by
  intro h Y Φ hY
  obtain ⟨Ψ, hb, hu⟩ := h Y Φ hY
  exact ⟨fun τ g => Ψ (toPM τ) g, bodyNarrow_of_PM hb hu⟩

/-- Pin the same fine witness as in the old assembly. Its complex point gives the
algebraic point required by `R1fpPropsAb`, without using any moduli clause about that point. -/
theorem witness_of_narrow (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3Narrow) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
      R1fpPropsAb Y Φ ∧ ∃ Ψ : UpperPointMap Y, BodyNarrow Y Φ Ψ := by
  obtain ⟨Y, Φ, h⟩ := h1
  obtain ⟨Ψ, hb⟩ := h2 Y Φ h
  exact ⟨Y, Φ, Y3Fix.ab_of_np (Y3Fix.np_of_P (AvSplit.torsionStructure_of_mumford hM) h)
    (Y3Fix.nonempty_qbar_of_cpt Y h.1 (Ψ UpperHalfPlane.I 1)), Ψ, hb⟩

/-- The holomorphic-family reader uses the moduli clause only at `1`, for all upper
half-plane parameters and all choices of the later map to the projective line. -/
theorem shimuraFamilyAb_of_narrow (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3Narrow) :
    HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  obtain ⟨Y, Φ, hY, Ψ, -, -, -, hhol, hmod, -⟩ := witness_of_narrow hM h1 h2
  have hm : (1 : BAQˣ) ∈ OhatU := by
    exact ⟨by simpa using OhatQ_one, by simpa using OhatQ_one⟩
  have hf : HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ (fun τ => Ψ τ 1) :=
    ⟨fun τ => by
      obtain ⟨P, hP, hH⟩ := hmod 1 hm τ (Or.inl rfl)
      exact ⟨P, hP, Y3Fix.lattice_of_hodge ((print_iff_hodge P τ).1 hH)⟩, hhol⟩
  exact ⟨Y, Φ, hY, fun π => ⟨fun τ => Ψ τ 1, HDec.HSyn.G0Split.FibreQM.isR1bFamily_of_hol hf π⟩⟩

open DCY3Used in
/-- Restriction of the proof of `DCY3Used.connected_of_body`. Only Zariski continuity,
upper half-plane surjectivity, forward fibre equality at `i` and the fixed CM action are used. -/
theorem connected_of_narrow_body {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} [LocallyOfFiniteType Y.hom]
    (hb : BodyNarrow Y Φ Ψ) : ConnectedSpace Y.left := by
  obtain ⟨hsurj, hrel, hhol, -, -, ε, δ, hrec, -⟩ := hb
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨ShimuraSplit.ptC (Ψ UpperHalfPlane.I 1).left⟩, fun U hU => ?_⟩
  have tind : ∀ (g : BAQˣ) (τ : UpperHalfPlane),
      (ShimuraSplit.ptC (Ψ τ g).left ∈ U ↔ ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U) := by
    intro g τ
    set S : Set UpperHalfPlane := {τ | ShimuraSplit.ptC (Ψ τ g).left ∈ U}
    have hSo : IsOpen S := hhol g ⟨U, hU.isOpen⟩
    have hSc : IsOpen Sᶜ := hhol g ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
    have hS : IsClopen S := ⟨isOpen_compl_iff.1 hSc, hSo⟩
    rcases isClopen_iff.1 hS with h0 | h0
    · have a : τ ∉ S := by rw [h0]; exact id
      have b : UpperHalfPlane.I ∉ S := by rw [h0]; exact id
      exact ⟨fun h => absurd h a, fun h => absurd h b⟩
    · have a : τ ∈ S := by rw [h0]; trivial
      have b : UpperHalfPlane.I ∈ S := by rw [h0]; trivial
      exact ⟨fun _ => b, fun _ => a⟩
  let P : BAQˣ → Prop := fun g => ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U
  have hD : ∀ γ : B, 0 < ShimuraGlue.nrdQ ℚ γ → ∀ g g' k : BAQˣ, k ∈ K3Q →
      (g' : BAQ) = bEmb γ * g * k → (P g ↔ P g') := by
    intro γ hγ g g' k hk hg'
    have hd : DCRel UpperHalfPlane.I g (iotaGL γ hγ.ne' • UpperHalfPlane.I) g' :=
      ⟨γ, hγ, ⟨_, iotaGL_coe _ _, rfl⟩, k, hk, hg'⟩
    have he := hrel _ _ _ _ (Or.inl rfl) hd
    show ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U ↔ _
    rw [he]
    exact tind g' _
  have hH : ∀ g, P (qHatU q4 s4 * g) ↔ P g := by
    intro g
    obtain ⟨s', hs₀, hs'⟩ : ∃ s' : IdeleGroup (𝓞 DCY3Used.K4) DCY3Used.K4, (s' = s4 ∨ s' = s4⁻¹) ∧
        qHatU q4 s' ^ (ε : ℤ) = qHatU q4 s4 := by
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact ⟨s4, Or.inl rfl, by simp⟩
      · exact ⟨s4⁻¹, Or.inr rfl, by simp⟩
    obtain ⟨σ, hσ⟩ := exists_sigma_artinCondC (if δ then kappa0 else (starRingEnd ℂ).comp kappa0) s'
    have h1 := hrec σ s' hs₀ hσ g
    rw [hs'] at h1
    have h2 : ShimuraSplit.ptC (Ψ tau0 (qHatU q4 s4 * g)).left = ShimuraSplit.ptC (Ψ tau0 g).left := by
      rw [← h1, ptC_galPt]
    show ShimuraSplit.ptC (Ψ UpperHalfPlane.I (qHatU q4 s4 * g)).left ∈ U ↔
      ShimuraSplit.ptC (Ψ UpperHalfPlane.I g).left ∈ U
    rw [← tind (qHatU q4 s4 * g) tau0, h2, tind g tau0]
  have hconst : ∀ g, P g ↔ P 1 := const_of_inv h4_mem yh_mem h4_eq hD hH
  by_contra hne
  rw [not_or] at hne
  obtain ⟨y, hy⟩ := exists_C_point Y U hU.isOpen (Set.nonempty_iff_ne_empty.2 hne.1)
  obtain ⟨y', hy'⟩ := exists_C_point Y Uᶜ hU.isClosed.isOpen_compl
    (Set.nonempty_compl.2 hne.2)
  obtain ⟨τ, g, rfl⟩ := hsurj y
  obtain ⟨τ', g', rfl⟩ := hsurj y'
  have a : P g := (tind g τ).1 hy
  have b : ¬ P g' := fun hp => hy' ((tind g' τ').2 hp)
  exact b ((hconst g').2 ((hconst g).1 a))

/-- The connected fine moduli witness from the narrowed input. -/
theorem y3ConnectedAb_of_narrow (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3Narrow) :
    DCY3Used.Y3ConnectedAb := by
  obtain ⟨Y, Φ, hY, Ψ, hb⟩ := witness_of_narrow hM h1 h2
  have : IsProper Y.hom := hY.1
  exact ⟨Y, Φ, hY, connected_of_narrow_body hb⟩

/-- The proof of `RayClassCFT.embed_core` with the two fibre equalities and single
reciprocity instance it actually uses. -/
theorem embed_core_narrow {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (hb : BodyNarrow Y Φ Ψ)
    (hCN : ClassNumberOneB) (k : Type) [Field k] [NumberField k] [IsTotallyComplex k]
    (hcase : RayCase k) (hk : Module.finrank ℚ k = 2) (hI : QHatIntegral k) (y : fieldPt Qbar ⟶ Y)
    (hcm : ∀ (τ : UpperHalfPlane) (u : BAQˣ), u ∈ OhatU → Ψ τ u = fieldMap ιC ≫ y →
      ∃ (q : k →ₐ[ℚ] LeafQM.B) (κ₀ : k →+* ℂ), (∀ x : 𝓞 k, InO (q x)) ∧ IsCMPoint q κ₀ τ) :
    Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (ShimuraGlue.Ray.mod3 k)) := by
  obtain ⟨hsurj, hfib, -, -, -, ε, δ, -, hrec⟩ := hb
  -- (a) a representative `(τ, u)` of `ιC^* y` with `u ∈ 𝒪̂^×` (class number one)
  obtain ⟨τ₀, g, hτ₀⟩ := hsurj (fieldMap ιC ≫ y)
  obtain ⟨γ, hγ, u, hu, hg⟩ := exists_pos_decomp hCN g
  let τ := (iotaGL (binv γ) (nrd_binv_pos hγ).ne') • τ₀
  have hτu : Ψ τ u = fieldMap ιC ≫ y := by
    rw [← hτ₀]; exact (hfib τ₀ g τ u (Or.inr (Or.inl hu)) (dcRel_of_decomp hγ τ₀ hg)).symm
  -- (b) the CM data at `τ`
  obtain ⟨q, κ₀, hqO, hcmτ⟩ := hcm τ u hu hτu
  -- (c) the reflex embedding in the convention `δ`
  let κ : k →+* ℂ := if δ then κ₀ else (starRingEnd ℂ).comp κ₀
  have hκκ : (if δ then κ else (starRingEnd ℂ).comp κ) = κ₀ := by
    cases δ <;> ext a <;> simp [κ]
  -- (d) the ray class field `L` and an embedding `j : L → ℚ̄` over `κ`
  let L := rayClassField (ShimuraGlue.Ray.mod3 k)
  let : Algebra k ℂ := κ.toAlgebra
  let j' : L →ₐ[k] ℂ := IsAlgClosed.lift
  have hj' : (j' : L →+* ℂ).comp (algebraMap k L) = κ := by
    ext a; exact j'.commutes a
  obtain ⟨j, hj⟩ := exists_lift_ringHom (L := L) (j' : L →+* ℂ)
  let jA : L →ₐ[ℚ] Qbar := j.toRatAlgHom
  let F : IntermediateField ℚ Qbar := jA.fieldRange
  -- (e) every `σ ∈ Gal(ℚ̄/F)` fixes `y`
  have hfix : ∀ σ ∈ F.fixingSubgroup,
      Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y.left = y.left := by
    intro σ hσ
    obtain ⟨σC, hσC⟩ := T5Glue.exists_ringEquiv_extend (ιC : Qbar →+* ℂ) σ.toRingEquiv
    have hσC' : ∀ a, σC (ιC a) = ιC (σ a) := fun a => hσC a
    have hσF : ∀ x : L, σ (j x) = j x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ (j x) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    have hσL : ∀ x : L, σC (j' x) = j' x := fun x => by
      rw [show j' x = (j' : L →+* ℂ) x from rfl, ← hj, hσC', hσF]
    have hσκ : ∀ a : k, σC (κ a) = κ a := fun a => by
      have e : (j' : L →+* ℂ) (algebraMap k L a) = κ a := congrArg (fun f => f a) hj'
      have := hσL (algebraMap k L a)
      rw [show j' (algebraMap k L a) = (j' : L →+* ℂ) (algebraMap k L a) from rfl, e] at this
      exact this
    obtain ⟨s, hs⟩ := exists_artinCondC κ σC hσκ
    -- the Artin symbol of `s` is trivial on `L`
    have hart : ideleClassArtinMap k L (QuotientGroup.mk s) = 1 := by
      refine AlgEquiv.ext fun x => ?_
      apply (j' : L →+* ℂ).injective
      rw [AlgEquiv.one_apply, ← hs L (j' : L →+* ℂ) hj' x]
      exact hσL x
    have hray : ((s : IdeleGroup (𝓞 k) k) : IdeleClassGroup (𝓞 k) k) ∈
        raySubgroup (ShimuraGlue.Ray.mod3 k) := by
      have hker : (QuotientGroup.mk s : IdeleClassGroup (𝓞 k) k) ∈ (ideleClassArtinMap k L).ker := hart
      rw [ker_ideleClassArtinMap, range_ideleClassNormMap_rayClassField] at hker
      exact hker
    obtain ⟨s₀, hs₀, z, ⟨c, rfl⟩, hsz⟩ := Subgroup.mem_sup.1 (mk_mem_raySubgroup_iff.mp hray)
    -- Shimura's reciprocity law at `(τ, u)`
    have h4 := hrec k hcase hk κ q τ hqO (by rw [hκκ]; exact hcmτ) σC s hs hray u hu
    let c' : kˣ := c ^ (ε : ℤ)
    have hsε : s ^ (ε : ℤ) = IdeleGroup.unitEmbedding (𝓞 k) k c' * s₀ ^ (ε : ℤ) := by
      rw [← hsz, mul_zpow, map_zpow, mul_comm]
    have hX : qHatU q s ^ (ε : ℤ) * u = qHatU q (IdeleGroup.unitEmbedding (𝓞 k) k c') * u *
        (u⁻¹ * qHatU q (s₀ ^ (ε : ℤ)) * u) := by
      rw [← map_zpow, hsε, map_mul]; group
    have hk3 : u⁻¹ * qHatU q (s₀ ^ (ε : ℤ)) * u ∈ K3Q :=
      conj_mem_K3Q hu (hI q hqO _ (Subgroup.zpow_mem _ hs₀ _))
    have hdc : DCRel τ u τ (qHatU q s ^ (ε : ℤ) * u) := by
      refine dcRel_fix (nrd_pos_of_cm q κ₀ τ hcmτ c') τ (hcmτ c') u _ _ hk3 ?_
      rw [hX, Units.val_mul, Units.val_mul, qHatU_unitEmbedding]
    have hΨ : galPt σC (Ψ τ u) = Ψ τ u := by
      rw [h4]; exact (hfib τ u τ _ (Or.inr (Or.inr ⟨rfl, hu⟩)) hdc).symm
    rw [hτu, galPt_fieldMap y σ σC hσC'] at hΨ
    have h5 := congrArg CommaMorphism.left (fieldMap_ιC_inj hΨ)
    exact h5
  -- (f) `ℚ(y) ⊆ F ≅ L`
  have hle : residueImage (X := Y.left) y.left ≤ F := residueImage_le y.left F hfix
  exact ⟨((AlgEquiv.ofInjectiveField jA).symm.toAlgHom.comp
    (IntermediateField.inclusion hle)).toRingHom⟩

/-- The proof of `RayClassCFT.obj_at` restricted to an algebraic CM point of a read type. -/
theorem obj_at_narrow {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (hR1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (hU : ModuliAtUsedUnitsHP Y Φ Ψ)
    (hB : CMBaseChange) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P)
    (hc : HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q)
    (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU) (hτu : Ψ τ u = fieldMap ιC ≫ y) :
    ∃ (P' : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts P'.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      HDec.HSyn.G0Split.FibreQM.IotaCompatible P' Φu ∧
      (HasCM4 P.q → HasCM4 P'.q) ∧ (HasCM3 P.q → HasCM3 P'.q) ∧ (HasCM24 P.q → HasCM24 P'.q) := by
  obtain ⟨-, -, -, hnat, -, -⟩ := hR1
  obtain ⟨Q, hQ, hbc⟩ := hnat Qbar ℂ ιC y P hP
  obtain ⟨P', hP', hH⟩ := hU u hu τ (Or.inr ⟨y, P, hτu, hP, hc⟩)
  obtain ⟨Φu, hun, hio⟩ := Y3Fix.lattice_of_hodge ((print_iff_hodge P' τ).1 hH)
  rw [hτu, hQ] at hP'
  obtain ⟨f⟩ := Quotient.exact hP'
  let g : QMIso Q.q P'.q := ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩
  obtain ⟨b4, b3, b24⟩ := hB (ιC : Qbar →+* ℂ) P Q hbc
  exact ⟨P', Φu, hun, hio, fun h => HasCM4.of_iso g (b4 h), fun h => HasCM3.of_iso g (b3 h),
    fun h => HasCM24.of_iso g (b24 h)⟩

/-- Ray class descent on the common fine witness, at the three CM types used by the proof. -/
theorem rayClassCMAb_of_narrow (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3Narrow) (hHL : ZInQ.HomUnify.HomLinearLift) :
    ShimuraGlue.Ray.RayClassCMAb := by
  obtain ⟨Y, Φ, hAb, Ψ, hb⟩ := witness_of_narrow hM h1 h2
  have hU := hb.2.2.2.2.1
  have hCN : ClassNumberOneB := classNumberOneB_proof
  have hB : CMBaseChange := cmBaseChange
  have hA : CMAnalytic := cmAnalytic_of hHL
  refine ⟨Y, Φ, hAb, fun y P hP => ⟨fun h4 => ?_, fun h3 => ?_, fun h24 => ?_⟩⟩
  · refine embed_core_narrow hb hCN K4 (Or.inl rfl) finrank_K4 (qHatIntegral K4) y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, c4, -, -⟩ := obj_at_narrow hAb hU hB y P hP (Or.inl h4) τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c4 h4
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K4 finrank_K4 (not_rat_of_disc y4_rel (by norm_num)) y4_rel ringOfIntegersGen_K4 τ _ hβO
      ?_ lam heig
    have := com_rel ρ hφ (P0 := 0) (Q0 := 1) (by rw [hφ2]; simp)
    simpa using this
  · refine embed_core_narrow hb hCN K3 (Or.inr (Or.inl rfl)) finrank_K3 (qHatIntegral K3) y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, -, c3, -⟩ := obj_at_narrow hAb hU hB y P hP (Or.inr (Or.inl h3)) τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c3 h3
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K3 finrank_K3 (not_rat_of_disc y3_rel (by norm_num)) y3_rel ringOfIntegersGen_K3 τ _ hβO
      ?_ lam heig
    have := com_rel ρ hφ (P0 := -1) (Q0 := 1) (by rw [← hφ2]; simp; abel)
    simpa using this
  · refine embed_core_narrow hb hCN K24 (Or.inr (Or.inr rfl)) finrank_K24 (qHatIntegral K24) y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, -, -, c24⟩ := obj_at_narrow hAb hU hB y P hP (Or.inr (Or.inr h24)) τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c24 h24
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K24 finrank_K24 (not_rat_of_disc y24_rel (by norm_num)) y24_rel ringOfIntegersGen_K24 τ _
      hβO ?_ lam heig
    have := com_rel ρ hφ (P0 := 0) (Q0 := 6) (by rw [hφ2]; simp)
    simpa using this

theorem rayClassCMAb_of_narrow_leaves (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3Narrow)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    RayClassCMAb :=
  rayClassCMAb_of_narrow hM h1 h2
    (ZInQ.HomUnify.homLinearLift_of_corr (AvSplit.Final.h69 hUL hG))

/-- The three outputs read from the assembled Deligne input. The bundle copy only needs
this interface, so none of its carriers can read additional parts of the old package. -/
def ReadData : Prop :=
  HDec.QMSplit.Moduli.ShimuraFamilyAb ∧
    (BPAnalytic.Uniformization.UniformizationLeafAll → ZInQ.HomLattice.GAGAMorphism → RayClassCMAb) ∧
    DCY3Used.Y3ConnectedAb

theorem readData_of_narrow (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3Narrow) : ReadData :=
  ⟨shimuraFamilyAb_of_narrow hM h1 h2, rayClassCMAb_of_narrow_leaves hM h1 h2,
    y3ConnectedAb_of_narrow hM h1 h2⟩

end Y3Hodge
