import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.UnrCoords
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# Bijectivity of unramified tame coordinates at finite precision

The coordinates are those of `SwitchInputs/UnrCoords.lean`, manuscript
`diophantine_zq.tex`, lines 3298–3306 and 5026–5037:
`[z] ↦ (z(φ) mod (Φ - 1)M, z(σ))`.

Injectivity uses the closed zero locus of a continuous cocycle and normalization by a
constant coboundary. For an actual local Galois group over a perfect local field, an
inertia homomorphism descends to a finite Galois extension. The first ramification group
is a `p`-group and the zeroth graded group is cyclic; these are invoked as proved
ramification lemmas. A normalized tame character therefore detects every homomorphism
with prime-to-`p` exponent. No wild-inertia assertion is introduced as a printed input.

Surjectivity is constructive: the inflated unramified cocycle realizes the Frobenius
value, and the tame character together with a profinite Frobenius section realizes each
vector in `ker(Φ-q)`. Frobenius need not act trivially on the coefficients or on roots of
unity.

The complete named input `TameCoordinatesUnr` is constructed on genuine finite-inertia
tame levels, including at every positive `2`-power precision at a place not above `2`.
The actual absolute-Galois cohomology map `coordQLocal` is also proved bijective, without
assuming an exact group-level tame relation; it equals `coordQUnr` whenever that relation
is available. No inverse-limit comparison for completed coefficients is claimed.

Definitions are explicitly labelled DEFINITION and every theorem is PROVED.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.TameBijective

open CategoryTheory Module
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.SwitchInputs

section Injectivity

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- PROVED: evaluation of a one-cocycle is continuous.
Locator: `InnerLimitArith/Realization.lean`, `continuous_evalOne`. -/
theorem continuous_ev1K (z : Z1K k G M) :
    Continuous fun g : G => ev1K (z : (contCochains k G M).X 1) g :=
  ((contSubCx k G M).el (z : (contCochains k G M).X 1)).2.comp
    (continuous_pi fun _ => continuous_id)

/-- DEFINITION: the zero locus of a continuous cocycle, as a subgroup. Closedness is
proved below for separated coefficients.
Locators: `SwitchInputs/UnrCoords.lean`, `ev1K_one_unr`, `ev1K_inv_unr`;
`Mathlib/Topology/Separation/Basic.lean`, closed fibres of continuous maps. -/
def cocycleZeroSubgroup (z : Z1K k G M) : Subgroup G where
  carrier := {g | ev1K (z : (contCochains k G M).X 1) g = 0}
  one_mem' := ev1K_one_unr z
  mul_mem' := by
    intro g h hg hh
    rw [Set.mem_ofPred_eq] at hg hh ⊢
    rw [ev1K_mul, hg, hh, smul_zero, add_zero]
  inv_mem' := by
    intro g hg
    rw [Set.mem_ofPred_eq] at hg ⊢
    rw [ev1K_inv_unr, hg, smul_zero, neg_zero]

/-- PROVED: the cocycle zero subgroup is closed for separated coefficients.
Locator: `Mathlib/Topology/Separation/Basic.lean`, `isClosed_singleton`. -/
theorem isClosed_cocycleZeroSubgroup [T1Space M] (z : Z1K k G M) :
    IsClosed (cocycleZeroSubgroup z : Set G) :=
  isClosed_singleton.preimage (continuous_ev1K z)

/-- PROVED: a continuous cocycle vanishes on a pro-`p` subgroup acting trivially on
coefficients killed by `n` prime to `p`.
Locators: `Profinite/ProP/Basic.lean`, `IsProP.isPGroup_range`;
`Mathlib/GroupTheory/PGroup.lean`, `IsPGroup.powEquiv`. -/
theorem ev1K_eq_zero_on_proP [DiscreteTopology M] (P : Subgroup G)
    {p n : ℕ} (hP : TauCeti.IsProP p P) (hpn : p.Coprime n)
    (hPM : ∀ g ∈ P, ∀ m : M, g • m = m) (hnM : ∀ m : M, n • m = 0)
    (z : Z1K k G M) : ∀ g ∈ P, ev1K (z : (contCochains k G M).X 1) g = 0 := by
  let f : P →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (ev1K (z : (contCochains k G M).X 1) g.1)
      map_one' := by
        change Multiplicative.ofAdd (ev1K (z : (contCochains k G M).X 1) 1) = 1
        rw [ev1K_one_unr]
        rfl
      map_mul' := by
        intro g h
        change Multiplicative.ofAdd (ev1K (z : (contCochains k G M).X 1) (g.1 * h.1)) = _
        rw [ev1K_mul, hPM g.1 g.2]
        rfl }
  have hf : Continuous f :=
    (continuous_of_discreteTopology (f := (Multiplicative.ofAdd : M → Multiplicative M))).comp
      ((continuous_ev1K z).comp continuous_subtype_val)
  have hker : IsOpen (f.ker : Set P) :=
    (isOpen_discrete ({1} : Set (Multiplicative M))).preimage hf
  have hR : IsPGroup p f.range := hP.isPGroup_range f hker
  intro g hg
  let y : f.range := ⟨f ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩
  have hyn : y ^ n = 1 := by
    apply Subtype.ext
    change Multiplicative.ofAdd (n • ev1K (z : (contCochains k G M).X 1) g) = 1
    rw [hnM]
    rfl
  have hy : y = 1 := (hR.powEquiv hpn).injective (hyn.trans (one_pow n).symm)
  have hval := congrArg (fun a : f.range => Multiplicative.toAdd (a : Multiplicative M)) hy
  exact hval

/-- PROVED: vanishing at Frobenius and on inertia forces a continuous cocycle to vanish.
Locator: `Mathlib/Topology/Algebra/Group/Subgroup.lean`,
`Subgroup.topologicalClosure_minimal`; manuscript lines 3298–3306. -/
theorem Z1K_eq_zero_of_frobenius_inertia [T1Space M] (I : Subgroup G) (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (z : Z1K k G M) (hφ : ev1K (z : (contCochains k G M).X 1) φ = 0)
    (hI : ∀ g ∈ I, ev1K (z : (contCochains k G M).X 1) g = 0) : z = 0 := by
  have hle : Subgroup.zpowers φ ⊔ I ≤ cocycleZeroSubgroup z :=
    sup_le (Subgroup.zpowers_le.mpr hφ) hI
  have hcl := Subgroup.topologicalClosure_minimal _ hle (isClosed_cocycleZeroSubgroup z)
  apply Z1K_eq_zero_of_ev z
  intro g
  exact hcl (hgen ▸ Subgroup.mem_top g)

/-- PROVED: tame-generator vanishing implies inertia vanishing when inertia is generated
by the tame generator and a pro-`p` subgroup, and `n` is prime to `p`.
Locators: the preceding pro-`p` lemma; `Mathlib/Topology/Algebra/Group/Subgroup.lean`,
`Subgroup.topologicalClosure_minimal`; `SwitchInputs/UnrCoords.lean`, field `hI`. -/
theorem ev1K_eq_zero_on_inertia_of_proP [DiscreteTopology M]
    (I P : Subgroup G) (σ : G) {p n : ℕ}
    (hP : TauCeti.IsProP p P) (hpn : p.Coprime n)
    (hItriv : ∀ g ∈ I, ∀ m : M, g • m = m) (hPI : P ≤ I)
    (hgenI : I ≤ (P ⊔ Subgroup.zpowers σ).topologicalClosure)
    (hnM : ∀ m : M, n • m = 0) (z : Z1K k G M)
    (hσ : ev1K (z : (contCochains k G M).X 1) σ = 0) :
    ∀ g ∈ I, ev1K (z : (contCochains k G M).X 1) g = 0 := by
  have hPz := ev1K_eq_zero_on_proP P hP hpn (fun g hg => hItriv g (hPI hg)) hnM z
  have hle : P ⊔ Subgroup.zpowers σ ≤ cocycleZeroSubgroup z :=
    sup_le hPz (Subgroup.zpowers_le.mpr hσ)
  have hcl := Subgroup.topologicalClosure_minimal _ hle (isClosed_cocycleZeroSubgroup z)
  exact fun g hg => hcl (hgenI hg)

/-- PROVED: the unramified coordinate map is injective for inertia generated by a tame
 generator and a pro-`p` subgroup acting trivially, with prime-to-`p` torsion coefficients.
Locators: `SwitchInputs/UnrCoords.lean`, field `hbij`; the preceding generation and
constant-coboundary lemmas. No coordinate injectivity is an input. -/
theorem coordQUnr_injective_of_proP [DiscreteTopology M]
    (I P : Subgroup G) (φ σ : G) (q : ℕ) {p n : ℕ}
    (hP : TauCeti.IsProP p P) (hpn : p.Coprime n)
    (hItriv : ∀ g ∈ I, ∀ m : M, g • m = m) (hPI : P ≤ I) (hσI : σ ∈ I)
    (hgenI : I ≤ (P ⊔ Subgroup.zpowers σ).topologicalClosure)
    (hgenG : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hnM : ∀ m : M, n • m = 0) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    Function.Injective (coordQUnr (k := k) (M := M) φ σ q (hItriv σ hσI) hrel) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have hf := congrArg Prod.fst hx
    have hs := congrArg (fun y : CokerFrob k M φ × KerFrob k M φ q => (y.2 : M)) hx
    change (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ) :
      CokerFrob k M φ) = 0 at hf
    rw [Submodule.Quotient.mk_eq_zero] at hf
    obtain ⟨m, hm⟩ := hf
    let w := z - relaxedDK k G M (const0K (k := k) (G := G) m)
    have hwφ : ev1K (w : (contCochains k G M).X 1) φ = 0 := by
      change ev1K (z : (contCochains k G M).X 1) φ -
        ev1K ((relaxedDK k G M (const0K m) : Z1K k G M) : (contCochains k G M).X 1) φ = 0
      rw [relaxedDK_ev, ev0K_const0K, ← hm, frobSub_apply, one_smul, sub_self]
    have hwσ : ev1K (w : (contCochains k G M).X 1) σ = 0 := by
      change ev1K (z : (contCochains k G M).X 1) σ -
        ev1K ((relaxedDK k G M (const0K m) : Z1K k G M) : (contCochains k G M).X 1) σ = 0
      rw [relaxedDK_ev, ev0K_const0K, hItriv σ hσI, sub_self, sub_zero]
      exact hs
    have hw : w = 0 := Z1K_eq_zero_of_frobenius_inertia I φ hgenG w hwφ
      (ev1K_eq_zero_on_inertia_of_proP I P σ hP hpn hItriv hPI hgenI hnM w hwσ)
    have hz : z = relaxedDK k G M (const0K m) := sub_eq_zero.mp hw
    rw [hz, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _

end Injectivity

section TameSurjectivity

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul G M]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- DEFINITION: the continuous homomorphism from the cyclic group of order `n` sending
its additive generator to `m`, where `n m = 0`.
Locator: `InnerLimitArith/Realization.lean`, `nsmul_mod_eq_of`. -/
def cyclicMultiple {n : ℕ} [NeZero n] (m : M) (hnm : n • m = 0) :
    Multiplicative (ZMod n) →ₜ* Multiplicative M where
  toFun a := Multiplicative.ofAdd (a.toAdd.val • m)
  map_one' := by
    change Multiplicative.ofAdd ((0 : ZMod n).val • m) = 1
    rw [ZMod.val_zero, zero_nsmul]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd ((a.toAdd + b.toAdd).val • m) =
      Multiplicative.ofAdd (a.toAdd.val • m + b.toAdd.val • m)
    rw [ZMod.val_add, ZInQ.Contrib.RC53Assist.InnerLimitArith.nsmul_mod_eq_of hnm,
      add_nsmul]
  continuous_toFun := continuous_of_discreteTopology

omit [DiscreteTopology M] in
/-- PROVED: the cyclic homomorphism has the stated formula.
Locator: the preceding definition `cyclicMultiple`. -/
theorem cyclicMultiple_apply {n : ℕ} [NeZero n] (m : M) (hnm : n • m = 0)
    (a : Multiplicative (ZMod n)) :
    (cyclicMultiple m hnm a).toAdd = a.toAdd.val • m := rfl

/-- DEFINITION: conjugation on a normal inertia subgroup.
Locator: `Mathlib/Algebra/Group/Subgroup/Defs.lean`, normal-subgroup conjugation. -/
def inertiaConj (I : Subgroup G) [I.Normal] (g : G) (i : I) : I :=
  ⟨g * i.1 * g⁻¹, Subgroup.Normal.conj_mem inferInstance i.1 i.2 g⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- PROVED: conjugations compose according to multiplication.
Locator: the preceding definition `inertiaConj`, the group laws. -/
theorem inertiaConj_mul (I : Subgroup G) [I.Normal] (g h : G) (i : I) :
    inertiaConj I (g * h) i = inertiaConj I g (inertiaConj I h i) := by
  apply Subtype.ext
  change (g * h) * i.1 * (g * h)⁻¹ = g * (h * i.1 * h⁻¹) * g⁻¹
  group

/-- PROVED: equivariance of a continuous inertia homomorphism follows from equivariance
at Frobenius and triviality of the inertia action.
Locator: `Mathlib/Topology/Algebra/Group/Subgroup.lean`,
`Subgroup.topologicalClosure_minimal`; manuscript lines 3298–3306. -/
theorem inertiaHom_equivariant (I : Subgroup G) [I.Normal] (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hItriv : ∀ g ∈ I, ∀ m : M, g • m = m) (f : I →ₜ* Multiplicative M)
    (hfφ : ∀ i : I, (f (inertiaConj I φ i)).toAdd = φ • (f i).toAdd) :
    ∀ (g : G) (i : I), (f (inertiaConj I g i)).toAdd = g • (f i).toAdd := by
  let N : Subgroup G :=
    { carrier := {g | ∀ i : I, (f (inertiaConj I g i)).toAdd = g • (f i).toAdd}
      one_mem' := by
        intro i
        rw [show inertiaConj I 1 i = i by apply Subtype.ext; simp [inertiaConj], one_smul]
      mul_mem' := by
        intro g h hg hh i
        rw [inertiaConj_mul, hg, hh, mul_smul]
      inv_mem' := by
        intro g hg i
        have hc : inertiaConj I g (inertiaConj I g⁻¹ i) = i := by
          apply Subtype.ext
          change g * (g⁻¹ * i.1 * (g⁻¹)⁻¹) * g⁻¹ = i.1
          group
        have he := hg (inertiaConj I g⁻¹ i)
        rw [hc] at he
        have he' := congrArg (fun m : M => g⁻¹ • m) he
        rw [inv_smul_smul] at he'
        exact he'.symm }
  have hN : IsClosed (N : Set G) := by
    change IsClosed {g : G | ∀ i : I,
      (f (inertiaConj I g i)).toAdd = g • (f i).toAdd}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    have hc : Continuous fun g : G => inertiaConj I g i :=
      ((continuous_id.mul continuous_const).mul continuous_inv).subtype_mk _
    have hfc : Continuous fun g : G => (f (inertiaConj I g i)).toAdd :=
      (continuous_of_discreteTopology
        (f := (Multiplicative.toAdd : Multiplicative M → M))).comp (f.continuous.comp hc)
    exact isClosed_eq hfc (continuous_id.smul continuous_const)
  have hIN : I ≤ N := by
    intro g hg i
    have hc : inertiaConj I g i = (⟨g, hg⟩ : I) * i * (⟨g, hg⟩ : I)⁻¹ := by
      apply Subtype.ext
      rfl
    have hfc : f (inertiaConj I g i) = f i := by
      rw [hc, map_mul, map_mul, map_inv]
      simp [mul_comm, mul_assoc]
    exact (congrArg Multiplicative.toAdd hfc).trans (hItriv g hg (f i).toAdd).symm
  have hle : Subgroup.zpowers φ ⊔ I ≤ N :=
    sup_le (Subgroup.zpowers_le.mpr hfφ) hIN
  have hcl := Subgroup.topologicalClosure_minimal _ hle hN
  exact fun g => hcl (hgen ▸ Subgroup.mem_top g)

/-- DEFINITION: the Frobenius section of an unramified quotient `H ≃ ℤ̂`, obtained by
lifting the chosen Frobenius element to profinite powers.
Locator: `Profinite/ZHat/Basic.lean`, `zHat.lift`. -/
def frobeniusSection [CompactSpace G] [TotallyDisconnectedSpace G]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (φ : G) : H →ₜ* G :=
  (TauCeti.zHat.lift φ).comp ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩

omit [IsTopologicalGroup H] in
/-- PROVED: the Frobenius section sends the Frobenius of the quotient to the chosen lift.
Locators: `UnramifiedComplex/ZHat.lean`, `frobElt`;
`Profinite/ZHat/Basic.lean`, `zHat.lift_gen`. -/
theorem frobeniusSection_frob [CompactSpace G] [TotallyDisconnectedSpace G]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (φ : G) :
    frobeniusSection e φ (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e) = φ := by
  simp [frobeniusSection, ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt]

omit [IsTopologicalGroup H] in
/-- PROVED: a Frobenius lift gives a right inverse of the unramified quotient.
Locator: `Profinite/ZHat/Basic.lean`, `zHat.hom_ext`. -/
theorem quotient_frobeniusSection [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space H]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (φ : G)
    (hφ : π φ = ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e) :
    ∀ h : H, π (frobeniusSection e φ h) = h := by
  have he : π.comp (TauCeti.zHat.lift φ) =
      (⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩ : TauCeti.zHat.{0} →ₜ* H) := by
    apply TauCeti.zHat.hom_ext
    change π (TauCeti.zHat.lift φ TauCeti.zHat.gen) = e.symm TauCeti.zHat.gen
    rw [TauCeti.zHat.lift_gen, hφ]
    rfl
  intro h
  have hh := DFunLike.congr_fun he (e h)
  change π (frobeniusSection e φ h) = h
  exact hh.trans (e.symm_apply_apply h)

/-- DEFINITION: the inertia component in the normal form `g = t(g) s(π g)` of a split
unramified quotient.
Locator: the group laws and the right-inverse property of the section. -/
def inertiaPart (π : G →ₜ* H) (s : H →ₜ* G) (hs : ∀ h : H, π (s h) = h)
    (g : G) : (π : G →* H).ker :=
  ⟨g * (s (π g))⁻¹, by
    change π (g * (s (π g))⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]⟩

omit [IsTopologicalGroup H] in
/-- PROVED: the inertia component is continuous.
Locator: the preceding definition `inertiaPart`, continuity of multiplication and inversion. -/
theorem continuous_inertiaPart (π : G →ₜ* H) (s : H →ₜ* G)
    (hs : ∀ h : H, π (s h) = h) : Continuous (inertiaPart π s hs) :=
  (continuous_id.mul (s.continuous.comp π.continuous).inv).subtype_mk _

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- PROVED: multiplication of inertia components is the semidirect-product formula.
Locator: the group laws and `inertiaPart`. -/
theorem inertiaPart_mul (π : G →ₜ* H) (s : H →ₜ* G)
    (hs : ∀ h : H, π (s h) = h) (g h : G) :
    inertiaPart π s hs (g * h) = inertiaPart π s hs g *
      inertiaConj (π : G →* H).ker (s (π g)) (inertiaPart π s hs h) := by
  apply Subtype.ext
  change (g * h) * (s (π (g * h)))⁻¹ =
    (g * (s (π g))⁻¹) * ((s (π g)) * (h * (s (π h))⁻¹) * (s (π g))⁻¹)
  rw [map_mul, map_mul]
  group

omit [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] [IsTopologicalGroup H] in
/-- PROVED: a group element acts as its unramified component if inertia acts trivially.
Locator: the normal form in `inertiaPart`. -/
theorem smul_eq_section_smul (π : G →ₜ* H) (s : H →ₜ* G)
    (hs : ∀ h : H, π (s h) = h)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m) (g : G) (m : M) :
    g • m = s (π g) • m := by
  have hg : g = (inertiaPart π s hs g : G) * s (π g) := by
    change g = (g * (s (π g))⁻¹) * s (π g)
    group
  conv_lhs => rw [hg]
  rw [mul_smul, hItriv _ (inertiaPart π s hs g).2]

/-- DEFINITION: the singular cocycle obtained from an equivariant continuous inertia
homomorphism and a section of the unramified quotient.
Locators: `inertiaPart_mul`, `smul_eq_section_smul`;
`SwitchInputs/UnrCoords.lean`, `mem_Z1K_of_cocycle`. -/
def singularCocycle (π : G →ₜ* H) (s : H →ₜ* G) (hs : ∀ h : H, π (s h) = h)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m)
    (f : (π : G →* H).ker →ₜ* Multiplicative M)
    (hf : ∀ (g : G) (i : (π : G →* H).ker),
      (f (inertiaConj (π : G →* H).ker g i)).toAdd = g • (f i).toAdd) : Z1K k G M := by
  let F : G → M := fun g => (f (inertiaPart π s hs g)).toAdd
  have hF : Continuous F :=
    (continuous_of_discreteTopology (f := (Multiplicative.toAdd : Multiplicative M → M))).comp
      (f.continuous.comp (continuous_inertiaPart π s hs))
  let c : (contCochains k G M).X 1 :=
    (contSubCx k G M).ofSub ⟨(fun v : Fin 1 → G => F (v 0)), hF.comp (continuous_apply 0)⟩
  refine ⟨c, mem_Z1K_of_cocycle c ?_⟩
  intro g h
  change F (g * h) = F g + g • F h
  dsimp [F]
  rw [inertiaPart_mul, map_mul]
  change (f (inertiaPart π s hs g)).toAdd +
    (f (inertiaConj (π : G →* H).ker (s (π g)) (inertiaPart π s hs h))).toAdd = _
  rw [hf, ← smul_eq_section_smul π s hs hItriv g]

omit [IsTopologicalGroup H] in
/-- PROVED: the singular cocycle has the stated evaluation formula.
Locator: the preceding definition `singularCocycle`. -/
theorem singularCocycle_ev (π : G →ₜ* H) (s : H →ₜ* G) (hs : ∀ h : H, π (s h) = h)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m)
    (f : (π : G →* H).ker →ₜ* Multiplicative M)
    (hf : ∀ (g : G) (i : (π : G →* H).ker),
      (f (inertiaConj (π : G →* H).ker g i)).toAdd = g • (f i).toAdd) (g : G) :
    ev1K (singularCocycle (k := k) π s hs hItriv f hf : (contCochains k G M).X 1) g =
      (f (inertiaPart π s hs g)).toAdd := rfl

omit [DiscreteTopology M] in
/-- PROVED: the cyclic homomorphism sends the standard generator to `m`.
Locators: `cyclicMultiple`; `Mathlib/Data/ZMod/Basic.lean`, `ZMod.val_one`. -/
theorem cyclicMultiple_one {n : ℕ} [NeZero n] [Fact (1 < n)]
    (m : M) (hnm : n • m = 0) :
    cyclicMultiple m hnm (Multiplicative.ofAdd (1 : ZMod n)) = Multiplicative.ofAdd m := by
  change Multiplicative.ofAdd ((1 : ZMod n).val • m) = Multiplicative.ofAdd m
  rw [ZMod.val_one, one_nsmul]

/-- PROVED: the tame character gives an equivariant inertia homomorphism for each vector
in `ker(Φ-q)`, without a trivial-Frobenius hypothesis.
Locators: `inertiaHom_equivariant`, `cyclicMultiple`;
`SwitchInputs/UnrCoords.lean`, `KerFrob`. -/
theorem cyclicMultiple_tame_equivariant (I : Subgroup G) [I.Normal] (φ : G) (q : ℕ)
    {n : ℕ} [NeZero n]
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hItriv : ∀ g ∈ I, ∀ m : M, g • m = m)
    (χ : I →ₜ* Multiplicative (ZMod n))
    (hχ : ∀ i : I, χ (inertiaConj I φ i) = χ i ^ q)
    (m : M) (hnm : n • m = 0) (hφm : φ • m = q • m) :
    ∀ (g : G) (i : I),
      ((cyclicMultiple m hnm).comp χ (inertiaConj I g i)).toAdd =
        g • ((cyclicMultiple m hnm).comp χ i).toAdd := by
  apply inertiaHom_equivariant I φ hgen hItriv ((cyclicMultiple m hnm).comp χ)
  intro i
  change (cyclicMultiple m hnm (χ (inertiaConj I φ i))).toAdd =
    φ • (cyclicMultiple m hnm (χ i)).toAdd
  rw [hχ]
  have he : cyclicMultiple m hnm (χ i ^ q) = cyclicMultiple m hnm (χ i) ^ q :=
    map_pow (cyclicMultiple m hnm) (χ i) q
  rw [he]
  change q • (cyclicMultiple m hnm (χ i)).toAdd =
    φ • (cyclicMultiple m hnm (χ i)).toAdd
  have hsmul : ∀ a : ℕ, φ • (a • m) = a • (φ • m) := by
    intro a
    induction a with
    | zero => rw [zero_nsmul, smul_zero, zero_nsmul]
    | succ a ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]
  rw [cyclicMultiple_apply, hsmul, hφm, ← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

omit [IsTopologicalGroup H] in
/-- PROVED: the cocycle built from a tame inertia character takes values `0` and `m`
at the chosen Frobenius and tame generator.
Locators: `singularCocycle_ev`, `frobeniusSection_frob`, `cyclicMultiple_one`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem singularCocycle_coordinates [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space H]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (φ σ : G) (q : ℕ)
    (hφ : π φ = ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e)
    (hσ : σ ∈ (π : G →* H).ker)
    (hgen : (Subgroup.zpowers φ ⊔ (π : G →* H).ker).topologicalClosure = ⊤)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m)
    {n : ℕ} [NeZero n] [Fact (1 < n)]
    (χ : (π : G →* H).ker →ₜ* Multiplicative (ZMod n))
    (hχσ : χ ⟨σ, hσ⟩ = Multiplicative.ofAdd (1 : ZMod n))
    (hχφ : ∀ i : (π : G →* H).ker,
      χ (inertiaConj (π : G →* H).ker φ i) = χ i ^ q)
    (m : M) (hnm : n • m = 0) (hφm : φ • m = q • m) :
    let s := frobeniusSection e φ
    let hs := quotient_frobeniusSection e π φ hφ
    let f := (cyclicMultiple m hnm).comp χ
    let hf := cyclicMultiple_tame_equivariant (π : G →* H).ker φ q hgen hItriv χ hχφ m hnm hφm
    ev1K (singularCocycle (k := k) π s hs hItriv f hf : (contCochains k G M).X 1) φ = 0 ∧
    ev1K (singularCocycle (k := k) π s hs hItriv f hf : (contCochains k G M).X 1) σ = m := by
  dsimp only
  constructor
  · rw [singularCocycle_ev]
    have ht : inertiaPart π (frobeniusSection e φ)
        (quotient_frobeniusSection e π φ hφ) φ = 1 := by
      apply Subtype.ext
      change φ * (frobeniusSection e φ (π φ))⁻¹ = 1
      rw [hφ, frobeniusSection_frob, mul_inv_cancel]
    rw [ht, map_one]
    rfl
  · rw [singularCocycle_ev]
    have ht : inertiaPart π (frobeniusSection e φ)
        (quotient_frobeniusSection e π φ hφ) σ = ⟨σ, hσ⟩ := by
      apply Subtype.ext
      change σ * (frobeniusSection e φ (π σ))⁻¹ = σ
      rw [show π σ = 1 from hσ, map_one, inv_one, mul_one]
    rw [ht]
    change (cyclicMultiple m hnm (χ ⟨σ, hσ⟩)).toAdd = m
    rw [hχσ, cyclicMultiple_one]
    rfl

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- PROVED: every compatible Frobenius value and tame eigenvector is realized by a
continuous one-cocycle. This construction does not require a group-level tame relation:
the inflated unramified cocycle and the singular cocycle supply the two values.
Locators: `InnerLimitArith/Realization.lean`, `urCondCocycle`, `tameCoord_urCondCocycle`;
`singularCocycle_coordinates`; manuscript lines 3298–3306 and 5026–5037. -/
theorem exists_Z1K_with_coordinates [CompactSpace G] [TotallyDisconnectedSpace G]
    [T2Space H] [TopologicalSpace k]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H)
    (X : TopRep.{0} k H) [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
    (hfs : Function.Surjective f) (φ σ : G) (q : ℕ)
    (hφ : π φ = ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e)
    (hσ : σ ∈ (π : G →* H).ker)
    (hgen : (Subgroup.zpowers φ ⊔ (π : G →* H).ker).topologicalClosure = ⊤)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m)
    {n : ℕ} [NeZero n] [Fact (1 < n)] (hnM : ∀ m : M, n • m = 0)
    (χ : (π : G →* H).ker →ₜ* Multiplicative (ZMod n))
    (hχσ : χ ⟨σ, hσ⟩ = Multiplicative.ofAdd (1 : ZMod n))
    (hχφ : ∀ i : (π : G →* H).ker,
      χ (inertiaConj (π : G →* H).ker φ i) = χ i ^ q)
    (a : M) (m : KerFrob k M φ q) :
    ∃ z : Z1K k G M, ev1K (z : (contCochains k G M).X 1) φ = a ∧
      ev1K (z : (contCochains k G M).X 1) σ = (m : M) := by
  obtain ⟨x, hx⟩ := hfs a
  let u : Z1K k G M := ZInQ.Contrib.RC53Assist.InnerLimitArith.urCondCocycle e π X f hf x
  have hu := ZInQ.Contrib.RC53Assist.InnerLimitArith.tameCoord_urCondCocycle
    e π X f hf φ σ hφ (show π σ = 1 from hσ) x
  have huφ : ev1K (u : (contCochains k G M).X 1) φ = a := (congrArg Prod.fst hu).trans hx
  have huσ : ev1K (u : (contCochains k G M).X 1) σ = 0 := congrArg Prod.snd hu
  have hφm : φ • (m : M) = q • (m : M) := by
    have hm := LinearMap.mem_ker.mp m.2
    rw [frobSub_apply, sub_eq_zero, Nat.cast_smul_eq_nsmul] at hm
    exact hm
  let s := frobeniusSection e φ
  let hs := quotient_frobeniusSection e π φ hφ
  let fm := (cyclicMultiple (m : M) (hnM m)).comp χ
  let hfm := cyclicMultiple_tame_equivariant (π : G →* H).ker φ q hgen hItriv
    χ hχφ (m : M) (hnM m) hφm
  let v := singularCocycle (k := k) π s hs hItriv fm hfm
  have hv := singularCocycle_coordinates (k := k) e π φ σ q hφ hσ hgen hItriv χ hχσ hχφ
    (m : M) (hnM m) hφm
  refine ⟨u + v, ?_, ?_⟩
  · change ev1K (u : (contCochains k G M).X 1) φ +
      ev1K (v : (contCochains k G M).X 1) φ = a
    rw [huφ, hv.1, add_zero]
  · change ev1K (u : (contCochains k G M).X 1) σ +
      ev1K (v : (contCochains k G M).X 1) σ = (m : M)
    rw [huσ, hv.2, zero_add]

/-- PROVED: unramified tame coordinates are surjective for finite unramified
coefficients. The hypotheses supply a scalar tame inertia character, not a cohomology
coordinate map or its surjectivity. Frobenius may act nontrivially.
Locators: `exists_Z1K_with_coordinates`; `SwitchInputs/UnrCoords.lean`, `coordQUnr`. -/
theorem coordQUnr_surjective_of_tame_character [CompactSpace G] [TotallyDisconnectedSpace G]
    [T2Space H] [TopologicalSpace k]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H)
    (X : TopRep.{0} k H) [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
    (hfs : Function.Surjective f) (φ σ : G) (q : ℕ)
    (hφ : π φ = ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e)
    (hσ : σ ∈ (π : G →* H).ker)
    (hgen : (Subgroup.zpowers φ ⊔ (π : G →* H).ker).topologicalClosure = ⊤)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    {n : ℕ} [NeZero n] [Fact (1 < n)]
    (hnM : ∀ m : M, n • m = 0)
    (χ : (π : G →* H).ker →ₜ* Multiplicative (ZMod n))
    (hχσ : χ ⟨σ, hσ⟩ = Multiplicative.ofAdd (1 : ZMod n))
    (hχφ : ∀ i : (π : G →* H).ker,
      χ (inertiaConj (π : G →* H).ker φ i) = χ i ^ q) :
    Function.Surjective (coordQUnr (k := k) (M := M) φ σ q (hItriv σ hσ) hrel) := by
  rintro ⟨c, m⟩
  induction c using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨z, hzφ, hzσ⟩ := exists_Z1K_with_coordinates e π X f hf hfs φ σ q hφ hσ hgen
      hItriv hnM χ hχσ hχφ a m
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [coordQUnr_mk]
    apply Prod.ext
    · change (Submodule.Quotient.mk (ev1K (z : (contCochains k G M).X 1) φ) :
        CokerFrob k M φ) = Submodule.Quotient.mk a
      rw [hzφ]
    · exact Subtype.ext hzσ

/-- PROVED: the named unramified tame-coordinate input follows from a pro-`p`
subgroup, topological generation, and a scalar tame character. Both bijectivity and the
inertia-vanishing field are proved; no cohomology coordinate is assumed bijective.
Locators: `SwitchInputs/UnrCoords.lean`, `TameCoordinatesUnr`;
`coordQUnr_injective_of_proP`, `coordQUnr_surjective_of_tame_character`. -/
theorem tameCoordinatesUnr_of_proP [CompactSpace G] [TotallyDisconnectedSpace G]
    [T2Space H] [TopologicalSpace k]
    (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H)
    (X : TopRep.{0} k H) [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
    (hfs : Function.Surjective f) (φ σ : G) (q : ℕ)
    (hφ : π φ = ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e)
    (hσ : σ ∈ (π : G →* H).ker)
    (hgen : (Subgroup.zpowers φ ⊔ (π : G →* H).ker).topologicalClosure = ⊤)
    (hItriv : ∀ g ∈ (π : G →* H).ker, ∀ m : M, g • m = m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (P : Subgroup G) {p n : ℕ} [NeZero n] [Fact (1 < n)]
    (hP : TauCeti.IsProP p P) (hpn : p.Coprime n) (hPI : P ≤ (π : G →* H).ker)
    (hgenI : (π : G →* H).ker ≤ (P ⊔ Subgroup.zpowers σ).topologicalClosure)
    (hnM : ∀ m : M, n • m = 0)
    (χ : (π : G →* H).ker →ₜ* Multiplicative (ZMod n))
    (hχσ : χ ⟨σ, hσ⟩ = Multiplicative.ofAdd (1 : ZMod n))
    (hχφ : ∀ i : (π : G →* H).ker,
      χ (inertiaConj (π : G →* H).ker φ i) = χ i ^ q) :
    TameCoordinatesUnr k M (π : G →* H).ker φ σ q where
  hItriv := hItriv
  hσI := hσ
  hrel := hrel
  hbij := ⟨coordQUnr_injective_of_proP (π : G →* H).ker P φ σ q hP hpn hItriv hPI
      hσ hgenI hgen hnM hrel,
    coordQUnr_surjective_of_tame_character e π X f hf hfs φ σ q hφ hσ hgen hItriv hrel
      hnM χ hχσ hχφ⟩
  hI := ev1K_eq_zero_on_inertia_of_proP (π : G →* H).ker P σ hP hpn hItriv hPI hgenI hnM

end TameSurjectivity

section ArithmeticCharacter

open TauCeti ValuativeRel IntermediateField
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-- DEFINITION: the canonical identity identification between the absolute Galois group
and the automorphisms of an algebraic closure, with their Krull topologies.
Locator: `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`, `Field.absoluteGaloisGroup`. -/
def algebraicGaloisEquiv (K : Type) [Field K] :
    Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) where
  toFun g := g
  invFun g := g
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n]
  {a : K} {β : AlgebraicClosure K} {σ : Field.absoluteGaloisGroup K}

/-- PROVED: the Kummer logarithm is additive on inertia, without assuming that
Frobenius fixes roots of unity.
Locators: `TameQuotient/TameCharacter.lean`, `kummerVal_mul_of_mem`;
`InnerLimitArith/Realization.lean`, `kummerLog_eq_iff`, `pow_kummerLog`. -/
theorem kummerLog_mul_inertia (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (g h : inertiaSubgroup K) :
    kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K (g.1 * h.1)) =
      kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K g.1) +
        kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K h.1) := by
  rw [map_mul, kummerLog_eq_iff, ZMod.val_add]
  have hmod := pow_mod_orderOf (kummerVal β (algebraicGaloisEquiv K σ))
    ((kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K g.1)).val +
      (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K h.1)).val)
  rw [← hζ.eq_orderOf] at hmod
  rw [hmod, pow_add, pow_kummerLog, pow_kummerLog,
    kummerVal_mul_of_mem hn hβ hβ0 (show algebraicGaloisEquiv K g.1 ∈ inertiaSubgroup K from g.2)]

/-- DEFINITION: the continuous tame inertia character at level `n`, in the basis
chosen by a primitive Kummer value. Only inertia, not the full local Galois group,
acts trivially on the prime-to-residue-characteristic roots of unity.
Locators: `TameQuotient/TameCharacter.lean`, `tameChar`;
`InnerLimitArith/Realization.lean`, `kummerLog`, `continuous_kummerLog`. -/
def tameLog (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n) :
    inertiaSubgroup K →ₜ* Multiplicative (ZMod n) := by
  let f : inertiaSubgroup K →* Multiplicative (ZMod n) :=
    { toFun := fun g => Multiplicative.ofAdd
        (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K g.1))
      map_one' := by
        change Multiplicative.ofAdd (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K 1)) = 1
        rw [map_one, kummerLog_of_fix hβ hβ0 hζ (AlgEquiv.one_apply β)]
        rfl
      map_mul' := by
        intro g h
        change Multiplicative.ofAdd (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K (g.1 * h.1))) = _
        rw [kummerLog_mul_inertia hn hβ hβ0 hζ g h]
        rfl }
  have : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have hopen := IntermediateField.fixingSubgroup_isOpen K⟮β⟯
  have hf : ContinuousAt f 1 := by
    refine (continuousAt_const (y := (1 : Multiplicative (ZMod n)))).congr ?_
    have hU : (fun g : inertiaSubgroup K => algebraicGaloisEquiv K g.1) ⁻¹'
        ((K⟮β⟯).fixingSubgroup : Set Gal(AlgebraicClosure K/K)) ∈
        nhds (1 : inertiaSubgroup K) :=
      (hopen.preimage ((algebraicGaloisEquiv K).continuous.comp continuous_subtype_val)).mem_nhds
        (by change algebraicGaloisEquiv K 1 ∈ (K⟮β⟯).fixingSubgroup
            rw [map_one]
            exact (K⟮β⟯).fixingSubgroup.one_mem)
    filter_upwards [hU] with g hg
    have hgβ : algebraicGaloisEquiv K g.1 β = β :=
      hg ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
    change (1 : Multiplicative (ZMod n)) =
      Multiplicative.ofAdd (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K g.1))
    rw [kummerLog_of_fix hβ hβ0 hζ hgβ]
    rfl
  exact ⟨f, continuous_of_continuousAt_one f hf⟩

/-- PROVED: the tame inertia character has the stated logarithmic formula.
Locator: the preceding definition `tameLog`. -/
theorem tameLog_apply (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n) (g : inertiaSubgroup K) :
    tameLog hn hβ hβ0 hζ g =
      Multiplicative.ofAdd (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K g.1)) := rfl

/-- PROVED: the chosen tame inertia element maps to the standard cyclic generator.
Locators: `tameLog_apply`; `InnerLimitArith/Realization.lean`, `kummerLog_self`. -/
theorem tameLog_generator [Fact (1 < n)] (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hσI : σ ∈ inertiaSubgroup K) :
    tameLog hn hβ hβ0 hζ ⟨σ, hσI⟩ = Multiplicative.ofAdd (1 : ZMod n) := by
  rw [tameLog_apply, kummerLog_self]

/-- PROVED: Frobenius acts on the tame inertia character by the residue cardinality.
Locators: `TameQuotient/TameCharacter.lean`, `kummerVal_conj_frobenius`;
`InnerLimitArith/Realization.lean`, `kummerLog_eq_iff`. -/
theorem tameLog_conj_frobenius (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    {φ : Field.absoluteGaloisGroup K} (hφ : IsArithFrobeniusLift K φ)
    (i : inertiaSubgroup K) :
    tameLog hn hβ hβ0 hζ (inertiaConj (inertiaSubgroup K) φ i) =
      tameLog hn hβ hβ0 hζ i ^ Nat.card 𝓀[K] := by
  apply Multiplicative.toAdd.injective
  rw [tameLog_apply, tameLog_apply]
  change kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K (φ * i.1 * φ⁻¹)) =
    (Nat.card 𝓀[K]) • kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K i.1)
  rw [map_mul, map_mul, map_inv, nsmul_eq_mul, kummerLog_eq_iff,
    ZMod.val_mul, ZMod.val_natCast]
  have hmod := pow_mod_orderOf (kummerVal β (algebraicGaloisEquiv K σ))
    (((Nat.card 𝓀[K]) % n) * (kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K i.1)).val)
  rw [← hζ.eq_orderOf] at hmod
  have hq := pow_mod_orderOf (kummerVal β (algebraicGaloisEquiv K σ)) (Nat.card 𝓀[K])
  rw [← hζ.eq_orderOf] at hq
  rw [hmod, pow_mul, hq, ← pow_mul,
    Nat.mul_comm (Nat.card 𝓀[K]), pow_mul, pow_kummerLog]
  exact (kummerVal_conj_frobenius hn hβ hβ0
    (show IsArithFrobeniusLift K (algebraicGaloisEquiv K φ) from hφ)
    (show algebraicGaloisEquiv K i.1 ∈ inertiaSubgroup K from i.2)).symm

end ArithmeticCharacter

section FiniteCyclicDetection

variable {C A : Type*} [Group C] [AddCommGroup A] {p n : ℕ}

/-- PROVED: a homomorphism from a `p`-group to a group killed by an integer prime to
`p` is trivial. This is a finite-group argument and requires no cohomology input.
Locator: `Mathlib/GroupTheory/PGroup.lean`, `IsPGroup.powEquiv`. -/
theorem pGroup_hom_trivial {B : Type*} [Group B] (hC : IsPGroup p C)
    (hpn : p.Coprime n) (f : C →* B) (hnB : ∀ b : B, b ^ n = 1) :
    ∀ c : C, f c = 1 := by
  intro c
  obtain ⟨d, hd⟩ := (hC.powEquiv hpn).surjective c
  change d ^ n = c at hd
  rw [← hd, map_pow, hnB]

/-- PROVED: for a cyclic group, a scalar character sending `σ` to `1 mod n` detects
all homomorphisms to groups killed by `n`: a homomorphism vanishing at `σ` vanishes.
Locators: `Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean`,
`IsCyclic.exists_generator`; `Mathlib/Algebra/Module/ZMod.lean`, `AddCommGroup.zmodModule`.
-/
theorem cyclic_hom_detect [IsCyclic C] (χ : C →* Multiplicative (ZMod n))
    (f : C →* Multiplicative A) (hnA : ∀ a : A, n • a = 0) (σ : C)
    (hχσ : χ σ = Multiplicative.ofAdd (1 : ZMod n)) (hfσ : f σ = 1) :
    ∀ c : C, f c = 1 := by
  let : Module (ZMod n) A := AddCommGroup.zmodModule hnA
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨r, hr⟩ := hτ σ
  change τ ^ r = σ at hr
  have hχr : (r : ZMod n) * (χ τ).toAdd = 1 := by
    have he : χ τ ^ r = Multiplicative.ofAdd (1 : ZMod n) := by
      rw [← map_zpow, hr, hχσ]
    have ha := congrArg Multiplicative.toAdd he
    change r • (χ τ).toAdd = (1 : ZMod n) at ha
    simpa only [zsmul_eq_mul] using ha
  have hfr : (r : ZMod n) • (f τ).toAdd = 0 := by
    have he : f τ ^ r = 1 := by rw [← map_zpow, hr, hfσ]
    have ha := congrArg Multiplicative.toAdd he
    change r • (f τ).toAdd = 0 at ha
    rw [Int.cast_smul_eq_zsmul]
    exact ha
  have hτf : f τ = 1 := by
    apply Multiplicative.toAdd.injective
    change (f τ).toAdd = 0
    calc
      (f τ).toAdd = (1 : ZMod n) • (f τ).toAdd := (one_smul _ _).symm
      _ = ((χ τ).toAdd * (r : ZMod n)) • (f τ).toAdd := by rw [mul_comm, hχr]
      _ = (χ τ).toAdd • ((r : ZMod n) • (f τ).toAdd) := mul_smul _ _ _
      _ = 0 := by rw [hfr, smul_zero]
  intro c
  obtain ⟨r, rfl⟩ := hτ c
  rw [map_zpow, hτf, one_zpow]

/-- PROVED: a tame cyclic quotient detects prime-to-`p` homomorphisms. The normal
`p`-subgroup is killed directly, and the resulting homomorphism on the cyclic quotient
is detected by a normalized scalar character.
Locators: `pGroup_hom_trivial`, `cyclic_hom_detect`;
`Mathlib/GroupTheory/QuotientGroup/Basic.lean`, `QuotientGroup.lift`. -/
theorem hom_trivial_of_cyclic_tame_quotient (P : Subgroup C) [P.Normal]
    [IsCyclic (C ⧸ P)] (hP : IsPGroup p P) (hpn : p.Coprime n)
    (χ : C →* Multiplicative (ZMod n)) (f : C →* Multiplicative A)
    (hnA : ∀ a : A, n • a = 0) (σ : C)
    (hχσ : χ σ = Multiplicative.ofAdd (1 : ZMod n)) (hfσ : f σ = 1) :
    ∀ c : C, f c = 1 := by
  have hχP : ∀ u ∈ P, χ u = 1 := by
    intro u hu
    apply pGroup_hom_trivial hP hpn (χ.comp P.subtype) ?_ ⟨u, hu⟩
    intro a
    apply Multiplicative.toAdd.injective
    change n • a.toAdd = (0 : ZMod n)
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hfP : ∀ u ∈ P, f u = 1 := by
    intro u hu
    apply pGroup_hom_trivial hP hpn (f.comp P.subtype) ?_ ⟨u, hu⟩
    intro a
    apply Multiplicative.toAdd.injective
    change n • a.toAdd = (0 : A)
    exact hnA a.toAdd
  let χQ : C ⧸ P →* Multiplicative (ZMod n) := QuotientGroup.lift P χ hχP
  let fQ : C ⧸ P →* Multiplicative A := QuotientGroup.lift P f hfP
  have hQ := cyclic_hom_detect χQ fQ hnA (QuotientGroup.mk σ) hχσ hfσ
  exact fun c => hQ (QuotientGroup.mk c)

end FiniteCyclicDetection

section FiniteLocalInertia

open TauCeti ValuativeRel IntermediateField
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-- PROVED: the prime-to-residue-characteristic quotient of any subgroup of finite
inertia is cyclic. It embeds into the zeroth graded ramification group.
Locators: `LocalField/UnitFiltration/RamificationGroup.lean`,
`isCyclic_ramificationGroupGraded_zero`; `Mathlib/GroupTheory/QuotientGroup/Basic.lean`,
`QuotientGroup.quotientKerEquivRange`. -/
theorem isCyclic_finite_tame_subquotient
    {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
    (A : Subgroup (L ≃ₐ[K] L))
    (hA : A ≤ LocalFieldsRamification.lowerRamificationGroup K L 0) :
    IsCyclic (A ⧸ (LocalFieldsRamification.lowerRamificationGroup K L 1).subgroupOf A) := by
  let G₀ := LocalFieldsRamification.lowerRamificationGroup K L 0
  let G₁ := LocalFieldsRamification.lowerRamificationGroup K L 1
  have hQ : IsCyclic (G₀ ⧸ G₁.subgroupOf G₀) := by
    change IsCyclic (TauCeti.IsLocalRing.RamificationGroupGraded (L ≃ₐ[K] L) 𝒪[L] (0 : ℤ))
    exact TauCeti.isCyclic_ramificationGroupGraded_zero (L := L) (G := L ≃ₐ[K] L)
  let j : A →* G₀ := Subgroup.inclusion hA
  let q : A →* G₀ ⧸ G₁.subgroupOf G₀ := (QuotientGroup.mk' (G₁.subgroupOf G₀)).comp j
  have hker : q.ker = G₁.subgroupOf A := by
    ext a
    change (QuotientGroup.mk (j a) : G₀ ⧸ G₁.subgroupOf G₀) = 1 ↔ a ∈ G₁.subgroupOf A
    exact QuotientGroup.eq_one_iff (j a)
  let e : (A ⧸ G₁.subgroupOf A) ≃* q.range :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange q)
  exact isCyclic_of_injective e.toMonoidHom e.injective

variable {K : Type} [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {σ : Field.absoluteGaloisGroup K}

/-- PROVED: every continuous inertia homomorphism with `n`-torsion coefficients is
determined by its value at a tame element having primitive Kummer value of order `n`.
The proof descends to a finite Galois extension containing the Kummer root. Its first
ramification group is a `p`-group and its zeroth graded group is cyclic; these facts
are proved ramification theorems, not additional printed inputs.
Locators: `LocalField/UnitFiltration/RamificationGroup.lean`,
`isPGroup_ramificationGroup`, `isCyclic_ramificationGroupGraded_zero`;
`Mathlib/FieldTheory/KrullTopology.lean`, `krullTopology_mem_nhds_one_iff_of_normal`;
`Profinite/Basic.lean`, `Subgroup.exists_openNormalSubgroup_comap_le`.
-/
theorem inertiaHom_trivial_of_tame_generator
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hnM : ∀ m : M, n • m = 0) (f : inertiaSubgroup K →ₜ* Multiplicative M)
    (hfσ : f ⟨σ, hσI⟩ = 1) : ∀ i : inertiaSubgroup K, f i = 1 := by
  let χ := tameLog hn hβ hβ0 hζ
  let V : OpenNormalSubgroup (inertiaSubgroup K) :=
    ⟨⟨(f : inertiaSubgroup K →* Multiplicative M).ker,
      (isOpen_discrete ({1} : Set (Multiplicative M))).preimage f.continuous⟩,
      inferInstance⟩
  obtain ⟨U, hUV⟩ := (inertiaSubgroup K).exists_openNormalSubgroup_comap_le V
  let e := algebraicGaloisEquiv K
  let U' := OpenNormalSubgroup.comap U e.symm.toMonoidHom e.symm.continuous
  obtain ⟨E, hE, hEN, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K)
      (U' : Set Gal(AlgebraicClosure K/K))).mp (U'.isOpen.mem_nhds U'.one_mem)
  let : FiniteDimensional K E := hE
  let : Normal K E := hEN
  let B : IntermediateField K (AlgebraicClosure K) := K⟮β⟯
  have : FiniteDimensional K B :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  let L : IntermediateField K (AlgebraicClosure K) := E ⊔ IntermediateField.normalClosure K B (AlgebraicClosure K)
  have : FiniteDimensional K L := inferInstance
  have : Normal K L := inferInstance
  have : IsGalois K L := ⟨⟩
  let : ValuativeRel L := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
  let : TopologicalSpace L := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
  have : IsNonarchimedeanLocalField L :=
    finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
  have : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
  have hβL : β ∈ L :=
    (le_sup_right : IntermediateField.normalClosure K B (AlgebraicClosure K) ≤ L)
      (B.le_normalClosure (IntermediateField.mem_adjoin_simple_self K β))
  let r : Gal(AlgebraicClosure K/K) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let r₀ : inertiaSubgroup K →* (L ≃ₐ[K] L) := r.comp (e.toMonoidHom.comp (inertiaSubgroup K).subtype)
  let A : Subgroup (L ≃ₐ[K] L) := r₀.range
  let rI : inertiaSubgroup K →* A := r₀.rangeRestrict
  have hrI : Function.Surjective rI := r₀.rangeRestrict_surjective
  have hrker : r.ker = L.fixingSubgroup := L.restrictNormalHom_ker
  have hiL : ∀ i : inertiaSubgroup K, rI i = 1 → e i.1 ∈ L.fixingSubgroup := by
    intro i hi
    have hi' : r (e i.1) = 1 := congrArg (fun x : A => x.1) hi
    exact hrker ▸ hi'
  have hfker : rI.ker ≤ (f : inertiaSubgroup K →* Multiplicative M).ker := by
    intro i hi
    have hiE : e i.1 ∈ E.fixingSubgroup :=
      (IntermediateField.fixingSubgroup_antitone (le_sup_left : E ≤ L)) (hiL i hi)
    have hiU' : e i.1 ∈ U' := hEU hiE
    have hiU : i.1 ∈ U := by
      change e.symm (e i.1) ∈ U at hiU'
      simpa only [e.symm_apply_apply] using hiU'
    exact hUV hiU
  have hχker : rI.ker ≤ (χ : inertiaSubgroup K →* Multiplicative (ZMod n)).ker := by
    intro i hi
    have hfix : e i.1 β = β := (hiL i hi) ⟨β, hβL⟩
    change χ i = 1
    rw [tameLog_apply, kummerLog_of_fix hβ hβ0 hζ hfix]
    rfl
  let fA : A →* Multiplicative M := rI.liftOfSurjective hrI ⟨f.toMonoidHom, hfker⟩
  let χA : A →* Multiplicative (ZMod n) := rI.liftOfSurjective hrI ⟨χ.toMonoidHom, hχker⟩
  have hfA : ∀ i : inertiaSubgroup K, fA (rI i) = f i := fun i =>
    rI.liftOfRightInverse_comp_apply _ _ ⟨f.toMonoidHom, hfker⟩ i
  have hχA : ∀ i : inertiaSubgroup K, χA (rI i) = χ i := fun i =>
    rI.liftOfRightInverse_comp_apply _ _ ⟨χ.toMonoidHom, hχker⟩ i
  let G₀ := LocalFieldsRamification.lowerRamificationGroup K L 0
  let G₁ := LocalFieldsRamification.lowerRamificationGroup K L 1
  have hAG₀ : A ≤ G₀ := by
    intro g hg
    obtain ⟨i, rfl⟩ := hg
    exact restrictNormal_mem_lowerRamificationGroup_zero L
      (show e i.1 ∈ inertiaSubgroup K from i.2)
  have : IsCyclic (A ⧸ G₁.subgroupOf A) := isCyclic_finite_tame_subquotient A hAG₀
  let p := ringChar 𝓀[K]
  have : CharP 𝓀[L] p := by
    dsimp [p]
    rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
    exact ringChar.charP 𝓀[L]
  have hG₁ : IsPGroup p G₁ :=
    isPGroup_ramificationGroup (L ≃ₐ[K] L) p (i := 1) (by norm_num)
  let j : G₁.subgroupOf A →* G₁ :=
    { toFun := fun w => ⟨w.1.1, w.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : G₁ => z.1) h))
  have hP : IsPGroup p (G₁.subgroupOf A) := hG₁.of_injective j hj
  have hσχ : χA (rI ⟨σ, hσI⟩) = Multiplicative.ofAdd (1 : ZMod n) :=
    (hχA ⟨σ, hσI⟩).trans (tameLog_generator hn hβ hβ0 hζ hσI)
  have hσf : fA (rI ⟨σ, hσI⟩) = 1 := (hfA ⟨σ, hσI⟩).trans hfσ
  have hzero := hom_trivial_of_cyclic_tame_quotient (G₁.subgroupOf A) hP hn.symm
    χA fA hnM (rI ⟨σ, hσI⟩) hσχ hσf
  exact fun i => (hfA i).symm.trans (hzero (rI i))

end FiniteLocalInertia

section LocalCoordinates

open TauCeti ValuativeRel IntermediateField
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- DEFINITION: the Galois group of the maximal unramified extension of a local field.
Locator: `LocalField/Unramified/Maximal.lean`, `maximalUnramifiedExtension`. -/
abbrev UnramifiedGaloisGroup : Type :=
  Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)

/-- DEFINITION: the continuous restriction from the absolute Galois group to the
maximal unramified extension.
Locator: `LocalField/Unramified/Inertia/Basic.lean`, `restrictMaximalUnramifiedHom`,
`continuous_restrictMaximalUnramifiedHom`. -/
def localUnramifiedProjection : Field.absoluteGaloisGroup K →ₜ* UnramifiedGaloisGroup K :=
  ⟨restrictMaximalUnramifiedHom K, continuous_restrictMaximalUnramifiedHom K⟩

/-- PROVED: the kernel of the unramified projection is inertia.
Locator: `LocalField/Unramified/Inertia/Basic.lean`, `ker_restrictMaximalUnramifiedHom`. -/
theorem localUnramifiedProjection_ker :
    (localUnramifiedProjection K : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker =
      inertiaSubgroup K := ker_restrictMaximalUnramifiedHom K

/-- PROVED: an arithmetic Frobenius lift projects to the topological generator of the
unramified quotient.
Locators: `LocalField/Unramified/ZHat.lean`,
`maximalUnramifiedGaloisGroupEquivZHat_symm_apply_gen`;
`LocalField/Unramified/Inertia/Basic.lean`, `isArithFrobeniusLift_def`. -/
theorem localUnramifiedProjection_frob {φ : Field.absoluteGaloisGroup K}
    (hφ : IsArithFrobeniusLift K φ) :
    localUnramifiedProjection K φ =
      ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt
        (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)) := by
  change restrictMaximalUnramifiedHom K φ =
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).symm zHat.gen
  rw [maximalUnramifiedGaloisGroupEquivZHat_symm_apply_gen]
  exact isArithFrobeniusLift_def.mp hφ

variable {K}
variable [PerfectField K] {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

/-- PROVED: the inertia-vanishing field of the named coordinate input holds for
prime-to-residue-characteristic torsion, with nontrivial Frobenius action allowed.
Locators: `inertiaHom_trivial_of_tame_generator`;
`SwitchInputs/UnrCoords.lean`, `TameCoordinatesUnr.hI`. -/
theorem ev1K_eq_zero_on_local_inertia
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (z : Z1K k (Field.absoluteGaloisGroup K) M)
    (hzσ : ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = 0) :
    ∀ g ∈ inertiaSubgroup K,
      ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) g = 0 := by
  let f : inertiaSubgroup K →ₜ* Multiplicative M :=
    { toFun := fun i => Multiplicative.ofAdd
        (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) i.1)
      map_one' := by
        change Multiplicative.ofAdd (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) 1) = 1
        rw [ev1K_one_unr]
        rfl
      map_mul' := by
        intro g h
        change Multiplicative.ofAdd
          (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) (g.1 * h.1)) = _
        rw [ev1K_mul, hItriv g.1 g.2]
        rfl
      continuous_toFun :=
        (continuous_of_discreteTopology (f := (Multiplicative.ofAdd : M → Multiplicative M))).comp
          ((continuous_ev1K z).comp continuous_subtype_val) }
  have hfσ : f ⟨σ, hσI⟩ = 1 := by
    change Multiplicative.ofAdd
      (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ) = 1
    rw [hzσ]
    rfl
  have hf := inertiaHom_trivial_of_tame_generator hn hβ hβ0 hσI hζ hnM f hfσ
  intro g hg
  exact congrArg Multiplicative.toAdd (hf ⟨g, hg⟩)

/-- PROVED: the unramified tame coordinate map is injective on actual continuous
local cohomology. A zero Frobenius class is removed by a constant coboundary; the
remaining cocycle vanishes on inertia and Frobenius, hence everywhere by continuity.
Locators: `ev1K_eq_zero_on_local_inertia`, `Z1K_eq_zero_of_frobenius_inertia`;
`LocalField/Unramified/Inertia/Basic.lean`,
`IsArithFrobeniusLift.topologicalClosure_zpowers_sup_inertiaSubgroup`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem coordQUnr_injective_local
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) :
    Function.Injective (coordQUnr (k := k) (M := M) φ σ (Nat.card 𝓀[K])
      (hItriv σ hσI) hrel) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have hf := congrArg Prod.fst hx
    have hs := congrArg (fun y : CokerFrob k M φ × KerFrob k M φ (Nat.card 𝓀[K]) => (y.2 : M)) hx
    change (Submodule.Quotient.mk
      (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ) :
      CokerFrob k M φ) = 0 at hf
    rw [Submodule.Quotient.mk_eq_zero] at hf
    obtain ⟨m, hm⟩ := hf
    let w := z - relaxedDK k (Field.absoluteGaloisGroup K) M
      (const0K (k := k) (G := Field.absoluteGaloisGroup K) m)
    have hwφ : ev1K (w : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ = 0 := by
      change ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ -
        ev1K ((relaxedDK k (Field.absoluteGaloisGroup K) M (const0K m) :
          Z1K k (Field.absoluteGaloisGroup K) M) :
          (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ = 0
      rw [relaxedDK_ev, ev0K_const0K, ← hm, frobSub_apply, one_smul, sub_self]
    have hwσ : ev1K (w : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = 0 := by
      change ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ -
        ev1K ((relaxedDK k (Field.absoluteGaloisGroup K) M (const0K m) :
          Z1K k (Field.absoluteGaloisGroup K) M) :
          (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = 0
      rw [relaxedDK_ev, ev0K_const0K, hItriv σ hσI, sub_self, sub_zero]
      exact hs
    have hw : w = 0 := Z1K_eq_zero_of_frobenius_inertia (inertiaSubgroup K) φ
      hφ.topologicalClosure_zpowers_sup_inertiaSubgroup w hwφ
      (ev1K_eq_zero_on_local_inertia hn hβ hβ0 hσI hζ hItriv hnM w hwσ)
    have hz : z = relaxedDK k (Field.absoluteGaloisGroup K) M (const0K m) := sub_eq_zero.mp hw
    rw [hz, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

omit [PerfectField K] in
/-- PROVED: the coordinate map is surjective for finite unramified local coefficients,
without assuming that Frobenius fixes roots of unity.
Locators: `coordQUnr_surjective_of_tame_character`, `tameLog_conj_frobenius`;
`InnerLimitArith/Realization.lean`, `urCondCocycle`. -/
theorem coordQUnr_surjective_local [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) :
    Function.Surjective (coordQUnr (k := k) (M := M) φ σ (Nat.card 𝓀[K])
      (hItriv σ hσI) hrel) := by
  let π := localUnramifiedProjection K
  let e := maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
  have hk : (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker = inertiaSubgroup K :=
    localUnramifiedProjection_ker K
  have hσπ : σ ∈ (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker := by
    rw [hk]
    exact hσI
  have hgen : (Subgroup.zpowers φ ⊔
      (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker).topologicalClosure = ⊤ := by
    rw [hk]
    exact hφ.topologicalClosure_zpowers_sup_inertiaSubgroup
  let χ₀ := tameLog hn hβ hβ0 hζ
  let j : (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker →ₜ* inertiaSubgroup K :=
    { toFun := fun i => ⟨i.1, hk ▸ i.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _ }
  let χ := χ₀.comp j
  have hχσ : χ ⟨σ, hσπ⟩ = Multiplicative.ofAdd (1 : ZMod n) :=
    tameLog_generator hn hβ hβ0 hζ hσI
  have hχφ : ∀ i : (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker,
      χ (inertiaConj (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker φ i) =
        χ i ^ Nat.card 𝓀[K] := by
    intro i
    exact tameLog_conj_frobenius hn hβ hβ0 hζ hφ (j i)
  exact coordQUnr_surjective_of_tame_character e π X f hf hfs φ σ (Nat.card 𝓀[K])
    (localUnramifiedProjection_frob K hφ) hσπ hgen (fun g hg => hItriv g (hk ▸ hg))
    hrel hnM χ hχσ hχφ

/-- PROVED: the named `TameCoordinatesUnr` input is constructed for finite unramified
local coefficients killed by an integer prime to the residue characteristic.
The only presentation equation is the tame relation already required by the input;
no coordinate injectivity, surjectivity, or inertia-detection statement is assumed.
Frobenius is not required to act trivially on the coefficients or on roots of unity.
Locators: `SwitchInputs/UnrCoords.lean`, `TameCoordinatesUnr`;
`coordQUnr_injective_local`, `coordQUnr_surjective_local`, `ev1K_eq_zero_on_local_inertia`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem tameCoordinatesUnr_local [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hnM : ∀ m : M, n • m = 0) (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) :
    TameCoordinatesUnr k M (inertiaSubgroup K) φ σ (Nat.card 𝓀[K]) := by
  have hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m := by
    intro g hg m
    obtain ⟨x, rfl⟩ := hfs m
    have hπg : localUnramifiedProjection K g = 1 := by
      change restrictMaximalUnramifiedHom K g = 1
      rw [← ker_restrictMaximalUnramifiedHom K] at hg
      exact hg
    have hx := hf g x
    rw [hπg, one_smul] at hx
    exact hx.symm
  refine ⟨hItriv, hσI, hrel, ?_, ?_⟩
  · exact ⟨coordQUnr_injective_local hn hβ hβ0 hφ hσI hζ hItriv hnM hrel,
      coordQUnr_surjective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hrel⟩
  · exact ev1K_eq_zero_on_local_inertia hn hβ hβ0 hσI hζ hItriv hnM

end LocalCoordinates

section TameLevel

open TauCeti ValuativeRel IntermediateField
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- DEFINITION: the kernel of the tame level obtained by adjoining a Kummer root to
the maximal unramified extension. Its elements are inertia elements fixing the root.
Locators: `LocalField/Unramified/Inertia/Basic.lean`, `inertiaSubgroup`;
`FieldTheory/Galois/FixedField.lean`, `fixingSubgroup_adjoin_simple`. -/
def tameLevelKernel (β : AlgebraicClosure K) : Subgroup (Field.absoluteGaloisGroup K) :=
  inertiaSubgroup K ⊓ (K⟮β⟯).fixingSubgroup.comap (algebraicGaloisEquiv K).toMonoidHom

/-- PROVED: tame-level kernel membership means inertia membership and root fixedness.
Locator: `tameLevelKernel`; `FieldTheory/Galois/FixedField.lean`,
`fixingSubgroup_adjoin_simple`. -/
theorem mem_tameLevelKernel {β : AlgebraicClosure K} {g : Field.absoluteGaloisGroup K} :
    g ∈ tameLevelKernel K β ↔ g ∈ inertiaSubgroup K ∧ algebraicGaloisEquiv K g β = β := by
  rw [tameLevelKernel, Subgroup.mem_inf, Subgroup.mem_comap,
    IntermediateField.fixingSubgroup_adjoin_simple, MulAction.mem_stabilizer_iff]
  rfl

/-- PROVED: the tame-level kernel is closed in the absolute Galois group.
Locators: `LocalField/Unramified/Inertia/Basic.lean`, `isClosed_inertiaSubgroup`;
`Mathlib/FieldTheory/KrullTopology.lean`, `IntermediateField.fixingSubgroup_isClosed`. -/
theorem isClosed_tameLevelKernel (β : AlgebraicClosure K) :
    IsClosed (tameLevelKernel K β : Set (Field.absoluteGaloisGroup K)) := by
  have : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  exact (isClosed_inertiaSubgroup K).inter
    ((IntermediateField.fixingSubgroup_isClosed K⟮β⟯).preimage (algebraicGaloisEquiv K).continuous)

variable {K} {n : ℕ} [NeZero n] {a : K} {β : AlgebraicClosure K}

omit [NeZero n] in
/-- PROVED: the kernel of a prime-to-residue-characteristic tame level is normal.
An inertia element fixing the chosen root fixes every conjugate of that root, since
inertia fixes the relevant roots of unity.
Locators: `LocalField/Unramified/Inertia/Basic.lean`,
`apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one`;
`TameQuotient/TameCharacter.lean`, `kummerVal_pow`, `apply_eq_kummerVal_mul`. -/
theorem tameLevelKernel_normal (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0) :
    (tameLevelKernel K β).Normal := by
  constructor
  intro t ht g
  obtain ⟨htI, htβ⟩ := (mem_tameLevelKernel K).mp ht
  apply (mem_tameLevelKernel K).mpr
  refine ⟨Subgroup.Normal.conj_mem inferInstance t htI g, ?_⟩
  have hζ : algebraicGaloisEquiv K t (kummerVal β (algebraicGaloisEquiv K g⁻¹)) =
      kummerVal β (algebraicGaloisEquiv K g⁻¹) :=
    apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one
      (show algebraicGaloisEquiv K t ∈ inertiaSubgroup K from htI) hn
      (kummerVal_pow hβ hβ0 (algebraicGaloisEquiv K g⁻¹))
  have htconj : algebraicGaloisEquiv K t (algebraicGaloisEquiv K g⁻¹ β) =
      algebraicGaloisEquiv K g⁻¹ β := by
    rw [apply_eq_kummerVal_mul hβ0, map_mul, hζ, htβ]
  rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, htconj,
    map_inv]
  exact AlgEquiv.apply_symm_apply (algebraicGaloisEquiv K g) β

/-- PROVED: the tame inertia character kills exactly the inertia elements fixing
the Kummer root.
Locators: `tameLog_apply`; `InnerLimitArith/Realization.lean`, `kummerLog_eq_iff`;
`TameQuotient/TameCharacter.lean`, `kummerVal`. -/
theorem tameLog_eq_one_iff (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ : Field.absoluteGaloisGroup K}
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (i : inertiaSubgroup K) :
    tameLog hn hβ hβ0 hζ i = 1 ↔ algebraicGaloisEquiv K i.1 β = β := by
  constructor
  · intro h
    have hk : kummerLog hβ hβ0 hζ (algebraicGaloisEquiv K i.1) = 0 :=
      congrArg Multiplicative.toAdd h
    have hp := (kummerLog_eq_iff hβ hβ0 hζ (algebraicGaloisEquiv K i.1) 0).mp hk
    rw [ZMod.val_zero, pow_zero, kummerVal] at hp
    exact (div_eq_one_iff_eq hβ0).mp hp.symm
  · intro h
    rw [tameLog_apply, kummerLog_of_fix hβ hβ0 hζ h]
    rfl

omit [NeZero n] in
/-- PROVED: the exact tame Frobenius relation holds in the tame level, not merely
on a cohomology class. The two sides agree on the Kummer root and differ by an
inertia element fixing that root.
Locators: `TameQuotient/TameCharacter.lean`, `conj_frobenius_apply_eq_pow_apply`;
`mem_tameLevelKernel`; `Mathlib/GroupTheory/QuotientGroup/Basic.lean`, `QuotientGroup.eq`.
-/
theorem tame_level_frobenius_relation (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {φ σ : Field.absoluteGaloisGroup K} (hφ : IsArithFrobeniusLift K φ)
    (hσI : σ ∈ inertiaSubgroup K) :
    letI : (tameLevelKernel K β).Normal := tameLevelKernel_normal hn hβ hβ0
    (QuotientGroup.mk φ : Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) *
        QuotientGroup.mk σ * (QuotientGroup.mk φ)⁻¹ =
      (QuotientGroup.mk σ) ^ Nat.card 𝓀[K] := by
  let : (tameLevelKernel K β).Normal := tameLevelKernel_normal hn hβ hβ0
  let A := φ * σ * φ⁻¹
  let B := σ ^ Nat.card 𝓀[K]
  have hAI : A ∈ inertiaSubgroup K := Subgroup.Normal.conj_mem inferInstance σ hσI φ
  have hBI : B ∈ inertiaSubgroup K := (inertiaSubgroup K).pow_mem hσI _
  have he : algebraicGaloisEquiv K A β = algebraicGaloisEquiv K B β := by
    change algebraicGaloisEquiv K (φ * σ * φ⁻¹) β =
      algebraicGaloisEquiv K (σ ^ Nat.card 𝓀[K]) β
    rw [map_mul, map_mul, map_inv, map_pow]
    exact conj_frobenius_apply_eq_pow_apply hn hβ hβ0
      (show IsArithFrobeniusLift K (algebraicGaloisEquiv K φ) from hφ)
      (show algebraicGaloisEquiv K σ ∈ inertiaSubgroup K from hσI)
  have hN : A⁻¹ * B ∈ tameLevelKernel K β := by
    apply (mem_tameLevelKernel K).mpr
    refine ⟨(inertiaSubgroup K).mul_mem ((inertiaSubgroup K).inv_mem hAI) hBI, ?_⟩
    rw [map_mul, map_inv, AlgEquiv.mul_apply, ← he]
    exact AlgEquiv.symm_apply_apply (algebraicGaloisEquiv K A) β
  have hq : (QuotientGroup.mk A : Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) =
      QuotientGroup.mk B := QuotientGroup.eq.mpr hN
  let q0 : Field.absoluteGaloisGroup K →* (Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) :=
    QuotientGroup.mk' (tameLevelKernel K β)
  change q0 φ * q0 σ * (q0 φ)⁻¹ = (q0 σ) ^ Nat.card 𝓀[K]
  rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
  exact hq

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- PROVED: the complete named coordinate input holds on the genuine finite-inertia
tame level of a local Galois group. The level is the quotient by inertia elements
fixing a prime-to-residue-characteristic Kummer root. Its inertia is cyclic, its
Frobenius relation is exact, and the coordinates are bijective for every finite
unramified coefficient representation killed by `n`.
No tame relation, topological-generation certificate, or cohomological bijectivity
is an input to this theorem.
Locators: `tameLevelKernel_normal`, `tame_level_frobenius_relation`, `tameLog_eq_one_iff`;
`Profinite/ZHat/Basic.lean`, the profinite Frobenius section;
`SwitchInputs/UnrCoords.lean`, `TameCoordinatesUnr`; manuscript lines 3298–3306, 5026–5037.
-/
theorem tameCoordinatesUnr_tame_level {k : Type} [Field k] [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    [Fact (1 < n)] (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {φ σ : Field.absoluteGaloisGroup K} (hφ : IsArithFrobeniusLift K φ)
    (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hnX : ∀ x : X.V, n • x = 0) :
    ∃ hN : (tameLevelKernel K β).Normal,
      letI : (tameLevelKernel K β).Normal := hN
      ∃ πt : (Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) →ₜ* UnramifiedGaloisGroup K,
        (∀ g : Field.absoluteGaloisGroup K, πt (QuotientGroup.mk g) = localUnramifiedProjection K g) ∧
        TameCoordinatesUnr k (ResMod πt X.V)
          (πt : (Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) →* UnramifiedGaloisGroup K).ker
          (QuotientGroup.mk φ) (QuotientGroup.mk σ) (Nat.card 𝓀[K]) := by
  let N := tameLevelKernel K β
  let hN : N.Normal := tameLevelKernel_normal hn hβ hβ0
  refine ⟨hN, ?_⟩
  let : N.Normal := hN
  have : IsClosed (N : Set (Field.absoluteGaloisGroup K)) := isClosed_tameLevelKernel K β
  let Q := Field.absoluteGaloisGroup K ⧸ N
  let q : Field.absoluteGaloisGroup K →ₜ* Q :=
    ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  let π := localUnramifiedProjection K
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  obtain ⟨πt, hπt⟩ := exists_continuousMonoidHom_factor q hq π (by
    intro g hg
    have hgN : g ∈ N := (QuotientGroup.eq_one_iff g).mp hg
    have hgI := ((mem_tameLevelKernel K).mp hgN).1
    change restrictMaximalUnramifiedHom K g = 1
    rw [← ker_restrictMaximalUnramifiedHom K] at hgI
    exact hgI)
  have hcomp : ∀ g : Field.absoluteGaloisGroup K, πt (q g) = π g :=
    fun g => (hπt g).symm
  refine ⟨πt, hcomp, ?_⟩
  let I := (πt : Q →* UnramifiedGaloisGroup K).ker
  have hσt : q σ ∈ I := by
    change πt (q σ) = 1
    rw [hcomp]
    change restrictMaximalUnramifiedHom K σ = 1
    rw [← ker_restrictMaximalUnramifiedHom K] at hσI
    exact hσI
  have hqI : ∀ i : inertiaSubgroup K, q i.1 ∈ I := by
    intro i
    change πt (q i.1) = 1
    rw [hcomp]
    change restrictMaximalUnramifiedHom K i.1 = 1
    exact (ker_restrictMaximalUnramifiedHom K).symm.le i.2
  let ψ : inertiaSubgroup K →ₜ* I :=
    { toFun := fun i => ⟨q i.1, hqI i⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' i j := Subtype.ext (map_mul q i.1 j.1)
      continuous_toFun := (q.continuous.comp continuous_subtype_val).subtype_mk hqI }
  have hψ : Function.Surjective ψ := by
    intro i
    obtain ⟨g, hg⟩ := hq i.1
    have hgπ : π g = 1 := by
      rw [← hcomp g, hg]
      exact i.2
    have hgI : g ∈ inertiaSubgroup K := by
      rw [← localUnramifiedProjection_ker K]
      exact hgπ
    exact ⟨⟨g, hgI⟩, Subtype.ext hg⟩
  have : IsClosed (inertiaSubgroup K : Set (Field.absoluteGaloisGroup K)) := isClosed_inertiaSubgroup K
  let χ₀ := tameLog hn hβ hβ0 hζ
  obtain ⟨χ, hχcomp⟩ := exists_continuousMonoidHom_factor ψ hψ χ₀ (by
    intro i hi
    have hiq : q i.1 = 1 := congrArg (fun x : I => x.1) hi
    have hiN : i.1 ∈ N := (QuotientGroup.eq_one_iff i.1).mp hiq
    exact (tameLog_eq_one_iff hn hβ hβ0 hζ i).mpr ((mem_tameLevelKernel K).mp hiN).2)
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨i, rfl⟩ := hψ y
    have hci : χ₀ i = 1 := (hχcomp i).trans hy
    have hiN : i.1 ∈ N := (mem_tameLevelKernel K).mpr
      ⟨i.2, (tameLog_eq_one_iff hn hβ hβ0 hζ i).mp hci⟩
    exact Subtype.ext ((QuotientGroup.eq_one_iff i.1).mpr hiN)
  have hχσ : χ (⟨q σ, hσt⟩ : I) = Multiplicative.ofAdd (1 : ZMod n) :=
    (hχcomp ⟨σ, hσI⟩).symm.trans (tameLog_generator hn hβ hβ0 hζ hσI)
  have hIle : I ≤ Subgroup.zpowers (q σ) := by
    intro g hg
    let i : I := ⟨g, hg⟩
    let m := (χ i).toAdd.val
    have hm : (Multiplicative.ofAdd (1 : ZMod n)) ^ m = χ i := by
      apply Multiplicative.toAdd.injective
      change m • (1 : ZMod n) = (χ i).toAdd
      rw [nsmul_eq_mul, mul_one]
      exact ZMod.natCast_zmod_val _
    have hi : (⟨q σ, hσt⟩ : I) ^ m = i := hχinj (by rw [map_pow, hχσ, hm])
    have hval : q σ ^ m = g := congrArg (fun x : I => x.1) hi
    exact hval ▸ (Subgroup.zpowers (q σ)).pow_mem (Subgroup.mem_zpowers (q σ)) m
  have hψconj (i : inertiaSubgroup K) :
      ψ (inertiaConj (inertiaSubgroup K) φ i) = inertiaConj I (q φ) (ψ i) := by
    apply Subtype.ext
    change q (φ * i.1 * φ⁻¹) = q φ * q i.1 * (q φ)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hχφ : ∀ i : I, χ (inertiaConj I (q φ) i) = χ i ^ Nat.card 𝓀[K] := by
    intro y
    obtain ⟨i, rfl⟩ := hψ y
    calc
      χ (inertiaConj I (q φ) (ψ i)) = χ (ψ (inertiaConj (inertiaSubgroup K) φ i)) :=
        congrArg χ (hψconj i).symm
      _ = χ₀ (inertiaConj (inertiaSubgroup K) φ i) := (hχcomp _).symm
      _ = χ₀ i ^ Nat.card 𝓀[K] := tameLog_conj_frobenius hn hβ hβ0 hζ hφ i
      _ = χ (ψ i) ^ Nat.card 𝓀[K] := congrArg (fun c => c ^ Nat.card 𝓀[K]) (hχcomp i)
  have hle : (Subgroup.zpowers φ ⊔ inertiaSubgroup K).map (q : Field.absoluteGaloisGroup K →* Q) ≤
      Subgroup.zpowers (q φ) ⊔ I := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply sup_le
    · apply Subgroup.zpowers_le.mpr
      change q φ ∈ Subgroup.zpowers (q φ) ⊔ I
      exact (le_sup_left : Subgroup.zpowers (q φ) ≤ Subgroup.zpowers (q φ) ⊔ I)
        (Subgroup.mem_zpowers (q φ))
    · intro g hg
      change q g ∈ Subgroup.zpowers (q φ) ⊔ I
      apply (le_sup_right : I ≤ Subgroup.zpowers (q φ) ⊔ I)
      change πt (q g) = 1
      rw [hcomp]
      change restrictMaximalUnramifiedHom K g = 1
      rw [← ker_restrictMaximalUnramifiedHom K] at hg
      exact hg
  have hqdense : DenseRange (q : Field.absoluteGaloisGroup K →* Q) := hq.denseRange
  have hgenmap := DenseRange.topologicalClosure_map_subgroup q.continuous hqdense
    hφ.topologicalClosure_zpowers_sup_inertiaSubgroup
  have hgen : (Subgroup.zpowers (q φ) ⊔ I).topologicalClosure = ⊤ :=
    top_le_iff.mp (hgenmap ▸ Subgroup.topologicalClosure_mono hle)
  have hrel : q φ * q σ * (q φ)⁻¹ = q σ ^ Nat.card 𝓀[K] :=
    tame_level_frobenius_relation hn hβ hβ0 hφ hσI
  let f : X.V →ₗ[k] ResMod πt X.V := toResMod (k := k) πt
  have hf : ∀ (g : Q) (x : X.V), f (πt g • x) = g • f x := fun _ _ => rfl
  have hfs : Function.Surjective f := fun m => ⟨(show X.V from m), rfl⟩
  have hItriv : ∀ g ∈ I, ∀ m : ResMod πt X.V, g • m = m := by
    intro g hg m
    change πt g • (show X.V from m) = m
    rw [show πt g = 1 from hg, one_smul]
  have hnM : ∀ m : ResMod πt X.V, n • m = 0 := fun m => hnX (show X.V from m)
  have hP : TauCeti.IsProP (ringChar 𝓀[K]) (⊥ : Subgroup Q) := IsPGroup.of_bot.isProP
  have hgenI : I ≤ ((⊥ : Subgroup Q) ⊔ Subgroup.zpowers (q σ)).topologicalClosure := by
    exact hIle.trans
      ((le_sup_right : Subgroup.zpowers (q σ) ≤ (⊥ : Subgroup Q) ⊔ Subgroup.zpowers (q σ)).trans
        (Subgroup.le_topologicalClosure _))
  exact tameCoordinatesUnr_of_proP
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)) πt X f hf hfs
    (q φ) (q σ) (Nat.card 𝓀[K])
    ((hcomp φ).trans (localUnramifiedProjection_frob K hφ)) hσt hgen hItriv hrel
    (⊥ : Subgroup Q) hP hn.symm bot_le hgenI hnM χ hχσ hχφ

/-- PROVED: finite unramified local coefficients of exponent prime to the residue
characteristic have genuine tame levels with the complete named coordinate input.
A root of a uniformizer supplies the normalized tame character; Frobenius lifts exist.
Locators: `TameQuotient/TameCharacter.lean`, `exists_tame_generator`;
`LocalField/Unramified/Inertia/Basic.lean`, `exists_isArithFrobeniusLift`;
`tameCoordinatesUnr_tame_level`; manuscript lines 3298–3306 and 5026–5037. -/
theorem exists_tameCoordinatesUnr_tame_level {k : Type} [Field k] [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    [Fact (1 < n)] (hn : n.Coprime (ringChar 𝓀[K])) (hnX : ∀ x : X.V, n • x = 0) :
    ∃ (ϖ : Kˣ) (β : AlgebraicClosure K) (φ σ : Field.absoluteGaloisGroup K),
      IsUniformizer K ϖ ∧ β ^ n = algebraMap K (AlgebraicClosure K) (ϖ : K) ∧
      IsArithFrobeniusLift K φ ∧ σ ∈ inertiaSubgroup K ∧
      ∃ hN : (tameLevelKernel K β).Normal,
        letI : (tameLevelKernel K β).Normal := hN
        ∃ πt : (Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) →ₜ* UnramifiedGaloisGroup K,
          (∀ g : Field.absoluteGaloisGroup K, πt (QuotientGroup.mk g) = localUnramifiedProjection K g) ∧
          TameCoordinatesUnr k (ResMod πt X.V)
            (πt : (Field.absoluteGaloisGroup K ⧸ tameLevelKernel K β) →* UnramifiedGaloisGroup K).ker
            (QuotientGroup.mk φ) (QuotientGroup.mk σ) (Nat.card 𝓀[K]) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (ϖ : K)) (Nat.pos_of_ne_zero (NeZero.ne n))
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne n)] at hβ
    exact ϖ.ne_zero ((map_eq_zero _).mp hβ.symm)
  have hv : (normalizedValuation K (Units.mk0 (ϖ : K) ϖ.ne_zero)).toAdd = 1 := by
    rw [show Units.mk0 (ϖ : K) ϖ.ne_zero = ϖ from Units.ext rfl,
      (isUniformizer_def ϖ).mp hϖ, toAdd_ofAdd]
  obtain ⟨σ₀, hσ₀, hζ₀⟩ := exists_tame_generator hn hβ hβ0 ϖ.ne_zero hv
  obtain ⟨φ, hφ⟩ := exists_isArithFrobeniusLift K
  let σ : Field.absoluteGaloisGroup K := (algebraicGaloisEquiv K).symm σ₀
  have hσI : σ ∈ inertiaSubgroup K := hσ₀
  have hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n := by
    rw [show algebraicGaloisEquiv K σ = σ₀ from (algebraicGaloisEquiv K).apply_symm_apply σ₀]
    exact hζ₀
  exact ⟨ϖ, β, φ, σ, hϖ, hβ, hφ, hσI,
    tameCoordinatesUnr_tame_level X hn hβ hβ0 hφ hσI hζ hnX⟩

end TameLevel

section OddPlace

open TauCeti ValuativeRel NumberField IsDedekindDomain

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- PROVED: at a finite place of a number field not above `2`, every finite
unramified coefficient representation killed by `2^i`, `i > 0`, has genuine tame
levels satisfying `TameCoordinatesUnr`. No roots-of-unity fixedness by Frobenius and
no cohomological coordinate input are assumed.
Locators: `InnerLimitArith/Realization.lean`, `exists_tameCoord_surjective_at`, the
residue-characteristic coprimality argument; `exists_tameCoordinatesUnr_tame_level`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem exists_tameCoordinatesUnr_at {K₀ : Type} [Field K₀] [NumberField K₀]
    (w : HeightOneSpectrum (𝓞 K₀)) (h2 : (2 : 𝓞 K₀) ∉ w.asIdeal)
    {i : ℕ} (hi : i ≠ 0) {k : Type} [Field k] [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup (w.adicCompletion K₀)))
    [ContinuousSMul (UnramifiedGaloisGroup (w.adicCompletion K₀)) X.V]
    [DiscreteTopology X.V] [Finite X.V]
    (hnX : ∀ x : X.V, (2 ^ i) • x = 0) :
    ∃ (ϖ : (w.adicCompletion K₀)ˣ) (β : AlgebraicClosure (w.adicCompletion K₀))
      (φ σ : Field.absoluteGaloisGroup (w.adicCompletion K₀)),
      IsUniformizer (w.adicCompletion K₀) ϖ ∧
      β ^ (2 ^ i) = algebraMap (w.adicCompletion K₀) (AlgebraicClosure (w.adicCompletion K₀)) (ϖ : w.adicCompletion K₀) ∧
      IsArithFrobeniusLift (w.adicCompletion K₀) φ ∧ σ ∈ inertiaSubgroup (w.adicCompletion K₀) ∧
      ∃ hN : (tameLevelKernel (w.adicCompletion K₀) β).Normal,
        letI : (tameLevelKernel (w.adicCompletion K₀) β).Normal := hN
        ∃ πt : (Field.absoluteGaloisGroup (w.adicCompletion K₀) ⧸
            tameLevelKernel (w.adicCompletion K₀) β) →ₜ* UnramifiedGaloisGroup (w.adicCompletion K₀),
          (∀ g : Field.absoluteGaloisGroup (w.adicCompletion K₀),
            πt (QuotientGroup.mk g) = localUnramifiedProjection (w.adicCompletion K₀) g) ∧
          TameCoordinatesUnr k (ResMod πt X.V)
            (πt : (Field.absoluteGaloisGroup (w.adicCompletion K₀) ⧸
              tameLevelKernel (w.adicCompletion K₀) β) →* UnramifiedGaloisGroup (w.adicCompletion K₀)).ker
            (QuotientGroup.mk φ) (QuotientGroup.mk σ) (Nat.card 𝓀[w.adicCompletion K₀]) := by
  let : NeZero (2 ^ i) := ⟨pow_ne_zero _ two_ne_zero⟩
  let : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  have hp : (ringChar 𝓀[w.adicCompletion K₀]).Prime := CharP.prime_ringChar 𝓀[w.adicCompletion K₀]
  have hnd : ¬ ringChar 𝓀[w.adicCompletion K₀] ∣ 2 := by
    rw [IsDedekindDomain.HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hcop : (2 ^ i).Coprime (ringChar 𝓀[w.adicCompletion K₀]) :=
    Nat.Coprime.pow_left i ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  exact exists_tameCoordinatesUnr_tame_level X hcop hnX

end OddPlace

section InertiaFormula

open TauCeti ValuativeRel

variable {K : Type} [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {M : Type} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K}
  {β : AlgebraicClosure K} {σ : Field.absoluteGaloisGroup K}

/-- PROVED: every continuous `n`-torsion inertia homomorphism is its value at the tame
generator multiplied by the normalized tame character. This proves factorization,
not just detection at zero.
Locators: `inertiaHom_trivial_of_tame_generator`, `tameLog_generator`, `cyclicMultiple`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem inertiaHom_tameLog_formula (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hnM : ∀ m : M, n • m = 0) (f : inertiaSubgroup K →ₜ* Multiplicative M) :
    ∀ i : inertiaSubgroup K, f i =
      cyclicMultiple (f ⟨σ, hσI⟩).toAdd (hnM (f ⟨σ, hσI⟩).toAdd) (tameLog hn hβ hβ0 hζ i) := by
  let g := (cyclicMultiple (f ⟨σ, hσI⟩).toAdd (hnM (f ⟨σ, hσI⟩).toAdd)).comp
    (tameLog hn hβ hβ0 hζ)
  let d : inertiaSubgroup K →ₜ* Multiplicative M := f / g
  have hdσ : d ⟨σ, hσI⟩ = 1 := by
    change f ⟨σ, hσI⟩ /
      cyclicMultiple (f ⟨σ, hσI⟩).toAdd (hnM (f ⟨σ, hσI⟩).toAdd)
        (tameLog hn hβ hβ0 hζ ⟨σ, hσI⟩) = 1
    rw [tameLog_generator, cyclicMultiple_one]
    change f ⟨σ, hσI⟩ / f ⟨σ, hσI⟩ = 1
    rw [div_eq_mul_inv, mul_inv_cancel]
  have hd := inertiaHom_trivial_of_tame_generator hn hβ hβ0 hσI hζ hnM d hdσ
  intro i
  have hi : f i / g i = 1 := hd i
  have he := congrArg (fun x : Multiplicative M => x * g i) hi
  change f i = g i
  simpa only [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one, one_mul] using he

end InertiaFormula

section ActualCoordinates

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {K : Type} [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

/-- DEFINITION: a continuous cocycle restricted to trivially acting inertia, read as
a continuous homomorphism.
Locators: `SwitchInputs/UnrCoords.lean`, `ev1K_mul`, `ev1K_one_unr`;
`continuous_ev1K`. -/
def cocycleInertiaHom (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (z : Z1K k (Field.absoluteGaloisGroup K) M) : inertiaSubgroup K →ₜ* Multiplicative M where
  toFun i := Multiplicative.ofAdd
    (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) i.1)
  map_one' := by
    change Multiplicative.ofAdd
      (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) 1) = 1
    rw [ev1K_one_unr]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd
      (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) (g.1 * h.1)) = _
    rw [ev1K_mul, hItriv g.1 g.2]
    rfl
  continuous_toFun :=
    (continuous_of_discreteTopology (f := (Multiplicative.ofAdd : M → Multiplicative M))).comp
      ((continuous_ev1K z).comp continuous_subtype_val)

/-- PROVED: every continuous unramified-module cocycle with `n`-torsion coefficients
vanishes on the tame-level kernel, including the wild part. No vanishing-on-wild-inertia
hypothesis is assumed.
Locators: `inertiaHom_tameLog_formula`, `tameLog_eq_one_iff`, `mem_tameLevelKernel`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem ev1K_eq_zero_on_tame_kernel (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (z : Z1K k (Field.absoluteGaloisGroup K) M) :
    ∀ g ∈ tameLevelKernel K β,
      ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) g = 0 := by
  let f := cocycleInertiaHom hItriv z
  have hf := inertiaHom_tameLog_formula hn hβ hβ0 hσI hζ hnM f
  intro g hg
  obtain ⟨hgI, hgβ⟩ := (mem_tameLevelKernel K).mp hg
  have hχ : tameLog hn hβ hβ0 hζ ⟨g, hgI⟩ = 1 :=
    (tameLog_eq_one_iff hn hβ hβ0 hζ ⟨g, hgI⟩).mpr hgβ
  have he : f ⟨g, hgI⟩ = 1 := (hf ⟨g, hgI⟩).trans (by rw [hχ, map_one])
  exact congrArg Multiplicative.toAdd he

/-- PROVED: the actual local tame value belongs to `ker(Φ-q)`, even though the exact
tame group relation need not hold in the absolute Galois group. The finite tame character
and the cocycle identity prove the relation on cocycle values.
Locators: `inertiaHom_tameLog_formula`, `tameLog_conj_frobenius`;
`SwitchInputs/UnrCoords.lean`, `ev1K_inv_unr`, `frobSub`;
manuscript lines 3298–3306 and 5026–5037. -/
theorem ev1K_sigma_mem_ker_local (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (z : Z1K k (Field.absoluteGaloisGroup K) M) :
    ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ ∈
      KerFrob k M φ (Nat.card 𝓀[K]) := by
  let f := cocycleInertiaHom hItriv z
  let i : inertiaSubgroup K := ⟨σ, hσI⟩
  let m := ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ
  have hf := inertiaHom_tameLog_formula hn hβ hβ0 hσI hζ hnM f
  have hc : f (inertiaConj (inertiaSubgroup K) φ i) = Multiplicative.ofAdd ((Nat.card 𝓀[K]) • m) := by
    refine (hf _).trans ?_
    change cyclicMultiple m (hnM m)
      (tameLog hn hβ hβ0 hζ (inertiaConj (inertiaSubgroup K) φ i)) = _
    rw [tameLog_conj_frobenius hn hβ hβ0 hζ hφ i, tameLog_generator,
      map_pow, cyclicMultiple_one]
    rfl
  have hq : ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1)
      (φ * σ * φ⁻¹) = (Nat.card 𝓀[K]) • m := congrArg Multiplicative.toAdd hc
  have hconj : ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1)
      (φ * σ * φ⁻¹) = φ • m := by
    rw [ev1K_mul, ev1K_mul, ev1K_inv_unr, smul_neg, ← mul_smul,
      hItriv (φ * σ * φ⁻¹) (Subgroup.Normal.conj_mem inferInstance σ hσI φ)]
    abel
  rw [LinearMap.mem_ker, frobSub_apply, Nat.cast_smul_eq_nsmul]
  change φ • m - (Nat.card 𝓀[K]) • m = 0
  rw [← hconj, hq, sub_self]

/-- DEFINITION: actual local cocycle coordinates, using the proved tame-value relation
rather than assuming an exact presentation of the absolute Galois group.
Locators: `ev1K_sigma_mem_ker_local`; `SwitchInputs/UnrCoords.lean`, `coordLUnr`. -/
def coordLLocal (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) :
    Z1K k (Field.absoluteGaloisGroup K) M →ₗ[k] CokerFrob k M φ × KerFrob k M φ (Nat.card 𝓀[K]) :=
  ((LinearMap.range (frobSub k M φ 1)).mkQ ∘ₗ ev1LK φ ∘ₗ
    (Z1K k (Field.absoluteGaloisGroup K) M).subtype).prod
    (LinearMap.codRestrict (KerFrob k M φ (Nat.card 𝓀[K]))
      (ev1LK σ ∘ₗ (Z1K k (Field.absoluteGaloisGroup K) M).subtype)
      fun z => ev1K_sigma_mem_ker_local hn hβ hβ0 hφ hσI hζ hItriv hnM z)

/-- PROVED: actual local cocycle coordinates kill coboundaries.
Locators: `SwitchInputs/UnrCoords.lean`, `relaxedDK_ev`, `frobSub_apply`;
`coordLLocal`. -/
theorem coordLLocal_relaxedD (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (c : (contCochains k (Field.absoluteGaloisGroup K) M).X 0) :
    coordLLocal hn hβ hβ0 hφ hσI hζ hItriv hnM
      (relaxedDK k (Field.absoluteGaloisGroup K) M c) = 0 := by
  apply Prod.ext
  · change (Submodule.Quotient.mk
      (ev1K ((relaxedDK k (Field.absoluteGaloisGroup K) M c :
        Z1K k (Field.absoluteGaloisGroup K) M) :
        (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ) : CokerFrob k M φ) = 0
    rw [Submodule.Quotient.mk_eq_zero, relaxedDK_ev]
    exact ⟨ev0K c, by rw [frobSub_apply, one_smul]⟩
  · apply Subtype.ext
    change ev1K ((relaxedDK k (Field.absoluteGaloisGroup K) M c :
      Z1K k (Field.absoluteGaloisGroup K) M) :
      (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = 0
    rw [relaxedDK_ev, hItriv σ hσI, sub_self]

/-- DEFINITION: the actual local cohomology coordinates
`[z] ↦ (z(φ) mod (Φ-1)M, z(σ))`. They are defined without any group-level tame-relation
assumption.
Locators: `coordLLocal_relaxedD`; `SwitchInputs/UnrCoords.lean`, `H1WrelK`, `coordQUnr`.
-/
def coordQLocal (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) :
    H1WrelK k (Field.absoluteGaloisGroup K) M →ₗ[k] CokerFrob k M φ × KerFrob k M φ (Nat.card 𝓀[K]) :=
  (LinearMap.range (relaxedDK k (Field.absoluteGaloisGroup K) M)).liftQ
    (coordLLocal hn hβ hβ0 hφ hσI hζ hItriv hnM) (by
      rintro _ ⟨c, rfl⟩
      exact LinearMap.mem_ker.mpr (coordLLocal_relaxedD hn hβ hβ0 hφ hσI hζ hItriv hnM c))

/-- PROVED: actual local cohomology coordinates evaluate as the stated pair.
Locator: `coordQLocal`, `coordLLocal`. -/
theorem coordQLocal_mk (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (z : Z1K k (Field.absoluteGaloisGroup K) M) :
    coordQLocal hn hβ hβ0 hφ hσI hζ hItriv hnM (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk
        (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ),
        ⟨ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ,
          ev1K_sigma_mem_ker_local hn hβ hβ0 hφ hσI hζ hItriv hnM z⟩) := rfl

/-- PROVED: the actual local cohomology coordinate map is injective, without an
exact tame-relation assumption on the absolute Galois group.
Locators: `coordQLocal_mk`, `ev1K_eq_zero_on_local_inertia`,
`Z1K_eq_zero_of_frobenius_inertia`; manuscript lines 3298–3306 and 5026–5037. -/
theorem coordQLocal_injective (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) :
    Function.Injective (coordQLocal (k := k) hn hβ hβ0 hφ hσI hζ hItriv hnM) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have hf := congrArg Prod.fst hx
    have hs := congrArg (fun y : CokerFrob k M φ × KerFrob k M φ (Nat.card 𝓀[K]) => (y.2 : M)) hx
    change (Submodule.Quotient.mk
      (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ) :
      CokerFrob k M φ) = 0 at hf
    rw [Submodule.Quotient.mk_eq_zero] at hf
    obtain ⟨m, hm⟩ := hf
    let w := z - relaxedDK k (Field.absoluteGaloisGroup K) M
      (const0K (k := k) (G := Field.absoluteGaloisGroup K) m)
    have hwφ : ev1K (w : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ = 0 := by
      change ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ -
        ev1K ((relaxedDK k (Field.absoluteGaloisGroup K) M (const0K m) :
          Z1K k (Field.absoluteGaloisGroup K) M) :
          (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ = 0
      rw [relaxedDK_ev, ev0K_const0K, ← hm, frobSub_apply, one_smul, sub_self]
    have hwσ : ev1K (w : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = 0 := by
      change ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ -
        ev1K ((relaxedDK k (Field.absoluteGaloisGroup K) M (const0K m) :
          Z1K k (Field.absoluteGaloisGroup K) M) :
          (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = 0
      rw [relaxedDK_ev, ev0K_const0K, hItriv σ hσI, sub_self, sub_zero]
      exact hs
    have hw : w = 0 := Z1K_eq_zero_of_frobenius_inertia (inertiaSubgroup K) φ
      hφ.topologicalClosure_zpowers_sup_inertiaSubgroup w hwφ
      (ev1K_eq_zero_on_local_inertia hn hβ hβ0 hσI hζ hItriv hnM w hwσ)
    have hz : z = relaxedDK k (Field.absoluteGaloisGroup K) M (const0K m) := sub_eq_zero.mp hw
    rw [hz, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

omit [PerfectField K] in
/-- PROVED: actual local continuous cocycles realize every compatible coordinate pair,
without assuming the exact tame group relation in the absolute Galois group.
Locators: `exists_Z1K_with_coordinates`, `tameLog_conj_frobenius`,
`localUnramifiedProjection_frob`; manuscript lines 3298–3306 and 5026–5037. -/
theorem exists_Z1K_local [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (b : M) (m : KerFrob k M φ (Nat.card 𝓀[K])) :
    ∃ z : Z1K k (Field.absoluteGaloisGroup K) M,
      ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ = b ∧
      ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) σ = (m : M) := by
  let π := localUnramifiedProjection K
  let e := maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
  have hk : (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker = inertiaSubgroup K :=
    localUnramifiedProjection_ker K
  have hσπ : σ ∈ (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker := hk.symm.le hσI
  have hgen : (Subgroup.zpowers φ ⊔
      (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker).topologicalClosure = ⊤ := by
    rw [hk]
    exact hφ.topologicalClosure_zpowers_sup_inertiaSubgroup
  let χ₀ := tameLog hn hβ hβ0 hζ
  let j : (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker →ₜ* inertiaSubgroup K :=
    { toFun := fun i => ⟨i.1, hk.le i.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      continuous_toFun := continuous_subtype_val.subtype_mk (fun i => hk.le i.2) }
  let χ := χ₀.comp j
  have hχσ : χ ⟨σ, hσπ⟩ = Multiplicative.ofAdd (1 : ZMod n) :=
    tameLog_generator hn hβ hβ0 hζ hσI
  have hχφ : ∀ i : (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker,
      χ (inertiaConj (π : Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker φ i) =
        χ i ^ Nat.card 𝓀[K] := fun i => tameLog_conj_frobenius hn hβ hβ0 hζ hφ (j i)
  exact exists_Z1K_with_coordinates e π X f hf hfs φ σ (Nat.card 𝓀[K])
    (localUnramifiedProjection_frob K hφ) hσπ hgen (fun g hg => hItriv g (hk.le hg))
    hnM χ hχσ hχφ b m

/-- PROVED: the actual local cohomology coordinate map is onto its stated target.
Locators: `exists_Z1K_local`, `coordQLocal_mk`; manuscript lines 3298–3306 and 5026–5037.
-/
theorem coordQLocal_surjective [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) :
    Function.Surjective (coordQLocal (k := k) hn hβ hβ0 hφ hσI hζ hItriv hnM) := by
  rintro ⟨c, m⟩
  induction c using Submodule.Quotient.induction_on with
  | H b =>
    obtain ⟨z, hzφ, hzσ⟩ := exists_Z1K_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM b m
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [coordQLocal_mk]
    apply Prod.ext
    · change (Submodule.Quotient.mk
        (ev1K (z : (contCochains k (Field.absoluteGaloisGroup K) M).X 1) φ) :
        CokerFrob k M φ) = Submodule.Quotient.mk b
      rw [hzφ]
    · exact Subtype.ext hzσ

/-- PROVED: the actual continuous local cohomology has bijective unramified tame
coordinates. Only inertia acts trivially; Frobenius may act nontrivially. No group-level
tame relation or cohomological coordinate input is assumed.
Locators: `coordQLocal_injective`, `coordQLocal_surjective`; manuscript lines 3298–3306
and 5026–5037. -/
theorem coordQLocal_bijective [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) :
    Function.Bijective (coordQLocal (k := k) hn hβ hβ0 hφ hσI hζ hItriv hnM) :=
  ⟨coordQLocal_injective hn hβ hβ0 hφ hσI hζ hItriv hnM,
    coordQLocal_surjective X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM⟩

/-- PROVED: whenever an exact tame relation is supplied, the actual local coordinate
map is exactly the existing named coordinate map, not just an abstract isomorphism.
Locators: `coordQLocal`; `SwitchInputs/UnrCoords.lean`, `coordQUnr`.
-/
theorem coordQLocal_eq_coordQUnr (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) :
    coordQLocal (k := k) hn hβ hβ0 hφ hσI hζ hItriv hnM =
      coordQUnr (k := k) (M := M) φ σ (Nat.card 𝓀[K]) (hItriv σ hσI) hrel := rfl

end ActualCoordinates

end ZInQ.Contrib.RC53Assist.TameBijective
