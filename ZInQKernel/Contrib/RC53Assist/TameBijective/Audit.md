# Unramified tame coordinates: finite-exponent proof and audit

## Result

The coordinate map is

`[z] ↦ (z(φ) mod (Φ − 1)M, z(σ)) : H¹_cont(G_K,M) → M/(Φ − 1)M × ker(Φ − q)`.

For the discrete, prime-to-residue-characteristic torsion setting in the exact statements below, it is bijective. Inertia acts trivially, but Frobenius need not act trivially. No cohomological coordinate bijectivity or inertia-detection result is assumed.

Principal exports:

- `coordQLocal_bijective`: bijectivity on actual continuous local cohomology, without an exact tame group relation in the absolute Galois group.
- `coordQLocal_eq_coordQUnr`: this actual map equals the existing named coordinate map whenever its group-level relation is available.
- `tameCoordinatesUnr_tame_level`: the complete named `TameCoordinatesUnr` input on the genuine finite-inertia tame quotient by inertia elements fixing a prime-to-residue-characteristic Kummer root. The exact Frobenius relation and topological generation are proved, not supplied.
- `exists_tameCoordinatesUnr_at`: genuine tame levels with that complete input at every place of a number field not above `2`, for positive `2`-power precision and the finite unramified coefficient representations stated below.
- `inertiaHom_trivial_of_tame_generator` and `inertiaHom_tameLog_formula`: the injection and factorization argument for continuous inertia homomorphisms. It descends to a finite Galois extension, kills its first ramification group by the proved `p`-group theorem, and uses cyclicity of the zeroth graded ramification group. No new printed local-cohomology assertion is used.

The raw absolute Galois group is not asserted to satisfy the exact tame presentation. That relation is proved in the genuine tame quotient. The actual absolute-Galois coordinate map is separately defined and proved bijective.

## Scope and what remains

- The actual-cohomology results use discrete coefficients killed by an integer `n` prime to the residue characteristic. Surjectivity uses the finite unramified coefficient model and the surjective coefficient map explicitly quantified in each statement.
- The finite-ramification injection proof uses a perfect local field; this includes completions of number fields. The genuine tame-level construction itself does not require that extra hypothesis.
- The scalar field assumption in the named input is preserved. The inertia-homomorphism lemmas themselves only require an additive group, so they can also be used at finite coefficient-ring stages.
- No comparison with non-discrete or completed coefficients, and no compatibility or inverse-limit comparison across coefficient stages, is proved here.
- Incorporation into the fixed RC53 assembly still requires choosing the corresponding group and coefficient identifications. A caller using the raw absolute Galois group must use the actual coordinate map or the tame-quotient comparison; its exact group relation is not silently assumed.
- Existing source files and assemblies were not edited, and no commit or repository operation was made. An independent review remains.

## Verification

Source: `ZInQKernel/Contrib/RC53Assist/TameBijective/CoordinateInjectivity.lean`

- Source SHA256: `deb08f38d4f441b1636abe38a486b06c1c3433645a8803f43d6456af42ce3f22`
- Source size: `104649` bytes
- Toolchain pin: `leanprover/lean4:v4.35.0`
- Supplied integration base: `3b0ffbb9` (the identifier from the work brief; no repository command was used to re-query it)
- Final single-file compilation: exit code `0`, no errors or warnings; source hashes before and after the run matched.
- Separate declaration audit: exit code `0`, no diagnostics, all `68` named declarations included exactly once (`54` theorems and `14` definitions).
- Every dependency report uses only `propext`, `Classical.choice`, and `Quot.sound`. Lean prints universe-instantiated forms such as `Classical.choice.{u}`; only those suffixes are removed for allowlist comparison, and the verbatim output is retained below.
- Raw declaration-audit SHA256: `94af9d2c88f1383a81a86aa30e1f8b3db23d4d9a569529afca350ba15b544be3`
- No forbidden proof shortcut or new logical assumption appears in the source. Every declaration has a kind-labelled, source-located docstring. The maximum heartbeat setting is `400000`.

## Exact declaration statements and individual dependency reports

The following is the complete, unedited Lean output from the separate declaration check. It contains every exact declaration type with qualified names and universes, immediately followed by its individual logical-dependency report.

```text
ZInQ.Contrib.RC53Assist.TameBijective.continuous_ev1K {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M]
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M)) :
  Continuous.{0, 0} fun g => ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) g
'ZInQ.Contrib.RC53Assist.TameBijective.continuous_ev1K' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cocycleZeroSubgroup {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M]
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M)) : Subgroup.{0} G
'ZInQ.Contrib.RC53Assist.TameBijective.cocycleZeroSubgroup' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.isClosed_cocycleZeroSubgroup {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M] [T1Space.{0} M]
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M)) :
  IsClosed.{0} ↑(ZInQ.Contrib.RC53Assist.TameBijective.cocycleZeroSubgroup z)
'ZInQ.Contrib.RC53Assist.TameBijective.isClosed_cocycleZeroSubgroup' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_proP {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M] [DiscreteTopology.{0} M] (P : Subgroup.{0} G) {p n : ℕ}
  (hP : TauCeti.IsProP.{0} p ↥P) (hpn : p.Coprime n)
  (hPM : ∀ (g : G), Membership.mem.{0, 0} P g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M))
  (g : G) : Membership.mem.{0, 0} P g → Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) g) 0
'ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_proP' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.Z1K_eq_zero_of_frobenius_inertia {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M] [T1Space.{0} M] (I : Subgroup.{0} G) (φ : G)
  (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ I)) Top.top.{0})
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M))
  (hφ : Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) φ) 0)
  (hI : ∀ (g : G), Membership.mem.{0, 0} I g → Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) g) 0) :
  Eq.{1} z 0
'ZInQ.Contrib.RC53Assist.TameBijective.Z1K_eq_zero_of_frobenius_inertia' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_inertia_of_proP {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M] [DiscreteTopology.{0} M] (I P : Subgroup.{0} G) (σ : G)
  {p n : ℕ} (hP : TauCeti.IsProP.{0} p ↥P) (hpn : p.Coprime n)
  (hItriv : ∀ (g : G), Membership.mem.{0, 0} I g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hPI : LE.le.{0} P I) (hgenI : LE.le.{0} I (Subgroup.topologicalClosure.{0} (P ⊔ Subgroup.zpowers.{0} σ)))
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M))
  (hσ : Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) σ) 0) (g : G) :
  Membership.mem.{0, 0} I g → Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) g) 0
'ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_inertia_of_proP' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_injective_of_proP {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [ContinuousAdd.{0} M]
  [ContinuousConstSMul.{0, 0} k M] [ContinuousSMul.{0, 0} G M] [DiscreteTopology.{0} M] (I P : Subgroup.{0} G) (φ σ : G)
  (q : ℕ) {p n : ℕ} (hP : TauCeti.IsProP.{0} p ↥P) (hpn : p.Coprime n)
  (hItriv : ∀ (g : G), Membership.mem.{0, 0} I g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hPI : LE.le.{0} P I) (hσI : Membership.mem.{0, 0} I σ)
  (hgenI : LE.le.{0} I (Subgroup.topologicalClosure.{0} (P ⊔ Subgroup.zpowers.{0} σ)))
  (hgenG : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ I)) Top.top.{0})
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hrel : Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ)) (HPow.hPow.{0, 0, 0} σ q)) :
  Function.Injective.{1, 1} ⇑(ZInQ.Contrib.CloudB3RC53.SwitchInputs.coordQUnr φ σ q (hItriv σ hσI) hrel)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_injective_of_proP' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple {M : Type} [AddCommGroup.{0} M] [TopologicalSpace.{0} M] {n : ℕ}
  [NeZero.{0} n] (m : M) (hnm : Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  ContinuousMonoidHom.{0, 0} (Multiplicative.{0} (ZMod n)) (Multiplicative.{0} M)
'ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_apply {M : Type} [AddCommGroup.{0} M] [TopologicalSpace.{0} M]
  {n : ℕ} [NeZero.{0} n] (m : M) (hnm : Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) (a : Multiplicative.{0} (ZMod n)) :
  Eq.{1} (Multiplicative.toAdd.{0} ((ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple m hnm) a))
    (HSMul.hSMul.{0, 0, 0} (Multiplicative.toAdd.{0} a).val m)
'ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj {G : Type} [Group.{0} G] (I : Subgroup.{0} G) [Subgroup.Normal.{0} I]
  (g : G) (i : ↥I) : ↥I
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj' depends on axioms: [propext]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj_mul {G : Type} [Group.{0} G] (I : Subgroup.{0} G)
  [Subgroup.Normal.{0} I] (g h : G) (i : ↥I) :
  Eq.{1} (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I (HMul.hMul.{0, 0, 0} g h) i)
    (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I g (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I h i))
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj_mul' depends on axioms: [propext]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaHom_equivariant {G : Type} [Group.{0} G] [TopologicalSpace.{0} G]
  [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [DistribMulAction.{0, 0} G M] [TopologicalSpace.{0} M]
  [DiscreteTopology.{0} M] [ContinuousSMul.{0, 0} G M] (I : Subgroup.{0} G) [Subgroup.Normal.{0} I] (φ : G)
  (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ I)) Top.top.{0})
  (hItriv : ∀ (g : G), Membership.mem.{0, 0} I g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (f : ContinuousMonoidHom.{0, 0} (↥I) (Multiplicative.{0} M))
  (hfφ :
    ∀ (i : ↥I),
      Eq.{1} (Multiplicative.toAdd.{0} (f (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I φ i)))
        (HSMul.hSMul.{0, 0, 0} φ (Multiplicative.toAdd.{0} (f i))))
  (g : G) (i : ↥I) :
  Eq.{1} (Multiplicative.toAdd.{0} (f (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I g i)))
    (HSMul.hSMul.{0, 0, 0} g (Multiplicative.toAdd.{0} (f i)))
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaHom_equivariant' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection {G : Type} [Group.{0} G] [TopologicalSpace.{0} G]
  [IsTopologicalGroup.{0} G] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [CompactSpace.{0} G]
  [TotallyDisconnectedSpace.{0} G]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0}))) (φ : G) :
  ContinuousMonoidHom.{0, 0} H G
'ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection_frob {G : Type} [Group.{0} G] [TopologicalSpace.{0} G]
  [IsTopologicalGroup.{0} G] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [CompactSpace.{0} G]
  [TotallyDisconnectedSpace.{0} G]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0}))) (φ : G) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection e φ)
      (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e))
    φ
'ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection_frob' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.quotient_frobeniusSection {G : Type} [Group.{0} G] [TopologicalSpace.{0} G]
  [IsTopologicalGroup.{0} G] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [CompactSpace.{0} G]
  [TotallyDisconnectedSpace.{0} G] [T2Space.{0} H]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0})))
  (π : ContinuousMonoidHom.{0, 0} G H) (φ : G)
  (hφ : Eq.{1} (π φ) (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e)) (h : H) :
  Eq.{1} (π ((ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection e φ) h)) h
'ZInQ.Contrib.RC53Assist.TameBijective.quotient_frobeniusSection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart {G : Type} [Group.{0} G] [TopologicalSpace.{0} G] {H : Type}
  [Group.{0} H] [TopologicalSpace.{0} H] (π : ContinuousMonoidHom.{0, 0} G H) (s : ContinuousMonoidHom.{0, 0} H G)
  (hs : ∀ (h : H), Eq.{1} (π (s h)) h) (g : G) : ↥(MonoidHom.ker.{0, 0} ↑π)
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart' depends on axioms: [propext]
ZInQ.Contrib.RC53Assist.TameBijective.continuous_inertiaPart {G : Type} [Group.{0} G] [TopologicalSpace.{0} G]
  [IsTopologicalGroup.{0} G] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] (π : ContinuousMonoidHom.{0, 0} G H)
  (s : ContinuousMonoidHom.{0, 0} H G) (hs : ∀ (h : H), Eq.{1} (π (s h)) h) :
  Continuous.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart π s hs)
'ZInQ.Contrib.RC53Assist.TameBijective.continuous_inertiaPart' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart_mul {G : Type} [Group.{0} G] [TopologicalSpace.{0} G] {H : Type}
  [Group.{0} H] [TopologicalSpace.{0} H] (π : ContinuousMonoidHom.{0, 0} G H) (s : ContinuousMonoidHom.{0, 0} H G)
  (hs : ∀ (h : H), Eq.{1} (π (s h)) h) (g h : G) :
  Eq.{1} (ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart π s hs (HMul.hMul.{0, 0, 0} g h))
    (HMul.hMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart π s hs g)
      (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) (s (π g))
        (ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart π s hs h)))
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart_mul' depends on axioms: [propext]
ZInQ.Contrib.RC53Assist.TameBijective.smul_eq_section_smul {G : Type} [Group.{0} G] [TopologicalSpace.{0} G] {M : Type}
  [AddCommGroup.{0} M] [DistribMulAction.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H]
  (π : ContinuousMonoidHom.{0, 0} G H) (s : ContinuousMonoidHom.{0, 0} H G) (hs : ∀ (h : H), Eq.{1} (π (s h)) h)
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (g : G) (m : M) : Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) (HSMul.hSMul.{0, 0, 0} (s (π g)) m)
'ZInQ.Contrib.RC53Assist.TameBijective.smul_eq_section_smul' depends on axioms: [propext]
ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] (π : ContinuousMonoidHom.{0, 0} G H)
  (s : ContinuousMonoidHom.{0, 0} H G) (hs : ∀ (h : H), Eq.{1} (π (s h)) h)
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (f : ContinuousMonoidHom.{0, 0} (↥(MonoidHom.ker.{0, 0} ↑π)) (Multiplicative.{0} M))
  (hf :
    ∀ (g : G) (i : ↥(MonoidHom.ker.{0, 0} ↑π)),
      Eq.{1}
        (Multiplicative.toAdd.{0} (f (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) g i)))
        (HSMul.hSMul.{0, 0, 0} g (Multiplicative.toAdd.{0} (f i)))) :
  ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k G M)
'ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle_ev {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] (π : ContinuousMonoidHom.{0, 0} G H)
  (s : ContinuousMonoidHom.{0, 0} H G) (hs : ∀ (h : H), Eq.{1} (π (s h)) h)
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (f : ContinuousMonoidHom.{0, 0} (↥(MonoidHom.ker.{0, 0} ↑π)) (Multiplicative.{0} M))
  (hf :
    ∀ (g : G) (i : ↥(MonoidHom.ker.{0, 0} ↑π)),
      Eq.{1}
        (Multiplicative.toAdd.{0} (f (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) g i)))
        (HSMul.hSMul.{0, 0, 0} g (Multiplicative.toAdd.{0} (f i))))
  (g : G) :
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K
      (↑(ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle π s hs hItriv f hf)) g)
    (Multiplicative.toAdd.{0} (f (ZInQ.Contrib.RC53Assist.TameBijective.inertiaPart π s hs g)))
'ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle_ev' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_one {M : Type} [AddCommGroup.{0} M] [TopologicalSpace.{0} M]
  {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] (m : M) (hnm : Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple m hnm) (Multiplicative.ofAdd.{0} 1))
    (Multiplicative.ofAdd.{0} m)
'ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_one' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_tame_equivariant {G : Type} [Group.{0} G] [TopologicalSpace.{0} G]
  [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [DistribMulAction.{0, 0} G M] [TopologicalSpace.{0} M]
  [DiscreteTopology.{0} M] [ContinuousSMul.{0, 0} G M] (I : Subgroup.{0} G) [Subgroup.Normal.{0} I] (φ : G) (q : ℕ)
  {n : ℕ} [NeZero.{0} n] (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ I)) Top.top.{0})
  (hItriv : ∀ (g : G), Membership.mem.{0, 0} I g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (χ : ContinuousMonoidHom.{0, 0} (↥I) (Multiplicative.{0} (ZMod n)))
  (hχ : ∀ (i : ↥I), Eq.{1} (χ (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I φ i)) (HPow.hPow.{0, 0, 0} (χ i) q))
  (m : M) (hnm : Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hφm : Eq.{1} (HSMul.hSMul.{0, 0, 0} φ m) (HSMul.hSMul.{0, 0, 0} q m)) (g : G) (i : ↥I) :
  Eq.{1}
    (Multiplicative.toAdd.{0}
      ((ContinuousMonoidHom.comp.{0, 0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple m hnm) χ)
        (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj I g i)))
    (HSMul.hSMul.{0, 0, 0} g
      (Multiplicative.toAdd.{0}
        ((ContinuousMonoidHom.comp.{0, 0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple m hnm) χ) i)))
'ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_tame_equivariant' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle_coordinates {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [CompactSpace.{0} G]
  [TotallyDisconnectedSpace.{0} G] [T2Space.{0} H]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0})))
  (π : ContinuousMonoidHom.{0, 0} G H) (φ σ : G) (q : ℕ)
  (hφ : Eq.{1} (π φ) (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e))
  (hσ : Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) σ)
  (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ MonoidHom.ker.{0, 0} ↑π)) Top.top.{0})
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)]
  (χ : ContinuousMonoidHom.{0, 0} (↥(MonoidHom.ker.{0, 0} ↑π)) (Multiplicative.{0} (ZMod n)))
  (hχσ : Eq.{1} (χ (Subtype.mk.{1} σ hσ)) (Multiplicative.ofAdd.{0} 1))
  (hχφ :
    ∀ (i : ↥(MonoidHom.ker.{0, 0} ↑π)),
      Eq.{1} (χ (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) φ i))
        (HPow.hPow.{0, 0, 0} (χ i) q))
  (m : M) (hnm : Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hφm : Eq.{1} (HSMul.hSMul.{0, 0, 0} φ m) (HSMul.hSMul.{0, 0, 0} q m)) :
  let s := ZInQ.Contrib.RC53Assist.TameBijective.frobeniusSection e φ;
  have hs := ZInQ.Contrib.RC53Assist.TameBijective.quotient_frobeniusSection e π φ hφ;
  let f := ContinuousMonoidHom.comp.{0, 0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple m hnm) χ;
  have hf :=
    ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple_tame_equivariant (MonoidHom.ker.{0, 0} ↑π) φ q hgen hItriv χ
      hχφ m hnm hφm;
  Eq.{1}
      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K
        (↑(ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle π s hs hItriv f hf)) φ)
      0 ∧
    Eq.{1}
      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K
        (↑(ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle π s hs hItriv f hf)) σ)
      m
'ZInQ.Contrib.RC53Assist.TameBijective.singularCocycle_coordinates' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.exists_Z1K_with_coordinates {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [IsTopologicalGroup.{0} H]
  [CompactSpace.{0} G] [TotallyDisconnectedSpace.{0} G] [T2Space.{0} H] [TopologicalSpace.{0} k]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0})))
  (π : ContinuousMonoidHom.{0, 0} G H) (X : TopRep.{0, 0, 0} k H) [ContinuousSMul.{0, 0} H ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf : ∀ (g : G) (x : ↑X), Eq.{1} (f (HSMul.hSMul.{0, 0, 0} (π g) x)) (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f) (φ σ : G) (q : ℕ)
  (hφ : Eq.{1} (π φ) (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e))
  (hσ : Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) σ)
  (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ MonoidHom.ker.{0, 0} ↑π)) Top.top.{0})
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (χ : ContinuousMonoidHom.{0, 0} (↥(MonoidHom.ker.{0, 0} ↑π)) (Multiplicative.{0} (ZMod n)))
  (hχσ : Eq.{1} (χ (Subtype.mk.{1} σ hσ)) (Multiplicative.ofAdd.{0} 1))
  (hχφ :
    ∀ (i : ↥(MonoidHom.ker.{0, 0} ↑π)),
      Eq.{1} (χ (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) φ i))
        (HPow.hPow.{0, 0, 0} (χ i) q))
  (a : M) (m : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.KerFrob k M φ q)) :
  ∃ z,
    Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) φ) a ∧
      Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) σ) ↑m
'ZInQ.Contrib.RC53Assist.TameBijective.exists_Z1K_with_coordinates' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_surjective_of_tame_character {k : Type} [Field.{0} k] {G : Type}
  [Group.{0} G] [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [IsTopologicalGroup.{0} H]
  [CompactSpace.{0} G] [TotallyDisconnectedSpace.{0} G] [T2Space.{0} H] [TopologicalSpace.{0} k]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0})))
  (π : ContinuousMonoidHom.{0, 0} G H) (X : TopRep.{0, 0, 0} k H) [ContinuousSMul.{0, 0} H ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf : ∀ (g : G) (x : ↑X), Eq.{1} (f (HSMul.hSMul.{0, 0, 0} (π g) x)) (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f) (φ σ : G) (q : ℕ)
  (hφ : Eq.{1} (π φ) (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e))
  (hσ : Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) σ)
  (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ MonoidHom.ker.{0, 0} ↑π)) Top.top.{0})
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hrel : Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ)) (HPow.hPow.{0, 0, 0} σ q)) {n : ℕ}
  [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (χ : ContinuousMonoidHom.{0, 0} (↥(MonoidHom.ker.{0, 0} ↑π)) (Multiplicative.{0} (ZMod n)))
  (hχσ : Eq.{1} (χ (Subtype.mk.{1} σ hσ)) (Multiplicative.ofAdd.{0} 1))
  (hχφ :
    ∀ (i : ↥(MonoidHom.ker.{0, 0} ↑π)),
      Eq.{1} (χ (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) φ i))
        (HPow.hPow.{0, 0, 0} (χ i) q)) :
  Function.Surjective.{1, 1} ⇑(ZInQ.Contrib.CloudB3RC53.SwitchInputs.coordQUnr φ σ q (hItriv σ hσ) hrel)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_surjective_of_tame_character' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameCoordinatesUnr_of_proP {k : Type} [Field.{0} k] {G : Type} [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} k M]
  [DistribMulAction.{0, 0} G M] [SMulCommClass.{0, 0, 0} G k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} G M] {H : Type} [Group.{0} H] [TopologicalSpace.{0} H] [IsTopologicalGroup.{0} H]
  [CompactSpace.{0} G] [TotallyDisconnectedSpace.{0} G] [T2Space.{0} H] [TopologicalSpace.{0} k]
  (e : ContinuousMulEquiv.{0, 0} H ↑(CompHausLike.toTop.{0} (ProfiniteGrp.toProfinite.{0} TauCeti.zHat.{0})))
  (π : ContinuousMonoidHom.{0, 0} G H) (X : TopRep.{0, 0, 0} k H) [ContinuousSMul.{0, 0} H ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf : ∀ (g : G) (x : ↑X), Eq.{1} (f (HSMul.hSMul.{0, 0, 0} (π g) x)) (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f) (φ σ : G) (q : ℕ)
  (hφ : Eq.{1} (π φ) (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt e))
  (hσ : Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) σ)
  (hgen : Eq.{1} (Subgroup.topologicalClosure.{0} (Subgroup.zpowers.{0} φ ⊔ MonoidHom.ker.{0, 0} ↑π)) Top.top.{0})
  (hItriv :
    ∀ (g : G), Membership.mem.{0, 0} (MonoidHom.ker.{0, 0} ↑π) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hrel : Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ)) (HPow.hPow.{0, 0, 0} σ q))
  (P : Subgroup.{0} G) {p n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] (hP : TauCeti.IsProP.{0} p ↥P)
  (hpn : p.Coprime n) (hPI : LE.le.{0} P (MonoidHom.ker.{0, 0} ↑π))
  (hgenI : LE.le.{0} (MonoidHom.ker.{0, 0} ↑π) (Subgroup.topologicalClosure.{0} (P ⊔ Subgroup.zpowers.{0} σ)))
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (χ : ContinuousMonoidHom.{0, 0} (↥(MonoidHom.ker.{0, 0} ↑π)) (Multiplicative.{0} (ZMod n)))
  (hχσ : Eq.{1} (χ (Subtype.mk.{1} σ hσ)) (Multiplicative.ofAdd.{0} 1))
  (hχφ :
    ∀ (i : ↥(MonoidHom.ker.{0, 0} ↑π)),
      Eq.{1} (χ (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (MonoidHom.ker.{0, 0} ↑π) φ i))
        (HPow.hPow.{0, 0, 0} (χ i) q)) :
  ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinatesUnr k M (MonoidHom.ker.{0, 0} ↑π) φ σ q
'ZInQ.Contrib.RC53Assist.TameBijective.tameCoordinatesUnr_of_proP' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv (K : Type) [Field.{0} K] :
  ContinuousMulEquiv.{0, 0} (Field.absoluteGaloisGroup.{0} K) Gal(AlgebraicClosure.{0} K/K)
'ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.kummerLog_mul_inertia {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (g h : ↥(TauCeti.inertiaSubgroup.{0} K)) :
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.InnerLimitArith.kummerLog hβ hβ0 hζ
      ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) (HMul.hMul.{0, 0, 0} ↑g ↑h)))
    (HAdd.hAdd.{0, 0, 0}
      (ZInQ.Contrib.RC53Assist.InnerLimitArith.kummerLog hβ hβ0 hζ
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) ↑g))
      (ZInQ.Contrib.RC53Assist.InnerLimitArith.kummerLog hβ hβ0 hζ
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) ↑h)))
'ZInQ.Contrib.RC53Assist.TameBijective.kummerLog_mul_inertia' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLog {K : Type} [Field.{0} K] [ValuativeRel.{0} K] [TopologicalSpace.{0} K]
  [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K} {β : AlgebraicClosure.{0} K}
  {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n) :
  ContinuousMonoidHom.{0, 0} (↥(TauCeti.inertiaSubgroup.{0} K)) (Multiplicative.{0} (ZMod n))
'ZInQ.Contrib.RC53Assist.TameBijective.tameLog' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLog_apply {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (g : ↥(TauCeti.inertiaSubgroup.{0} K)) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.TameBijective.tameLog hn hβ hβ0 hζ) g)
    (Multiplicative.ofAdd.{0}
      (ZInQ.Contrib.RC53Assist.InnerLimitArith.kummerLog hβ hβ0 hζ
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) ↑g)))
'ZInQ.Contrib.RC53Assist.TameBijective.tameLog_apply' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLog_generator {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K} [Fact (LT.lt.{0} 1 n)]
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.TameBijective.tameLog hn hβ hβ0 hζ) (Subtype.mk.{1} σ hσI))
    (Multiplicative.ofAdd.{0} 1)
'ZInQ.Contrib.RC53Assist.TameBijective.tameLog_generator' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLog_conj_frobenius {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  {φ : Field.absoluteGaloisGroup.{0} K} (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ)
  (i : ↥(TauCeti.inertiaSubgroup.{0} K)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.TameBijective.tameLog hn hβ hβ0 hζ)
      (ZInQ.Contrib.RC53Assist.TameBijective.inertiaConj (TauCeti.inertiaSubgroup.{0} K) φ i))
    (HPow.hPow.{0, 0, 0} ((ZInQ.Contrib.RC53Assist.TameBijective.tameLog hn hβ hβ0 hζ) i)
      (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
'ZInQ.Contrib.RC53Assist.TameBijective.tameLog_conj_frobenius' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.pGroup_hom_trivial.{u_1, u_3} {C : Type u_1} [Group.{u_1} C] {p n : ℕ}
  {B : Type u_3} [Group.{u_3} B] (hC : IsPGroup.{u_1} p C) (hpn : p.Coprime n) (f : MonoidHom.{u_1, u_3} C B)
  (hnB : ∀ (b : B), Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} b n) 1) (c : C) : Eq.{u_3 + 1} (f c) 1
'ZInQ.Contrib.RC53Assist.TameBijective.pGroup_hom_trivial' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cyclic_hom_detect.{u_1, u_2} {C : Type u_1} {A : Type u_2} [Group.{u_1} C]
  [AddCommGroup.{u_2} A] {n : ℕ} [IsCyclic.{u_1} C] (χ : MonoidHom.{u_1, 0} C (Multiplicative.{0} (ZMod n)))
  (f : MonoidHom.{u_1, u_2} C (Multiplicative.{u_2} A))
  (hnA : ∀ (a : A), Eq.{u_2 + 1} (HSMul.hSMul.{0, u_2, u_2} n a) 0) (σ : C)
  (hχσ : Eq.{1} (χ σ) (Multiplicative.ofAdd.{0} 1)) (hfσ : Eq.{u_2 + 1} (f σ) 1) (c : C) : Eq.{u_2 + 1} (f c) 1
'ZInQ.Contrib.RC53Assist.TameBijective.cyclic_hom_detect' depends on axioms: [propext, Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.hom_trivial_of_cyclic_tame_quotient.{u_1, u_2} {C : Type u_1} {A : Type u_2}
  [Group.{u_1} C] [AddCommGroup.{u_2} A] {p n : ℕ} (P : Subgroup.{u_1} C) [Subgroup.Normal.{u_1} P]
  [IsCyclic.{u_1} (HasQuotient.Quotient.{u_1, u_1} C P)] (hP : IsPGroup.{u_1} p ↥P) (hpn : p.Coprime n)
  (χ : MonoidHom.{u_1, 0} C (Multiplicative.{0} (ZMod n))) (f : MonoidHom.{u_1, u_2} C (Multiplicative.{u_2} A))
  (hnA : ∀ (a : A), Eq.{u_2 + 1} (HSMul.hSMul.{0, u_2, u_2} n a) 0) (σ : C)
  (hχσ : Eq.{1} (χ σ) (Multiplicative.ofAdd.{0} 1)) (hfσ : Eq.{u_2 + 1} (f σ) 1) (c : C) : Eq.{u_2 + 1} (f c) 1
'ZInQ.Contrib.RC53Assist.TameBijective.hom_trivial_of_cyclic_tame_quotient' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.isCyclic_finite_tame_subquotient {K L : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] [Field.{0} L] [ValuativeRel.{0} L]
  [TopologicalSpace.{0} L] [IsNonarchimedeanLocalField.{0} L] [Algebra.{0, 0} K L] [ValuativeExtension.{0, 0} K L]
  [Module.Finite.{0, 0} K L] (A : Subgroup.{0} Gal(L/K))
  (hA : LE.le.{0} A (TauCeti.LocalFieldsRamification.lowerRamificationGroup.{0, 0} K L 0)) :
  IsCyclic.{0}
    (HasQuotient.Quotient.{0, 0} (↥A)
      (Subgroup.subgroupOf.{0} (TauCeti.LocalFieldsRamification.lowerRamificationGroup.{0, 0} K L 1) A))
'ZInQ.Contrib.RC53Assist.TameBijective.isCyclic_finite_tame_subquotient' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaHom_trivial_of_tame_generator {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {M : Type} [AddCommGroup.{0} M]
  [TopologicalSpace.{0} M] [DiscreteTopology.{0} M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (f : ContinuousMonoidHom.{0, 0} (↥(TauCeti.inertiaSubgroup.{0} K)) (Multiplicative.{0} M))
  (hfσ : Eq.{1} (f (Subtype.mk.{1} σ hσI)) 1) (i : ↥(TauCeti.inertiaSubgroup.{0} K)) : Eq.{1} (f i) 1
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaHom_trivial_of_tame_generator' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] : Type
'ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] :
  ContinuousMonoidHom.{0, 0} (Field.absoluteGaloisGroup.{0} K)
    (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K)
'ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection_ker (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] :
  Eq.{1} (MonoidHom.ker.{0, 0} ↑(ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K))
    (TauCeti.inertiaSubgroup.{0} K)
'ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection_ker' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection_frob (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {φ : Field.absoluteGaloisGroup.{0} K}
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) φ)
    (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt
      (TauCeti.maximalUnramifiedGaloisGroupEquivZHat.{0, 0} K (AlgebraicClosure.{0} K)))
'ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection_frob' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_local_inertia {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] [PerfectField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k (Field.absoluteGaloisGroup.{0} K) M))
  (hzσ : Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) σ) 0) (g : Field.absoluteGaloisGroup.{0} K) :
  Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) g) 0
'ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_local_inertia' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_injective_local {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] [PerfectField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hrel :
    Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ))
      (HPow.hPow.{0, 0, 0} σ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))) :
  Function.Injective.{1, 1}
    ⇑(ZInQ.Contrib.CloudB3RC53.SwitchInputs.coordQUnr φ σ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))
        (hItriv σ hσI) hrel)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_injective_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_surjective_local {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K} [TopologicalSpace.{0} k]
  (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf :
    ∀ (g : Field.absoluteGaloisGroup.{0} K) (x : ↑X),
      Eq.{1} (f (HSMul.hSMul.{0, 0, 0} ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g) x))
        (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f)
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hrel :
    Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ))
      (HPow.hPow.{0, 0, 0} σ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))) :
  Function.Surjective.{1, 1}
    ⇑(ZInQ.Contrib.CloudB3RC53.SwitchInputs.coordQUnr φ σ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))
        (hItriv σ hσI) hrel)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQUnr_surjective_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameCoordinatesUnr_local {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] [PerfectField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K} [TopologicalSpace.{0} k]
  (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf :
    ∀ (g : Field.absoluteGaloisGroup.{0} K) (x : ↑X),
      Eq.{1} (f (HSMul.hSMul.{0, 0, 0} ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g) x))
        (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f)
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hrel :
    Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ))
      (HPow.hPow.{0, 0, 0} σ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))) :
  ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinatesUnr k M (TauCeti.inertiaSubgroup.{0} K) φ σ
    (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))
'ZInQ.Contrib.RC53Assist.TameBijective.tameCoordinatesUnr_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] (β : AlgebraicClosure.{0} K) :
  Subgroup.{0} (Field.absoluteGaloisGroup.{0} K)
'ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.mem_tameLevelKernel (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {β : AlgebraicClosure.{0} K}
  {g : Field.absoluteGaloisGroup.{0} K} :
  Membership.mem.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel K β) g ↔
    Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g ∧
      Eq.{1} (((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) g) β) β
'ZInQ.Contrib.RC53Assist.TameBijective.mem_tameLevelKernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.isClosed_tameLevelKernel (K : Type) [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] (β : AlgebraicClosure.{0} K) :
  IsClosed.{0} ↑(ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel K β)
'ZInQ.Contrib.RC53Assist.TameBijective.isClosed_tameLevelKernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel_normal {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} {a : K} {β : AlgebraicClosure.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a))
  (hβ0 : Ne.{1} β 0) : Subgroup.Normal.{0} (ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel K β)
'ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel_normal' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameLog_eq_one_iff {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K}
  {β : AlgebraicClosure.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  {σ : Field.absoluteGaloisGroup.{0} K}
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (i : ↥(TauCeti.inertiaSubgroup.{0} K)) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.TameBijective.tameLog hn hβ hβ0 hζ) i) 1 ↔
    Eq.{1} (((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) ↑i) β) β
'ZInQ.Contrib.RC53Assist.TameBijective.tameLog_eq_one_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tame_level_frobenius_relation {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} {a : K} {β : AlgebraicClosure.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  {φ σ : Field.absoluteGaloisGroup.{0} K} (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ) :
  Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} ↑φ ↑σ) (Inv.inv.{0} ↑φ))
    (HPow.hPow.{0, 0, 0} (↑σ)
      (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
'ZInQ.Contrib.RC53Assist.TameBijective.tame_level_frobenius_relation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.tameCoordinatesUnr_tame_level {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {a : K}
  {β : AlgebraicClosure.{0} K} {k : Type} [Field.{0} k] [TopologicalSpace.{0} k]
  (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] [Fact (LT.lt.{0} 1 n)]
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  {φ σ : Field.absoluteGaloisGroup.{0} K} (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hnX : ∀ (x : ↑X), Eq.{1} (HSMul.hSMul.{0, 0, 0} n x) 0) :
  ∃ (hN : Subgroup.Normal.{0} (ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel K β)),
    ∃ πt,
      (∀ (g : Field.absoluteGaloisGroup.{0} K),
          Eq.{1} (πt ↑g) ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g)) ∧
        ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinatesUnr k (ZInQ.Manuscript.RC.SelmerComplex.ResMod.{0} πt ↑X)
          (MonoidHom.ker.{0, 0} ↑πt) (↑φ) (↑σ)
          (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))
'ZInQ.Contrib.RC53Assist.TameBijective.tameCoordinatesUnr_tame_level' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.exists_tameCoordinatesUnr_tame_level {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {n : ℕ} [NeZero.{0} n] {k : Type} [Field.{0} k]
  [TopologicalSpace.{0} k] (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] [Fact (LT.lt.{0} 1 n)]
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hnX : ∀ (x : ↑X), Eq.{1} (HSMul.hSMul.{0, 0, 0} n x) 0) :
  ∃ ϖ β φ σ,
    TauCeti.IsUniformizer.{0} K ϖ ∧
      Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) ↑ϖ) ∧
        TauCeti.IsArithFrobeniusLift.{0} K φ ∧
          Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ ∧
            ∃ (hN : Subgroup.Normal.{0} (ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel K β)),
              ∃ πt,
                (∀ (g : Field.absoluteGaloisGroup.{0} K),
                    Eq.{1} (πt ↑g) ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g)) ∧
                  ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinatesUnr k
                    (ZInQ.Manuscript.RC.SelmerComplex.ResMod.{0} πt ↑X) (MonoidHom.ker.{0, 0} ↑πt) (↑φ) (↑σ)
                    (Nat.card.{0}
                      (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))
'ZInQ.Contrib.RC53Assist.TameBijective.exists_tameCoordinatesUnr_tame_level' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.exists_tameCoordinatesUnr_at {K₀ : Type} [Field.{0} K₀] [NumberField.{0} K₀]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K₀))
  (h2 : 2 ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} w) {i : ℕ} (hi : Ne.{1} i 0) {k : Type} [Field.{0} k]
  [TopologicalSpace.{0} k]
  (X :
    TopRep.{0, 0, 0} k
      (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w)))
  [ContinuousSMul.{0, 0}
      (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w))
      ↑X]
  [DiscreteTopology.{0} ↑X] [Finite.{1} ↑X]
  (hnX : ∀ (x : ↑X), Eq.{1} (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 i) x) 0) :
  ∃ ϖ β φ σ,
    TauCeti.IsUniformizer.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w) ϖ ∧
      Eq.{1} (HPow.hPow.{0, 0, 0} β (HPow.hPow.{0, 0, 0} 2 i))
          ((Algebra.algebraMap.{0, 0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w)
              (AlgebraicClosure.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w)))
            ↑ϖ) ∧
        TauCeti.IsArithFrobeniusLift.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w) φ ∧
          Membership.mem.{0, 0}
              (TauCeti.inertiaSubgroup.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w)) σ ∧
            ∃ (hN :
              Subgroup.Normal.{0}
                (ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w) β)),
              ∃ πt,
                (∀ (g : Field.absoluteGaloisGroup.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w)),
                    Eq.{1} (πt ↑g)
                      ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection
                          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w))
                        g)) ∧
                  ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinatesUnr k
                    (ZInQ.Manuscript.RC.SelmerComplex.ResMod.{0} πt ↑X) (MonoidHom.ker.{0, 0} ↑πt) (↑φ) (↑σ)
                    (Nat.card.{0}
                      (IsLocalRing.ResidueField.{0}
                        ↥(Valuation.integer.{0, 0}
                            (ValuativeRel.valuation.{0}
                              (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K₀ w)))))
'ZInQ.Contrib.RC53Assist.TameBijective.exists_tameCoordinatesUnr_at' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.inertiaHom_tameLog_formula {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {M : Type} [AddCommGroup.{0} M]
  [TopologicalSpace.{0} M] [DiscreteTopology.{0} M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (f : ContinuousMonoidHom.{0, 0} (↥(TauCeti.inertiaSubgroup.{0} K)) (Multiplicative.{0} M))
  (i : ↥(TauCeti.inertiaSubgroup.{0} K)) :
  Eq.{1} (f i)
    ((ZInQ.Contrib.RC53Assist.TameBijective.cyclicMultiple (Multiplicative.toAdd.{0} (f (Subtype.mk.{1} σ hσI)))
        (hnM (Multiplicative.toAdd.{0} (f (Subtype.mk.{1} σ hσI)))))
      ((ZInQ.Contrib.RC53Assist.TameBijective.tameLog hn hβ hβ0 hζ) i))
'ZInQ.Contrib.RC53Assist.TameBijective.inertiaHom_tameLog_formula' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.cocycleInertiaHom {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k (Field.absoluteGaloisGroup.{0} K) M)) :
  ContinuousMonoidHom.{0, 0} (↥(TauCeti.inertiaSubgroup.{0} K)) (Multiplicative.{0} M)
'ZInQ.Contrib.RC53Assist.TameBijective.cocycleInertiaHom' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_tame_kernel {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k (Field.absoluteGaloisGroup.{0} K) M))
  (g : Field.absoluteGaloisGroup.{0} K) :
  Membership.mem.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.tameLevelKernel K β) g →
    Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) g) 0
'ZInQ.Contrib.RC53Assist.TameBijective.ev1K_eq_zero_on_tame_kernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.ev1K_sigma_mem_ker_local {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k (Field.absoluteGaloisGroup.{0} K) M)) :
  Membership.mem.{0, 0}
    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.KerFrob k M φ
      (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) σ)
'ZInQ.Contrib.RC53Assist.TameBijective.ev1K_sigma_mem_ker_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordLLocal {K : Type} [Field.{0} K] [PerfectField.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k)
    (↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k (Field.absoluteGaloisGroup.{0} K) M))
    (Prod.{0, 0} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.CokerFrob k M φ)
      ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.KerFrob k M φ
          (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))))
'ZInQ.Contrib.RC53Assist.TameBijective.coordLLocal' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordLLocal_relaxedD {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Manuscript.RC.SelmerComplex.contCochains.{0} k (Field.absoluteGaloisGroup.{0} K) M) 0)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.TameBijective.coordLLocal hn hβ hβ0 hφ hσI hζ hItriv hnM)
      ((ZInQ.Contrib.CloudB3RC53.SwitchInputs.relaxedDK k (Field.absoluteGaloisGroup.{0} K) M) c))
    0
'ZInQ.Contrib.RC53Assist.TameBijective.coordLLocal_relaxedD' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal {K : Type} [Field.{0} K] [PerfectField.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k)
    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.H1WrelK k (Field.absoluteGaloisGroup.{0} K) M)
    (Prod.{0, 0} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.CokerFrob k M φ)
      ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.KerFrob k M φ
          (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))))
'ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_mk {K : Type} [Field.{0} K] [PerfectField.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (z : ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.Z1K k (Field.absoluteGaloisGroup.{0} K) M)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal hn hβ hβ0 hφ hσI hζ hItriv hnM)
      (Submodule.Quotient.mk.{0, 0} z))
    (Prod.mk.{0, 0} (Submodule.Quotient.mk.{0, 0} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) φ))
      (Subtype.mk.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) σ)
        (ZInQ.Contrib.RC53Assist.TameBijective.ev1K_sigma_mem_ker_local hn hβ hβ0 hφ hσI hζ hItriv hnM z)))
'ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_injective {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  Function.Injective.{1, 1} ⇑(ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal hn hβ hβ0 hφ hσI hζ hItriv hnM)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.exists_Z1K_local {K : Type} [Field.{0} K] [ValuativeRel.{0} K]
  [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K} [TopologicalSpace.{0} k]
  (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf :
    ∀ (g : Field.absoluteGaloisGroup.{0} K) (x : ↑X),
      Eq.{1} (f (HSMul.hSMul.{0, 0, 0} ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g) x))
        (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f)
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) (b : M)
  (m :
    ↥(ZInQ.Contrib.CloudB3RC53.SwitchInputs.KerFrob k M φ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))) :
  ∃ z,
    Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) φ) b ∧
      Eq.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.ev1K (↑z) σ) ↑m
'ZInQ.Contrib.RC53Assist.TameBijective.exists_Z1K_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_surjective {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K} [TopologicalSpace.{0} k]
  (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf :
    ∀ (g : Field.absoluteGaloisGroup.{0} K) (x : ↑X),
      Eq.{1} (f (HSMul.hSMul.{0, 0, 0} ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g) x))
        (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f)
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  Function.Surjective.{1, 1} ⇑(ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal hn hβ hβ0 hφ hσI hζ hItriv hnM)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_bijective {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K} [TopologicalSpace.{0} k]
  (X : TopRep.{0, 0, 0} k (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K))
  [ContinuousSMul.{0, 0} (ZInQ.Contrib.RC53Assist.TameBijective.UnramifiedGaloisGroup K) ↑X] [DiscreteTopology.{0} ↑X]
  [Finite.{1} ↑X] (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} k) (↑X) M)
  (hf :
    ∀ (g : Field.absoluteGaloisGroup.{0} K) (x : ↑X),
      Eq.{1} (f (HSMul.hSMul.{0, 0, 0} ((ZInQ.Contrib.RC53Assist.TameBijective.localUnramifiedProjection K) g) x))
        (HSMul.hSMul.{0, 0, 0} g (f x)))
  (hfs : Function.Surjective.{1, 1} ⇑f)
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0) :
  Function.Bijective.{1, 1} ⇑(ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal hn hβ hβ0 hφ hσI hζ hItriv hnM)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_bijective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_eq_coordQUnr {K : Type} [Field.{0} K] [PerfectField.{0} K]
  [ValuativeRel.{0} K] [TopologicalSpace.{0} K] [IsNonarchimedeanLocalField.{0} K] {k : Type} [Field.{0} k] {M : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} k M] [DistribMulAction.{0, 0} (Field.absoluteGaloisGroup.{0} K) M]
  [SMulCommClass.{0, 0, 0} (Field.absoluteGaloisGroup.{0} K) k M] [TopologicalSpace.{0} M] [DiscreteTopology.{0} M]
  [ContinuousSMul.{0, 0} (Field.absoluteGaloisGroup.{0} K) M] {n : ℕ} [NeZero.{0} n] [Fact (LT.lt.{0} 1 n)] {a : K}
  {β : AlgebraicClosure.{0} K} {φ σ : Field.absoluteGaloisGroup.{0} K}
  (hn :
    n.Coprime (ringChar.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))
  (hβ : Eq.{1} (HPow.hPow.{0, 0, 0} β n) ((Algebra.algebraMap.{0, 0} K (AlgebraicClosure.{0} K)) a)) (hβ0 : Ne.{1} β 0)
  (hφ : TauCeti.IsArithFrobeniusLift.{0} K φ) (hσI : Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) σ)
  (hζ :
    IsPrimitiveRoot.{0}
      (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal.{0} β
        ((ZInQ.Contrib.RC53Assist.TameBijective.algebraicGaloisEquiv K) σ))
      n)
  (hItriv :
    ∀ (g : Field.absoluteGaloisGroup.{0} K),
      Membership.mem.{0, 0} (TauCeti.inertiaSubgroup.{0} K) g → ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} g m) m)
  (hnM : ∀ (m : M), Eq.{1} (HSMul.hSMul.{0, 0, 0} n m) 0)
  (hrel :
    Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} φ σ) (Inv.inv.{0} φ))
      (HPow.hPow.{0, 0, 0} σ
        (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))) :
  Eq.{1} (ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal hn hβ hβ0 hφ hσI hζ hItriv hnM)
    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.coordQUnr φ σ
      (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))))
      (hItriv σ hσI) hrel)
'ZInQ.Contrib.RC53Assist.TameBijective.coordQLocal_eq_coordQUnr' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

```
