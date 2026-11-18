import ZInQKernel.Contrib.CloudB3RC53.Hsw.CupOne
import ZInQKernel.Contrib.CloudB3RC53.Hsw.Descent

/-!
# RC53 cup-one: reverse isotropy from graded commutativity

`Descent.lean` reduced the descent behind `hsw` (tex L2790–2818) to `StrictOrth`. It showed that
`StrictOrth` follows from `ReverseIsotropy`, a homotopy on `U_rel × U_str` (the reverse order of
the isotropy homotopy `h`) with boundary `ι u ∪ ι f t'`. Here `ReverseIsotropy` is built from the
graded commutativity of the local cup product (the cup-one product of `CupOne.lean`) and the given
isotropy homotopy:

  `h'(u, t') = −c • h(t', u) − ι u ∪₁ ι f t'`,   `h'(x, t') = c • h(t', x) + X(ι x, ι f t')`.

## Results

* `CupOneDatum`: an abstract cup-one datum for the local cup product of `SelPairData` in degrees
  `(1, 1)`.
* `reverseIsotropy_of_cupOne`: a cup-one datum gives `ReverseIsotropy` when the strict condition
  vanishes in degree two. This uses only the isotropy identity in degrees `(1, 1) → 2`, which the
  truncated data of `SelPairDataTrunc` also satisfy exactly.
* `sumCupOne`, `sumX2`, `sumCupOne_formula`: the place-wise cup-one product on
  `⊕_v C^•_cont(G_v, −)`.
* `genuineCupOne`: the cup-one datum of the genuine local cup product `galoisPairData`, for a
  `c`-symmetric equivariant self-pairing `β`.
* `genuine_strictOrth`, `genuine_exists_residuePairing`: for the genuine switch, with any
  isotropy data and strict condition complexes vanishing in degree two, `StrictOrth` holds. The
  left-hand side of `hsw` is then a residue pairing `P(eR[g t], eR[g u])`.
* Non-vacuity (LESSON 2):
  * `weil_cSymm`: the Weil pairing is `c`-symmetric with `c = −1`.
  * `exGenuineSwitch_US2`, `exIsotropy`, `exGenuine_residuePairing`: all hypotheses at once on the
    example switch with the trivial module.
  * `exGenuineSwitchW`, `exIsotropyW`, `exGenuineW_residuePairing`: all hypotheses at once with
    `𝔽₂²` coefficients and the nonzero alternating Weil pairing `e₂` (`weil_two_ne_zero`).

## Scope

The hypothesis `US v` vanishing in degree two covers the zero condition and the two-term
unramified complexes in degrees `0, 1`. For a strict condition with nonzero degree-two terms,
`ReverseIsotropy` also needs `h` to be graded-symmetric on strict × strict cochains up to the term
`X`. That is a constraint on the chosen isotropy data and is not automatic.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs

section Abstract

variable {k : Type} [Field k] (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)
  (Q : SelPairData (restrictData D f) D)

/-- **A cup-one datum** for the local cup product of `Q` in degrees `(1, 1)`: a homotopy `C₁₁`
and a correction `X₂` with `d(a ∪₁ b) = −a ∪ b − c • (b ∪ a) + X₂(da, b)` for every local
`1`-cocycle `b` (graded commutativity up to homotopy, with sign `c`). -/
structure CupOneDatum (c : k) where
  /-- The cup-one product `L¹ × L¹ → E_L¹`. -/
  C11 : D.L.X 1 →ₗ[k] D.L.X 1 →ₗ[k] Q.EL.X 1
  /-- The correction term `L² × L¹ → E_L²`. -/
  X2 : D.L.X 2 →ₗ[k] D.L.X 1 →ₗ[k] Q.EL.X 2
  /-- The coboundary formula. -/
  formula : ∀ a b : D.L.X 1, D.L.d 1 2 rfl b = 0 →
    Q.EL.d 1 2 rfl (C11 a b) = -Q.cupL.P 1 1 2 rfl a b - c • Q.cupL.P 1 1 2 rfl b a +
      X2 (D.L.d 1 2 rfl a) b

/-- The isotropy homotopy in degrees `(1, 1)`, arguments swapped. -/
def hUrev11 : D.U.X 1 →ₗ[k] Ustr.X 1 →ₗ[k] Q.EL.X 1 := (Q.hU 1 1 1 rfl).flip

/-- The isotropy homotopy in degrees `(1, 2)`, arguments swapped. -/
def hUrev12 : D.U.X 2 →ₗ[k] Ustr.X 1 →ₗ[k] Q.EL.X 2 := (Q.hU 1 2 2 rfl).flip

/-- **Reverse isotropy from a cup-one datum** (`PROVED`), when the strict condition vanishes in
degree two. Put `h'(u, t') = −c • h(t', u) − ι u ∪₁ ι f t'` in degree one and
`h'(x, t') = c • h(t', x) + X₂(ι x, ι f t')` in degree two. -/
def reverseIsotropy_of_cupOne (c : k) (Cd : CupOneDatum D Ustr f Q c)
    (h2 : ∀ x : Ustr.X 2, x = 0) : ReverseIsotropy D Ustr f Q where
  h11 := -(c • hUrev11 D Ustr f Q) -
    Cd.C11.compl₁₂ (D.ι.f 1 1 rfl) (D.ι.f 1 1 rfl ∘ₗ f.f 1 1 rfl)
  h21 := c • hUrev12 D Ustr f Q + Cd.X2.compl₁₂ (D.ι.f 2 2 rfl) (D.ι.f 1 1 rfl ∘ₗ f.f 1 1 rfl)
  h12 := 0
  iso u t' := by
    have hdt : Ustr.d 1 2 rfl t' = 0 := h2 _
    have hb : D.L.d 1 2 rfl (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) = 0 := by
      rw [← D.ι.comm 1 2 1 2 rfl rfl rfl rfl, ← f.comm 1 2 1 2 rfl rfl rfl rfl, hdt, map_zero,
        map_zero]
    have hform := Cd.formula (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) hb
    have iso : Q.EL.d 1 2 rfl (Q.hU 1 1 1 rfl t' u) + Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl t') u +
        sgn 1 • Q.hU 1 2 2 rfl t' (D.U.d 1 2 rfl u) =
        Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) (D.ι.f 1 1 rfl u) :=
      Q.isotropy 1 2 1 2 1 2 rfl rfl rfl rfl t' u
    have h0 : Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl t') u = 0 :=
      (congrArg (fun z => Q.hU 2 1 2 rfl z u) hdt).trans (LinearMap.map_zero₂ _ _)
    have hda : D.L.d 1 2 rfl (D.ι.f 1 1 rfl u) = D.ι.f 2 2 rfl (D.U.d 1 2 rfl u) :=
      (D.ι.comm 1 2 1 2 rfl rfl rfl rfl u).symm
    rw [h0, add_zero, sgn_one, neg_one_smul] at iso
    rw [hda] at hform
    change Q.EL.d 1 2 rfl (-(c • Q.hU 1 1 1 rfl t' u) -
        Cd.C11 (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))) +
      (c • Q.hU 1 2 2 rfl t' (D.U.d 1 2 rfl u) +
        Cd.X2 (D.ι.f 2 2 rfl (D.U.d 1 2 rfl u)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))) +
      sgn 1 • (0 : Q.EL.X 2) = _
    rw [map_sub, map_neg, map_smul, hform, ← iso, smul_zero, add_zero, smul_add, smul_neg]
    abel
  compat s t' := by
    have hs : s = 0 := h2 s
    subst hs
    change Q.hU 2 1 2 rfl 0 (f.f 1 1 rfl t') =
      c • Q.hU 1 2 2 rfl t' (f.f 2 2 rfl 0) +
        Cd.X2 (D.ι.f 2 2 rfl (f.f 2 2 rfl 0)) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))
    rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, map_zero, smul_zero, map_zero,
      LinearMap.zero_apply, add_zero]

end Abstract

/-! ### The local cup product on continuous cochains -/

section Local

variable {k : Type} [Field k] (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {M T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- The place-wise cup-one product on `⊕_v C¹_cont(G_v, M)`. -/
def sumCupOne : (localSumCx k GS Gv loc M).X 1 →ₗ[k] (localSumCx k GS Gv loc M).X 1 →ₗ[k]
    (localSumCx k GS Gv loc T).X 1 :=
  LinearMap.mk₂ k (fun a b v =>
      contCupOne (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v)) (a v) (b v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by
      funext v
      exact LinearMap.map_smul₂
        (contCupOne (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))) _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun c a b => by
      funext v
      exact map_smul (contCupOne (resPairing k GS β (loc v))
        (resPairing_continuous k GS β hβc (loc v)) (a v)) c (b v))

/-- The place-wise correction term `⊕_v C²_cont × ⊕_v C¹_cont → ⊕_v C²_cont`. -/
def sumX2 : (localSumCx k GS Gv loc M).X 2 →ₗ[k] (localSumCx k GS Gv loc M).X 1 →ₗ[k]
    (localSumCx k GS Gv loc T).X 2 :=
  LinearMap.mk₂ k (fun a b v =>
      contX2 (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v)) (a v) (b v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by
      funext v
      exact LinearMap.map_smul₂
        (contX2 (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))) _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun c a b => by
      funext v
      exact map_smul (contX2 (resPairing k GS β (loc v))
        (resPairing_continuous k GS β hβc (loc v)) (a v)) c (b v))

omit [IsTopologicalGroup GS] in
/-- **The cup-one formula for the local cup product** `⊕_v` (`PROVED`, place-wise
`contCupOne_d`). -/
theorem sumCupOne_formula (hβ : ∀ (g : GS) (a b : M), β (g • a) (g • b) = g • β a b) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (a b : (localSumCx k GS Gv loc M).X 1)
    (hb : (localSumCx k GS Gv loc M).d 1 2 rfl b = 0) :
    (localSumCx k GS Gv loc T).d 1 2 rfl (sumCupOne GS Gv loc β hβc a b) =
      -(localSumPair k GS Gv loc β hβ hβc).P 1 1 2 rfl a b -
        c • (localSumPair k GS Gv loc β hβ hβc).P 1 1 2 rfl b a +
        sumX2 GS Gv loc β hβc ((localSumCx k GS Gv loc M).d 1 2 rfl a) b := by
  funext v
  exact contCupOne_d (resPairing k GS β (loc v)) (resPairing_continuous k GS β hβc (loc v))
    (fun h x y => hβ (loc v h) x y) c hc (a v) (b v) (congrFun hb v)

end Local

/-! ### The genuine switch -/

section Genuine

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **The cup-one datum of the genuine local cup product** (`PROVED`). Let `β : M × M → T` be a
`c`-symmetric equivariant self-pairing, `β x y = c • β y x`. Then the local cup product of the
genuine pairing data `galoisPairData` is graded-commutative up to the place-wise cup-one product
of continuous cochains. -/
def genuineCupOne (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR) :
    CupOneDatum X.toQuasi.D (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) c where
  C11 := sumCupOne (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
    (continuous_pairing β)
  X2 := sumX2 (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
    (continuous_pairing β)
  formula a b hb := sumCupOne_formula (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β (continuous_pairing β) hβ c hc a b hb

/-- **`StrictOrth` for the genuine switch** (`PROVED`). Let `β` be a `c`-symmetric equivariant
self-pairing, let `I` be any isotropy data for (strict, relaxed), and suppose the strict condition
complexes vanish in degree two (true for the zero condition and for the two-term unramified
complexes in degrees `0, 1`). Then the cone-trace cup product vanishes on strict cocycles in the
second slot. -/
theorem genuine_strictOrth (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) :
    StrictOrth X.toQuasi.D (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr :=
  strictOrth_of_reverseIsotropy _ _ _ _ tr htr
    (reverseIsotropy_of_cupOne _ _ _ _ c (genuineCupOne X β hβ c hc I)
      (fun x => funext fun v => hUS2 v (x v)))

/-- **The descent for the genuine switch** (tex L2790–2818), `PROVED`. Under the hypotheses of
`genuine_strictOrth`, the left-hand side of `hsw` for the genuine pairing data is a residue
pairing: `tr((0, s, −ι u) ∪ (0, t, 0)) = P(eR[g t], eR[g u])` for a bilinear form `P`. -/
theorem genuine_exists_residuePairing (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b) (c : k)
    (hc : ∀ x y, β x y = c • β y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) :
    ∃ P, ResiduePairing X.toQuasi (piCx X.US) (piMap X.φ)
      (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr P :=
  exists_residuePairing X.toQuasi (piCx X.US) (piMap X.φ) _ tr X.hfg X.φ_inj X.g_surj X.ex htr
    (genuine_strictOrth X β hβ c hc I tr htr hUS2)

end Genuine

/-! ### Non-vacuity (LESSON 2) -/

section NonVacuity

/-- The Weil pairing `e₂(x, y) = x₀ y₁ − x₁ y₀` is `c`-symmetric with `c = −1`, the hypothesis
`hc` of `genuine_strictOrth`. `PROVED`. -/
theorem weil_cSymm {k : Type} [Field k] (x y : Fin 2 → k) :
    ZInQ.Manuscript.RC.Uniform.weil x y = (-1 : k) • ZInQ.Manuscript.RC.Uniform.weil y x := by
  rw [ZInQ.Manuscript.RC.Uniform.weil_swap, smul_eq_mul]
  ring

/-- The genuine switch example `exGenuineSwitch` has strict condition complexes vanishing in
degree two, the hypothesis `hUS2` of `genuine_strictOrth`. `PROVED`. -/
theorem exGenuineSwitch_US2 {k : Type} [Field k] (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ v (x : ((exGenuineSwitch (k := k) K q).US v).X 2), x = 0 :=
  fun _ _ => rfl

/-- Zero isotropy data for the example switch, with the zero pairing on the trivial module. -/
def exIsotropy {k : Type} [Field k] (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    GaloisIsotropyData K {q} k
      (0 : TrivMod (GKS K {q}) PUnit →ₗ[k] TrivMod (GKS K {q}) PUnit →ₗ[k]
        TrivMod (GKS K {q}) PUnit) (fun _ _ _ => rfl)
      (exGenuineSwitch (k := k) K q).ΔS (exGenuineSwitch (k := k) K q).ΔR where
  h _ _ _ _ _ := 0
  isotropy _ _ _ _ _ _ _ _ _ _ _ _ _ := by
    simp only [LinearMap.zero_apply, map_zero, smul_zero, add_zero]
    exact (map_zero _).symm

/-- **End-to-end non-vacuity** (`PROVED`): all hypotheses of `genuine_exists_residuePairing` hold
together for the example genuine switch (zero pairing, `c = 1`, zero isotropy data, zero
trace). -/
theorem exGenuine_residuePairing {k : Type} [Field k] (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ P, ResiduePairing (exGenuineSwitch (k := k) K q).toQuasi (piCx (exGenuineSwitch K q).US)
      (piMap (exGenuineSwitch K q).φ) (galoisPairData K {q} k _ _ _ _ (exIsotropy K q)) 0 P :=
  genuine_exists_residuePairing (exGenuineSwitch (k := k) K q) _ _ (1 : k) (fun _ _ => rfl)
    (exIsotropy K q) 0
    (fun _ => rfl) (exGenuineSwitch_US2 K q)

/-- The `𝔽₂²` coefficient module with the trivial action. -/
abbrev WMod (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type :=
  TrivMod (GKS K {q}) (Fin 2 → ZMod 2)

/-- The `𝔽₂` target module with the trivial action. -/
abbrev WTarget (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type :=
  TrivMod (GKS K {q}) (ZMod 2)

/-- The Weil pairing `e₂` on `𝔽₂²`, as a pairing of trivial modules. -/
def weilW (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    WMod K q →ₗ[ZMod 2] WMod K q →ₗ[ZMod 2] WTarget K q :=
  ZInQ.Manuscript.RC.Uniform.weil (K := ZMod 2)

/-- The example genuine switch with coefficients `𝔽₂²`: the same data as `exGenuineSwitch`. -/
def exGenuineSwitchW (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    GenuineSwitch K {q} (ZMod 2) (WMod K q) where
  ΔR := ⟨fun _ => constCx ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)), fun _ => zeroGHom _ _⟩
  US _ := ZInQ.Manuscript.RC.SelmerComplex.zeroCx (ZMod 2)
  φ _ := zeroGHom _ _
  W := constCx ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
  g :=
    { f := fun n m h => by
        subst h
        exact LinearMap.proj (R := ZMod 2)
          (φ := fun _ : Places K {q} => ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))) ⟨q, rfl⟩
      comm := fun i i₁ j j₁ hij h₁ h₂ hj x => by
        subst hij hj
        rfl }
  hfg _ _ := rfl
  φ_inj _ _ _ _ := funext fun _ => rfl
  g_surj _ y := ⟨fun _ => y, rfl⟩
  ex n u hu := ⟨0, by
    funext v
    have hv : v = ⟨q, rfl⟩ := Subsingleton.elim _ _
    subst hv
    exact hu.symm⟩
  eR := constCxH1 _

/-- Zero isotropy data for the `𝔽₂²` example, with the Weil pairing. -/
def exIsotropyW (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    GaloisIsotropyData K {q} (ZMod 2) (weilW K q) (fun _ _ _ => rfl)
      (exGenuineSwitchW K q).ΔS (exGenuineSwitchW K q).ΔR where
  h _ _ _ _ _ := 0
  isotropy _ _ _ _ _ _ _ _ _ _ _ _ _ := by
    simp only [LinearMap.zero_apply, map_zero, smul_zero, add_zero]
    exact (map_zero _).symm

/-- **End-to-end non-vacuity with the Weil pairing** (`PROVED`): all hypotheses of
`genuine_exists_residuePairing` hold together for the `𝔽₂²` example with the nonzero alternating
Weil pairing `e₂` (`c = −1`, `weil_cSymm`). -/
theorem exGenuineW_residuePairing (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ P, ResiduePairing (exGenuineSwitchW K q).toQuasi (piCx (exGenuineSwitchW K q).US)
      (piMap (exGenuineSwitchW K q).φ)
      (galoisPairData K {q} (ZMod 2) _ _ _ _ (exIsotropyW K q)) 0 P :=
  genuine_exists_residuePairing (exGenuineSwitchW K q) (weilW K q) (fun _ _ _ => rfl) (-1)
    (fun x y => (weil_cSymm (k := ZMod 2) x y : _)) (exIsotropyW K q) 0 (fun _ => rfl)
    (fun _ _ => rfl)

/-- The Weil pairing of the example is nonzero. -/
theorem weil_two_ne_zero :
    ZInQ.Manuscript.RC.Uniform.weil (K := ZMod 2) (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  simp [ZInQ.Manuscript.RC.Uniform.weil_apply]

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.Hsw
