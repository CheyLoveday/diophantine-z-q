import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncIsotropyGenuine
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncTrace
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchDuality
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Orthogonality
import ZInQKernel.Contrib.CloudB3RC53.Duality.KummerTruncIsotropy

/-!
# Lane RC26 (round 4): genuine Selmer duality from `τ≥2` isotropy data

Manuscript `diophantine_zq.tex`: Lemma `ex:arith-conjugate-duality` (tex 2761–2830), (4.3) (tex
3455–3463), Lemma `ex:arith-local-kummer` (tex 3413–3456), tex 3829–3835, and the switch
(tex 5055–5075); Nekovář, *Selmer complexes* (Astérisque 310): 5.4.1–5.4.3 (the global trace on
`E_3 = Cone(τ_{≥2} C(G_S, J(1)) → ⊕_v τ_{≥2} C(G_v, J(1)))[−1]`), 6.2.1.3, 6.2.7, 6.3.1–6.3.4.

The isotropy input is restated in Nekovář's convention (local products into `τ≥2`), and the
round-1/2 results are re-derived from it:

* data: `GaloisTruncIsotropyData`, `galoisPairDataTrunc` (`SelPairDataTrunc`), `galoisPairDataT`
  (`SelPairData` over `τ≥2`), `galoisCompactTT` (the truncated compact cone);
* the per-place bridge to the consumer interface `Duality.LocalTruncIsotropy`
  (`TruncIsotropyData.toLocal`, `TruncIsotropyData.ofLocal`, mutually inverse), and the Kummer
  plug-in `TruncIsotropyData.ofKummer` (via `Duality.kummerTruncIsotropy`);
* PRINTs restated: `NekovarProp543T` (global duality with the trace on the truncated cone),
  `NekovarProp541T`; **`nekovarProp543T_iff : NekovarProp543T K ↔ NekovarProp543 K`** (PROVED: the
  global duality map involves no isotropy homotopy, and traces on the full and truncated cones
  correspond) and `nekovarProp541T_of` (PROVED);
* `OrthogonalComplementsT`, `genuineSelmerDualityT`, `orthogonal_relaxed_strictT`,
  `orthogonal_strict_relaxedT(_of_print)`, `GenuineSwitch.adjunction_of_printsT` and
  `GenuineSwitch.adjunction_of_truncData` (the other group's `switchAdjunction_of_trunc`, its
  duality hypothesis supplied by `genuineSelmerDualityT`);
* **the full-target versions are special cases**: `orthogonalComplements_iff_toTrunc`,
  `selmerDualityMap_toTrunc_galois`, `genuineSelmerDuality_special`,
  `GenuineSwitch.adjunction_of_prints_special` (the round-1/2 statements, now as corollaries of the
  truncated ones through `IsotropyData.toTrunc` and the descended trace).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Manuscript.RC.Uniform

/-! ### Bridge to the per-place interface -/

section Bridge

universe u

variable {k : Type u} [CommRing k] {GS : Type u} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS]
  {ι : Type u} {Gv : ι → Type u} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {A B T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction GS A] [SMulCommClass GS k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul GS A]
  [AddCommGroup B] [Module k B] [DistribMulAction GS B] [SMulCommClass GS k B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul k B] [ContinuousSMul GS B]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  {β : A →ₗ[k] B →ₗ[k] T} {hβ : ∀ (g : GS) (a : A) (b : B), β (g • a) (g • b) = g • β a b}
  {hβc : Continuous fun x : A × B => β x.1 x.2}
  {ΔA : LocalConditions k GS Gv loc A} {ΔB : LocalConditions k GS Gv loc B}

/-- **Truncated isotropy data, place by place, satisfy the per-place interface**
`Duality.LocalTruncIsotropy (ΔA.i v) (ΔB.i v) (localPair v)` (same fields). -/
def TruncIsotropyData.toLocal (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB) (v : ι) :
    ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy (ΔA.i v) (ΔB.i v)
      (localPair k GS Gv loc β hβ hβc v) :=
  ⟨I.h v, I.isotropy₂ v, I.isotropy₃ v⟩

/-- **Per-place interface data give truncated isotropy data** (so per-place constructions, e.g.
the Kummer conditions, plug in). -/
def TruncIsotropyData.ofLocal
    (J : ∀ v, ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy (ΔA.i v) (ΔB.i v)
      (localPair k GS Gv loc β hβ hβc v)) :
    TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB :=
  ⟨fun v => (J v).h, fun v => (J v).isotropy₂, fun v => (J v).isotropy₃⟩

omit [IsTopologicalGroup GS] in
/-- `ofLocal ∘ toLocal = id`. -/
theorem TruncIsotropyData.ofLocal_toLocal (I : TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB) :
    TruncIsotropyData.ofLocal I.toLocal = I :=
  rfl

omit [IsTopologicalGroup GS] in
/-- `toLocal ∘ ofLocal = id`. -/
theorem TruncIsotropyData.toLocal_ofLocal
    (J : ∀ v, ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy (ΔA.i v) (ΔB.i v)
      (localPair k GS Gv loc β hβ hβc v)) :
    (TruncIsotropyData.ofLocal J).toLocal = J :=
  rfl

/-- **The Kummer conditions plug in** (Lemma `ex:arith-local-kummer`, tex 3443–3450, at finite
level, via the other group's `kummerTruncIsotropy`): local conditions concentrated in degrees
`0, 1`, local traces whose kernel on degree-two cocycles consists of coboundaries, and vanishing
traces of the `(1, 1)` cup values give truncated isotropy data (zero homotopies). -/
def TruncIsotropyData.ofKummer
    (hA : ∀ v, ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.VanishesOutside (ΔA.U v)
      (fun i => i = 0 ∨ i = 1))
    (hB : ∀ v, ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.VanishesOutside (ΔB.U v)
      (fun i => i = 0 ∨ i = 1))
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (hker : ∀ v (z : (localCx k GS Gv loc T v).X 2), (localCx k GS Gv loc T v).d 2 3 rfl z = 0 →
      trv v z = 0 → ∃ y, (localCx k GS Gv loc T v).d 1 2 rfl y = z)
    (hcup : ∀ v (x : (ΔA.U v).X 1) (y : (ΔB.U v).X 1),
      trv v ((localPair k GS Gv loc β hβ hβc v).P 1 1 2 rfl ((ΔA.i v).f 1 1 rfl x)
        ((ΔB.i v).f 1 1 rfl y)) = 0) :
    TruncIsotropyData k GS Gv loc β hβ hβc ΔA ΔB :=
  TruncIsotropyData.ofLocal fun v =>
    ZInQ.Contrib.CloudB3RC53.Duality.kummerTruncIsotropy (hA v) (hB v) (trv v) (hker v) (hcup v)

end Bridge

/-! ### The `τ≥2` restatement for the Galois data -/

variable (K : Type) [Field K] [NumberField K]

section Data

variable (S : Set (HeightOneSpectrum (𝓞 K))) (R : Type) [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- Truncated isotropy data for the Galois Selmer data (Nekovář 6.2.1.3, 6.3.1: local products
into `τ_{≥2} C^•_cont(G_{K_v}, T)`). -/
abbrev GaloisTruncIsotropyData (ΔA : GaloisLocalConditions K S R M)
    (ΔB : GaloisLocalConditions K S R M') : Type :=
  TruncIsotropyData R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    (continuous_pairing β) ΔA ΔB

/-- The genuine truncated pairing data on the Galois Selmer data (`SelPairDataTrunc`). -/
abbrev galoisPairDataTrunc (ΔA : GaloisLocalConditions K S R M)
    (ΔB : GaloisLocalConditions K S R M') (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB) :
    SelPairDataTrunc (galoisSelData K S R M ΔA) (galoisSelData K S R M' ΔB) :=
  genuinePairDataTrunc R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
    hβ (continuous_pairing β) ΔA ΔB I

/-- The genuine Selmer pairing data over `τ≥2` on the Galois Selmer data. -/
abbrev galoisPairDataT (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
    (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB) :
    SelPairData (galoisSelData K S R M ΔA) (galoisSelData K S R M' ΔB) :=
  (galoisPairDataTrunc K S R β hβ ΔA ΔB I).toSelPairData

/-- The truncated compact cone `Cone(C(G_{K,S}, T) → ⊕_v τ_{≥2} C(G_v, T))[−1]` (Nekovář's `E_3`
of 5.4.1 up to the truncation of the global term, which does not change degree three). -/
abbrev galoisCompactTT (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
    (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB) : GCx R :=
  coneCx (galoisPairDataT K S R β hβ ΔA ΔB I).resE

end Data

/-- **PRINT — Nekovář 5.4.3 (p. 126), with the trace of 5.4.1 on the truncated cone**: as
`NekovarProp543`, for truncated isotropy data and a trace on
`Cone(C(G_{K,S}, T) → ⊕_v τ_{≥2} C(G_v, T))[−1]` killing coboundaries and inducing `H³ ≅ R`, the
global duality map `a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^i res a ∪ y))` is a quasi-isomorphism. Equivalent
to `NekovarProp543` (`nekovarProp543T_iff`). -/
def NekovarProp543T : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R →
    ∀ (M M' T : Type)
      [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
      [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
      [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
      [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
      [ContinuousSMul (GKS K S) M'] [Finite M']
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
      (β : M →ₗ[R] M' →ₗ[R] T)
      (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b),
      Function.Bijective β → Function.Bijective β.flip → IsCyclotomicTwist K S R T →
      ∀ (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
        (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB)
        (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
        (htr : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0),
        InducesIsoH3 tr →
        QuasiIso (GHom.toCC (globalDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr))

/-- **PRINT — Nekovář 5.4.1 on the truncated cone**: a trace on the truncated compact cone killing
coboundaries and inducing `H³ ≅ R` exists. Follows from `NekovarProp541` (`nekovarProp541T_of`). -/
def NekovarProp541T : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R →
    ∀ (M M' T : Type)
      [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
      [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
      [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
      [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
      [ContinuousSMul (GKS K S) M']
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
      (β : M →ₗ[R] M' →ₗ[R] T)
      (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b),
      IsCyclotomicTwist K S R T →
      ∀ (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
        (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB),
        ∃ (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
          (_ : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0), InducesIsoH3 tr

/-! ### The restated PRINTs are equivalent to the old ones -/

section Equivalence

/-- **The global term of the Selmer cup product**: `(a, 0, 0) ∪ (b, 0, y) =
(a ∪ b, (−1)^i res a ∪ y)` — no local condition and no isotropy homotopy enters. PROVED. -/
theorem selCupFun_global {S : Type} [CommRing S] {D D' : SelData S} (Q : SelPairData D D')
    (i j k : ℤ) (h : i + j = k) (a : D.G.X i) (b : D'.G.X j) (y : D'.L.X (j - 1)) :
    selCupFun Q i j k h ((a, 0, 0) : selT D i) ((b, 0, y) : selT D' j) =
      ((Q.cupG.P i j k h a b, sgn i • Q.cupL.P i (j - 1) (k - 1) (by omega) (D.res.f i i rfl a) y) :
        coneT Q.resE k) := by
  refine Prod.ext rfl ?_
  change Q.cupL.P (i - 1) j (k - 1) _ 0 (D'.ι.f j j rfl 0) +
      sgn i • Q.cupL.P i (j - 1) (k - 1) _ (D.res.f i i rfl a) y + Q.hU i j (k - 1) _ 0 0 = _
  simp

/-- **The new global PRINT implies the old one** (the old statement is the special case
`I.toTrunc` with the descended trace). PROVED. -/
theorem nekovarProp543_of_T (h : NekovarProp543T K) : NekovarProp543 K := by
  intro S p R _ _ hset M M' T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ β hβ hb hb' hT ΔA ΔB I
    tr0 htr0 h3
  have hQ := h S p R hset M M' T β hβ hb hb' hT ΔA ΔB I.toTrunc
    ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT tr0 htr0)
    ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT_kills tr0 htr0)
    ((inducesIsoH3_trT_iff (galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc) tr0 htr0).2 h3)
  have e : GHom.toCC (globalDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I.toTrunc)
      ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT tr0 htr0)
      ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT_kills tr0 htr0)) =
      GHom.toCC (globalDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr0 htr0) :=
    (dualityMaps_toTrunc (galoisPairData K S R β hβ ΔA ΔB I) tr0 htr0).2.2
  rw [e] at hQ
  exact hQ

/-- **The old global PRINT implies the new one**: the global duality map does not involve local
conditions or isotropy homotopies (`selCupFun_global`), so it may be computed with the strict
conditions and zero homotopies, and traces on the truncated and full cones correspond
(`trOfTrunc`, `inducesIsoH3_trOfTrunc_iff`). PROVED. -/
theorem nekovarProp543T_of (h : NekovarProp543 K) : NekovarProp543T K := by
  intro S p R _ _ hset M M' T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ β hβ hb hb' hT ΔA ΔB I
    tr htr h3
  have hQ := h S p R hset M M' T β hβ hb hb' hT (strictConditions R _ _ _ M)
    (strictConditions R _ _ _ M')
    (strictIsotropy R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
      (continuous_pairing β))
    (trOfTrunc (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr)
    (trOfTrunc_kills (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr htr)
    ((inducesIsoH3_trOfTrunc_iff (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr).2 h3)
  have e : GHom.toCC (globalDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr) =
      GHom.toCC (globalDualityMap (galoisPairData K S R β hβ (strictConditions R _ _ _ M)
        (strictConditions R _ _ _ M')
        (strictIsotropy R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
          hβ (continuous_pairing β)))
        (trOfTrunc (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr)
        (trOfTrunc_kills (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr htr)) := by
    refine GHom.toCC_ext fun i a => dualCx_ext fun c' => ?_
    obtain ⟨b, y⟩ := c'
    have e1 := globalDualityMap_apply (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr i a b y
    have e2 := globalDualityMap_apply (galoisPairData K S R β hβ (strictConditions R _ _ _ M)
      (strictConditions R _ _ _ M')
      (strictIsotropy R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
        (continuous_pairing β)))
      (trOfTrunc (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr)
      (trOfTrunc_kills (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr htr) i a b y
    have g1 := congrArg tr
      (selCupFun_global (galoisPairDataT K S R β hβ ΔA ΔB I) i (3 - i) 3 (by omega) a b y)
    have g2 := (congrArg (trOfTrunc (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr)
      (selCupFun_global (galoisPairData K S R β hβ (strictConditions R _ _ _ M)
        (strictConditions R _ _ _ M')
        (strictIsotropy R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
          hβ (continuous_pairing β))) i (3 - i) 3 (by omega) a b y)).trans
      (trOfTrunc_apply (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr _)
    refine e1.trans ((g1.trans (Eq.trans ?_ g2.symm)).trans e2.symm)
    congr 1
  rw [e]
  exact hQ

/-- **The restated global PRINT is equivalent to the old one.** PROVED. -/
theorem nekovarProp543T_iff : NekovarProp543T K ↔ NekovarProp543 K :=
  ⟨nekovarProp543_of_T K, nekovarProp543T_of K⟩

/-- **The truncated trace PRINT from the old one** (descend the trace of the full cone). PROVED. -/
theorem nekovarProp541T_of (h : NekovarProp541 K) : NekovarProp541T K := by
  intro S p R _ _ hset M M' T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ β hβ hT ΔA ΔB I
  obtain ⟨tr0, htr0, h3⟩ := h S p R hset M M' T β hβ hT (strictConditions R _ _ _ M)
    (strictConditions R _ _ _ M')
    (strictIsotropy R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
      (continuous_pairing β))
  exact ⟨(galoisPairDataTrunc K S R β hβ ΔA ΔB I).trT tr0 htr0,
    (galoisPairDataTrunc K S R β hβ ΔA ΔB I).trT_kills tr0 htr0,
    (inducesIsoH3_trT_iff (galoisPairDataTrunc K S R β hβ ΔA ΔB I) tr0 htr0).2 h3⟩

end Equivalence

/-! ### The abstract inputs and finite Selmer duality, from truncated isotropy -/

section Inputs

variable {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
  (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB)
  (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
  (htr : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0)

/-- **`GlobalDualityInput` for the genuine `τ≥2` data, from the PRINT** `NekovarProp543T`. -/
theorem globalDualityInputT_of_print (h : NekovarProp543T K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) (htr3 : InducesIsoH3 tr)
    (P : PerfectCoefficientPairing R) :
    GlobalDualityInput (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr P :=
  h S p R hset M M' T β hβ hb hb' hT ΔA ΔB I tr htr htr3

/-- **Nekovář's orthogonality with `τ≥2` isotropy** (6.2.2, 6.2.7, with `prod_v` into
`τ_{≥2} C(G_v, T)`): the local duality map
`(u, x) ↦ (v ↦ tr(0, x ∪ i' v + h(u, v) mod d(C¹)))` of the truncated data is a
quasi-isomorphism. -/
def OrthogonalComplementsT : Prop :=
  QuasiIso (GHom.toCC (localDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr))

/-- `LocalOrthogonalityInput` for the truncated genuine data is `OrthogonalComplementsT`. -/
theorem localOrthogonalityInputT_iff (P : PerfectCoefficientPairing R) :
    LocalOrthogonalityInput (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr P ↔
      OrthogonalComplementsT K β hβ ΔA ΔB I tr htr :=
  Iff.rfl

/-- **Finite Selmer duality for the genuine complexes, from `τ≥2` isotropy** (Lemma
`ex:arith-conjugate-duality`, tex 2761–2830; (4.3), tex 3455–3463; Nekovář 6.3.4): from the PRINT
`NekovarProp543T` (equivalently `NekovarProp543`) and the orthogonality of the local conditions with
truncated isotropy data, the genuine Selmer duality map of the `τ≥2` data is a quasi-isomorphism.
PROVED (by `finiteSelmerDualityNode_proof`). -/
theorem genuineSelmerDualityT (h : NekovarProp543T K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) (htr3 : InducesIsoH3 tr)
    (horth : OrthogonalComplementsT K β hβ ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr)) := by
  have hT' := hT
  obtain ⟨N, -, e, -⟩ := hT'
  exact finiteSelmerDualityNode_proof R _ _ (galoisPairDataT K S R β hβ ΔA ΔB I) tr htr
    (perfectOfTwist β e hb hb') (Or.inl hset.selfInjective)
    (globalDualityInputT_of_print K β hβ ΔA ΔB I tr htr h p hset hb hb' hT htr3 _) horth

end Inputs

/-! ### Orthogonality of the full and the zero condition, from truncated isotropy -/

section Orthogonal

variable {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- **The full condition is the orthogonal complement of the zero condition, with truncated
isotropy** (tex 2813–2816): for any truncated isotropy data and any trace on the truncated cone,
the local duality map is a quasi-isomorphism (both sides are acyclic). PROVED. -/
theorem orthogonal_relaxed_strictT
    (I : GaloisTruncIsotropyData K S R β hβ (relaxedConditions R _ _ _ M)
      (strictConditions R _ _ _ M'))
    (tr : (galoisCompactTT K S R β hβ _ _ I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ _ _ I).d 2 3 rfl z) = 0) :
    OrthogonalComplementsT K β hβ _ _ I tr htr := by
  unfold OrthogonalComplementsT
  apply quasiIso_of_acyclic
  · rw [acyclic_toCC_iff]
    exact relaxed_locCx_acyclic (k := R) (GS := GKS K S) (Gv := fun v : Places K S => Gloc K v.1)
      (loc := fun v => locMap K S v.1) (M := M)
  · rw [acyclic_toCC_iff]
    intro i j l hij hjl φ _
    refine ⟨0, dualCx_ext fun x => ?_⟩
    have hx : x = 0 := funext fun _ => rfl
    rw [hx, map_zero, map_zero]

/-- **The zero condition is the orthogonal complement of the full condition, with truncated
isotropy** (Nekovář 6.2.7 via local duality 5.2.4; tex 2813–2816): for finitely many places,
local traces `tr_v` killing coboundaries with every local duality map a quasi-isomorphism, any
truncated isotropy data, and a trace on the truncated cone whose local part is `∑_v tr_v`, the
zero condition on `M` and the full condition on `M'` are orthogonal complements. PROVED (the local
duality map of the truncated data is that of the round-1 data for the trace `trOfTrunc tr`). -/
theorem orthogonal_strict_relaxedT [Fintype (Places K S)]
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0)
    (hqi : ∀ v, QuasiIso (GHom.toCC (adjHom (localPair R (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ (continuous_pairing β) v)
        2 (trv v) (htrv v))))
    (I : GaloisTruncIsotropyData K S R β hβ (strictConditions R _ _ _ M)
      (relaxedConditions R _ _ _ M'))
    (tr : (galoisCompactTT K S R β hβ _ _ I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ _ _ I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K β hβ _ _ I tr htr := by
  have h0 := orthogonal_strict_relaxed K β hβ trv htrv hqi
    (trOfTrunc (galoisPairDataTrunc K S R β hβ _ _ I) tr)
    (trOfTrunc_kills (galoisPairDataTrunc K S R β hβ _ _ I) tr htr)
    (fun z => (trOfTrunc_apply (galoisPairDataTrunc K S R β hβ _ _ I) tr _).trans (hsum z))
  unfold OrthogonalComplements at h0
  unfold OrthogonalComplementsT
  have e : GHom.toCC (localDualityMap (galoisPairDataT K S R β hβ _ _ I) tr htr) =
      GHom.toCC (localDualityMap (galoisPairData K S R β hβ _ _ (strictRelaxedIsotropy K β hβ))
        (trOfTrunc (galoisPairDataTrunc K S R β hβ _ _ I) tr)
        (trOfTrunc_kills (galoisPairDataTrunc K S R β hβ _ _ I) tr htr)) := by
    refine (dualityMaps_eq_of_trace_eq _ _ _ _ _ _ fun i c c' => ?_).2.1
    obtain ⟨a, u, x⟩ := c
    have hu : u = 0 := funext fun _ => rfl
    subst hu
    refine (congrArg tr (selCupFun_toSelPairData (galoisPairDataTrunc K S R β hβ _ _ I) i (3 - i) 3
      (by omega) (a, 0, x) c')).trans
      (Eq.trans ?_ (trOfTrunc_apply (galoisPairDataTrunc K S R β hβ _ _ I) tr _).symm)
    congr 1
    refine Prod.ext rfl ?_
    change (truncSub _ (3 - 1)).mkQ _ = (truncSub _ (3 - 1)).mkQ _
    congr 1
    simp [selCupFunT, selCupFun]
    rfl
  rw [e]
  exact h0

/-- **`orthogonal_strict_relaxedT` from the local duality PRINT** (`NekovarProp524`, Nekovář
5.2.4). PROVED. -/
theorem orthogonal_strict_relaxedT_of_print (h : NekovarProp524 K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) [Fintype (Places K S)]
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (I : GaloisTruncIsotropyData K S R β hβ (strictConditions R _ _ _ M)
      (relaxedConditions R _ _ _ M'))
    (tr : (galoisCompactTT K S R β hβ _ _ I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ _ _ I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K β hβ _ _ I tr htr :=
  orthogonal_strict_relaxedT K β hβ trv htrv
    (fun v => h S p R hset M M' T β hβ hb hb' hT v (trv v) (htrv v) (htrv2 v)) I tr htr hsum

end Orthogonal

/-! ### The full-target versions as special cases -/

section Special

variable {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
  (I : GaloisIsotropyData K S R β hβ ΔA ΔB)
  (tr₀ : (galoisCompactT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
  (htr₀ : ∀ z, tr₀ ((galoisCompactT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0)

/-- **The round-1 orthogonality is the truncated one for `I.toTrunc`** and the descended trace
(the two local duality maps coincide). PROVED. -/
theorem orthogonalComplements_iff_toTrunc :
    OrthogonalComplements K β hβ ΔA ΔB I tr₀ htr₀ ↔
      OrthogonalComplementsT K β hβ ΔA ΔB I.toTrunc
        ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT tr₀ htr₀)
        ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT_kills tr₀ htr₀) := by
  have e : GHom.toCC (localDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I.toTrunc)
      ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT tr₀ htr₀)
      ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT_kills tr₀ htr₀)) =
      GHom.toCC (localDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr₀ htr₀) :=
    (dualityMaps_toTrunc (galoisPairData K S R β hβ ΔA ΔB I) tr₀ htr₀).2.1
  unfold OrthogonalComplements OrthogonalComplementsT
  rw [e]

/-- **The round-1 Selmer duality map is the truncated one for `I.toTrunc`** and the descended
trace. PROVED. -/
theorem selmerDualityMap_toTrunc_galois :
    GHom.toCC (selmerDualityMap (galoisPairDataT K S R β hβ ΔA ΔB I.toTrunc)
      ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT tr₀ htr₀)
      ((galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc).trT_kills tr₀ htr₀)) =
      GHom.toCC (selmerDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr₀ htr₀) :=
  (dualityMaps_toTrunc (galoisPairData K S R β hβ ΔA ΔB I) tr₀ htr₀).1

/-- **The round-1 `genuineSelmerDuality` as a special case of `genuineSelmerDualityT`**: the same
statement (full-target isotropy `I`, trace `tr₀` on the full cone, `NekovarProp543`), derived from
the truncated theorem through `I.toTrunc`, the descended trace and `nekovarProp543T_iff`. PROVED. -/
theorem genuineSelmerDuality_special (h : NekovarProp543 K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) (htr3 : InducesIsoH3 tr₀)
    (horth : OrthogonalComplements K β hβ ΔA ΔB I tr₀ htr₀) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr₀ htr₀)) := by
  have hq := genuineSelmerDualityT K β hβ ΔA ΔB I.toTrunc _ _ ((nekovarProp543T_iff K).2 h) p hset
    hb hb' hT ((inducesIsoH3_trT_iff (galoisPairDataTrunc K S R β hβ ΔA ΔB I.toTrunc) tr₀ htr₀).2
      htr3) ((orthogonalComplements_iff_toTrunc K β hβ ΔA ΔB I tr₀ htr₀).1 horth)
  rw [selmerDualityMap_toTrunc_galois K β hβ ΔA ΔB I tr₀ htr₀] at hq
  exact hq

end Special

/-! ### The switch adjunction from truncated isotropy -/

section Switch

variable {K} {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k] {M : Type} [AddCommGroup M]
  [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **The switch adjunction from the PRINTs, with truncated isotropy** (tex 5055–5075; Nekovář
6.3.3–6.3.4): as `GenuineSwitch.adjunction_of_prints`, with `τ≥2` isotropy data for
(strict, relaxed), a trace on the truncated compact cone, `NekovarProp543T` and
`OrthogonalComplementsT`. PROVED (the duality quasi-isomorphism is `genuineSelmerDualityT`). -/
theorem GenuineSwitch.adjunction_of_printsT (X : GenuineSwitch K S k M) (h543 : NekovarProp543T K)
    (p : ℕ) (hset : NekovarFiniteSetting K S p k) [Finite M] (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S k T)
    (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (galoisCompactTT K S k β hβ X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactTT K S k β hβ X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) (horth : OrthogonalComplementsT K β hβ X.ΔS X.ΔR I tr htr)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hsw : X.SwitchCoordinates (galoisPairDataT K S k β hβ X.ΔS X.ΔR I) tr ε σ J) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  X.adjunction (galoisPairDataT K S k β hβ X.ΔS X.ΔR I) tr htr ε σ J hε hσ hJ2
    (genuineSelmerDualityT K β hβ X.ΔS X.ΔR I tr htr h543 p hset hb hb' hT htr3 horth) hsw

/-- **The other group's `switchAdjunction_of_trunc` for the genuine data**: the trace `tr₀` lives on
the full cone, the coordinate identity `hsw` uses the original cup formula `selCupFunT`, and the
duality hypothesis is supplied by `genuineSelmerDualityT` for the descended trace. PROVED. -/
theorem GenuineSwitch.adjunction_of_truncData (X : GenuineSwitch K S k M)
    (h543 : NekovarProp543T K) (p : ℕ) (hset : NekovarFiniteSetting K S p k) [Finite M]
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S k T)
    (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr₀ : (coneCx (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr₀ : ∀ z, tr₀ ((coneCx (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr₀)
    (horth : OrthogonalComplementsT K β hβ X.ΔS X.ΔR I
      ((galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I).trT tr₀ htr₀)
      ((galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I).trT_kills tr₀ htr₀))
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hsw : ∀ (t u : X.toQuasi.D.U.X 1) (s : (piCx X.US).X 2)
        (_ht : X.toQuasi.D.U.d 1 2 rfl t = 0)
        (_hu : X.toQuasi.D.U.d 1 2 rfl u = (piMap X.φ).f 2 2 rfl s)
        (ct cu : LinearMap.ker (X.toQuasi.Wrel.d 1 2 rfl))
        (_hct : ct.1 = X.toQuasi.gR.f 1 1 rfl t) (_hcu : cu.1 = X.toQuasi.gR.f 1 1 rfl u),
      tr₀ (selCupFunT (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I) 2 1 3 rfl
          ((0 : X.toQuasi.D.G.X 2), s, -(X.toQuasi.D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : X.toQuasi.D.G.X 1), t, (0 : X.toQuasi.D.L.X (1 - 1)))) =
        switchPairing ε σ J (X.toQuasi.eR (cls1 X.toQuasi.Wrel ct))
          (X.toQuasi.eR (cls1 X.toQuasi.Wrel cu))) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  switchAdjunction_of_trunc k X.toQuasi (piCx X.US) (piMap X.φ) X.hfg X.φ_inj X.g_surj X.ex
    (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I) tr₀ htr₀ ε σ J hε hσ hJ2
    (genuineSelmerDualityT K β hβ X.ΔS X.ΔR I _ _ h543 p hset hb hb' hT
      ((inducesIsoH3_trT_iff (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I) tr₀ htr₀).2 htr3) horth)
    hsw

/-- **The round-2 `GenuineSwitch.adjunction_of_prints` as a special case** of
`adjunction_of_printsT` (through `I.toTrunc` and the descended trace). PROVED. -/
theorem GenuineSwitch.adjunction_of_prints_special (X : GenuineSwitch K S k M)
    (h543 : NekovarProp543 K) (p : ℕ) (hset : NekovarFiniteSetting K S p k) [Finite M]
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S k T)
    (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr₀ : (galoisCompactT K S k β hβ X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr₀ : ∀ z, tr₀ ((galoisCompactT K S k β hβ X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr₀) (horth : OrthogonalComplements K β hβ X.ΔS X.ΔR I tr₀ htr₀)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hsw : X.SwitchCoordinates (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr₀ ε σ J) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  X.adjunction_of_printsT ((nekovarProp543T_iff K).2 h543) p hset β hβ hb hb' hT I.toTrunc
    ((galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I.toTrunc).trT tr₀ htr₀)
    ((galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I.toTrunc).trT_kills tr₀ htr₀)
    ((inducesIsoH3_trT_iff (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I.toTrunc) tr₀ htr₀).2 htr3)
    ((orthogonalComplements_iff_toTrunc K β hβ X.ΔS X.ΔR I tr₀ htr₀).1 horth) ε σ J hε hσ hJ2
    (fun t u s ht hu ct cu hct hcu =>
      (trT_selCupFun (galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I.toTrunc) tr₀ htr₀ 2 1 rfl _ _).trans
        (hsw t u s ht hu ct cu hct hcu))

end Switch

end ZInQ.Manuscript.RC.SelmerComplex
