import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchAdjunction
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints

/-!
# Lane RC26 (round 2): the switch duality adjunction for the genuine Selmer complexes

Manuscript `diophantine_zq.tex`, tex 5055–5086 (Proposition `ex:limits-uniform-lower-bound`, the
switch exact sequences (5.5a)) and tex 5068–5075 ("localization's connecting map is its dual under
the strict/relaxed duality, so its kernel is both `U` and `U^⊥`"); Nekovář, *Selmer complexes*
(Astérisque 310, 2006), Proposition 6.3.3 (p. 142: the duality maps are compatible with the cone
triangles, by the explicit cup-product formulas) and Theorem 6.3.4 (p. 143).

At the switch place the strict and relaxed (derivative) local conditions `U_str ⊆ U_rel` of the text
give genuine Selmer complexes `C_str ⊆ C_rel` with quotient `W_rel` (the switch quotient,
`(F ⊕ S)[−1]` up to quasi-isomorphism). This file instantiates the other group's
`QuasiRelaxedLocalization` and `SwitchDualityAdjunction` with these genuine complexes:

* `GenuineSwitch`: genuine relaxed Galois local conditions `ΔR`, strict condition complexes `U_v`
  with injective maps `φ_v : U_v → ΔR.U v` (the strict conditions `ΔS`, with the composite maps to
  the local complexes), the switch quotient `g : ⊕_v ΔR.U v → W_rel` (surjective, kernel the image
  of `φ`), and coordinates `H¹(W_rel) ≃ k² × k²`;
* `GenuineSwitch.toQuasi : QuasiRelaxedLocalization k`, `GenuineSwitch.Dstr` (definitionally the
  genuine Selmer data of `ΔS`), the connecting map `GenuineSwitch.δ` and its exactness
  `GenuineSwitch.hex` (PROVED, from the short exact sequence `0 → C_str → C_rel → W_rel → 0`);
* `GenuineSwitch.adjunction` (PROVED, by `switchAdjunctionFromDuality_proof`, the cochain-level
  form of Nekovář 6.3.3): `SwitchDualityAdjunction` for the genuine complexes, given the Selmer
  duality quasi-isomorphism `γ : C_str → Hom(C_rel, k)[−3]` (Nekovář 6.3.4) and the identification
  of the local residue pairing on `H¹(W_rel)` with the switch pairing `β(x, y) = ε e₂(x, J y)` in
  the coordinates (tex 2816–2818);
* `GenuineSwitch.adjunction_of_prints`: over a finite residue field, the duality quasi-isomorphism
  is supplied by the PRINT `NekovarProp543` and the orthogonality of the local conditions
  (`genuineSelmerDuality`);
* `GenuineSwitch.localizationDualityInput`: the other group's `LocalizationDualityInput` for the
  genuine relaxed localization image (via their `localizationDualityInput_of_adjunction`);
* non-vacuity of `GenuineSwitch`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Manuscript.RC.Uniform

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **Genuine switch data** (tex 5055–5075): genuine relaxed local conditions `ΔR`, strict
condition complexes `US v` with injective maps `φ v : US v → ΔR.U v`, the switch quotient
`g : ⊕_v ΔR.U v → W` (degreewise surjective with kernel the image of `φ`), and coordinates
`eR : H¹(W) ≃ k² × k²` (`F ⊕ S`). -/
structure GenuineSwitch where
  ΔR : GaloisLocalConditions K S k M
  US : Places K S → GCx k
  φ : ∀ v, GHom (US v) (ΔR.U v)
  W : GCx k
  g : GHom (galoisSelData K S k M ΔR).U W
  hfg : ∀ n (u : (piCx US).X n), g.f n n rfl ((piMap φ).f n n rfl u) = 0
  φ_inj : ∀ n, Function.Injective ((piMap φ).f n n rfl)
  g_surj : ∀ n, Function.Surjective (g.f n n rfl)
  ex : ∀ n (u : (galoisSelData K S k M ΔR).U.X n), g.f n n rfl u = 0 →
    ∃ u', (piMap φ).f n n rfl u' = u
  eR : W.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)

namespace GenuineSwitch

variable {K S k M} (X : GenuineSwitch K S k M)

/-- The strict local conditions `ΔS`: the complexes `US v` with the composite maps
`US v → ΔR.U v → C(G_v, M)`. -/
def ΔS : GaloisLocalConditions K S k M := ⟨X.US, fun v => ghomComp (X.φ v) (X.ΔR.i v)⟩

/-- **The genuine relaxed localization** (`QuasiRelaxedLocalization`): the genuine relaxed Selmer
data, the switch quotient and its coordinates. -/
def toQuasi : QuasiRelaxedLocalization k := ⟨galoisSelData K S k M X.ΔR, X.W, X.g, X.eR⟩

/-- The strict Selmer data `C_str` (the restriction of the relaxed data along `φ`; definitionally
the genuine Selmer data of `ΔS`). -/
abbrev Dstr : SelData k := restrictData X.toQuasi.D (piMap X.φ)

theorem Dstr_eq : X.Dstr = galoisSelData K S k M X.ΔS := rfl

/-- **The connecting map** `δ : H¹(W_rel) → H²(C_str)` of `0 → C_str → C_rel → W_rel → 0`. -/
def δ : X.toQuasi.Wrel.toCC.homology 1 →ₗ[k] (selCx X.Dstr).toCC.homology 2 :=
  switchDelta X.toQuasi (piMap X.φ) X.hfg X.φ_inj X.g_surj X.ex

/-- Exactness at `H¹(W_rel)`: `im H¹(λ) = ker δ`. PROVED. -/
theorem hex : LinearMap.range (H1 (quotMap X.toQuasi.D X.toQuasi.gR)) = LinearMap.ker X.δ :=
  switchDelta_exact X.toQuasi (piMap X.φ) X.hfg X.φ_inj X.g_surj X.ex

/-- The local residue pairing hypothesis (tex 2816–2818, "in the chosen coordinates this is the
pairing `β(x, y) = ε⟨x, J y⟩`"): for degree-one relaxed condition cochains `t` (a cocycle) and `u`
with `du = φ s`, the trace of the Selmer cup product of `(0, s, −ι u)` and `(0, t, 0)` — a local
expression, `tr(0, h(s, t) − ι u ∪ ι t)` — is the switch pairing of the classes of `g t`, `g u` in
the coordinates. -/
def SwitchCoordinates (Q : SelPairData X.Dstr X.toQuasi.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) : Prop :=
  ∀ (t u : X.toQuasi.D.U.X 1) (s : (piCx X.US).X 2) (_ht : X.toQuasi.D.U.d 1 2 rfl t = 0)
    (_hu : X.toQuasi.D.U.d 1 2 rfl u = (piMap X.φ).f 2 2 rfl s)
    (ct cu : LinearMap.ker (X.toQuasi.Wrel.d 1 2 rfl))
    (_hct : ct.1 = X.toQuasi.gR.f 1 1 rfl t) (_hcu : cu.1 = X.toQuasi.gR.f 1 1 rfl u),
    tr (selCupFun Q 2 1 3 rfl ((0 : X.toQuasi.D.G.X 2), s,
        -(X.toQuasi.D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : X.toQuasi.D.G.X 1), t, (0 : X.toQuasi.D.L.X (1 - 1)))) =
      switchPairing ε σ J (X.toQuasi.eR (cls1 X.toQuasi.Wrel ct))
        (X.toQuasi.eR (cls1 X.toQuasi.Wrel cu))

/-- **The switch duality adjunction for the genuine complexes** (Nekovář 6.3.3 in cochain form,
`switchAdjunctionFromDuality_proof`; PROVED): if the Selmer duality map `C_str → Hom(C_rel, k)[−3]` of the
pairing data `Q` is a quasi-isomorphism (Nekovář 6.3.4) and the local residue pairing is the switch
pairing in the coordinates, then the other group's `SwitchDualityAdjunction` holds for the genuine
relaxed localization and the genuine connecting map. -/
theorem adjunction (Q : SelPairData X.Dstr X.toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : X.SwitchCoordinates Q tr ε σ J) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  switchAdjunctionFromDuality_proof k X.toQuasi (piCx X.US) (piMap X.φ) X.hfg X.φ_inj X.g_surj
    X.ex Q tr htr ε σ J hε hσ hJ2 hγ hsw

/-- **`LocalizationDualityInput` for the genuine relaxed localization image** (tex 5068–5075):
under the hypotheses of `adjunction`, the image `U` of `H¹(C_rel) → H¹(W_rel) ≃ F ⊕ S` is its own
annihilator for the switch pairing (the other group's `localizationDualityInput_of_adjunction`). -/
theorem localizationDualityInput (Q : SelPairData X.Dstr X.toQuasi.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : X.SwitchCoordinates Q tr ε σ J) :
    LocalizationDualityInput ε σ J hε hσ hJ2 X.toQuasi.U :=
  localizationDualityInput_of_adjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex
    (X.adjunction Q tr htr ε σ J hε hσ hJ2 hγ hsw)

end GenuineSwitch

/-! ### Over a finite residue field: the duality quasi-isomorphism from the PRINTs -/

section Finite

variable {K S k M}
variable {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **The switch adjunction from the PRINTs over a finite residue field** (`k` finite of
characteristic `p`, Nekovář's finite setting with `R = k`): for genuine switch data, a perfect
self-pairing `β : M × M → T`, `T ≅ k(1)`, isotropy data for (strict, relaxed), a trace inducing
`H³_c ≅ k`, the orthogonality of the strict and relaxed local conditions (Nekovář 6.2.7) and the
switch coordinates, `SwitchDualityAdjunction` holds — the duality quasi-isomorphism is
`genuineSelmerDuality` (from `NekovarProp543`). -/
theorem GenuineSwitch.adjunction_of_prints (X : GenuineSwitch K S k M)
    (h543 : NekovarProp543 K) (p : ℕ)
    (hset : NekovarFiniteSetting K S p k) [Finite M]
    (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S k T)
    (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (galoisCompactT K S k β hβ X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactT K S k β hβ X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (horth : OrthogonalComplements K β hβ X.ΔS X.ΔR I tr htr)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hsw : X.SwitchCoordinates (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr ε σ J) :
    SwitchDualityAdjunction X.toQuasi X.Dstr ε σ J hε hσ hJ2 X.δ X.hex :=
  X.adjunction (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr htr ε σ J hε hσ hJ2
    (genuineSelmerDuality K β hβ X.ΔS X.ΔR I tr htr h543 p hset hb hb' hT htr3 horth) hsw

end Finite

/-! ### Non-vacuity -/

section NonVacuity

variable {k : Type} [Field k]

/-- The complex with `V` in every degree and zero differentials. -/
def constCx (V : Type) [AddCommGroup V] [Module k V] : GCx k where
  X _ := ModuleCat.of k V
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

theorem constCx_toCC_d (V : Type) [AddCommGroup V] [Module k V] (i j : ℤ) :
    (constCx (k := k) V).toCC.d i j = 0 := by
  by_cases h : i + 1 = j
  · ext x
    exact GCx.toCC_d_hom (constCx (k := k) V) i j h x
  · exact (constCx (k := k) V).toCC.shape i j h

/-- `H¹` of the complex with zero differentials is `V`. -/
def constCxH1 (V : Type) [AddCommGroup V] [Module k V] :
    (constCx (k := k) V).toCC.homology 1 ≃ₗ[k] V :=
  (((constCx (k := k) V).toCC.isoHomologyπ 0 1 (by simp) (constCx_toCC_d V 0 1)).symm ≪≫
    (constCx (k := k) V).toCC.iCyclesIso 1 2 (by simp) (constCx_toCC_d V 1 2)).toLinearEquiv

variable (K : Type) [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K))

/-- **Non-vacuity of `GenuineSwitch`**: for `S = {q}` and the trivial coefficient module, the
relaxed condition `F ⊕ S = k² × k²` (in every degree, zero differential, zero map to the local
complex), the strict condition `0`, and the switch quotient the identity onto `F ⊕ S`. -/
def exGenuineSwitch :
    GenuineSwitch K {q} k (TrivMod (GKS K {q}) PUnit) where
  ΔR := ⟨fun _ => constCx ((Fin 2 → k) × (Fin 2 → k)), fun _ => zeroGHom _ _⟩
  US _ := zeroCx k
  φ _ := zeroGHom _ _
  W := constCx ((Fin 2 → k) × (Fin 2 → k))
  g :=
    { f := fun n m h => by
        subst h
        exact LinearMap.proj (R := k)
          (φ := fun _ : Places K {q} => ((Fin 2 → k) × (Fin 2 → k))) ⟨q, rfl⟩
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

end NonVacuity

end ZInQ.Manuscript.RC.SelmerComplex
