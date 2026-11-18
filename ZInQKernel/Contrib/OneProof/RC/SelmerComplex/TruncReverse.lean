import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncPrints
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.CupOne
import ZInQKernel.Contrib.CloudB3RC53.Hsw.Descent

/-!
# Lane RC26 (round 4): reverse isotropy for the genuine switch data

Manuscript `diophantine_zq.tex`, tex 2790–2818 (the switch coordinates: descent of
`tr((0, s, −ι u) ∪ (0, t, 0))` to `H¹(W_rel)`) and tex 5068–5075 (the derivative conditions);
Nekovář, *Selmer complexes* (Astérisque 310), 3.4.5 (graded commutativity of cup products up to
homotopy) and 6.2–6.3.

The other group (`Hsw/Descent.lean`) showed that the switch coordinate claim needs `StrictOrth`,
which does not follow from Selmer pairing data (`Hsw.strictOrth_counterexample`), and that the
other group's `Hsw.ReverseIsotropy` — a homotopy on `U_rel × U_str` agreeing with `h` on
strict × strict — suffices. This file supplies it for the genuine `τ≥2` data:

* the cup-1 homotopy of the continuous cup product in degree `(1, 1)` (`CupOne.lean`:
  `a ∪ b + ε (b ∪ a) = d H₁₁(a, b) + H₂₁(da, b) + H₁₂(a, db)` for an `ε`-symmetric equivariant
  pairing, PROVED) turns the forward truncated isotropy homotopy `h` into a reverse one:
  `h'₂₁(u, t') = ε h(t', u) + H₂₁(ι u, ι φ t')`, `h'₁₂(u, s') = ε h(s', u) − H₁₂(ι u, ι φ s')`;
* the reverse isotropy identity then holds modulo `d(C¹)` (`revIso_place`, PROVED), and the
  agreement with `h` on strict × strict is **exactly** the condition `StrictSymm` (stated as GLUE,
  exact shape: `h(s, φ t') − ε h(t', φ s) − H₂₁(ι φ s, ι φ t') ∈ d(C¹_cont(G_v, T))`);
* `reverseIsotropyOfCupOne` (PROVED): `StrictSymm` gives the other group's
  `Hsw.ReverseIsotropy X.toQuasi.D (⊕ US) φ (galoisPairDataT … I)` for the `τ≥2` data;
* `strictSymm_of_subsingleton` (PROVED): `StrictSymm` holds when the strict conditions have no
  degree-one cochains — the text's strict condition `D⁰` is concentrated in degree `0`
  (tex 5068–5072), so for it reverse isotropy is PROVED;
* `SwitchTruncIsotropy` (truncated isotropy data together with the reverse field), its
  `strictOrth` and the descent `exists_residuePairing` (via the other group's
  `strictOrth_of_reverseIsotropy` and `exists_residuePairing_of_reverseIsotropy`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Manuscript.RC.Uniform

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
  [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]
  (X : GenuineSwitch K S k M) (β : M →ₗ[k] M →ₗ[k] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)

/-- The forward truncated isotropy homotopy at a place, with the strict condition complexes
written as `US v` (definitionally `ΔS.U v`). -/
def fwdH (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (v : Places K S) (i j l : ℤ)
    (h : i + j = l + 1) :
    (X.US v).X i →ₗ[k] (X.ΔR.U v).X j →ₗ[k]
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).X l :=
  I.h v i j l h

/-- **The reverse homotopy in degrees `(2, 1) → 2`, at a place** (cup-1 construction):
`h'₂₁(u, t') = ε h(t', u) + H₂₁(ι u, ι φ t')`. -/
def revH21 (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k) (v : Places K S) :
    (X.ΔR.U v).X 2 →ₗ[k] (X.US v).X 1 →ₗ[k]
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).X 2 :=
  ε • (fwdH X β hβ I v 1 2 2 rfl).flip +
    (localCupOne21 k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
      (continuous_pairing β) v).compl₁₂ ((X.ΔR.i v).f 2 2 rfl)
      (((X.ΔR.i v).f 1 1 rfl).comp ((X.φ v).f 1 1 rfl))

/-- **The reverse homotopy in degrees `(1, 2) → 2`, at a place** (cup-1 construction):
`h'₁₂(u, s') = ε h(s', u) − H₁₂(ι u, ι φ s')`. -/
def revH12 (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k) (v : Places K S) :
    (X.ΔR.U v).X 1 →ₗ[k] (X.US v).X 2 →ₗ[k]
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).X 2 :=
  ε • (fwdH X β hβ I v 2 1 2 rfl).flip -
    (localCupOne12 k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
      (continuous_pairing β) v).compl₁₂ ((X.ΔR.i v).f 1 1 rfl)
      (((X.ΔR.i v).f 2 2 rfl).comp ((X.φ v).f 2 2 rfl))

/-- **GLUE (exact shape): strict symmetry of the forward homotopy.** At every place, for strict
cochains `s` (degree two) and `t'` (degree one),
`h(s, φ t') − ε h(t', φ s) − H₂₁(ι φ s, ι φ t') ∈ d(C¹_cont(G_v, T))`: the forward isotropy
homotopy is `ε`-symmetric on strict × strict up to the cup-1 term, modulo coboundaries (the `τ≥2`
form of the agreement field `compat` of `Hsw.ReverseIsotropy`). -/
def StrictSymm (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k) : Prop :=
  ∀ (v : Places K S) (s : (X.US v).X 2) (t' : (X.US v).X 1),
    I.h v 2 1 2 rfl s ((X.φ v).f 1 1 rfl t') - ε • I.h v 1 2 2 rfl t' ((X.φ v).f 2 2 rfl s) -
        localCupOne21 k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β
          (continuous_pairing β) v ((X.ΔR.i v).f 2 2 rfl ((X.φ v).f 2 2 rfl s))
          ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl t')) ∈
      LinearMap.range ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T v).d 1 2 rfl)

/-- **`StrictSymm` holds when the strict conditions have no degree-one cochains** (e.g. the text's
strict derivative condition `D⁰`, concentrated in degree `0`, tex 5068–5072). PROVED. -/
theorem strictSymm_of_subsingleton (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k)
    (hUS : ∀ v, Subsingleton ((X.US v).X 1)) : StrictSymm X β hβ I ε := by
  intro v s t'
  have h1 : (X.φ v).f 1 1 rfl t' = 0 := by rw [Subsingleton.elim t' 0]; exact map_zero _
  have h2 : I.h v 1 2 2 rfl t' = 0 := by rw [Subsingleton.elim t' 0]; exact map_zero _
  simp only [h1, h2, map_zero, LinearMap.zero_apply, smul_zero, sub_zero]
  exact Submodule.zero_mem _

/-- **The reverse isotropy identity at a place, modulo coboundaries** (cup-1 homotopy plus the
forward truncated isotropy in bidegree `(1, 1)`): for `u ∈ U_rel¹`, `t' ∈ U_str¹`,
`h'₂₁(du, t') − h'₁₂(u, dt') − ι u ∪ ι φ t' ∈ d(C¹_cont(G_v, T))`. PROVED. -/
theorem revIso_place (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k)
    (hε : ∀ a a' : M, β a a' = ε • β a' a) (v : Places K S) (u : (X.ΔR.U v).X 1)
    (t' : (X.US v).X 1) :
    revH21 X β hβ I ε v ((X.ΔR.U v).d 1 2 rfl u) t' - revH12 X β hβ I ε v u ((X.US v).d 1 2 rfl t') -
        (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
          (continuous_pairing β) v).P 1 1 2 rfl ((X.ΔR.i v).f 1 1 rfl u)
          ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl t')) ∈
      LinearMap.range ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T v).d 1 2 rfl) := by
  obtain ⟨w, hw⟩ := I.isotropy₂ v 1 2 1 2 rfl rfl rfl t' u
  have hc := localPair_comm_homotopy k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ (continuous_pairing β) ε hε v ((X.ΔR.i v).f 1 1 rfl u)
    ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl t'))
  have hda := (X.ΔR.i v).comm 1 2 1 2 rfl rfl rfl rfl u
  have hdb : (X.ΔR.i v).f 2 2 rfl ((X.φ v).f 2 2 rfl ((X.US v).d 1 2 rfl t')) =
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v).d 1 2
        rfl ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl t')) := by
    rw [(X.φ v).comm 1 2 1 2 rfl rfl rfl rfl t', (X.ΔR.i v).comm 1 2 1 2 rfl rfl rfl rfl]
  rw [← hda, ← hdb] at hc
  have hs : sgn 1 = -1 := by simp [sgn]
  have hw' : (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T
      v).d 1 2 rfl w = fwdH X β hβ I v 2 1 2 rfl ((X.US v).d 1 2 rfl t') u +
        -(fwdH X β hβ I v 1 2 2 rfl t' ((X.ΔR.U v).d 1 2 rfl u)) -
        (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
          (continuous_pairing β) v).P 1 1 2 rfl ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl t'))
          ((X.ΔR.i v).f 1 1 rfl u) := by
    rw [hw, hs, neg_one_zsmul]
    rfl
  refine ⟨-(ε • w) - localCupOne11 k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β (continuous_pairing β) v ((X.ΔR.i v).f 1 1 rfl u)
    ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl t')), ?_⟩
  rw [map_sub, map_neg, map_smul, hw']
  simp only [revH21, revH12, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.flip_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
  linear_combination (norm := module) hc

/-- **Membership in the coboundaries of the product, place by place.** -/
theorem mem_range_localSum (x : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X 2)
    (h : ∀ v, x v ∈ LinearMap.range ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl)) :
    x ∈ LinearMap.range ((localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).d 1 2 rfl) := by
  choose w hw using h
  exact ⟨fun v => w v, funext fun v => hw v⟩

/-- The reverse homotopy `h'₂₁` on the products over the places. -/
def revPi21 (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k) :
    (piCx X.ΔR.U).X 2 →ₗ[k] (piCx X.US).X 1 →ₗ[k]
      (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T).X 2 :=
  LinearMap.mk₂ k (fun u t' v => revH21 X β hβ I ε v (u v) (t' v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact LinearMap.map_smul₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun _ _ _ => by funext v; exact map_smul _ _ _)

/-- The reverse homotopy `h'₁₂` on the products over the places. -/
def revPi12 (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k) :
    (piCx X.ΔR.U).X 1 →ₗ[k] (piCx X.US).X 2 →ₗ[k]
      (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T).X 2 :=
  LinearMap.mk₂ k (fun u s' v => revH12 X β hβ I ε v (u v) (s' v))
    (fun _ _ _ => by funext v; exact LinearMap.map_add₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact LinearMap.map_smul₂ _ _ _ _)
    (fun _ _ _ => by funext v; exact map_add _ _ _)
    (fun _ _ _ => by funext v; exact map_smul _ _ _)

omit [NumberField K] in
/-- In `τ≥2 A` (degree two): `[x] + (−1)¹ [y] = [z]` as soon as `x − y − z ∈ d(A¹)`. -/
theorem mkQ_add_sgn_one (A : GCx k) (x y z : A.X 2)
    (h : x - y - z ∈ LinearMap.range (A.d 1 2 rfl)) :
    (truncSub A 2).mkQ x + sgn 1 • (truncSub A 2).mkQ y = (truncSub A 2).mkQ z := by
  have hs : sgn 1 = -1 := by simp [sgn]
  rw [hs, neg_one_zsmul, ← map_neg, ← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, truncSub_of_eq A rfl]
  have e : x + -y - z = x - y - z := by abel
  rw [e]
  exact h

omit [NumberField K] in
/-- In `τ≥2 A` (degree two): `[x] = [y]` as soon as `x − y ∈ d(A¹)`. -/
theorem mkQ_eq_of_sub (A : GCx k) (x y : A.X 2) (h : x - y ∈ LinearMap.range (A.d 1 2 rfl)) :
    (truncSub A 2).mkQ x = (truncSub A 2).mkQ y := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, truncSub_of_eq A rfl]
  exact h

/-- **Reverse isotropy for the genuine `τ≥2` switch data from the cup-1 homotopy** (Nekovář 3.4.5
and 6.2–6.3; tex 2790–2818): for an `ε`-symmetric pairing, the forward truncated isotropy
homotopy `I` and `StrictSymm`, the reverse homotopies `h'₁₁ = 0` (degree one dies in `τ≥2`),
`h'₂₁`, `h'₁₂` form the other group's `Hsw.ReverseIsotropy` for the genuine `τ≥2` pairing data.
PROVED. -/
def reverseIsotropyOfCupOne (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k)
    (hε : ∀ a a' : M, β a a' = ε • β a' a) (hsym : StrictSymm X β hβ I ε) :
    ZInQ.Contrib.CloudB3RC53.Hsw.ReverseIsotropy X.toQuasi.D (piCx X.US) (piMap X.φ)
      (galoisPairDataT K S k β hβ X.ΔS X.ΔR I) where
  h11 := 0
  h21 := (revPi21 X β hβ I ε).compr₂
    (truncSub (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) 2).mkQ
  h12 := (revPi12 X β hβ I ε).compr₂
    (truncSub (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) 2).mkQ
  iso u t' := by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero, zero_add]
    exact mkQ_add_sgn_one _ (revPi21 X β hβ I ε ((piCx X.ΔR.U).d 1 2 rfl u) t')
      (revPi12 X β hβ I ε u ((piCx X.US).d 1 2 rfl t'))
      ((localSumPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
        (continuous_pairing β)).P 1 1 2 rfl ((piMap X.ΔR.i).f 1 1 rfl u)
        ((piMap X.ΔR.i).f 1 1 rfl ((piMap X.φ).f 1 1 rfl t')))
      (mem_range_localSum _ fun v => revIso_place X β hβ I ε hε v (u v) (t' v))
  compat s t' := by
    have hpl : ∀ v, I.h v 2 1 2 rfl (s v) ((X.φ v).f 1 1 rfl (t' v)) -
        revH21 X β hβ I ε v ((X.φ v).f 2 2 rfl (s v)) (t' v) ∈
          LinearMap.range ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T v).d 1 2 rfl) := fun v => by
      have e : revH21 X β hβ I ε v ((X.φ v).f 2 2 rfl (s v)) (t' v) =
          ε • I.h v 1 2 2 rfl (t' v) ((X.φ v).f 2 2 rfl (s v)) +
            localCupOne21 k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
              β (continuous_pairing β) v ((X.ΔR.i v).f 2 2 rfl ((X.φ v).f 2 2 rfl (s v)))
              ((X.ΔR.i v).f 1 1 rfl ((X.φ v).f 1 1 rfl (t' v))) :=
        rfl
      rw [e, ← sub_sub]
      exact hsym v (s v) (t' v)
    exact mkQ_eq_of_sub _ (fun v => I.h v 2 1 2 rfl (s v) ((X.φ v).f 1 1 rfl (t' v)))
      (revPi21 X β hβ I ε ((piMap X.φ).f 2 2 rfl s) t') (mem_range_localSum _ hpl)

/-- **Truncated isotropy data for the switch with the reverse field** (the request of the other
group's `Hsw/Descent.lean`): forward `τ≥2` isotropy data for (strict, relaxed) together with the
other group's `Hsw.ReverseIsotropy` for the genuine `τ≥2` pairing data. -/
structure SwitchTruncIsotropy where
  /-- Forward truncated isotropy data for (strict, relaxed). -/
  I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR
  /-- The reverse isotropy field. -/
  rev : ZInQ.Contrib.CloudB3RC53.Hsw.ReverseIsotropy X.toQuasi.D (piCx X.US) (piMap X.φ)
    (galoisPairDataT K S k β hβ X.ΔS X.ΔR I)

/-- **Construction from the cup-1 homotopy** (PROVED), given the GLUE condition `StrictSymm`. -/
def SwitchTruncIsotropy.ofCupOne (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR) (ε : k)
    (hε : ∀ a a' : M, β a a' = ε • β a' a) (hsym : StrictSymm X β hβ I ε) :
    SwitchTruncIsotropy X β hβ :=
  ⟨I, reverseIsotropyOfCupOne X β hβ I ε hε hsym⟩

/-- **For strict conditions without degree-one cochains (the text's `D⁰`) the reverse field is
PROVED**: no GLUE remains. -/
def SwitchTruncIsotropy.ofStrictDegreeZero (I : GaloisTruncIsotropyData K S k β hβ X.ΔS X.ΔR)
    (ε : k) (hε : ∀ a a' : M, β a a' = ε • β a' a) (hUS : ∀ v, Subsingleton ((X.US v).X 1)) :
    SwitchTruncIsotropy X β hβ :=
  SwitchTruncIsotropy.ofCupOne X β hβ I ε hε (strictSymm_of_subsingleton X β hβ I ε hUS)

/-- **`StrictOrth` for the genuine `τ≥2` data** (via the other group's
`strictOrth_of_reverseIsotropy`). PROVED. -/
theorem SwitchTruncIsotropy.strictOrth (P : SwitchTruncIsotropy X β hβ)
    (tr : (galoisCompactTT K S k β hβ X.ΔS X.ΔR P.I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactTT K S k β hβ X.ΔS X.ΔR P.I).d 2 3 rfl z) = 0) :
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictOrth X.toQuasi.D (piCx X.US) (piMap X.φ)
      (galoisPairDataT K S k β hβ X.ΔS X.ΔR P.I) tr :=
  ZInQ.Contrib.CloudB3RC53.Hsw.strictOrth_of_reverseIsotropy X.toQuasi.D (piCx X.US) (piMap X.φ)
    _ tr htr P.rev

/-- **The descent of the switch coordinate pairing to `H¹(W_rel)` for the genuine `τ≥2` data**
(tex 2790–2818; via the other group's `exists_residuePairing_of_reverseIsotropy`). PROVED. -/
theorem SwitchTruncIsotropy.exists_residuePairing (P : SwitchTruncIsotropy X β hβ)
    (tr : (galoisCompactTT K S k β hβ X.ΔS X.ΔR P.I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactTT K S k β hβ X.ΔS X.ΔR P.I).d 2 3 rfl z) = 0) :
    ∃ Pf, ZInQ.Contrib.CloudB3RC53.Hsw.ResiduePairing X.toQuasi (piCx X.US) (piMap X.φ)
      (galoisPairDataT K S k β hβ X.ΔS X.ΔR P.I) tr Pf :=
  ZInQ.Contrib.CloudB3RC53.Hsw.exists_residuePairing_of_reverseIsotropy X.toQuasi (piCx X.US)
    (piMap X.φ) _ tr X.hfg X.φ_inj X.g_surj X.ex htr P.rev

end ZInQ.Manuscript.RC.SelmerComplex
