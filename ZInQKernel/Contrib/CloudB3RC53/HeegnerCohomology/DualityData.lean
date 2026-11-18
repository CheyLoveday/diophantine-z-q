import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerPairing

/-!
# HeegnerCohomology, part 14: the local duality data at the derivative places

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3359–3364:

"For the isotropy diagrams, `U_v ⊗ U'_v` is free in degrees `0, 1, 2`, whereas the trace target
is `A[−2]`.  Its negative Hom groups vanish, so the restricted zero pairing has compatible
null-homotopies and the requisite 2-homotopies.  This constructs the local data required in
[Nekovář, 8.6.2.1–8.6.2.4] before using 8.6.4."

The duality data are those of the Selmer cup product (`PairedFunctional/SelmerPairing.lean`,
`SelPairData`: global and local cup products, compatibility with restriction, and an isotropy
homotopy `h` of degree `−1` with `dh + h d = ι ∪ ι'`), as used by `SelmerDuality/Duality.lean`.
Here (all `PROVED`):

* `SelPairData.ofZeroIsotropy`: when the local cup product vanishes on `ι U × ι' U'` (the
  restricted zero pairing), the zero map is an isotropy homotopy, giving the duality data;
* `negHom_eq_zero`: if `U, U'` vanish outside degrees `0, 1` (the `D⁰`-retaining finite/singular
  conditions at a derivative place: `D⁰` in degree `0`, `F_v`, `S_v` in degree `1`, tex 3300–3305)
  and the target vanishes outside degree `2` (`A[−2]`), every family of degree `−m`, `m ≥ 1`, from
  `U ⊗ U'` to the target is zero ("its negative Hom groups vanish");
* `isotropy_unique`: under these degree bounds every isotropy homotopy is zero and the restricted
  pairing must vanish; so the null-homotopy is unique, and the null-homotopies of two conditions
  related by a map `U₁ → U₂` over `L` are compatible (`isotropy_compatible`, the 2-homotopies being
  zero);
* `restrictedPairing_zero_of_degree`: in these degree bounds the restricted pairing can only be
  nonzero in bidegree `(1, 1)`, so its vanishing is the isotropy of the degree-one parts
  (`F_v ⊥ F_v`, `S_v ⊥ S_v` for the finite and singular conditions).

The global complexes (genuine Galois cochains of `G_{K,S}` in all degrees) and the global cup
product are not constructed here: they are the global fields of `SelData`/`SelPairData`, supplied
as `GLUE` inputs by the consumer, exactly as in `SelmerDuality/Duality.lean`.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open ZInQ.Contrib.CloudB3RC53.PairedFunctional

universe u

variable {S : Type u} [CommRing S]

/-- **The duality data from a restricted zero pairing** (tex 3360–3363), `PROVED`: given the
global and local cup products and their compatibility (the `GLUE` part), and the vanishing of the
local cup product on `ι U × ι' U'`, the zero map is an isotropy homotopy. -/
def SelPairData.ofZeroIsotropy {D D' : SelData S} (E EL : GCx S) (resE : GHom E EL)
    (cupG : GPair D.G D'.G E) (cupL : GPair D.L D'.L EL)
    (compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i')
      (hj : j = j') (hk : k = k') (a : D.G.X i) (b : D'.G.X j),
      resE.f k k' hk (cupG.P i j k h a b) =
        cupL.P i' j' k' h' (D.res.f i i' hi a) (D'.res.f j j' hj b))
    (hzero : ∀ (i j k : ℤ) (h : i + j = k) (u : D.U.X i) (v : D'.U.X j),
      cupL.P i j k h (D.ι.f i i rfl u) (D'.ι.f j j rfl v) = 0) :
    SelPairData D D' where
  E := E
  EL := EL
  resE := resE
  cupG := cupG
  cupL := cupL
  compat := compat
  hU _ _ _ _ := 0
  isotropy i _ j _ k k₁ _ _ _ _ u v := by
    simp only [LinearMap.zero_apply, map_zero, add_zero, smul_zero]
    exact (hzero i j k₁ _ u v).symm

/-- A complex vanishes outside an index set: its terms are subsingletons there. -/
def VanishesOutside (A : GCx S) (P : ℤ → Prop) : Prop := ∀ i, ¬ P i → Subsingleton (A.X i)

/-- **The negative Hom groups vanish** (tex 3360–3361), `PROVED`: if `U, U'` vanish outside
degrees `0, 1` and `T` vanishes outside degree `2`, every bilinear family
`U^i × U'^j → T^{i+j−m}` with `m ≥ 1` is zero. -/
theorem negHom_eq_zero {U U' T : GCx S} (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)) (hT : VanishesOutside T (fun k => k = 2))
    (m : ℤ) (hm : 1 ≤ m) (f : ∀ i j k : ℤ, i + j = k + m → U.X i →ₗ[S] U'.X j →ₗ[S] T.X k)
    (i j k : ℤ) (h : i + j = k + m) (u : U.X i) (v : U'.X j) : f i j k h u v = 0 := by
  by_cases hi : i = 0 ∨ i = 1
  · by_cases hj : j = 0 ∨ j = 1
    · have hk : ¬ k = 2 := by omega
      have := hT k hk
      exact Subsingleton.elim _ _
    · have := hU' j hj
      rw [Subsingleton.elim v 0, map_zero]
  · have := hU i hi
    rw [Subsingleton.elim u 0, map_zero, LinearMap.zero_apply]

/-- **The restricted pairing lives in bidegree `(1,1)`**, `PROVED`: under the degree bounds, the
restricted local pairing vanishes as soon as it vanishes on `U¹ × U'¹` (the isotropy of the
degree-one parts `F_v`, `S_v`). -/
theorem restrictedPairing_zero_of_degree {D D' : SelData S} {EL : GCx S}
    (cupL : GPair D.L D'.L EL)
    (hU : VanishesOutside D.U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside D'.U (fun i => i = 0 ∨ i = 1))
    (hT : VanishesOutside EL (fun k => k = 2))
    (h11 : ∀ (u : D.U.X 1) (v : D'.U.X 1),
      cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D'.ι.f 1 1 rfl v) = 0)
    (i j k : ℤ) (h : i + j = k) (u : D.U.X i) (v : D'.U.X j) :
    cupL.P i j k h (D.ι.f i i rfl u) (D'.ι.f j j rfl v) = 0 := by
  by_cases hi : i = 0 ∨ i = 1
  · by_cases hj : j = 0 ∨ j = 1
    · by_cases hk : k = 2
      · obtain rfl : i = 1 := by omega
        obtain rfl : j = 1 := by omega
        subst hk
        exact h11 u v
      · have := hT k hk
        exact Subsingleton.elim _ _
    · have := hU' j hj
      rw [Subsingleton.elim v 0, map_zero, map_zero]
  · have := hU i hi
    rw [Subsingleton.elim u 0, map_zero, map_zero, LinearMap.zero_apply]

/-- **Uniqueness of the null-homotopy** (tex 3361–3362), `PROVED`: under the degree bounds, every
isotropy homotopy of a `SelPairData` is zero, and the restricted local pairing vanishes. -/
theorem isotropy_unique {D D' : SelData S} (Q : SelPairData D D')
    (hU : VanishesOutside D.U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside D'.U (fun i => i = 0 ∨ i = 1))
    (hT : VanishesOutside Q.EL (fun k => k = 2)) :
    (∀ i j k (h : i + j = k + 1) u v, Q.hU i j k h u v = 0) ∧
      ∀ (i j k : ℤ) (h : i + j = k) (u : D.U.X i) (v : D'.U.X j),
        Q.cupL.P i j k h (D.ι.f i i rfl u) (D'.ι.f j j rfl v) = 0 := by
  have h0 : ∀ i j k (h : i + j = k + 1) u v, Q.hU i j k h u v = 0 :=
    fun i j k h u v => negHom_eq_zero hU hU' hT 1 le_rfl Q.hU i j k h u v
  refine ⟨h0, fun i j k h u v => ?_⟩
  have := Q.isotropy i (i + 1) j (j + 1) (k - 1) k (by omega) rfl rfl (by omega) u v
  rw [h0, h0, h0, map_zero, zero_add, zero_add, smul_zero] at this
  convert this.symm using 2 <;> first | rfl | (congr 1; omega)

/-- **Compatible null-homotopies and the 2-homotopies** (tex 3361–3363), `PROVED`: for a map of
local conditions `φ : U₁ → U₂` (over the same local complex), the null-homotopies of the two
isotropy diagrams agree after pulling back along `φ` (both are zero), so the required
2-homotopies (of degree `−2`) can be taken to be zero, and every degree `−2` family vanishes. -/
theorem isotropy_compatible {D₁ D₂ D' : SelData S} (Q₁ : SelPairData D₁ D') (Q₂ : SelPairData D₂ D')
    (φ : GHom D₁.U D₂.U)
    (hU₁ : VanishesOutside D₁.U (fun i => i = 0 ∨ i = 1))
    (hU₂ : VanishesOutside D₂.U (fun i => i = 0 ∨ i = 1))
    (hU' : VanishesOutside D'.U (fun i => i = 0 ∨ i = 1))
    (hT₁ : VanishesOutside Q₁.EL (fun k => k = 2)) (hT₂ : VanishesOutside Q₂.EL (fun k => k = 2)) :
    (∀ i j k (h : i + j = k + 1) u v,
      Q₂.hU i j k h (φ.f i i rfl u) v = 0 ∧ Q₁.hU i j k h u v = 0) ∧
    ∀ (f : ∀ i j k : ℤ, i + j = k + 2 → D₁.U.X i →ₗ[S] D'.U.X j →ₗ[S] Q₁.EL.X k)
      i j k (h : i + j = k + 2) u v, f i j k h u v = 0 :=
  ⟨fun i j k h u v => ⟨(isotropy_unique Q₂ hU₂ hU' hT₂).1 i j k h _ v,
      (isotropy_unique Q₁ hU₁ hU' hT₁).1 i j k h u v⟩,
    fun f i j k h u v => negHom_eq_zero hU₁ hU' hT₁ 2 (by norm_num) f i j k h u v⟩

/-- **Node: the local duality data at the derivative places** (tex 3359–3364), `PROVED`: for local
conditions concentrated in degrees `0, 1` and local target concentrated in degree `2`, with global
data supplied (`GLUE`), duality data `SelPairData` exist iff the restricted pairing vanishes in
bidegree `(1, 1)`; and then the isotropy homotopy is unique (zero). -/
def LocalDualityDataNode : Prop :=
  ∀ (S : Type u) [CommRing S] (D D' : SelData S) (E EL : GCx S) (resE : GHom E EL)
    (cupG : GPair D.G D'.G E) (cupL : GPair D.L D'.L EL)
    (compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i')
      (hj : j = j') (hk : k = k') (a : D.G.X i) (b : D'.G.X j),
      resE.f k k' hk (cupG.P i j k h a b) =
        cupL.P i' j' k' h' (D.res.f i i' hi a) (D'.res.f j j' hj b)),
    VanishesOutside D.U (fun i => i = 0 ∨ i = 1) →
    VanishesOutside D'.U (fun i => i = 0 ∨ i = 1) →
    VanishesOutside EL (fun k => k = 2) →
    (∀ (u : D.U.X 1) (v : D'.U.X 1), cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D'.ι.f 1 1 rfl v) = 0) →
    ∃ Q : SelPairData D D', Q.E = E ∧ Q.EL = EL ∧ ∀ i j k (h : i + j = k + 1) u v,
      Q.hU i j k h u v = 0

theorem localDualityDataNode_proof : LocalDualityDataNode.{u} := by
  intro S _ D D' E EL resE cupG cupL compat hU hU' hT h11
  refine ⟨SelPairData.ofZeroIsotropy E EL resE cupG cupL compat
    (restrictedPairing_zero_of_degree cupL hU hU' hT h11), rfl, rfl, fun _ _ _ _ _ _ => rfl⟩

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
